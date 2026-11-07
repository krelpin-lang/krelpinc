use std::collections::{HashSet, VecDeque};

use krelpin_errors::{DiagCtxt, Diagnostic};
use krelpin_mir::{
    BasicBlock, Body, BodySource, Local, Operand, Place, PlaceBase, PlaceElem, ReturnSource,
    StatementKind, TerminatorKind, Unwind, place_locals_of, rvalue_locals_of,
    terminator_input_locals_of,
};
use krelpin_span::Span;
use krelpin_typeck::{Callee, Ty};

use crate::bitset::BitSet;
use crate::dataflow::{Forward, Location, solve};
use crate::forwarded::Forwarded;
use crate::init::{MoveData, MoveKind, MoveOut};
use crate::liveness::Liveness;
use crate::loans::{Holdings, LoanData, LoanOrigin};
use crate::places::{
    self, Access, PlacePath, PlaceTys, base_local, has_deref, operand_place, overlaps,
};

pub(crate) struct Checker<'a, 'tcx> {
    body: &'a Body,
    tys: &'a PlaceTys<'a, 'tcx>,
    moves: MoveData,
    loans: LoanData<'a, 'tcx>,
    forwarded: Forwarded,
    liveness: Liveness,
    dcx: &'a DiagCtxt,
    reported: HashSet<(Span, String)>,
    reported_places: HashSet<(Location, String)>,
}

impl<'a, 'tcx> Checker<'a, 'tcx> {
    pub(crate) fn new(body: &'a Body, tys: &'a PlaceTys<'a, 'tcx>, dcx: &'a DiagCtxt) -> Self {
        Checker {
            body,
            tys,
            moves: MoveData::collect(body),
            loans: LoanData::collect(body, tys),
            forwarded: Forwarded::compute(body, tys),
            liveness: Liveness::compute(body),
            dcx,
            reported: HashSet::new(),
            reported_places: HashSet::new(),
        }
    }

    pub(crate) fn run(mut self) {
        let init_entries = solve(&self.moves, self.body);
        let loan_entries = solve(&self.loans, self.body);
        for (index, data) in self.body.blocks.iter().enumerate() {
            let block = BasicBlock(index as u32);
            let mut init = init_entries[index].clone();
            let mut held = loan_entries[index].clone();
            for (index, statement) in data.statements.iter().enumerate() {
                let location = Location { block, index };
                self.check_statement(location, &statement.kind, statement.span, &init, &held);
                self.moves.statement(&mut init, location, &statement.kind);
                self.loans.statement(&mut held, location, &statement.kind);
            }
            let location = Location {
                block,
                index: data.statements.len(),
            };
            self.check_terminator(
                location,
                &data.terminator.kind,
                data.terminator.span,
                &init,
                &held,
            );
        }
    }

    fn check_statement(
        &mut self,
        location: Location,
        kind: &StatementKind,
        span: Span,
        init: &BitSet,
        held: &Holdings,
    ) {
        match kind {
            StatementKind::Assign(_) | StatementKind::FakeRead(_) => {
                for (place, access) in places::statement_accesses(kind) {
                    self.check_access(location, span, &place, access, init, held);
                }
            }
            StatementKind::StorageDead(local) => {
                let live = self.live_loans(location, held);
                let dangling = live.iter().find(|&loan| {
                    let place = &self.loans.loans[loan].place;
                    base_local(place) == Some(*local) && !has_deref(place)
                });
                if let Some(loan) = dangling {
                    self.report_dangling(loan, span);
                }
            }
            StatementKind::StorageLive(_) => {}
        }
    }

    fn check_terminator(
        &mut self,
        location: Location,
        kind: &TerminatorKind,
        span: Span,
        init: &BitSet,
        held: &Holdings,
    ) {
        for (place, access) in places::terminator_accesses(kind) {
            self.check_access(location, span, &place, access, init, held);
        }
        match kind {
            TerminatorKind::Call { callee, args, .. } => {
                let has_receiver = args.len() > callee.method.params.len();
                if has_receiver && self.loans.reaches_static(held, &args[0]) {
                    self.check_kept_in_static(callee, args, span, held);
                }
                for (index, arg) in args.iter().enumerate().skip(usize::from(has_receiver)) {
                    let param = index - usize::from(has_receiver);
                    let detached = callee
                        .method
                        .storage
                        .get(param)
                        .is_some_and(|storage| storage.detached);
                    if !detached {
                        continue;
                    }
                    let loans = self.loans.operand_loans(held, arg);
                    if let Some(loan) = loans.iter().next() {
                        self.report_detached(loan, callee.method.name.name, span);
                        break;
                    }
                    let forwarded = operand_place(arg)
                        .and_then(base_local)
                        .and_then(|local| self.forwarded.source(local))
                        .filter(|&param| !self.is_detached_param(param));
                    if let Some(param) = forwarded {
                        self.report_forwarded(param, callee.method.name.name, span);
                        break;
                    }
                }
            }
            TerminatorKind::Return => {
                let mut escaping = held[Local::RETURN.index()].clone();
                for arg in self.body.args() {
                    if matches!(self.body.local(arg).ty, Ty::Ref { mutable: true, .. }) {
                        escaping.union(&held[arg.index()]);
                    }
                }
                if let Some(loan) = escaping.iter().find(|&loan| self.is_local_data(loan)) {
                    self.report_escape(loan, span, "returned");
                } else {
                    self.check_ret_sources(&held[Local::RETURN.index()], span);
                    self.check_stores(held, span);
                }
            }
            TerminatorKind::Throw {
                value,
                unwind: Unwind::Resume,
            } => {
                let escaping = operand_place(value)
                    .and_then(base_local)
                    .map(|local| held[local.index()].clone());
                let loan = escaping
                    .and_then(|escaping| escaping.iter().find(|&loan| self.is_local_data(loan)));
                if let Some(loan) = loan {
                    self.report_escape(loan, span, "thrown");
                }
            }
            _ => {}
        }
    }

    fn check_ret_sources(&mut self, returned: &BitSet, span: Span) {
        let Some(allowed) = self.body.ret_sources.clone() else {
            return;
        };
        let outside = returned.iter().find_map(|index| {
            let loan = &self.loans.loans[index];
            let (local, contents) = match loan.origin {
                LoanOrigin::Arg(local) => (local, false),
                LoanOrigin::ArgContents(local) => (local, true),
                LoanOrigin::Local => return None,
            };
            let permitted = allowed.iter().any(|source| match *source {
                ReturnSource::Whole(allowed) => allowed == local,
                ReturnSource::Contents(allowed, _) => contents && allowed == local,
            });
            (!permitted).then_some((index, local))
        });
        let Some((index, local)) = outside else {
            return;
        };
        let name = |local: Local| {
            self.body
                .local(local)
                .name
                .map_or_else(|| "value".to_owned(), |name| name.to_string())
        };
        let borrowed = name(local);
        let declared: Vec<String> = allowed
            .iter()
            .map(|source| match *source {
                ReturnSource::Whole(local) => format!("`{}`", name(local)),
                ReturnSource::Contents(_, source) => format!("`{source}`"),
            })
            .collect();
        let mut sources: Vec<String> = allowed
            .iter()
            .map(|source| match *source {
                ReturnSource::Whole(local) => name(local),
                ReturnSource::Contents(_, source) => source.to_string(),
            })
            .collect();
        sources.push(borrowed.clone());
        let loan = &self.loans.loans[index];
        let diagnostic = Diagnostic::error(format!(
            "`{}` returns a value borrowed from `{borrowed}`, \
             but its signature only borrows from {}",
            self.body.name,
            declared.join(", ")
        ))
        .with_span(span)
        .with_label(format!("this borrows from `{borrowed}`"))
        .with_secondary(loan.span, format!("`{borrowed}` comes in here"))
        .with_help(format!(
            "add `{borrowed}` to the borrow sources: `borrows {}`",
            sources.join(", ")
        ));
        self.emit(span, diagnostic);
    }

    fn check_stores(&mut self, held: &Holdings, span: Span) {
        if let BodySource::Closure { .. } = self.body.source {
            return;
        }
        for target in self.body.args() {
            if !matches!(self.body.local(target).ty, Ty::Ref { mutable: true, .. }) {
                continue;
            }
            for index in held[target.index()].iter() {
                let loan = &self.loans.loans[index];
                let (local, contents) = match loan.origin {
                    LoanOrigin::Arg(local) => (local, false),
                    LoanOrigin::ArgContents(local) => (local, true),
                    LoanOrigin::Local => continue,
                };
                if local == target {
                    continue;
                }
                let storage = self
                    .body
                    .arg_storage
                    .get(local.index() - 1)
                    .copied()
                    .unwrap_or_default();
                if storage.whole || (contents && storage.contents) {
                    continue;
                }
                self.report_store(local, target, span);
                return;
            }
        }
    }

    fn report_store(&mut self, stored: Local, target: Local, span: Span) {
        let name = |local: Local| {
            self.body
                .local(local)
                .name
                .map_or_else(|| "value".to_owned(), |name| name.to_string())
        };
        let stored_name = name(stored);
        let target_name = name(target);
        let declaration = self.body.local(stored).span;
        let diagnostic = Diagnostic::error(format!(
            "`{}` keeps `{stored_name}` in `{target_name}`, but its signature does not allow it",
            self.body.name
        ))
        .with_span(declaration)
        .with_label(format!("`{stored_name}` is only borrowed for this call"))
        .with_secondary(
            span,
            format!("`{stored_name}` is still in `{target_name}` here"),
        )
        .with_note("a method can only keep a reference it was given when its signature says so")
        .with_help(format!(
            "write `keeps {stored_name}` after the parameters of `{}`",
            self.body.name
        ));
        self.emit(declaration, diagnostic);
    }

    fn is_local_data(&self, loan: usize) -> bool {
        let place = &self.loans.loans[loan].place;
        matches!(place.base, PlaceBase::Local(_)) && !has_deref(place)
    }

    fn live_loans(&self, location: Location, held: &Holdings) -> BitSet {
        let defined = self.defined_at(location);
        let mut live = BitSet::new(self.loans.loans.len());
        for local in self.liveness.live_after(location).iter() {
            if Some(local) != defined {
                live.union(&held[local]);
            }
        }
        live
    }

    fn defined_at(&self, location: Location) -> Option<usize> {
        let data = self.body.block(location.block);
        let place = match data.statements.get(location.index) {
            Some(statement) => match &statement.kind {
                StatementKind::Assign(assign) => Some(&assign.0),
                _ => None,
            },
            None => match &data.terminator.kind {
                TerminatorKind::Call { dest, .. } => dest.as_ref(),
                _ => None,
            },
        };
        place.and_then(Place::as_local).map(Local::index)
    }

    fn check_access(
        &mut self,
        location: Location,
        span: Span,
        place: &Place,
        access: Access,
        init: &BitSet,
        held: &Holdings,
    ) {
        let path = PlacePath::of(place);
        if let Some(path) = &path
            && let Some(moved) = self.moves.conflicting(init, path, access).cloned()
        {
            self.report_moved(location, span, place, access, &moved);
            return;
        }
        if access == Access::Move && path.as_ref().is_none_or(|path| path.indirect) {
            self.report_move_out(span, place);
            return;
        }
        if access.mutates()
            && let Some(immutable) = self.tys.immutable_prefix(place)
        {
            self.report_immutable(span, place, access, &immutable);
            return;
        }
        let live = self.live_loans(location, held);
        let conflict = live.iter().find(|&loan| {
            let loan = &self.loans.loans[loan];
            if loan.origin != LoanOrigin::Local {
                return false;
            }
            overlaps(&loan.place, place)
                && (loan.mutable
                    || !matches!(access, Access::Read | Access::Borrow { mutable: false }))
        });
        if let Some(loan) = conflict {
            self.report_conflict(location, span, place, access, loan, held);
        }
    }

    fn emit(&mut self, span: Span, diagnostic: Diagnostic) {
        if self.reported.insert((span, diagnostic.message.clone())) {
            self.dcx.emit(diagnostic);
        }
    }

    fn describe_path(&self, path: &PlacePath) -> String {
        let mut out = self
            .body
            .local(path.local)
            .name
            .map_or_else(|| "value".to_owned(), |name| name.to_string());
        for elem in &path.elems {
            match elem {
                places::PathElem::Field(_, name) => {
                    out.push('.');
                    out.push_str(name.as_str());
                }
                places::PathElem::Capture(index) => {
                    out = self.body.captures[*index].name.to_string();
                }
            }
        }
        out
    }

    fn report_moved(
        &mut self,
        location: Location,
        span: Span,
        place: &Place,
        access: Access,
        moved: &MoveOut,
    ) {
        let name = self.tys.describe(place);
        if !self.reported_places.insert((location, name.clone())) {
            return;
        }
        if moved.kind == MoveKind::Uninit {
            let diagnostic = Diagnostic::error(format!("`{name}` is used before it has a value"))
                .with_span(span)
                .with_label(format!(
                    "`{name}` is used here, but it may not have been assigned"
                ))
                .with_secondary(moved.span, "declared here");
            self.emit(span, diagnostic);
            return;
        }
        let moved_name = self.describe_path(&moved.path);
        let partial =
            moved.path.elems.len() > PlacePath::of(place).map_or(0, |path| path.elems.len());
        let verb = match access {
            Access::Borrow { .. } => "borrow",
            Access::Write => "assignment",
            Access::Read | Access::Move => "use",
        };
        let message = if partial {
            format!("{verb} of partially moved value: `{name}`")
        } else {
            format!("{verb} of moved value: `{name}`")
        };
        let moved_label = if moved.span == span {
            "value moved here, in an earlier iteration of the loop".to_owned()
        } else if partial {
            format!("`{moved_name}` was moved here")
        } else {
            "value moved here".to_owned()
        };
        let mut diagnostic = Diagnostic::error(message)
            .with_span(span)
            .with_label(format!("value {} here after move", past(access)));
        if moved.span != span {
            diagnostic = diagnostic.with_secondary(moved.span, moved_label);
        } else {
            diagnostic = diagnostic.with_label(moved_label);
        }
        let ty = self.tys.place_ty(&path_place(&moved.path));
        if !ty.is_unknown() {
            diagnostic = match self.tys.tcx.uncopyable_part(&ty) {
                Some((part, part_ty)) => diagnostic
                    .with_note(format!(
                        "`{moved_name}` has type `{ty}`, which is moved instead of copied \
                         because `{part}` in it has type `{part_ty}`, which can't be copied"
                    ))
                    .with_help(format!(
                        "borrow it with `&{moved_name}`, or keep a copy with `{moved_name}.clone()`"
                    )),
                None => diagnostic.with_note(format!(
                    "`{moved_name}` has type `{ty}`, which is moved instead of copied"
                )),
            };
        }
        self.emit(span, diagnostic);
    }

    fn report_move_out(&mut self, span: Span, place: &Place) {
        let name = self.tys.describe(place);
        let ty = self.tys.place_ty(place);
        let first = place
            .projection
            .iter()
            .find(|elem| matches!(elem, PlaceElem::Deref | PlaceElem::Index(_)));
        let diagnostic = if let PlaceBase::Static { .. } = place.base {
            Diagnostic::error(format!("cannot move out of the static field `{name}`"))
                .with_span(span)
                .with_label("value moved here")
                .with_help(format!("borrow it instead: `&{name}`"))
        } else if self.tys.is_capture(place) {
            Diagnostic::error(format!("cannot move `{name}` out of a lambda"))
                .with_span(span)
                .with_label("value moved here")
                .with_note(
                    "the lambda can be called more than once, \
                     so it can only copy or borrow what it captured",
                )
        } else if let Some(PlaceElem::Index(_)) = first {
            let index = place
                .projection
                .iter()
                .position(|elem| matches!(elem, PlaceElem::Index(_)))
                .unwrap_or(place.projection.len());
            let array = self.tys.describe(&Place {
                base: place.base,
                projection: place.projection[..index].to_vec(),
            });
            Diagnostic::error(format!("cannot move out of an element of `{array}`"))
                .with_span(span)
                .with_label("value moved here")
                .with_note(format!("`{ty}` values are moved instead of copied"))
                .with_help("borrow the element instead")
        } else {
            Diagnostic::error(format!("cannot move out of `{name}`, which is borrowed"))
                .with_span(span)
                .with_label("value moved here")
                .with_note(format!("`{ty}` values are moved instead of copied"))
                .with_help(format!("borrow it instead: `&{name}`"))
        };
        self.emit(span, diagnostic);
    }

    fn report_immutable(
        &mut self,
        span: Span,
        place: &Place,
        access: Access,
        immutable: &places::Immutable,
    ) {
        let name = self.tys.describe(place);
        let action = match access {
            Access::Write => format!("cannot assign to `{name}`"),
            _ => format!("cannot borrow `{name}` as mutable"),
        };
        let through_this = immutable.through.projection.is_empty()
            && base_local(&immutable.through)
                .and_then(|local| self.body.local(local).name)
                .is_some_and(|name| name.as_str() == "this");
        let diagnostic = if immutable.is_static {
            Diagnostic::error(format!("{action}, because it is a static field"))
                .with_span(span)
                .with_note("a `static` field can be used from many threads at once")
        } else if self.tys.is_capture(place) {
            Diagnostic::error(format!("cannot change `{name}` inside a lambda"))
                .with_span(span)
                .with_label(format!("`{name}` is changed here"))
                .with_note("a lambda can only read the variables it captures")
        } else if through_this {
            Diagnostic::error(format!("{action} in a method that is not `mut`"))
                .with_span(span)
                .with_label("this changes the object")
                .with_help("mark the method `mut` to let it change `this`")
        } else {
            let holder = self.tys.describe(&immutable.through);
            Diagnostic::error(format!("{action}, because it is behind a `&` reference"))
                .with_span(span)
                .with_label(format!("`{holder}` only lets you read it"))
                .with_help(format!(
                    "borrow it with `&mut` to change it through `{holder}`"
                ))
        };
        self.emit(span, diagnostic);
    }

    fn report_conflict(
        &mut self,
        location: Location,
        span: Span,
        place: &Place,
        access: Access,
        index: usize,
        held: &Holdings,
    ) {
        let name = self.tys.describe(place);
        if !self.reported_places.insert((location, name.clone())) {
            return;
        }
        let loan = &self.loans.loans[index];
        if self.is_temporary(&loan.place) && matches!(access, Access::Write | Access::Move) {
            // The compiler's own temporary is reused or dropped while
            // something still points at it, like `list.add(new R(i * 10))`
            // for a record holding `&int`.
            let mut diagnostic = Diagnostic::error("temporary value dropped while borrowed")
                .with_span(loan.span)
                .with_label("this creates a temporary value which is freed while still in use")
                .with_help(
                    "store the value in a local variable that lives as long as the reference",
                );
            let holders = self.holders(location, held, index);
            if let Some(later) = self
                .later_use(location, &holders)
                .filter(|later| *later != loan.span)
            {
                diagnostic = diagnostic.with_secondary(later, "the borrow is used later here");
            }
            self.emit(loan.span, diagnostic);
            return;
        }
        let borrowed = self.tys.describe(&loan.place);
        let kind = if loan.mutable { "mutable" } else { "shared" };
        let (message, label) = match access {
            Access::Borrow { mutable: true } if loan.mutable => (
                format!("cannot borrow `{name}` as mutable more than once at a time"),
                "second mutable borrow happens here".to_owned(),
            ),
            Access::Borrow { mutable: true } => (
                format!("cannot borrow `{name}` as mutable because it is also borrowed as shared"),
                "mutable borrow happens here".to_owned(),
            ),
            Access::Borrow { mutable: false } => (
                format!("cannot borrow `{name}` because it is borrowed as mutable"),
                "shared borrow happens here".to_owned(),
            ),
            Access::Read => (
                format!("cannot use `{name}` because it is borrowed as mutable"),
                format!("`{name}` is used here"),
            ),
            Access::Write => (
                format!("cannot assign to `{name}` because it is borrowed"),
                format!("`{name}` is assigned here while it is borrowed"),
            ),
            Access::Move => (
                format!("cannot move out of `{name}` because it is borrowed"),
                format!("`{name}` is moved here while it is borrowed"),
            ),
        };
        let first = if loan.captured {
            format!("`{borrowed}` is borrowed by a lambda here")
        } else {
            format!("{kind} borrow of `{borrowed}` happens here")
        };
        let mut diagnostic = Diagnostic::error(message)
            .with_span(span)
            .with_label(label)
            .with_secondary(loan.span, first);
        let holders = self.holders(location, held, index);
        if let Some(later) = self
            .later_use(location, &holders)
            .filter(|later| *later != loan.span)
        {
            diagnostic = diagnostic.with_secondary(later, "the borrow is used later here");
        }
        if loan.captured {
            diagnostic = diagnostic.with_help("use a `move` lambda to give it its own copy");
        }
        self.emit(span, diagnostic);
    }

    /// Whether `place` is a whole temporary the compiler made, which has no
    /// name to show the user.
    fn is_temporary(&self, place: &Place) -> bool {
        matches!(place.base, PlaceBase::Local(local)
            if self.body.local(local).name.is_none() && place.projection.is_empty())
    }

    fn holders(&self, location: Location, held: &Holdings, index: usize) -> BitSet {
        let mut holders = BitSet::new(self.body.locals.len());
        let defined = self.defined_at(location);
        for local in self.liveness.live_after(location).iter() {
            if Some(local) != defined && held[local].contains(index) {
                holders.insert(local);
            }
        }
        holders
    }

    fn later_use(&self, location: Location, holders: &BitSet) -> Option<Span> {
        let mut queue = VecDeque::from([(location.block, location.index + 1)]);
        let mut visited = HashSet::new();
        while let Some((block, start)) = queue.pop_front() {
            if start == 0 && !visited.insert(block) {
                continue;
            }
            let data = self.body.block(block);
            for statement in data.statements.iter().skip(start) {
                let mut used = Vec::new();
                match &statement.kind {
                    StatementKind::Assign(assign) => {
                        rvalue_locals_of(&assign.1, &mut |local| used.push(local));
                        if assign.0.as_local().is_none() {
                            place_locals_of(&assign.0, &mut |local| used.push(local));
                        }
                    }
                    StatementKind::FakeRead(place) => {
                        place_locals_of(place, &mut |local| used.push(local));
                    }
                    StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {}
                }
                if used.iter().any(|local| holders.contains(local.index())) {
                    return Some(statement.span);
                }
            }
            if start <= data.statements.len() {
                let kind = &data.terminator.kind;
                let mut used = Vec::new();
                terminator_input_locals_of(kind, &mut |local| used.push(local));
                if matches!(kind, TerminatorKind::Return) {
                    used.push(Local::RETURN);
                }
                if used.iter().any(|local| holders.contains(local.index())) {
                    return Some(data.terminator.span);
                }
            }
            for successor in data.terminator.kind.successors() {
                queue.push_back((successor, 0));
            }
        }
        None
    }

    fn report_dangling(&mut self, loan: usize, span: Span) {
        let loan = &self.loans.loans[loan];
        let name = self.tys.describe(&loan.place);
        let diagnostic = if loan.captured {
            Diagnostic::error(format!("a lambda that borrows `{name}` outlives it"))
                .with_span(loan.span)
                .with_label(format!("`{name}` is borrowed by the lambda here"))
                .with_secondary(span, format!("`{name}` stops existing here"))
                .with_help("use a `move` lambda to give it its own copy")
        } else {
            Diagnostic::error(format!("`{name}` does not live long enough"))
                .with_span(loan.span)
                .with_label("borrowed value does not live long enough")
                .with_secondary(
                    span,
                    format!("`{name}` stops existing here while still borrowed"),
                )
        };
        self.emit(loan.span, diagnostic);
    }

    /// Whether the body's own signature keeps `param` forever, so its
    /// callers already check that it borrows nothing.
    fn is_detached_param(&self, param: Local) -> bool {
        self.body
            .arg_storage
            .get(param.index() - 1)
            .is_some_and(|storage| storage.detached)
    }

    fn has_receiver(&self) -> bool {
        self.body
            .args()
            .next()
            .and_then(|arg| self.body.local(arg).name)
            .is_some_and(|name| name.as_str() == "this")
    }

    fn report_forwarded(&mut self, param: Local, method: krelpin_span::Symbol, span: Span) {
        let decl = self.body.local(param);
        let name = decl
            .name
            .map_or_else(|| "argument".to_owned(), |name| name.to_string());
        let diagnostic = Diagnostic::error(format!(
            "`{method}` keeps `{name}` after `{}` ends, but `{name}` may borrow from the caller",
            self.body.name
        ))
        .with_span(span)
        .with_label(format!("`{method}` keeps `{name}` here"))
        .with_secondary(decl.span, format!("`{name}` comes from the caller"))
        .with_note(format!(
            "the caller's checks don't know that `{}` passes `{name}` on to be kept",
            self.body.name
        ))
        .with_help(if self.has_receiver() {
            format!(
                "make `{}` static and write `keeps {name}` after its parameters, so its callers \
                 can't pass anything borrowed",
                self.body.name
            )
        } else {
            format!(
                "write `keeps {name}` after the parameters of `{}`, so its callers can't pass \
                 anything borrowed",
                self.body.name
            )
        });
        self.emit(span, diagnostic);
    }

    fn check_kept_in_static(
        &mut self,
        callee: &Callee,
        args: &[Operand],
        span: Span,
        held: &Holdings,
    ) {
        for index in 1..args.len() {
            let passed = self.loans.passed(held, callee, args, index);
            let stored = passed.stored();
            if let Some(loan) = stored.iter().find(|&loan| !self.loans.is_static_loan(loan)) {
                self.report_kept_in_static(loan, callee.method.name.name, span);
                return;
            }
            if stored.is_empty() && passed.storage.is_none_or(|storage| !storage.whole) {
                continue;
            }
            let forwarded = operand_place(&args[index])
                .and_then(base_local)
                .and_then(|local| self.forwarded.source(local))
                .filter(|&param| !self.is_detached_param(param));
            if let Some(param) = forwarded {
                self.report_forwarded(param, callee.method.name.name, span);
                return;
            }
        }
    }

    fn report_kept_in_static(&mut self, loan: usize, method: krelpin_span::Symbol, span: Span) {
        let loan = &self.loans.loans[loan];
        let name = self.tys.describe(&loan.place);
        let diagnostic = Diagnostic::error(format!(
            "`{method}` keeps its argument in a static field, but the argument borrows `{name}`"
        ))
        .with_span(span)
        .with_label(format!("`{method}` keeps the argument here"))
        .with_secondary(loan.span, format!("`{name}` is borrowed here"))
        .with_note(
            "a `static` field lives as long as the program, longer than anything it could borrow",
        )
        .with_help(
            "use a `move` lambda, or give the argument its own values instead of references",
        );
        self.emit(span, diagnostic);
    }

    fn report_detached(&mut self, loan: usize, method: krelpin_span::Symbol, span: Span) {
        let loan = &self.loans.loans[loan];
        let name = self.tys.describe(&loan.place);
        let diagnostic = Diagnostic::error(format!(
            "`{method}` keeps its argument after this method ends, but the argument borrows `{name}`"
        ))
        .with_span(span)
        .with_label(format!("`{method}` keeps the argument here"))
        .with_secondary(loan.span, format!("`{name}` is borrowed here"))
        .with_note(format!(
            "`{method}` is static and keeps its argument, so the argument may outlive everything the caller owns"
        ))
        .with_help("give the argument its own values instead of references");
        self.emit(span, diagnostic);
    }

    fn report_escape(&mut self, loan: usize, span: Span, how: &str) {
        let loan = &self.loans.loans[loan];
        let name = self.tys.describe(&loan.place);
        let diagnostic = if loan.captured {
            Diagnostic::error(format!(
                "a {how} lambda borrows `{name}`, which belongs to this method"
            ))
            .with_span(loan.span)
            .with_label(format!("`{name}` is borrowed by the lambda here"))
            .with_secondary(span, format!("the lambda is {how} here"))
            .with_note(format!("`{name}` stops existing when the method ends"))
            .with_help("use a `move` lambda to give it its own copy")
        } else {
            Diagnostic::error(format!(
                "cannot let a reference to `{name}` escape the method"
            ))
            .with_span(loan.span)
            .with_label(format!("`{name}` is borrowed here"))
            .with_secondary(span, format!("the reference is {how} here"))
            .with_note(format!("`{name}` stops existing when the method ends"))
        };
        self.emit(loan.span, diagnostic);
    }
}

fn past(access: Access) -> &'static str {
    match access {
        Access::Borrow { .. } => "borrowed",
        Access::Write => "assigned",
        Access::Read | Access::Move => "used",
    }
}

fn path_place(path: &PlacePath) -> Place {
    let mut place = Place::local(path.local);
    for elem in &path.elems {
        place = place.project(match elem {
            places::PathElem::Field(owner, name) => PlaceElem::Field {
                owner: *owner,
                name: *name,
            },
            places::PathElem::Capture(index) => PlaceElem::Capture(*index),
        });
    }
    place
}
