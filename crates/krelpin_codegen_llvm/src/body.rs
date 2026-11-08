use krelpin_ast::ast::{BinOp, PrimitiveTy, ReceiverKind};
use krelpin_ast::token::{Lit, LitKind};
use krelpin_hir::Dispatch;
use krelpin_mir::{
    AggregateKind, BasicBlock, Body, BodyId, CaptureMode, Check, ClosureTarget, Constant, Operand,
    Place, PlaceBase, PlaceElem, Rvalue, StatementKind, TerminatorKind, UnaryOp, Unwind,
};
use krelpin_span::def_id::DefId;
use krelpin_typeck::{Callee, LangItem, Subst, Ty};

use crate::cx::Cx;
use crate::func::{FnCx, Val, array_ll, float_const, float32_const};
use crate::instance::Instance;
use crate::layout::Shape;
use crate::rtti::{ClosureInfo, ClosureKind, RtKey};

struct BodyCx<'f, 'c, 'a, 'tcx> {
    fx: &'f mut FnCx<'c, 'a, 'tcx>,
    body: &'a Body,
    locals: Vec<Ty>,
    slots: Vec<String>,
    closure: Option<usize>,
    instance: usize,
    uses_resume: bool,
    /// In the poll function of an `async` body: where the frame's state is.
    state: Option<String>,
    /// The state each `suspend` stores, by block.
    suspends: std::collections::HashMap<usize, (u32, BasicBlock)>,
    block: usize,
}

impl<'a, 'tcx> Cx<'a, 'tcx> {
    pub(crate) fn body_subst(&self, body: BodyId, args: &[Ty]) -> Subst {
        let names = self.body_generics(body);
        self.subst_of(&names, args)
    }

    /// Emits a body as a function. With `poll`, the body belongs to an
    /// `async` method and becomes its future's `poll`: its locals live in the
    /// frame that `%a0` points to, and it continues where the frame's state
    /// says.
    pub(crate) fn emit_body(
        &mut self,
        id: usize,
        body_id: BodyId,
        args: &[Ty],
        poll: bool,
    ) -> String {
        let mir: &'a krelpin_mir::Mir = self.mir;
        let body = mir.body(body_id);
        let subst = self.body_subst(body_id, args);
        let locals: Vec<Ty> = body
            .locals
            .iter()
            .map(|decl| decl.ty.subst(&subst))
            .collect();
        let ret = locals[0].clone();
        if let Some((index, ty)) = locals.iter().enumerate().find(|(_, ty)| !is_concrete(ty)) {
            let decl = &body.locals[index];
            let what = decl.name.map_or_else(
                || "a temporary value".to_owned(),
                |name| format!("`{name}`"),
            );
            self.error(
                krelpin_errors::Diagnostic::error(format!(
                    "cannot generate code for `{}` because the type of {what} is not known",
                    body.name
                ))
                .with_span(decl.span)
                .with_label(format!("this has the type `{ty}`"))
                .with_help("write the type arguments explicitly"),
            );
            let name = self.fn_name(id);
            return format!("define internal void {name}() {{\n  unreachable\n}}\n");
        }
        let closure = self.closure_bodies.get(&(body_id, args.to_vec())).copied();
        let static_id = self.instance_static(id);
        let previous = std::mem::replace(&mut self.current_static, static_id);
        let previous_fn = self.current_fn.replace(id);
        let name = self.fn_name(id);
        let frame = poll.then(|| {
            let index = self.async_frame(body_id, args);
            self.frame_type(index)
        });
        let cx_local = body.arg_count + 1;
        let mut fx = FnCx::new(self, subst, ret.clone());
        let mut params = Vec::new();
        let mut slots = Vec::new();
        let mut state = None;
        if let Some(frame_ty) = &frame {
            params.push("ptr %a0".to_owned());
            params.push("ptr %a1".to_owned());
            fx.allocas.push_str("  %frame = load ptr, ptr %a0\n");
            fx.allocas.push_str(&format!(
                "  %state = getelementptr inbounds {frame_ty}, ptr %frame, i32 0, i32 1\n"
            ));
            state = Some("%state".to_owned());
        }
        for (index, ty) in locals.iter().enumerate() {
            if let Some(frame_ty) = &frame
                && index != 0
            {
                let slot = if index == cx_local {
                    let slot = fx.alloca(ty);
                    fx.allocas
                        .push_str(&format!("  store ptr %a1, ptr {slot}\n"));
                    slot
                } else if *ty == Ty::Void {
                    String::new()
                } else {
                    let slot = format!("%fs{index}");
                    fx.allocas.push_str(&format!(
                        "  {slot} = getelementptr inbounds {frame_ty}, ptr %frame, i32 0, i32 {}\n",
                        Cx::frame_field(index)
                    ));
                    slot
                };
                slots.push(slot);
                continue;
            }
            let slot = if *ty == Ty::Void {
                String::new()
            } else {
                fx.alloca(ty)
            };
            if frame.is_none() && (1..=body.arg_count).contains(&index) {
                let llty = fx.ll(ty);
                params.push(format!("{llty} %a{index}"));
                fx.allocas
                    .push_str(&format!("  store {llty} %a{index}, ptr {slot}\n"));
            }
            slots.push(slot);
        }
        let mut cx = BodyCx {
            fx: &mut fx,
            body,
            locals,
            slots,
            closure,
            instance: id,
            uses_resume: false,
            state,
            suspends: Default::default(),
            block: 0,
        };
        let mut entry = "  br label %bb0\n".to_owned();
        if poll {
            let mut cases = vec!["i32 0, label %bb0".to_owned()];
            for (index, block) in body.blocks.iter().enumerate() {
                if let TerminatorKind::Suspend { resume } = block.terminator.kind {
                    let k = cx.suspends.len() as u32 + 1;
                    cx.suspends.insert(index, (k, resume));
                    cases.push(format!("i32 {k}, label %bb{}", resume.index()));
                }
            }
            entry = format!(
                "  %state.now = load i32, ptr %state\n  store i32 -1, ptr %state\n  switch i32 %state.now, label %finished [ {} ]\n",
                cases.join(" ")
            );
            cx.fx.start("finished");
            cx.uses_resume = true;
            cx.fx.throw_new(
                LangItem::IllegalStateException,
                "a future was polled after it finished",
                "resume",
            );
            cx.fx.line("unreachable");
        }
        for (index, block) in body.blocks.iter().enumerate() {
            cx.block = index;
            cx.fx.start(&format!("bb{index}"));
            for statement in &block.statements {
                cx.statement(&statement.kind);
            }
            cx.terminator(&block.terminator.kind);
        }
        if cx.uses_resume {
            cx.fx.start("resume");
            cx.drop_locals(true);
            let ret_ty = cx.locals[0].clone();
            cx.fx.ret_zero(&ret_ty);
        }
        let _ = cx.instance;
        fx.finish_fail();
        let llret = fx.cx.llty(&ret);
        let text = format!(
            "define internal {llret} {name}({}) {{\nallocas:\n{}{entry}{}}}\n",
            params.join(", "),
            fx.allocas,
            fx.out
        );
        self.current_static = previous;
        self.current_fn = previous_fn;
        text
    }
}

impl<'f, 'c, 'a, 'tcx> BodyCx<'f, 'c, 'a, 'tcx> {
    fn unwind_label(&mut self, unwind: &Unwind) -> String {
        match unwind {
            Unwind::Handler(block) => format!("bb{}", block.index()),
            Unwind::Resume => {
                self.uses_resume = true;
                "resume".to_owned()
            }
        }
    }

    fn drop_locals(&mut self, include_return: bool) {
        for index in (0..self.locals.len()).rev() {
            if index == 0 && !include_return {
                continue;
            }
            let ty = self.locals[index].clone();
            if ty == Ty::Void || !self.fx.cx.needs_drop(&ty) {
                continue;
            }
            let slot = self.slots[index].clone();
            self.fx.drop_at(&ty, &slot);
        }
    }

    fn statement(&mut self, kind: &StatementKind) {
        match kind {
            StatementKind::Assign(assign) => {
                let (place, rvalue) = assign.as_ref();
                let dest_ty = self.place_ty(place);
                let Some(value) = self.rvalue(rvalue, &dest_ty) else {
                    return;
                };
                let (address, ty) = self.place_addr(place);
                let converted = self.fx.convert(&value.v, &value.ty, &ty);
                self.store_owned(&ty, &converted, &address);
            }
            StatementKind::StorageLive(_) | StatementKind::FakeRead(_) => {}
            StatementKind::StorageDead(local) => {
                let ty = self.locals[local.index()].clone();
                if ty != Ty::Void {
                    let slot = self.slots[local.index()].clone();
                    self.fx.drop_at(&ty, &slot);
                }
            }
        }
    }

    fn store_owned(&mut self, ty: &Ty, value: &str, address: &str) {
        if *ty == Ty::Void {
            return;
        }
        if self.fx.cx.needs_drop(ty) {
            let old = self.fx.load(ty, address);
            self.fx.store(ty, value, address);
            self.fx.drop_value(&old, ty);
        } else {
            self.fx.store(ty, value, address);
        }
    }

    fn place_ty(&mut self, place: &Place) -> Ty {
        let mut ty = match place.base {
            PlaceBase::Local(local) => self.locals[local.index()].clone(),
            PlaceBase::Static { owner, name } => self.static_ty(owner, name),
        };
        let mut variant = None;
        for elem in &place.projection {
            ty = self.project_ty(&ty, elem, &mut variant);
        }
        ty
    }

    fn static_ty(&self, owner: DefId, name: krelpin_span::Symbol) -> Ty {
        self.fx
            .cx
            .tcx
            .sig(owner)
            .fields
            .get(&name)
            .map_or(Ty::Unknown, |field| field.ty.clone())
    }

    fn project_ty(&mut self, ty: &Ty, elem: &PlaceElem, variant: &mut Option<usize>) -> Ty {
        let base = ty.non_null().clone();
        match elem {
            PlaceElem::Deref => match base {
                Ty::Ref { ty, .. } => ty.as_ref().clone(),
                other => other,
            },
            PlaceElem::Field { owner, name } => {
                if let Some(index) = variant.take() {
                    let Ty::Adt { def, args, .. } = &base else {
                        return Ty::Unknown;
                    };
                    return self
                        .fx
                        .cx
                        .variant_fields(*def, args, index)
                        .into_iter()
                        .find(|(field, _)| field == name)
                        .map_or(Ty::Unknown, |(_, ty)| ty);
                }
                match &base {
                    Ty::Adt { def, args, .. } => {
                        let args = self
                            .fx
                            .cx
                            .tcx
                            .upcast(*def, args, *owner)
                            .unwrap_or_else(|| args.clone());
                        self.fx.cx.field_ty(*owner, &args, *name)
                    }
                    _ => Ty::Unknown,
                }
            }
            PlaceElem::Index(_) => match base {
                Ty::Array(elem) => elem.as_ref().clone(),
                other => other,
            },
            PlaceElem::Variant { index, .. } => {
                *variant = Some(*index);
                base
            }
            PlaceElem::Subtype(target) => self.fx.sub(target),
            PlaceElem::Capture(index) => self.capture_ty(*index),
        }
    }

    fn capture_ty(&self, index: usize) -> Ty {
        let info = &self.body.captures[index];
        let ty = info.ty.subst(&self.fx.subst);
        match info.mode {
            CaptureMode::Value => ty,
            CaptureMode::Ref => Ty::Ref {
                mutable: false,
                ty: Box::new(ty),
            },
            CaptureMode::RefMut => Ty::Ref {
                mutable: true,
                ty: Box::new(ty),
            },
        }
    }

    /// A local narrowed from `R?` to `R` keeps its `{ i1, R }` slot. This
    /// returns the address and type of the `R` inside it, and leaves any
    /// other place as it is.
    fn narrowed(&mut self, address: String, ty: Ty) -> (String, Ty) {
        if !matches!(self.fx.cx.shape(&ty), Shape::NullableValue(_)) {
            return (address, ty);
        }
        let nullable_ll = self.fx.ll(&ty);
        let payload = self.fx.assign(format!(
            "getelementptr inbounds {nullable_ll}, ptr {address}, i32 0, i32 1"
        ));
        (payload, ty.non_null().clone())
    }

    fn place_addr(&mut self, place: &Place) -> (String, Ty) {
        let (mut address, mut ty) = match place.base {
            PlaceBase::Local(local) => (
                self.slots[local.index()].clone(),
                self.locals[local.index()].clone(),
            ),
            PlaceBase::Static { owner, name } => {
                let id = self.fx.cx.static_info(owner, name);
                (
                    self.fx.cx.statics[id].global.clone(),
                    self.fx.cx.statics[id].ty.clone(),
                )
            }
        };
        let mut variant: Option<usize> = None;
        for elem in &place.projection {
            let base = ty.non_null().clone();
            if matches!(elem, PlaceElem::Field { .. } | PlaceElem::Variant { .. }) {
                (address, ty) = self.narrowed(address, ty);
            }
            match elem {
                PlaceElem::Deref => {
                    address = self.fx.assign(format!("load ptr, ptr {address}"));
                }
                PlaceElem::Field { owner, name } => {
                    if let Some(index) = variant {
                        let Ty::Adt { def, args, .. } = &base else {
                            panic!("variant field on `{base}`");
                        };
                        let fields = self.fx.cx.variant_fields(*def, args, index);
                        let position = fields
                            .iter()
                            .position(|(field, _)| field == name)
                            .unwrap_or(0);
                        let variant_ll = self.fx.cx.variant_type(*def, args, index);
                        address = self.fx.assign(format!(
                            "getelementptr inbounds {variant_ll}, ptr {address}, i32 0, i32 {}",
                            position + 1
                        ));
                        let field_ty = fields
                            .get(position)
                            .map_or(Ty::Unknown, |(_, ty)| ty.clone());
                        address = self.fx.indirect_slot(&base, &field_ty, address);
                    } else {
                        match self.fx.cx.shape(&base) {
                            Shape::Record(def, args) => {
                                let position = self
                                    .fx
                                    .cx
                                    .tcx
                                    .sig(def)
                                    .components
                                    .iter()
                                    .position(|component| component == name)
                                    .unwrap_or(0);
                                let record_ll = self.fx.ll(&base);
                                address = self.fx.gep(&record_ll, &address, position);
                                let field_ty = self.fx.cx.field_ty(def, &args, *name);
                                address = self.fx.indirect_slot(&base, &field_ty, address);
                            }
                            _ => {
                                let object = self.fx.assign(format!("load ptr, ptr {address}"));
                                let object_ll = self.fx.cx.object_type(&base);
                                let index = self.fx.cx.field_index(&base, *owner, *name);
                                address = self.fx.gep(&object_ll, &object, index);
                            }
                        }
                    }
                }
                PlaceElem::Index(local) => {
                    let array = self.fx.assign(format!("load ptr, ptr {address}"));
                    let index = self
                        .fx
                        .assign(format!("load i32, ptr {}", self.slots[local.index()]));
                    let wide = self.fx.assign(format!("sext i32 {index} to i64"));
                    let Ty::Array(elem) = &base else {
                        panic!("indexing into `{base}`");
                    };
                    let elem = elem.as_ref().clone();
                    let elem_ll = self.fx.cx.mem_llty(&elem);
                    address = self.fx.assign(format!(
                        "getelementptr inbounds {}, ptr {array}, i32 0, i32 2, i64 {wide}",
                        array_ll(&elem_ll)
                    ));
                }
                PlaceElem::Variant { .. } => {}
                PlaceElem::Subtype(target) => {
                    let target = self.fx.sub(target);
                    match (self.fx.cx.shape(&ty), self.fx.cx.shape(&target)) {
                        (Shape::Ptr(_), Shape::Prim(_) | Shape::Record(..) | Shape::Enum(..)) => {
                            let object = self.fx.assign(format!("load ptr, ptr {address}"));
                            let box_ty = self.fx.cx.box_type(&target);
                            address = self.fx.assign(format!(
                                "getelementptr inbounds {box_ty}, ptr {object}, i32 0, i32 1"
                            ));
                        }
                        (Shape::NullableValue(_), shape)
                            if !matches!(shape, Shape::NullableValue(_)) =>
                        {
                            let nullable_ll = self.fx.ll(&ty);
                            address = self.fx.assign(format!(
                                "getelementptr inbounds {nullable_ll}, ptr {address}, i32 0, i32 1"
                            ));
                        }
                        _ => {}
                    }
                }
                PlaceElem::Capture(index) => {
                    let object = self.fx.assign(format!("load ptr, ptr {address}"));
                    let closure = self
                        .closure
                        .expect("captures only appear in closure bodies");
                    let closure_ll = self.fx.cx.closure_type(closure);
                    address = self.fx.assign(format!(
                        "getelementptr inbounds {closure_ll}, ptr {object}, i32 0, i32 {}",
                        index + 1
                    ));
                }
            }
            ty = self.project_ty(&ty, elem, &mut variant);
        }
        (address, ty)
    }

    fn constant_ty(&self, constant: &Constant) -> Ty {
        match constant {
            Constant::Lit(lit) => match lit.kind {
                LitKind::Integer => match lit.suffix.map(|s| s.as_str().to_ascii_lowercase()) {
                    Some(suffix) if suffix == "l" => Ty::LONG,
                    _ => Ty::INT,
                },
                LitKind::Float => match lit.suffix.map(|s| s.as_str().to_ascii_lowercase()) {
                    Some(suffix) if suffix == "f" => Ty::FLOAT,
                    _ => Ty::DOUBLE,
                },
                LitKind::Char => Ty::CHAR,
                LitKind::Str | LitKind::TextBlock => self.fx.cx.tcx.string_ty(),
                LitKind::Err => Ty::Unknown,
            },
            Constant::Int { ty, .. } => Ty::Primitive(*ty),
            Constant::Bool(_) => Ty::BOOLEAN,
            Constant::Null => Ty::Null,
        }
    }

    fn constant(&mut self, constant: &Constant) -> Val {
        let ty = self.constant_ty(constant);
        let v = match constant {
            Constant::Lit(lit) => self.literal(lit, &ty),
            Constant::Int { value, ty } => self.fx.const_int(&Ty::Primitive(*ty), *value),
            Constant::Bool(value) => value.to_string(),
            Constant::Null => "null".to_owned(),
        };
        Val { ty, v }
    }

    fn literal(&mut self, lit: &Lit, ty: &Ty) -> String {
        let text = lit.symbol.as_str();
        match lit.kind {
            LitKind::Integer => {
                let value = parse_int(text);
                if *ty == Ty::INT {
                    (value as i32).to_string()
                } else {
                    value.to_string()
                }
            }
            LitKind::Float => {
                let cleaned: String = text.chars().filter(|c| *c != '_').collect();
                let value: f64 = cleaned.parse().unwrap_or(0.0);
                if *ty == Ty::FLOAT {
                    float32_const(value as f32)
                } else {
                    float_const(value)
                }
            }
            LitKind::Char => {
                let mut result = 0u32;
                krelpin_lexer::unescape::unescape(
                    text,
                    krelpin_lexer::unescape::Mode::Char,
                    |_, c| {
                        if let Ok(c) = c {
                            result = c as u32;
                        }
                    },
                );
                result.to_string()
            }
            LitKind::Str | LitKind::TextBlock => {
                let source = if lit.kind == LitKind::TextBlock {
                    krelpin_lexer::unescape::strip_indent(text)
                } else {
                    text.to_owned()
                };
                let mode = if lit.kind == LitKind::TextBlock {
                    krelpin_lexer::unescape::Mode::TextBlock
                } else {
                    krelpin_lexer::unescape::Mode::Str
                };
                let mut value = String::new();
                krelpin_lexer::unescape::unescape(&source, mode, |_, c| {
                    if let Ok(c) = c {
                        value.push(c);
                    }
                });
                self.fx.cx.string_literal(&value)
            }
            LitKind::Err => "zeroinitializer".to_owned(),
        }
    }

    fn operand_owned(&mut self, operand: &Operand) -> Val {
        match operand {
            Operand::Constant(constant) => self.constant(constant),
            Operand::Copy(place) => {
                let (address, ty) = self.place_addr(place);
                let value = self.fx.load(&ty, &address);
                let v = self.fx.copy_value(&value, &ty);
                Val { ty, v }
            }
            Operand::Move(place) => {
                let (address, ty) = self.place_addr(place);
                let v = self.fx.load(&ty, &address);
                if self.fx.cx.needs_drop(&ty) {
                    self.fx.zero(&ty, &address);
                }
                Val { ty, v }
            }
        }
    }

    fn operand_read(&mut self, operand: &Operand) -> (Val, bool) {
        match operand {
            Operand::Copy(place) => {
                let (address, ty) = self.place_addr(place);
                let v = self.fx.load(&ty, &address);
                (Val { ty, v }, false)
            }
            Operand::Move(_) => {
                let value = self.operand_owned(operand);
                let owned = self.fx.cx.needs_drop(&value.ty);
                (value, owned)
            }
            Operand::Constant(constant) => (self.constant(constant), false),
        }
    }

    fn release(&mut self, value: &Val, owned: bool) {
        if owned {
            self.fx.drop_value(&value.v, &value.ty);
        }
    }

    fn rvalue(&mut self, rvalue: &Rvalue, dest: &Ty) -> Option<Val> {
        Some(match rvalue {
            Rvalue::Use(operand) => self.operand_owned(operand),
            Rvalue::Ref { place, mutable } => {
                let (mut address, mut ty) = self.place_addr(place);
                // `&value` where `value` was narrowed to non-null lends the `R`.
                if let Ty::Ref { ty: pointee, .. } = dest
                    && !matches!(self.fx.cx.shape(pointee), Shape::NullableValue(_))
                {
                    (address, ty) = self.narrowed(address, ty);
                }
                Val {
                    ty: Ty::Ref {
                        mutable: *mutable,
                        ty: Box::new(ty),
                    },
                    v: address,
                }
            }
            Rvalue::Binary(op, lhs, rhs) => self.binary(*op, lhs, rhs, dest),
            Rvalue::Unary(op, operand) => {
                let (value, owned) = self.operand_read(operand);
                let value = self.unwrap_narrowed(value);
                let ll = self.fx.ll(&value.ty);
                let v = match op {
                    UnaryOp::Not => self.fx.assign(format!("xor i1 {}, true", value.v)),
                    UnaryOp::BitNot => self.fx.assign(format!("xor {ll} {}, -1", value.v)),
                    UnaryOp::Neg => {
                        if matches!(
                            value.ty,
                            Ty::Primitive(PrimitiveTy::Float | PrimitiveTy::Double)
                        ) {
                            self.fx.assign(format!("fneg {ll} {}", value.v))
                        } else {
                            self.fx.assign(format!("sub {ll} 0, {}", value.v))
                        }
                    }
                };
                self.release(&value, owned);
                Val {
                    ty: value.ty.clone(),
                    v,
                }
            }
            Rvalue::Cast(operand, target) => {
                let target = self.fx.sub(target);
                let value = self.operand_owned(operand);
                let v = self.fx.convert(&value.v, &value.ty, &target);
                Val { ty: target, v }
            }
            Rvalue::Len(place) => {
                let (address, _) = self.place_addr(place);
                let array = self.fx.assign(format!("load ptr, ptr {address}"));
                let len_addr = self.fx.assign(format!(
                    "getelementptr inbounds {{ ptr, i64 }}, ptr {array}, i32 0, i32 1"
                ));
                let len = self.fx.assign(format!("load i64, ptr {len_addr}"));
                let v = self.fx.assign(format!("trunc i64 {len} to i32"));
                Val { ty: Ty::INT, v }
            }
            Rvalue::Discriminant(place) => {
                let (address, ty) = self.place_addr(place);
                let (address, ty) = self.narrowed(address, ty);
                let enum_ll = self.fx.ll(ty.non_null());
                let tag = self.fx.assign(format!(
                    "getelementptr inbounds {enum_ll}, ptr {address}, i32 0, i32 0"
                ));
                let v = self.fx.assign(format!("load i32, ptr {tag}"));
                Val { ty: Ty::INT, v }
            }
            Rvalue::InstanceOf(place, target) => {
                let target = self.fx.sub(target);
                let (address, ty) = self.place_addr(place);
                let v = self.instance_of(&address, &ty, &target);
                Val { ty: Ty::BOOLEAN, v }
            }
            Rvalue::IsNull(place) => {
                let (address, ty) = self.place_addr(place);
                let v = match self.fx.cx.shape(&ty) {
                    Shape::Ptr(_) => {
                        let value = self.fx.assign(format!("load ptr, ptr {address}"));
                        self.fx.assign(format!("icmp eq ptr {value}, null"))
                    }
                    Shape::NullableValue(_) => {
                        let ll = self.fx.ll(&ty);
                        let flag_addr = self.fx.assign(format!(
                            "getelementptr inbounds {ll}, ptr {address}, i32 0, i32 0"
                        ));
                        let flag = self.fx.assign(format!("load i1, ptr {flag_addr}"));
                        self.fx.assign(format!("xor i1 {flag}, true"))
                    }
                    _ => "false".to_owned(),
                };
                Val { ty: Ty::BOOLEAN, v }
            }
            Rvalue::New(ty) => {
                let ty = self.fx.sub(ty);
                match self.fx.cx.shape(&ty) {
                    Shape::Ptr(_) => {
                        self.uses_resume = true;
                        let v = self.fx.new_object(&ty, Some("resume"));
                        Val { ty, v }
                    }
                    _ => Val {
                        v: "zeroinitializer".to_owned(),
                        ty,
                    },
                }
            }
            Rvalue::NewArray { elem, len } => {
                let elem = self.fx.sub(elem);
                let (len, _) = self.operand_read(len);
                self.uses_resume = true;
                let negative = self.fx.assign(format!("icmp slt i32 {}, 0", len.v));
                let bad = self.fx.label("negative");
                let ok = self.fx.label("sized");
                self.fx
                    .line(format!("br i1 {negative}, label %{bad}, label %{ok}"));
                self.fx.start(&bad);
                self.fx.throw_new(
                    LangItem::IllegalArgumentException,
                    "array size is negative",
                    "resume",
                );
                self.fx.line(format!("br label %{ok}"));
                self.fx.start(&ok);
                let wide = self.fx.assign(format!("sext i32 {} to i64", len.v));
                let array_ty = Ty::Array(Box::new(elem));
                let v = self.fx.new_array(&array_ty, &wide);
                Val { ty: array_ty, v }
            }
            Rvalue::Aggregate(kind, operands) => self.aggregate(kind, operands, dest),
            Rvalue::Caught => {
                let v = self.fx.assign("load ptr, ptr @kr_pending");
                self.fx.line("store ptr null, ptr @kr_pending");
                Val {
                    ty: self.fx.cx.lang_ty(LangItem::Throwable),
                    v,
                }
            }
        })
    }

    fn instance_of(&mut self, address: &str, ty: &Ty, target: &Ty) -> String {
        match self.fx.cx.shape(ty) {
            Shape::Ptr(_) => {
                let object = self.fx.assign(format!("load ptr, ptr {address}"));
                self.fx.object_is(&object, target)
            }
            Shape::NullableValue(inner) => {
                if inner.as_ref() == target.non_null() {
                    let ll = self.fx.ll(ty);
                    let flag = self.fx.assign(format!(
                        "getelementptr inbounds {ll}, ptr {address}, i32 0, i32 0"
                    ));
                    self.fx.assign(format!("load i1, ptr {flag}"))
                } else {
                    "false".to_owned()
                }
            }
            _ => {
                if ty == target.non_null() || self.fx.cx.is_subtype(ty, target.non_null()) {
                    "true".to_owned()
                } else {
                    "false".to_owned()
                }
            }
        }
    }

    fn unwrap_narrowed(&mut self, value: Val) -> Val {
        if !matches!(self.fx.cx.shape(&value.ty), Shape::NullableValue(_)) {
            return value;
        }
        let ty = value.ty.non_null().clone();
        let v = self.fx.convert(&value.v, &value.ty, &ty);
        Val { ty, v }
    }

    fn binary(&mut self, op: BinOp, lhs: &Operand, rhs: &Operand, dest: &Ty) -> Val {
        let (a, a_owned) = self.operand_read(lhs);
        let (b, b_owned) = self.operand_read(rhs);
        let string = self.fx.cx.tcx.string_ty();
        // The same test as the type checker's, which looks through references.
        let is_string = |cx: &Cx<'_, '_>, ty: &Ty| {
            cx.tcx.is_string(ty.strip_refs()) || cx.tcx.is_string(ty.non_null())
        };
        if op == BinOp::Add && (is_string(self.fx.cx, &a.ty) || is_string(self.fx.cx, &b.ty)) {
            let left = self.fx.stringify(&a.v, &a.ty);
            let right = self.fx.stringify(&b.v, &b.ty);
            let v = self.fx.runtime(
                "ptr",
                "kr_string_concat",
                &format!("ptr {left}, ptr {right}"),
            );
            self.fx.drop_value(&left, &string);
            self.fx.drop_value(&right, &string);
            self.release(&a, a_owned);
            self.release(&b, b_owned);
            return Val { ty: string, v };
        }
        let (a, b) = if matches!(op, BinOp::Eq | BinOp::Ne) {
            (a, b)
        } else {
            (self.unwrap_narrowed(a), self.unwrap_narrowed(b))
        };
        let operand_ty = if a.ty == Ty::Null {
            b.ty.clone()
        } else {
            a.ty.clone()
        };
        let b_v = if b.ty != operand_ty && !matches!(op, BinOp::Shl | BinOp::Shr | BinOp::UShr) {
            self.fx.convert(&b.v, &b.ty, &operand_ty)
        } else {
            b.v.clone()
        };
        let a_v = if a.ty != operand_ty {
            self.fx.convert(&a.v, &a.ty, &operand_ty)
        } else {
            a.v.clone()
        };
        let ll = self.fx.ll(&operand_ty);
        let float = matches!(
            operand_ty,
            Ty::Primitive(PrimitiveTy::Float | PrimitiveTy::Double)
        );
        let pointer = self.fx.cx.is_ptr(&operand_ty);
        let compare = |op: BinOp| -> &'static str {
            match (op, float) {
                (BinOp::Eq, false) => "icmp eq",
                (BinOp::Ne, false) => "icmp ne",
                (BinOp::Lt, false) => "icmp slt",
                (BinOp::Le, false) => "icmp sle",
                (BinOp::Gt, false) => "icmp sgt",
                (BinOp::Ge, false) => "icmp sge",
                (BinOp::Eq, true) => "fcmp oeq",
                (BinOp::Ne, true) => "fcmp une",
                (BinOp::Lt, true) => "fcmp olt",
                (BinOp::Le, true) => "fcmp ole",
                (BinOp::Gt, true) => "fcmp ogt",
                _ => "fcmp oge",
            }
        };
        let (ty, v) = match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let ll = if pointer {
                    "ptr".to_owned()
                } else {
                    ll.clone()
                };
                let instruction = compare(op);
                let instruction = if pointer {
                    instruction.replace("slt", "ult").replace("sgt", "ugt")
                } else {
                    instruction.to_owned()
                };
                (
                    Ty::BOOLEAN,
                    self.fx.assign(format!("{instruction} {ll} {a_v}, {b_v}")),
                )
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                let name = match (op, float) {
                    (BinOp::Add, false) => "add",
                    (BinOp::Sub, false) => "sub",
                    (BinOp::Mul, false) => "mul",
                    (BinOp::Add, true) => "fadd",
                    (BinOp::Sub, true) => "fsub",
                    _ => "fmul",
                };
                (
                    operand_ty.clone(),
                    self.fx.assign(format!("{name} {ll} {a_v}, {b_v}")),
                )
            }
            BinOp::Div | BinOp::Rem if float => {
                let name = if op == BinOp::Div { "fdiv" } else { "frem" };
                (
                    operand_ty.clone(),
                    self.fx.assign(format!("{name} {ll} {a_v}, {b_v}")),
                )
            }
            BinOp::Div | BinOp::Rem => {
                let minus_one = self.fx.assign(format!("icmp eq {ll} {b_v}, -1"));
                let divisor = self
                    .fx
                    .assign(format!("select i1 {minus_one}, {ll} 1, {ll} {b_v}"));
                let (name, special) = if op == BinOp::Div {
                    let negated = self.fx.assign(format!("sub {ll} 0, {a_v}"));
                    ("sdiv", negated)
                } else {
                    ("srem", "0".to_owned())
                };
                let normal = self.fx.assign(format!("{name} {ll} {a_v}, {divisor}"));
                (
                    operand_ty.clone(),
                    self.fx.assign(format!(
                        "select i1 {minus_one}, {ll} {special}, {ll} {normal}"
                    )),
                )
            }
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
                let name = match op {
                    BinOp::BitAnd => "and",
                    BinOp::BitOr => "or",
                    _ => "xor",
                };
                (
                    operand_ty.clone(),
                    self.fx.assign(format!("{name} {ll} {a_v}, {b_v}")),
                )
            }
            BinOp::Shl | BinOp::Shr | BinOp::UShr => {
                let width = if ll == "i64" { 63 } else { 31 };
                let amount_ty = b.ty.clone();
                let amount = match (amount_ty.primitive(), operand_ty.primitive()) {
                    (Some(from), Some(to)) => self.fx.numeric(&b.v, from, to),
                    _ => b.v.clone(),
                };
                let masked = self.fx.assign(format!("and {ll} {amount}, {width}"));
                let name = match op {
                    BinOp::Shl => "shl",
                    BinOp::Shr => "ashr",
                    _ => "lshr",
                };
                (
                    operand_ty.clone(),
                    self.fx.assign(format!("{name} {ll} {a_v}, {masked}")),
                )
            }
            BinOp::And | BinOp::Or => {
                let name = if op == BinOp::And { "and" } else { "or" };
                (
                    Ty::BOOLEAN,
                    self.fx.assign(format!("{name} i1 {a_v}, {b_v}")),
                )
            }
            BinOp::Elvis => (dest.clone(), a_v.clone()),
        };
        self.release(&a, a_owned);
        self.release(&b, b_owned);
        Val { ty, v }
    }

    fn aggregate(&mut self, kind: &AggregateKind, operands: &[Operand], dest: &Ty) -> Val {
        match kind {
            AggregateKind::Array(elem) => {
                let elem = self.fx.sub(elem);
                let array_ty = Ty::Array(Box::new(elem.clone()));
                let array = self.fx.new_array(&array_ty, &operands.len().to_string());
                let elem_ll = self.fx.cx.mem_llty(&elem);
                for (index, operand) in operands.iter().enumerate() {
                    let value = self.operand_owned(operand);
                    let converted = self.fx.convert(&value.v, &value.ty, &elem);
                    let address = self.fx.assign(format!(
                        "getelementptr inbounds {}, ptr {array}, i32 0, i32 2, i64 {index}",
                        array_ll(&elem_ll)
                    ));
                    self.fx.store(&elem, &converted, &address);
                }
                Val {
                    ty: array_ty,
                    v: array,
                }
            }
            AggregateKind::Record { def, ty } => {
                let ty = self.fx.sub(ty);
                let args = match &ty {
                    Ty::Adt { args, .. } => args.clone(),
                    _ => Vec::new(),
                };
                let fields = self.fx.cx.record_fields(*def, &args);
                let ll = self.fx.ll(&ty);
                let mut current = "zeroinitializer".to_owned();
                for (index, (operand, (_, field_ty))) in operands.iter().zip(&fields).enumerate() {
                    let value = self.operand_owned(operand);
                    let converted = self.fx.convert(&value.v, &value.ty, field_ty);
                    let converted = self.fx.wrap_indirect(&ty, field_ty, &converted);
                    let field_ll = self.fx.cx.field_llty(&ty, field_ty);
                    current = self.fx.assign(format!(
                        "insertvalue {ll} {current}, {field_ll} {converted}, {index}"
                    ));
                }
                Val { ty, v: current }
            }
            AggregateKind::Variant { def, index, ty } => {
                let ty = self.fx.sub(ty);
                let args = match &ty {
                    Ty::Adt { args, .. } => args.clone(),
                    _ => Vec::new(),
                };
                let slot = self.fx.alloca(&ty);
                let variant_ll = self.fx.cx.variant_type(*def, &args, *index);
                let tag = self.fx.assign(format!(
                    "getelementptr inbounds {variant_ll}, ptr {slot}, i32 0, i32 0"
                ));
                self.fx.line(format!("store i32 {index}, ptr {tag}"));
                let fields = self.fx.cx.variant_fields(*def, &args, *index);
                for (position, (operand, (_, field_ty))) in operands.iter().zip(&fields).enumerate()
                {
                    let value = self.operand_owned(operand);
                    let converted = self.fx.convert(&value.v, &value.ty, field_ty);
                    let address = self.fx.assign(format!(
                        "getelementptr inbounds {variant_ll}, ptr {slot}, i32 0, i32 {}",
                        position + 1
                    ));
                    if self.fx.cx.is_indirect(&ty, field_ty) {
                        let cell = self.fx.wrap_indirect(&ty, field_ty, &converted);
                        self.fx.line(format!("store ptr {cell}, ptr {address}"));
                    } else {
                        self.fx.store(field_ty, &converted, &address);
                    }
                }
                let v = self.fx.load(&ty, &slot);
                self.fx.zero(&ty, &slot);
                Val { ty, v }
            }
            AggregateKind::Closure(target) => self.closure(target, operands, dest),
        }
    }

    fn closure(&mut self, target: &ClosureTarget, operands: &[Operand], dest: &Ty) -> Val {
        let iface = dest.non_null().clone();
        let values: Vec<Val> = operands
            .iter()
            .map(|operand| self.operand_owned(operand))
            .collect();
        let captures: Vec<Ty> = values.iter().map(|value| value.ty.clone()).collect();
        let kind = match target {
            ClosureTarget::Lambda(body) => {
                let args = match &self.fx.cx.instances[self.instance] {
                    Instance::Body { args, .. } => args.clone(),
                    _ => Vec::new(),
                };
                ClosureKind::Lambda { body: *body, args }
            }
            ClosureTarget::MethodRef { callee, constructs } => ClosureKind::MethodRef {
                callee: callee.clone(),
                subst: self.fx.subst.clone(),
                bound: captures.first().cloned(),
                constructs: *constructs,
            },
        };
        let index = self.fx.cx.closure_info(ClosureInfo {
            iface: iface.clone(),
            captures: captures.clone(),
            kind,
        });
        let descriptor = self.fx.cx.rt_global(RtKey::Closure(index));
        self.fx.cx.drop_closure_fn(index);
        let object = self
            .fx
            .runtime("ptr", "kr_new_object", &format!("ptr {descriptor}"));
        let closure_ll = self.fx.cx.closure_type(index);
        for (position, value) in values.iter().enumerate() {
            let address = self.fx.assign(format!(
                "getelementptr inbounds {closure_ll}, ptr {object}, i32 0, i32 {}",
                position + 1
            ));
            self.fx.store(&value.ty, &value.v, &address);
        }
        Val {
            ty: iface,
            v: object,
        }
    }

    fn terminator(&mut self, kind: &TerminatorKind) {
        match kind {
            TerminatorKind::Goto { target } => {
                self.fx.line(format!("br label %bb{}", target.index()));
            }
            TerminatorKind::SwitchInt {
                discr,
                targets,
                otherwise,
            } => {
                let (value, owned) = self.operand_read(discr);
                let ll = self.fx.ll(&value.ty);
                let cases: Vec<String> = targets
                    .iter()
                    .map(|(constant, block)| {
                        let constant = if ll == "i1" {
                            (*constant != 0).to_string()
                        } else {
                            (*constant as i64).to_string()
                        };
                        format!("{ll} {constant}, label %bb{}", block.index())
                    })
                    .collect();
                self.release(&value, owned);
                self.fx.line(format!(
                    "switch {ll} {}, label %bb{} [ {} ]",
                    value.v,
                    otherwise.index(),
                    cases.join(" ")
                ));
            }
            TerminatorKind::Return => {
                self.drop_locals(false);
                let ret = self.locals[0].clone();
                if ret == Ty::Void {
                    self.fx.line("ret void");
                } else {
                    let slot = self.slots[0].clone();
                    let value = self.fx.load(&ret, &slot);
                    let ll = self.fx.ll(&ret);
                    self.fx.line(format!("ret {ll} {value}"));
                }
            }
            TerminatorKind::Unreachable => self.fx.line("unreachable"),
            TerminatorKind::Suspend { .. } => {
                let (k, _) = self.suspends[&self.block];
                let state = self.state.clone().expect("only `async` bodies suspend");
                self.fx.line(format!("store i32 {k}, ptr {state}"));
                let ret = self.locals[0].clone();
                let slot = self.slots[0].clone();
                let value = self.fx.load(&ret, &slot);
                let ll = self.fx.ll(&ret);
                self.fx.line(format!("ret {ll} {value}"));
            }
            TerminatorKind::Throw { value, unwind } => {
                let value = self.operand_owned(value);
                let throwable = self.fx.cx.lang_ty(LangItem::Throwable);
                let object = self.fx.convert(&value.v, &value.ty, &throwable);
                self.fx.line(format!("store ptr {object}, ptr @kr_pending"));
                let label = self.unwind_label(unwind);
                self.fx.line(format!("br label %{label}"));
            }
            TerminatorKind::Assert {
                check,
                target,
                unwind,
            } => self.assert(check, *target, unwind),
            TerminatorKind::Call {
                callee,
                dispatch,
                args,
                dest,
                target,
                unwind,
            } => self.call(callee, *dispatch, args, dest.as_ref(), *target, unwind),
        }
    }

    fn assert(&mut self, check: &Check, target: BasicBlock, unwind: &Unwind) {
        let unwind = self.unwind_label(unwind);
        let fail = self.fx.label("check");
        let ok = format!("bb{}", target.index());
        match check {
            Check::Bounds { index, len } => {
                let (index, _) = self.operand_read(index);
                let (len, _) = self.operand_read(len);
                let inside = self
                    .fx
                    .assign(format!("icmp ult i32 {}, {}", index.v, len.v));
                self.fx
                    .line(format!("br i1 {inside}, label %{ok}, label %{fail}"));
                self.fx.start(&fail);
                let wide_index = self.fx.assign(format!("sext i32 {} to i64", index.v));
                let wide_len = self.fx.assign(format!("sext i32 {} to i64", len.v));
                let message = self.fx.runtime(
                    "ptr",
                    "kr_string_bounds",
                    &format!("i64 {wide_index}, i64 {wide_len}"),
                );
                self.fx
                    .throw_with(LangItem::IndexOutOfBoundsException, &message, &unwind);
                self.fx.line("unreachable");
            }
            Check::NonZero(divisor) => {
                let (divisor, _) = self.operand_read(divisor);
                let ll = self.fx.ll(&divisor.ty);
                let nonzero = self.fx.assign(format!("icmp ne {ll} {}, 0", divisor.v));
                self.fx
                    .line(format!("br i1 {nonzero}, label %{ok}, label %{fail}"));
                self.fx.start(&fail);
                self.fx
                    .throw_new(LangItem::ArithmeticException, "/ by zero", &unwind);
                self.fx.line("unreachable");
            }
            Check::InstanceOf { place, ty } => {
                let target = self.fx.sub(ty);
                let (address, place_ty) = self.place_addr(place);
                let passes = match self.fx.cx.shape(&place_ty) {
                    Shape::Ptr(_) => {
                        let object = self.fx.assign(format!("load ptr, ptr {address}"));
                        let is_null = self.fx.assign(format!("icmp eq ptr {object}, null"));
                        let is = self.fx.object_is(&object, &target);
                        self.fx.assign(format!("or i1 {is_null}, {is}"))
                    }
                    _ => self.instance_of(&address, &place_ty, &target),
                };
                self.fx
                    .line(format!("br i1 {passes}, label %{ok}, label %{fail}"));
                self.fx.start(&fail);
                let object = self.fx.assign(format!("load ptr, ptr {address}"));
                let name = self.fx.cx.box_name(&target);
                let name = self.fx.cx.string_literal(&name);
                let message = self.fx.runtime(
                    "ptr",
                    "kr_string_cast",
                    &format!("ptr {object}, ptr {name}"),
                );
                self.fx
                    .throw_with(LangItem::ClassCastException, &message, &unwind);
                self.fx.line("unreachable");
            }
        }
    }

    fn call(
        &mut self,
        callee: &Callee,
        dispatch: Dispatch,
        args: &[Operand],
        dest: Option<&Place>,
        target: BasicBlock,
        unwind: &Unwind,
    ) {
        let unwind = self.unwind_label(unwind);
        let values: Vec<Val> = args
            .iter()
            .map(|operand| self.operand_owned(operand))
            .collect();
        let full: Subst = callee
            .subst
            .iter()
            .map(|(name, ty)| (*name, ty.subst(&self.fx.subst)))
            .collect();
        let method = &callee.method;
        let has_receiver = self.fx.cx.receiver_kind(method).is_some() && !values.is_empty();
        let (result, result_ty) = if has_receiver && dispatch == Dispatch::Virtual {
            let selector = self.fx.cx.selector_for(callee, &self.fx.subst);
            let receiver = values[0].clone();
            let result = self
                .fx
                .dispatch(&selector, &receiver.ty, &receiver.v, &values[1..]);
            (result, selector.ret.clone())
        } else {
            let self_ty = if has_receiver {
                values[0].ty.strip_refs().non_null().clone()
            } else {
                self.fx.cx.tcx.self_ty(method.owner).subst(&full)
            };
            let instance = self.fx.cx.instance_for(method, &full, &self_ty);
            let params = self.fx.cx.instance_params(&instance);
            let ret = self.fx.cx.instance_ret(&instance);
            let mut rendered = Vec::new();
            for (index, value) in values.iter().enumerate() {
                let param = params.get(index).cloned().unwrap_or(value.ty.clone());
                let converted = self.fx.convert(&value.v, &value.ty, &param);
                let ll = self.fx.ll(&param);
                rendered.push((ll, converted));
            }
            let id = self.fx.cx.instance(instance);
            let result = self.fx.call_instance(id, &rendered, &ret);
            (result, ret)
        };
        self.fx.release_borrowed_boxes();
        self.fx.check_pending(&unwind);
        if let Some(dest) = dest
            && result_ty != Ty::Void
        {
            let (address, ty) = self.place_addr(dest);
            let converted = self.fx.convert(&result, &result_ty, &ty);
            self.store_owned(&ty, &converted, &address);
        }
        self.fx.line(format!("br label %bb{}", target.index()));
    }
}

impl FnCx<'_, '_, '_> {
    pub(crate) fn object_is(&mut self, object: &str, target: &Ty) -> String {
        let target = target.non_null().clone();
        let object_ty = self.cx.lang_ty(LangItem::Object);
        if target == object_ty {
            return self.assign(format!("icmp ne ptr {object}, null"));
        }
        let key = self.cx.instance_target(&target);
        let exact = matches!(key, RtKey::Box(_) | RtKey::Array(_) | RtKey::String);
        let descriptor = self.cx.rt_global(key);
        if exact {
            let is_null = self.assign(format!("icmp eq ptr {object}, null"));
            let present = self.label("typed");
            let absent = self.label("untyped");
            let join = self.label("typedone");
            self.line(format!(
                "br i1 {is_null}, label %{absent}, label %{present}"
            ));
            self.start(&present);
            let actual = self.assign(format!("load ptr, ptr {object}"));
            let same = self.assign(format!("icmp eq ptr {actual}, {descriptor}"));
            self.line(format!("br label %{join}"));
            self.start(&absent);
            self.line(format!("br label %{join}"));
            self.start(&join);
            self.assign(format!(
                "phi i1 [ {same}, %{present} ], [ false, %{absent} ]"
            ))
        } else {
            self.runtime(
                "i1",
                "kr_instance_of",
                &format!("ptr {object}, ptr {descriptor}"),
            )
        }
    }

    pub(crate) fn new_array(&mut self, array_ty: &Ty, len: &str) -> String {
        let Ty::Array(elem) = array_ty else {
            panic!("`{array_ty}` is not an array");
        };
        let elem = elem.as_ref().clone();
        let descriptor = self.cx.rt_global(RtKey::Array(array_ty.clone()));
        self.cx.drop_array_fn(array_ty);
        let (size, _) = self.cx.size_align(&elem);
        let bytes = self.assign(format!("mul i64 {len}, {size}"));
        let total = self.assign(format!("add i64 {bytes}, 16"));
        let array = self.runtime("ptr", "kr_alloc", &format!("i64 {total}"));
        self.line(format!("store ptr {descriptor}, ptr {array}"));
        let len_addr = self.assign(format!(
            "getelementptr inbounds {{ ptr, i64 }}, ptr {array}, i32 0, i32 1"
        ));
        self.line(format!("store i64 {len}, ptr {len_addr}"));
        array
    }
}

impl Cx<'_, '_> {
    pub(crate) fn closure_info(&mut self, info: ClosureInfo) -> usize {
        if let ClosureKind::Lambda { body, args } = &info.kind
            && let Some(&index) = self.closure_bodies.get(&(*body, args.clone()))
        {
            return index;
        }
        let index = self.closures.len();
        if let ClosureKind::Lambda { body, args } = &info.kind {
            self.closure_bodies.insert((*body, args.clone()), index);
        }
        self.closures.push(info);
        index
    }

    pub(crate) fn instance_params(&mut self, instance: &Instance) -> Vec<Ty> {
        match instance {
            Instance::Body { body, args } => {
                let subst = self.body_subst(*body, args);
                let mir = self.mir.body(*body);
                (1..=mir.arg_count)
                    .map(|index| mir.locals[index].ty.subst(&subst))
                    .collect()
            }
            Instance::AsyncPoll { body, args } => {
                let index = self.async_frame(*body, args);
                let future = self.frame_future(index);
                let subst = self.body_subst(*body, args);
                let mir = self.mir.body(*body);
                let cx = mir.locals[mir.arg_count + 1].ty.subst(&subst);
                vec![
                    Ty::Ref {
                        mutable: true,
                        ty: Box::new(future),
                    },
                    cx,
                ]
            }
            Instance::Builtin {
                owner,
                name,
                member,
                args,
                self_ty,
            } => {
                let method = self.builtin_method(*owner, *name, *member);
                let subst = self.subst_of(&self.method_generics(&method), args);
                let mut params = Vec::new();
                match self.receiver_kind(&method) {
                    Some(ReceiverKind::Owned) => params.push(self_ty.clone()),
                    Some(kind) => params.push(Ty::Ref {
                        mutable: kind == ReceiverKind::RefMut,
                        ty: Box::new(self_ty.clone()),
                    }),
                    None => {}
                }
                params.extend(method.params.iter().map(|ty| ty.subst(&subst)));
                params
            }
            _ => Vec::new(),
        }
    }

    pub(crate) fn instance_ret(&mut self, instance: &Instance) -> Ty {
        match instance {
            Instance::Body { body, args } if self.mir.body(*body).asyncness.is_some() => {
                let index = self.async_frame(*body, args);
                self.frame_future(index)
            }
            Instance::Body { body, args } | Instance::AsyncPoll { body, args } => {
                let subst = self.body_subst(*body, args);
                self.mir.body(*body).locals[0].ty.subst(&subst)
            }
            Instance::Builtin {
                owner,
                name,
                member,
                args,
                ..
            } => {
                let method = self.builtin_method(*owner, *name, *member);
                let subst = self.subst_of(&self.method_generics(&method), args);
                method.ret.subst(&subst)
            }
            _ => Ty::Void,
        }
    }

    pub(crate) fn builtin_method(
        &self,
        owner: DefId,
        name: krelpin_span::Symbol,
        member: Option<u32>,
    ) -> krelpin_typeck::MethodSig {
        let sig = self.tcx.sig(owner);
        sig.methods
            .get(&name)
            .into_iter()
            .flatten()
            .chain(&sig.ctors)
            .find(|method| method.member == member && method.name.name == name)
            .cloned()
            .unwrap_or_else(|| panic!("`{}` has no method `{name}`", sig.name.name))
    }
}

pub(crate) fn is_concrete(ty: &Ty) -> bool {
    match ty {
        Ty::Param(_) | Ty::Unknown => false,
        Ty::Adt { args, .. } => args.iter().all(is_concrete),
        Ty::Ref { ty, .. } | Ty::Nullable(ty) | Ty::Array(ty) => is_concrete(ty),
        Ty::Primitive(_) | Ty::Void | Ty::Null => true,
    }
}

fn parse_int(text: &str) -> i64 {
    let cleaned: String = text
        .chars()
        .filter(|c| *c != '_')
        .collect::<String>()
        .to_ascii_lowercase();
    let (digits, radix) = if let Some(rest) = cleaned.strip_prefix("0x") {
        (rest, 16)
    } else if let Some(rest) = cleaned.strip_prefix("0b") {
        (rest, 2)
    } else if let Some(rest) = cleaned.strip_prefix("0o") {
        (rest, 8)
    } else {
        (cleaned.as_str(), 10)
    };
    u64::from_str_radix(digits, radix).map_or(0, |value| value as i64)
}
