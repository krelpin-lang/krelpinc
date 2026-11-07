use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::fmt::Write;

use krelpin_ast::ast::{FieldStorage, ReceiverKind};
use krelpin_errors::Diagnostic;
use krelpin_mir::{BodyId, BodySource, Mir};
use krelpin_span::Symbol;
use krelpin_span::def_id::DefId;
use krelpin_typeck::{Callee, LangItem, Tcx, Ty};

use crate::instance::{Instance, Selector};
use crate::rtti::{ClosureInfo, RtInfo, RtKey};

pub(crate) struct StaticInfo {
    pub ty: Ty,
    pub global: String,
    pub init: Option<usize>,
    pub deps: Vec<usize>,
}

pub(crate) struct Cx<'a, 'tcx> {
    pub mir: &'a Mir,
    pub tcx: &'a Tcx<'tcx>,
    pub body_of: HashMap<(DefId, u32), BodyId>,
    pub field_inits: HashMap<(DefId, Symbol), BodyId>,
    pub instances: Vec<Instance>,
    pub instance_ids: HashMap<Instance, usize>,
    pub queue: VecDeque<usize>,
    pub functions: Vec<String>,
    pub type_defs: Vec<String>,
    pub named_types: HashMap<Ty, String>,
    pub object_types: HashMap<Ty, String>,
    pub box_types: HashMap<Ty, String>,
    pub globals: Vec<String>,
    pub strings: HashMap<String, String>,
    pub declares: BTreeMap<String, String>,
    pub rt: Vec<RtInfo>,
    pub rt_ids: HashMap<RtKey, usize>,
    pub selectors: Vec<Selector>,
    pub selector_ids: HashMap<Selector, usize>,
    pub impls: BTreeMap<(usize, usize), String>,
    pub closures: Vec<ClosureInfo>,
    pub statics: Vec<StaticInfo>,
    pub static_ids: HashMap<(DefId, Symbol), usize>,
    pub current_static: Option<usize>,
    pub current_fn: Option<usize>,
    pub fn_statics: HashMap<usize, Vec<usize>>,
    pub fn_calls: HashMap<usize, Vec<usize>>,
    pub glue: HashMap<(char, Ty), String>,
    pub table_shapes: HashMap<(Ty, Ty), String>,
    pub errors: Vec<Diagnostic>,
    pub entry: Option<crate::main_fn::Compiled>,
    pub reported: HashSet<String>,
    pub closure_bodies: HashMap<(BodyId, Vec<Ty>), usize>,
    pub closure_types: HashMap<usize, String>,
    pub closure_drops: HashSet<usize>,
    pub message_fn: Option<usize>,
    pub async_frames: Vec<crate::asyncness::AsyncFrame>,
    pub async_frame_ids: HashMap<crate::asyncness::AsyncFrame, usize>,
    pub frame_types: HashMap<usize, String>,
    pub frame_drops: HashSet<usize>,
}

impl<'a, 'tcx> Cx<'a, 'tcx> {
    pub(crate) fn new(mir: &'a Mir, tcx: &'a Tcx<'tcx>) -> Self {
        let mut body_of = HashMap::new();
        let mut field_inits = HashMap::new();
        for (index, body) in mir.bodies.iter().enumerate() {
            let id = BodyId(index as u32);
            if let Some(member) = body.member {
                body_of.insert((body.owner, member), id);
            }
            if body.source == BodySource::FieldInit {
                field_inits.insert((body.owner, body.name), id);
            }
        }
        Cx {
            mir,
            tcx,
            body_of,
            field_inits,
            instances: Vec::new(),
            instance_ids: HashMap::new(),
            queue: VecDeque::new(),
            functions: Vec::new(),
            type_defs: Vec::new(),
            named_types: HashMap::new(),
            object_types: HashMap::new(),
            box_types: HashMap::new(),
            globals: Vec::new(),
            strings: HashMap::new(),
            declares: BTreeMap::new(),
            rt: Vec::new(),
            rt_ids: HashMap::new(),
            selectors: Vec::new(),
            selector_ids: HashMap::new(),
            impls: BTreeMap::new(),
            closures: Vec::new(),
            statics: Vec::new(),
            static_ids: HashMap::new(),
            current_static: None,
            current_fn: None,
            fn_statics: HashMap::new(),
            fn_calls: HashMap::new(),
            glue: HashMap::new(),
            table_shapes: HashMap::new(),
            errors: Vec::new(),
            entry: None,
            reported: HashSet::new(),
            closure_bodies: HashMap::new(),
            closure_types: HashMap::new(),
            closure_drops: HashSet::new(),
            message_fn: None,
            async_frames: Vec::new(),
            async_frame_ids: HashMap::new(),
            frame_types: HashMap::new(),
            frame_drops: HashSet::new(),
        }
    }

    pub(crate) fn compile(&mut self, entry: &crate::main_fn::Entry) {
        self.rt_key(RtKey::String);
        self.prepare_entry(entry);
        loop {
            while let Some(id) = self.queue.pop_front() {
                let instance = self.instances[id].clone();
                let text = self.emit_instance(id, &instance);
                self.functions.push(text);
            }
            self.complete_vtables();
            if self.queue.is_empty() {
                break;
            }
        }
    }

    pub(crate) fn instance(&mut self, instance: Instance) -> usize {
        let id = if let Some(&id) = self.instance_ids.get(&instance) {
            id
        } else {
            let id = self.instances.len();
            self.instances.push(instance.clone());
            self.instance_ids.insert(instance, id);
            self.queue.push_back(id);
            id
        };
        if let Some(current) = self.current_fn {
            let calls = self.fn_calls.entry(current).or_default();
            if !calls.contains(&id) {
                calls.push(id);
            }
        }
        id
    }

    fn note_static_use(&mut self, id: usize) {
        if let Some(current) = self.current_fn {
            let uses = self.fn_statics.entry(current).or_default();
            if !uses.contains(&id) {
                uses.push(id);
            }
        }
    }

    pub(crate) fn fn_name(&self, id: usize) -> String {
        let label = match &self.instances[id] {
            Instance::Body { body, args } => {
                let body = self.mir.body(*body);
                let owner = self.tcx.sig(body.owner).name.name;
                let args = if args.is_empty() {
                    String::new()
                } else {
                    let args: Vec<String> = args.iter().map(|ty| self.display(ty)).collect();
                    format!("<{}>", args.join(", "))
                };
                match body.source {
                    BodySource::Closure { index, .. } => {
                        format!("{owner}.{}{args}#{index}", body.name)
                    }
                    _ => format!("{owner}.{}{args}", body.name),
                }
            }
            Instance::Builtin {
                owner,
                name,
                self_ty,
                ..
            } => {
                format!(
                    "{}.{name}[{}]",
                    self.tcx.sig(*owner).name.name,
                    self.display(self_ty)
                )
            }
            Instance::AsyncPoll { body, .. } => {
                let body = self.mir.body(*body);
                format!("{}.{}$poll", self.tcx.sig(body.owner).name.name, body.name)
            }
            Instance::Thunk(_) => "thunk".to_owned(),
        };
        format!("@\"k{id}.{}\"", label.replace('"', "'"))
    }

    pub(crate) fn declare(&mut self, name: &str, signature: &str) {
        self.declares
            .entry(name.to_owned())
            .or_insert_with(|| signature.to_owned());
    }

    pub(crate) fn declare_dynamic(&mut self, name: &str, signature: &str) {
        self.declare(name, signature);
    }

    pub(crate) fn string_literal(&mut self, value: &str) -> String {
        if let Some(name) = self.strings.get(value) {
            return name.clone();
        }
        let name = format!("@\"str.{}\"", self.strings.len());
        let bytes = value.as_bytes();
        let chars = value.chars().count();
        let mut encoded = String::new();
        for &byte in bytes {
            if byte.is_ascii_alphanumeric() || byte == b' ' {
                encoded.push(byte as char);
            } else {
                let _ = write!(encoded, "\\{byte:02X}");
            }
        }
        self.globals.push(format!(
            "{name} = private unnamed_addr constant {{ ptr, i64, i64, i64, [{} x i8] }} \
             {{ ptr @kr_string_type, i64 -1, i64 {}, i64 {chars}, [{} x i8] c\"{encoded}\\00\" }}, \
             align 16",
            bytes.len() + 1,
            bytes.len(),
            bytes.len() + 1,
        ));
        self.strings.insert(value.to_owned(), name.clone());
        name
    }

    pub(crate) fn static_info(&mut self, owner: DefId, name: Symbol) -> usize {
        if let Some(&id) = self.static_ids.get(&(owner, name)) {
            self.note_static_use(id);
            if let Some(current) = self.current_static
                && current != id
                && !self.statics[current].deps.contains(&id)
            {
                self.statics[current].deps.push(id);
            }
            return id;
        }
        let ty = self
            .tcx
            .sig(owner)
            .fields
            .get(&name)
            .map_or(Ty::Unknown, |field| field.ty.clone());
        let id = self.statics.len();
        let global = format!("@\"static.{}.{name}\"", self.tcx.sig(owner).name.name);
        let llty = self.mem_llty(&ty);
        let zero = self.null_value(&ty);
        self.globals
            .push(format!("{global} = internal global {llty} {zero}"));
        self.statics.push(StaticInfo {
            ty,
            global,
            init: None,
            deps: Vec::new(),
        });
        self.static_ids.insert((owner, name), id);
        self.note_static_use(id);
        if let Some(current) = self.current_static {
            self.statics[current].deps.push(id);
        }
        if let Some(&body) = self.field_inits.get(&(owner, name)) {
            let init = self.instance(Instance::Body {
                body,
                args: Vec::new(),
            });
            self.statics[id].init = Some(init);
        }
        id
    }

    pub(crate) fn instance_static(&self, id: usize) -> Option<usize> {
        let Instance::Body { body, .. } = &self.instances[id] else {
            return None;
        };
        let body = self.mir.body(*body);
        if body.source != BodySource::FieldInit {
            return None;
        }
        let field = self.tcx.sig(body.owner).fields.get(&body.name)?;
        if field.storage == FieldStorage::Instance {
            return None;
        }
        self.static_ids.get(&(body.owner, body.name)).copied()
    }

    pub(crate) fn error(&mut self, diagnostic: Diagnostic) {
        if self.reported.insert(diagnostic.message.clone()) {
            self.errors.push(diagnostic);
        }
    }

    pub(crate) fn lang(&self, item: LangItem) -> DefId {
        self.tcx
            .lang_items
            .get(item)
            .unwrap_or_else(|| panic!("the standard library defines `{}`", item.path()))
    }

    pub(crate) fn lang_ty(&self, item: LangItem) -> Ty {
        self.tcx.lang_ty(item)
    }

    pub(crate) fn selector_for(&self, callee: &Callee, subst: &krelpin_typeck::Subst) -> Selector {
        let method = &callee.method;
        let full: krelpin_typeck::Subst = callee
            .subst
            .iter()
            .map(|(name, ty)| (*name, ty.subst(subst)))
            .collect();
        let owner_args: Vec<Ty> = self
            .tcx
            .sig(method.owner)
            .generics
            .iter()
            .map(|param| full.get(&param.name).cloned().unwrap_or(Ty::Unknown))
            .collect();
        Selector {
            owner: Ty::Adt {
                def: method.owner,
                name: self.tcx.ty_name(method.owner),
                args: owner_args,
            },
            name: method.name.name,
            params: method.params.iter().map(|ty| ty.subst(&full)).collect(),
            method_args: method
                .generics
                .iter()
                .map(|param| full.get(&param.name).cloned().unwrap_or(Ty::Unknown))
                .collect(),
            receiver: method.receiver.unwrap_or(ReceiverKind::Ref),
            ret: method.ret.subst(&full),
        }
    }

    pub(crate) fn finish(mut self) -> String {
        let selectors = self.selector_slots();
        self.emit_descriptors(&selectors);
        let main = self.emit_entry();
        let mut out = String::new();
        out.push_str("; ModuleID = 'krelpin'\n\n");
        out.push_str("%KrTableShape = type { ptr, ptr, ptr, ptr, i64, i64, i64, i64 }\n");
        for def in &self.type_defs {
            out.push_str(def);
            out.push('\n');
        }
        out.push('\n');
        out.push_str("@kr_pending = external thread_local global ptr\n");
        for global in &self.globals {
            out.push_str(global);
            out.push('\n');
        }
        out.push('\n');
        for signature in self.declares.values() {
            out.push_str(signature);
            out.push('\n');
        }
        out.push('\n');
        for function in &self.functions {
            out.push_str(&replace_slots(function, &selectors));
            out.push('\n');
        }
        out.push_str(&main);
        out
    }
}

fn replace_slots(text: &str, slots: &[usize]) -> String {
    if !text.contains("$slot.") {
        return text.to_owned();
    }
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(start) = rest.find("$slot.") {
        out.push_str(&rest[..start]);
        let after = &rest[start + 6..];
        let end = after.find('$').unwrap_or(after.len());
        let index: usize = after[..end].parse().unwrap_or(0);
        let _ = write!(out, "{}", slots[index]);
        rest = &after[(end + 1).min(after.len())..];
    }
    out.push_str(rest);
    out
}
