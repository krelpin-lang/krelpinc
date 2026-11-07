use std::collections::{BTreeSet, HashMap};
use std::fmt::Write;

use krelpin_ast::ast::ReceiverKind;
use krelpin_mir::BodyId;
use krelpin_typeck::{AdtKind, Callee, LangItem, ParamEnv, Subst, Ty};

use crate::cx::Cx;
use crate::instance::{Instance, Selector, Thunk};
use crate::layout::{PtrKind, Shape};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum RtKey {
    Class(Ty),
    Interface(Ty),
    Box(Ty),
    Array(Ty),
    Closure(usize),
    /// The future of an `async` body, by its index in `Cx::async_frames`.
    Async(usize),
    String,
}

pub(crate) struct RtInfo {
    pub key: RtKey,
    pub global: String,
    pub concrete: bool,
    pub checked: BTreeSet<usize>,
}

#[derive(Clone, Debug)]
pub(crate) enum ClosureKind {
    Lambda {
        body: BodyId,
        args: Vec<Ty>,
    },
    MethodRef {
        callee: Option<Box<Callee>>,
        subst: Subst,
        bound: Option<Ty>,
        constructs: bool,
    },
}

#[derive(Clone, Debug)]
pub(crate) struct ClosureInfo {
    pub iface: Ty,
    pub captures: Vec<Ty>,
    pub kind: ClosureKind,
}

pub(crate) const KIND_CLASS: i64 = 0;
pub(crate) const KIND_STRING: i64 = 1;
pub(crate) const KIND_ARRAY: i64 = 2;
pub(crate) const KIND_BOX: i64 = 3;
pub(crate) const KIND_CLOSURE: i64 = 4;
pub(crate) const KIND_INTERFACE: i64 = 5;

impl Cx<'_, '_> {
    pub(crate) fn rt_key(&mut self, key: RtKey) -> usize {
        if let Some(&id) = self.rt_ids.get(&key) {
            return id;
        }
        let id = self.rt.len();
        let global = match &key {
            RtKey::String => "@kr_string_type".to_owned(),
            _ => format!("@\"type.{id}\""),
        };
        let concrete = matches!(
            key,
            RtKey::Box(_) | RtKey::Array(_) | RtKey::Closure(_) | RtKey::Async(_) | RtKey::String
        );
        self.rt.push(RtInfo {
            key: key.clone(),
            global,
            concrete,
            checked: BTreeSet::new(),
        });
        self.rt_ids.insert(key.clone(), id);
        if let RtKey::Class(ty) = &key
            && let Some(parent) = self.superclass_of(ty)
        {
            self.rt_key(RtKey::Class(parent));
        }
        for iface in self.interfaces_of(&key) {
            self.rt_key(RtKey::Interface(iface));
        }
        id
    }

    pub(crate) fn rt_global(&mut self, key: RtKey) -> String {
        let id = self.rt_key(key);
        self.rt[id].global.clone()
    }

    pub(crate) fn concrete_class(&mut self, ty: &Ty) -> String {
        let id = self.rt_key(RtKey::Class(ty.clone()));
        self.rt[id].concrete = true;
        self.rt[id].global.clone()
    }

    pub(crate) fn instance_target(&mut self, ty: &Ty) -> RtKey {
        match self.shape(ty) {
            Shape::Ptr(PtrKind::String) => RtKey::String,
            Shape::Ptr(PtrKind::Array) => RtKey::Array(ty.clone()),
            Shape::Ptr(_) => {
                let Ty::Adt { def, .. } = ty else {
                    panic!("`{ty}` cannot be tested at run time");
                };
                if self.tcx.sig(*def).kind == AdtKind::Interface {
                    RtKey::Interface(ty.clone())
                } else {
                    RtKey::Class(ty.clone())
                }
            }
            _ => RtKey::Box(ty.clone()),
        }
    }

    pub(crate) fn superclass_of(&self, ty: &Ty) -> Option<Ty> {
        let Ty::Adt { def, args, .. } = ty else {
            return None;
        };
        let parent = self.tcx.sig(*def).superclass.clone()?;
        Some(parent.subst(&self.tcx.subst_for(*def, args)))
    }

    fn interfaces_of(&self, key: &RtKey) -> Vec<Ty> {
        let ty = match key {
            RtKey::Class(ty) | RtKey::Interface(ty) | RtKey::Box(ty) => ty.clone(),
            RtKey::String => self.tcx.string_ty(),
            RtKey::Closure(index) => self.closures[*index].iface.clone(),
            RtKey::Async(index) => self.frame_future(*index),
            RtKey::Array(_) => return Vec::new(),
        };
        let Some((def, args)) = self.adt_of(&ty) else {
            return Vec::new();
        };
        let subst = self.tcx.subst_for(def, &args);
        let mut out = Vec::new();
        if matches!(key, RtKey::Closure(_) | RtKey::Async(_)) {
            out.push(ty.clone());
        }
        for (parent, parent_subst) in self.tcx.supertypes(def) {
            if self.tcx.sig(parent).kind != AdtKind::Interface {
                continue;
            }
            let parent_args: Vec<Ty> = self
                .tcx
                .sig(parent)
                .generics
                .iter()
                .map(|param| {
                    parent_subst
                        .get(&param.name)
                        .map_or(Ty::Unknown, |ty| ty.subst(&subst))
                })
                .collect();
            let iface = Ty::Adt {
                def: parent,
                name: self.tcx.ty_name(parent),
                args: parent_args,
            };
            let holds = matches!(key, RtKey::Interface(_))
                || self.tcx.is_assignable(&ParamEnv::default(), &ty, &iface);
            if holds && !out.contains(&iface) {
                out.push(iface);
            }
        }
        out
    }

    pub(crate) fn selector(&mut self, selector: Selector) -> usize {
        if let Some(&id) = self.selector_ids.get(&selector) {
            return id;
        }
        let id = self.selectors.len();
        self.selectors.push(selector.clone());
        self.selector_ids.insert(selector, id);
        id
    }

    pub(crate) fn complete_vtables(&mut self) {
        for rt in 0..self.rt.len() {
            if !self.rt[rt].concrete {
                continue;
            }
            for selector in 0..self.selectors.len() {
                if !self.rt[rt].checked.insert(selector) {
                    continue;
                }
                if let Some(function) = self.vtable_entry(rt, selector) {
                    self.impls.insert((rt, selector), function);
                }
            }
        }
    }

    fn runtime_ty(&self, key: &RtKey) -> Ty {
        match key {
            RtKey::Class(ty) | RtKey::Interface(ty) | RtKey::Box(ty) | RtKey::Array(ty) => {
                ty.clone()
            }
            RtKey::String => self.tcx.string_ty(),
            RtKey::Closure(index) => self.closures[*index].iface.clone(),
            RtKey::Async(index) => self.frame_future(*index),
        }
    }

    fn implements_conditionally(&self, ty: &Ty, selector: &Selector) -> bool {
        let object = self.lang_ty(LangItem::Object);
        if selector.owner == object {
            return true;
        }
        self.tcx
            .is_assignable(&ParamEnv::default(), ty, &selector.owner)
    }

    fn implements_structurally(&self, ty: &Ty, selector: &Selector) -> bool {
        let Ty::Adt { def, args, .. } = &selector.owner else {
            return false;
        };
        let structural = [LangItem::Equatable, LangItem::Hashable, LangItem::Cloneable]
            .into_iter()
            .any(|item| self.tcx.lang_items.get(item) == Some(*def));
        structural
            && args
                .first()
                .is_some_and(|target| self.is_subtype(ty, target))
    }

    fn vtable_entry(&mut self, rt: usize, selector_id: usize) -> Option<String> {
        let selector = self.selectors[selector_id].clone();
        let key = self.rt[rt].key.clone();
        let ty = self.runtime_ty(&key);
        let object = self.lang_ty(LangItem::Object);
        let applies = match &key {
            RtKey::Array(_) => selector.owner == object,
            _ => {
                (self.is_subtype(&ty, &selector.owner)
                    && self.implements_conditionally(&ty, &selector))
                    || self.implements_structurally(&ty, &selector)
            }
        };
        if !applies {
            return None;
        }
        if let RtKey::Closure(index) = &key
            && selector.owner != object
            && self.tcx.sig(self.adt_of(&selector.owner)?.0).kind == AdtKind::Interface
        {
            let thunk = match self.closures[*index].kind {
                ClosureKind::Lambda { .. } => Thunk::Lambda {
                    closure: *index,
                    selector: selector_id,
                },
                ClosureKind::MethodRef { .. } => Thunk::MethodRef {
                    closure: *index,
                    selector: selector_id,
                },
            };
            if self.is_functional_method(&selector) {
                let id = self.instance(Instance::Thunk(thunk));
                return Some(self.fn_name(id));
            }
        }
        if let RtKey::Async(index) = &key
            && self.is_future_poll(&selector)
        {
            let frame = self.async_frames[*index].clone();
            let id = self.instance(Instance::AsyncPoll {
                body: frame.body,
                args: frame.args,
            });
            return Some(self.fn_name(id));
        }
        let lookup_ty = match &key {
            RtKey::Array(_) | RtKey::Closure(_) | RtKey::Async(_) => object.clone(),
            _ => ty.clone(),
        };
        let resolved = match &key {
            RtKey::Closure(index) => {
                let iface = self.closures[*index].iface.clone();
                self.find_impl(&iface, &selector)
                    .or_else(|| self.find_impl(&lookup_ty, &selector))?
            }
            _ => self.find_impl(&lookup_ty, &selector)?,
        };
        let target = self.resolved_instance(&resolved, &ty);
        let impl_receiver = self
            .receiver_kind(&resolved.method)
            .unwrap_or(ReceiverKind::Ref);
        let needs_thunk = matches!(key, RtKey::Box(_))
            || (impl_receiver == ReceiverKind::Owned) != (selector.receiver == ReceiverKind::Owned);
        let id = if needs_thunk {
            self.instance(Instance::Thunk(Thunk::Boxed {
                value: ty,
                selector: selector_id,
                target: Box::new(target),
            }))
        } else {
            self.instance(target)
        };
        Some(self.fn_name(id))
    }

    fn is_functional_method(&self, selector: &Selector) -> bool {
        let Some(sig) = self.tcx.fn_sig(&selector.owner) else {
            return false;
        };
        sig.name == selector.name && sig.params == selector.params
    }

    pub(crate) fn selector_slots(&self) -> Vec<usize> {
        let mut by_rt: HashMap<usize, Vec<usize>> = HashMap::new();
        for &(rt, selector) in self.impls.keys() {
            by_rt.entry(rt).or_default().push(selector);
        }
        let mut neighbours: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); self.selectors.len()];
        for selectors in by_rt.values() {
            for &a in selectors {
                for &b in selectors {
                    if a != b {
                        neighbours[a].insert(b);
                    }
                }
            }
        }
        let mut slots: Vec<Option<usize>> = vec![None; self.selectors.len()];
        for selector in 0..self.selectors.len() {
            let taken: BTreeSet<usize> = neighbours[selector]
                .iter()
                .filter_map(|&other| slots[other])
                .collect();
            let slot = (0..).find(|slot| !taken.contains(slot)).unwrap_or(0);
            slots[selector] = Some(slot);
        }
        slots.into_iter().map(|slot| slot.unwrap_or(0)).collect()
    }

    pub(crate) fn emit_descriptors(&mut self, slots: &[usize]) {
        let mut index = 0;
        while index < self.rt.len() {
            self.emit_descriptor(index, slots);
            index += 1;
        }
    }

    fn emit_descriptor(&mut self, rt: usize, slots: &[usize]) {
        let key = self.rt[rt].key.clone();
        let ty = self.runtime_ty(&key);
        let name = match &key {
            RtKey::Box(ty) => self.box_name(ty),
            RtKey::Closure(_) => format!("{}$lambda", self.display(&ty)),
            RtKey::Async(index) => self.frame_name(*index),
            RtKey::Array(ty) => self.display(ty),
            _ => self.display(&ty),
        };
        let name_global = format!("@\"name.{rt}\"");
        self.globals.push(format!(
            "{name_global} = private unnamed_addr constant [{} x i8] c\"{}\\00\"",
            name.len() + 1,
            escape_bytes(&name)
        ));
        let parent = match &key {
            RtKey::Class(ty) => self
                .superclass_of(ty)
                .map(|parent| self.rt_global(RtKey::Class(parent))),
            _ => None,
        };
        let ifaces: Vec<String> = self
            .interfaces_of(&key)
            .into_iter()
            .map(|iface| self.rt_global(RtKey::Interface(iface)))
            .collect();
        let ifaces_global = format!("@\"ifaces.{rt}\"");
        let mut entries: Vec<String> = ifaces.iter().map(|g| format!("ptr {g}")).collect();
        entries.push("ptr null".to_owned());
        self.globals.push(format!(
            "{ifaces_global} = private unnamed_addr constant [{} x ptr] [{}]",
            entries.len(),
            entries.join(", ")
        ));
        let (kind, size, drop) = match &key {
            RtKey::Class(ty) => {
                let concrete = self.rt[rt].concrete;
                let size = self.object_size(ty);
                let drop = if concrete {
                    self.drop_object_fn(ty)
                } else {
                    "null".to_owned()
                };
                (KIND_CLASS, size, drop)
            }
            RtKey::Interface(_) => (KIND_INTERFACE, 0, "null".to_owned()),
            RtKey::String => {
                self.declare("kr_string_release", "declare void @kr_string_release(ptr)");
                (KIND_STRING, 0, "@kr_string_release".to_owned())
            }
            RtKey::Box(value) => {
                let (size, _) = self.box_layout(value);
                (KIND_BOX, size, self.drop_box_fn(value))
            }
            RtKey::Array(array) => (KIND_ARRAY, 16, self.drop_array_fn(array)),
            RtKey::Closure(index) => {
                let size = self.closure_size(*index);
                (KIND_CLOSURE, size, self.drop_closure_fn(*index))
            }
            RtKey::Async(index) => {
                let size = self.frame_size(*index);
                (KIND_CLOSURE, size, self.drop_frame_fn(*index))
            }
        };
        let mut vtable: Vec<String> = Vec::new();
        for (&(owner, selector), function) in &self.impls {
            if owner != rt {
                continue;
            }
            let slot = slots[selector];
            if vtable.len() <= slot {
                vtable.resize(slot + 1, "ptr null".to_owned());
            }
            vtable[slot] = format!("ptr {function}");
        }
        let global = self.rt[rt].global.clone();
        let linkage = if matches!(key, RtKey::String) {
            "hidden "
        } else {
            "internal "
        };
        let mut text = String::new();
        let _ = write!(
            text,
            "{global} = {linkage}constant {{ ptr, ptr, ptr, i64, ptr, i64, i64, [{} x ptr] }} \
             {{ ptr {name_global}, ptr {}, ptr {drop}, i64 {size}, ptr {ifaces_global}, \
             i64 {kind}, i64 {}, [{} x ptr] [{}] }}, align 16",
            vtable.len(),
            parent.unwrap_or_else(|| "null".to_owned()),
            vtable.len(),
            vtable.len(),
            vtable.join(", ")
        );
        self.globals.push(text);
    }

    pub(crate) fn box_name(&self, ty: &Ty) -> String {
        match ty {
            Ty::Primitive(primitive) => {
                let item = LangItem::primitive(*primitive);
                self.tcx.lang_items.get(item).map_or_else(
                    || self.display(ty),
                    |def| self.tcx.sig(def).name.name.to_string(),
                )
            }
            _ => self.display(ty),
        }
    }

    pub(crate) fn box_type(&mut self, value: &Ty) -> String {
        if let Some(name) = self.box_types.get(value) {
            return name.clone();
        }
        let name = format!("%\"box.{}\"", self.type_key(value));
        self.box_types.insert(value.clone(), name.clone());
        let llty = self.mem_llty(value);
        self.type_defs
            .push(format!("{name} = type {{ ptr, {llty} }}"));
        name
    }

    pub(crate) fn box_layout(&mut self, value: &Ty) -> (u64, u64) {
        let inner = self.size_align(value);
        crate::layout::struct_layout(&[(8, 8), inner])
    }

    pub(crate) fn closure_type(&mut self, index: usize) -> String {
        if let Some(name) = self.closure_types.get(&index) {
            return name.clone();
        }
        let name = format!("%\"closure.{index}\"");
        self.closure_types.insert(index, name.clone());
        let mut tys = vec!["ptr".to_owned()];
        for ty in self.closures[index].captures.clone() {
            tys.push(self.mem_llty(&ty));
        }
        self.type_defs
            .push(format!("{name} = type {{ {} }}", tys.join(", ")));
        name
    }

    pub(crate) fn closure_size(&mut self, index: usize) -> u64 {
        let mut layout = vec![(8, 8)];
        for ty in self.closures[index].captures.clone() {
            layout.push(self.size_align(&ty));
        }
        crate::layout::struct_layout(&layout).0
    }
}

pub(crate) fn escape_bytes(text: &str) -> String {
    let mut out = String::new();
    for &byte in text.as_bytes() {
        if byte.is_ascii_graphic() && byte != b'"' && byte != b'\\' || byte == b' ' {
            out.push(byte as char);
        } else {
            let _ = write!(out, "\\{byte:02X}");
        }
    }
    out
}
