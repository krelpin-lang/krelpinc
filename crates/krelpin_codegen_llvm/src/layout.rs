use krelpin_ast::ast::{FieldStorage, PrimitiveTy};
use krelpin_span::Symbol;
use krelpin_span::def_id::DefId;
use krelpin_typeck::{AdtKind, LangItem, Ty};

use crate::cx::Cx;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Shape {
    Void,
    Prim(PrimitiveTy),
    Ptr(PtrKind),
    Record(DefId, Vec<Ty>),
    Enum(DefId, Vec<Ty>),
    NullableValue(Box<Ty>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PtrKind {
    Object,
    String,
    Array,
    Ref,
    Null,
}

/// The classes of `std.net` that keep a socket or a poller in a native slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NetClass {
    Listener,
    Stream,
    Udp,
    Poller,
}

#[derive(Clone, Debug)]
pub(crate) struct ClassField {
    pub owner: DefId,
    pub name: Symbol,
    pub ty: Ty,
}

impl Cx<'_, '_> {
    pub(crate) fn shape(&self, ty: &Ty) -> Shape {
        match ty {
            Ty::Primitive(primitive) => Shape::Prim(*primitive),
            Ty::Void => Shape::Void,
            Ty::Null => Shape::Ptr(PtrKind::Null),
            Ty::Ref { .. } => Shape::Ptr(PtrKind::Ref),
            Ty::Array(_) => Shape::Ptr(PtrKind::Array),
            Ty::Adt { def, args, .. } => {
                if self.tcx.is_string(ty) {
                    return Shape::Ptr(PtrKind::String);
                }
                if let Some(primitive) = self.tcx.lang_items.primitive_of(*def) {
                    return Shape::Prim(primitive);
                }
                match self.tcx.sig(*def).kind {
                    AdtKind::Record => Shape::Record(*def, args.clone()),
                    AdtKind::Enum => Shape::Enum(*def, args.clone()),
                    AdtKind::Class | AdtKind::Interface => Shape::Ptr(PtrKind::Object),
                }
            }
            Ty::Nullable(inner) => match self.shape(inner) {
                Shape::Ptr(kind) => Shape::Ptr(kind),
                _ => Shape::NullableValue(inner.clone()),
            },
            Ty::Param(name) => panic!("generic parameter `{name}` survived monomorphization"),
            Ty::Unknown => panic!("an unknown type reached codegen"),
        }
    }

    pub(crate) fn is_ptr(&self, ty: &Ty) -> bool {
        matches!(self.shape(ty), Shape::Ptr(_))
    }

    pub(crate) fn is_value_type(&self, ty: &Ty) -> bool {
        matches!(
            self.shape(ty),
            Shape::Prim(_) | Shape::Record(..) | Shape::Enum(..)
        )
    }

    pub(crate) fn llty(&mut self, ty: &Ty) -> String {
        match self.shape(ty) {
            Shape::Void => "void".to_owned(),
            Shape::Prim(primitive) => prim_llty(primitive).to_owned(),
            Shape::Ptr(_) => "ptr".to_owned(),
            Shape::Record(def, args) => self.record_type(def, &args),
            Shape::Enum(def, args) => self.enum_type(def, &args),
            Shape::NullableValue(inner) => format!("{{ i1, {} }}", self.llty(&inner)),
        }
    }

    pub(crate) fn mem_llty(&mut self, ty: &Ty) -> String {
        match self.shape(ty) {
            Shape::Void => "{}".to_owned(),
            _ => self.llty(ty),
        }
    }

    pub(crate) fn field_ty(&self, owner: DefId, args: &[Ty], name: Symbol) -> Ty {
        let subst = self.tcx.subst_for(owner, args);
        self.tcx
            .sig(owner)
            .fields
            .get(&name)
            .map_or(Ty::Unknown, |field| field.ty.subst(&subst))
    }

    pub(crate) fn record_fields(&self, def: DefId, args: &[Ty]) -> Vec<(Symbol, Ty)> {
        self.tcx
            .sig(def)
            .components
            .iter()
            .map(|name| (*name, self.field_ty(def, args, *name)))
            .collect()
    }

    pub(crate) fn variant_fields(
        &self,
        def: DefId,
        args: &[Ty],
        index: usize,
    ) -> Vec<(Symbol, Ty)> {
        let subst = self.tcx.subst_for(def, args);
        self.tcx.sig(def).variants[index]
            .fields
            .iter()
            .map(|field| (field.name.name, field.ty.subst(&subst)))
            .collect()
    }

    fn record_type(&mut self, def: DefId, args: &[Ty]) -> String {
        let key = Ty::Adt {
            def,
            name: self.tcx.sig(def).name.name,
            args: args.to_vec(),
        };
        if let Some(name) = self.named_types.get(&key) {
            return name.clone();
        }
        let name = format!("%\"rec.{}\"", self.type_key(&key));
        self.named_types.insert(key.clone(), name.clone());
        let fields: Vec<String> = self
            .record_fields(def, args)
            .iter()
            .map(|(_, ty)| self.field_llty(&key, ty))
            .collect();
        self.type_defs
            .push(format!("{name} = type {{ {} }}", fields.join(", ")));
        name
    }

    fn enum_type(&mut self, def: DefId, args: &[Ty]) -> String {
        let key = Ty::Adt {
            def,
            name: self.tcx.sig(def).name.name,
            args: args.to_vec(),
        };
        if let Some(name) = self.named_types.get(&key) {
            return name.clone();
        }
        let display = self.type_key(&key);
        let name = format!("%\"enum.{display}\"");
        self.named_types.insert(key.clone(), name.clone());
        let variants = self.tcx.sig(def).variants.len();
        let mut largest = 8;
        for index in 0..variants {
            let fields = self.variant_fields(def, args, index);
            let mut tys = vec!["i32".to_owned()];
            let mut layout = vec![(4, 4)];
            for (_, ty) in &fields {
                tys.push(self.field_llty(&key, ty));
                layout.push(self.field_layout(&key, ty));
            }
            let (size, _) = struct_layout(&layout);
            largest = largest.max(size);
            self.type_defs.push(format!(
                "%\"enum.{display}.v{index}\" = type {{ {} }}",
                tys.join(", ")
            ));
        }
        let words = largest.div_ceil(8);
        self.type_defs
            .push(format!("{name} = type [{words} x i64]"));
        name
    }

    pub(crate) fn variant_type(&mut self, def: DefId, args: &[Ty], index: usize) -> String {
        let key = Ty::Adt {
            def,
            name: self.tcx.sig(def).name.name,
            args: args.to_vec(),
        };
        self.enum_type(def, args);
        format!("%\"enum.{}.v{index}\"", self.type_key(&key))
    }

    pub(crate) fn size_align(&mut self, ty: &Ty) -> (u64, u64) {
        match self.shape(ty) {
            Shape::Void => (0, 1),
            Shape::Prim(primitive) => {
                let size = prim_size(primitive);
                (size, size)
            }
            Shape::Ptr(_) => (8, 8),
            Shape::Record(def, args) => {
                let layout: Vec<(u64, u64)> = self
                    .record_fields(def, &args)
                    .iter()
                    .map(|(_, field)| self.field_layout(ty, field))
                    .collect();
                struct_layout(&layout)
            }
            Shape::Enum(def, args) => {
                let variants = self.tcx.sig(def).variants.len();
                let mut largest = 8;
                let mut align = 4;
                for index in 0..variants {
                    let mut layout = vec![(4, 4)];
                    for (_, field) in self.variant_fields(def, &args, index) {
                        layout.push(self.field_layout(ty, &field));
                    }
                    let (size, variant_align) = struct_layout(&layout);
                    largest = largest.max(size);
                    align = align.max(variant_align);
                }
                let _ = align;
                (largest.div_ceil(8) * 8, 8)
            }
            Shape::NullableValue(inner) => {
                let inner = self.size_align(&inner);
                struct_layout(&[(1, 1), inner])
            }
        }
    }

    pub(crate) fn is_indirect(&self, container: &Ty, field: &Ty) -> bool {
        let mut visited = Vec::new();
        self.reaches(field, container, &mut visited)
    }

    fn reaches(&self, ty: &Ty, target: &Ty, visited: &mut Vec<Ty>) -> bool {
        let ty = ty.non_null();
        if ty == target {
            return true;
        }
        if visited.contains(ty) {
            return false;
        }
        visited.push(ty.clone());
        match self.shape(ty) {
            Shape::Record(def, args) => self
                .record_fields(def, &args)
                .iter()
                .any(|(_, field)| self.reaches(field, target, visited)),
            Shape::Enum(def, args) => (0..self.tcx.sig(def).variants.len()).any(|index| {
                self.variant_fields(def, &args, index)
                    .iter()
                    .any(|(_, field)| self.reaches(field, target, visited))
            }),
            Shape::NullableValue(inner) => self.reaches(&inner, target, visited),
            _ => false,
        }
    }

    pub(crate) fn field_llty(&mut self, container: &Ty, field: &Ty) -> String {
        if self.is_indirect(container, field) {
            "ptr".to_owned()
        } else {
            self.mem_llty(field)
        }
    }

    pub(crate) fn field_layout(&mut self, container: &Ty, field: &Ty) -> (u64, u64) {
        if self.is_indirect(container, field) {
            (8, 8)
        } else {
            self.size_align(field)
        }
    }

    pub(crate) fn needs_drop(&self, ty: &Ty) -> bool {
        match self.shape(ty) {
            Shape::Void | Shape::Prim(_) => false,
            Shape::Ptr(kind) => !matches!(kind, PtrKind::Ref | PtrKind::Null),
            Shape::Record(def, args) => self
                .record_fields(def, &args)
                .iter()
                .any(|(_, field)| self.is_indirect(ty, field) || self.needs_drop(field)),
            Shape::Enum(def, args) => (0..self.tcx.sig(def).variants.len()).any(|index| {
                self.variant_fields(def, &args, index)
                    .iter()
                    .any(|(_, field)| self.is_indirect(ty, field) || self.needs_drop(field))
            }),
            Shape::NullableValue(inner) => self.needs_drop(&inner),
        }
    }

    pub(crate) fn class_fields(&self, def: DefId, args: &[Ty]) -> Vec<ClassField> {
        let mut chain = vec![(def, args.to_vec())];
        let mut current = (def, args.to_vec());
        while let Some(parent) = self.tcx.sig(current.0).superclass.clone() {
            let parent = parent.subst(&self.tcx.subst_for(current.0, &current.1));
            let Ty::Adt { def, args, .. } = parent else {
                break;
            };
            chain.push((def, args.clone()));
            current = (def, args);
        }
        let mut fields = Vec::new();
        for (class, class_args) in chain.into_iter().rev() {
            let sig = self.tcx.sig(class);
            let mut own: Vec<_> = sig
                .fields
                .values()
                .filter(|field| field.storage == FieldStorage::Instance && field.owner == class)
                .collect();
            own.sort_by_key(|field| field.name.span.lo);
            let subst = self.tcx.subst_for(class, &class_args);
            for field in own {
                fields.push(ClassField {
                    owner: class,
                    name: field.name.name,
                    ty: field.ty.subst(&subst),
                });
            }
        }
        fields
    }

    pub(crate) fn net_class(&self, def: DefId) -> Option<NetClass> {
        let items = &self.tcx.lang_items;
        if items.is(def, LangItem::TcpListener) {
            Some(NetClass::Listener)
        } else if items.is(def, LangItem::TcpStream) {
            Some(NetClass::Stream)
        } else if items.is(def, LangItem::UdpSocket) {
            Some(NetClass::Udp)
        } else if items.is(def, LangItem::Poller) {
            Some(NetClass::Poller)
        } else {
            None
        }
    }

    pub(crate) fn net_class_of(&self, ty: &Ty) -> Option<NetClass> {
        match ty {
            Ty::Adt { def, .. } => self.net_class(*def),
            _ => None,
        }
    }

    pub(crate) fn native_fields(&self, def: DefId) -> Vec<&'static str> {
        let items = &self.tcx.lang_items;
        if items.is(def, LangItem::ArrayList) {
            vec!["ptr", "i64", "i64"]
        } else if items.is_table(def) {
            vec!["ptr", "i64", "i64", "i64", "ptr", "i64"]
        } else if items.is(def, LangItem::StringBuilder) {
            vec!["ptr", "i64", "i64", "i64"]
        } else if items.is(def, LangItem::Thread)
            || items.is(def, LangItem::FileReader)
            || items.is(def, LangItem::FileWriter)
            || items.is(def, LangItem::TcpListener)
            || items.is(def, LangItem::TcpStream)
            || items.is(def, LangItem::UdpSocket)
            || items.is(def, LangItem::Poller)
            || items.is(def, LangItem::Mutex)
            || items.is(def, LangItem::MutexGuard)
            || items.is(def, LangItem::ReadWriteLock)
            || items.is(def, LangItem::ReadGuard)
            || items.is(def, LangItem::WriteGuard)
        {
            vec!["ptr"]
        } else {
            Vec::new()
        }
    }

    pub(crate) fn object_type(&mut self, ty: &Ty) -> String {
        if let Some(name) = self.object_types.get(ty) {
            return name.clone();
        }
        let Ty::Adt { def, args, .. } = ty else {
            panic!("`{ty}` is not a class");
        };
        let name = format!("%\"obj.{}\"", self.type_key(ty));
        self.object_types.insert(ty.clone(), name.clone());
        let mut tys = vec!["ptr".to_owned()];
        for field in self.class_fields(*def, args) {
            tys.push(self.mem_llty(&field.ty));
        }
        for native in self.native_fields(*def) {
            tys.push(native.to_owned());
        }
        self.type_defs
            .push(format!("{name} = type {{ {} }}", tys.join(", ")));
        name
    }

    pub(crate) fn object_size(&mut self, ty: &Ty) -> u64 {
        let Ty::Adt { def, args, .. } = ty else {
            panic!("`{ty}` is not a class");
        };
        let mut layout = vec![(8, 8)];
        for field in self.class_fields(*def, args) {
            layout.push(self.size_align(&field.ty));
        }
        for native in self.native_fields(*def) {
            layout.push(if native == "i32" { (4, 4) } else { (8, 8) });
        }
        struct_layout(&layout).0
    }

    pub(crate) fn field_index(&self, ty: &Ty, owner: DefId, name: Symbol) -> usize {
        let Ty::Adt { def, args, .. } = ty else {
            panic!("`{ty}` has no fields");
        };
        self.class_fields(*def, args)
            .iter()
            .position(|field| field.owner == owner && field.name == name)
            .or_else(|| {
                self.class_fields(*def, args)
                    .iter()
                    .position(|field| field.name == name)
            })
            .map(|index| index + 1)
            .unwrap_or_else(|| panic!("`{ty}` has no field `{name}`"))
    }

    pub(crate) fn native_index(&self, ty: &Ty, slot: usize) -> usize {
        let Ty::Adt { def, args, .. } = ty else {
            panic!("`{ty}` has no native fields");
        };
        1 + self.class_fields(*def, args).len() + slot
    }

    pub(crate) fn display(&self, ty: &Ty) -> String {
        ty.to_string().replace('"', "'")
    }

    pub(crate) fn type_key(&self, ty: &Ty) -> String {
        let mut defs = Vec::new();
        collect_defs(ty, &mut defs);
        let mut key = self.display(ty);
        for def in defs {
            key.push_str(&format!(".d{}", def.index()));
        }
        key
    }

    pub(crate) fn null_value(&mut self, ty: &Ty) -> String {
        match self.shape(ty) {
            Shape::Ptr(_) => "null".to_owned(),
            _ => "zeroinitializer".to_owned(),
        }
    }
}

pub(crate) fn prim_llty(primitive: PrimitiveTy) -> &'static str {
    match primitive {
        PrimitiveTy::Boolean => "i1",
        PrimitiveTy::Byte => "i8",
        PrimitiveTy::Short => "i16",
        PrimitiveTy::Char | PrimitiveTy::Int => "i32",
        PrimitiveTy::Long => "i64",
        PrimitiveTy::Float => "float",
        PrimitiveTy::Double => "double",
    }
}

/// The extension attribute `ty` needs in a C signature. C widens integers
/// narrower than 32 bits to a full register, but the targets disagree on
/// whether the caller or the callee does it, so the attribute is spelled out
/// the way clang does.
pub(crate) fn c_abi_ext(ty: &Ty) -> Option<&'static str> {
    match ty {
        Ty::Primitive(PrimitiveTy::Boolean) => Some("zeroext"),
        Ty::Primitive(PrimitiveTy::Byte | PrimitiveTy::Short) => Some("signext"),
        _ => None,
    }
}

fn prim_size(primitive: PrimitiveTy) -> u64 {
    match primitive {
        PrimitiveTy::Boolean | PrimitiveTy::Byte => 1,
        PrimitiveTy::Short => 2,
        PrimitiveTy::Char | PrimitiveTy::Int | PrimitiveTy::Float => 4,
        PrimitiveTy::Long | PrimitiveTy::Double => 8,
    }
}

pub(crate) fn struct_layout(fields: &[(u64, u64)]) -> (u64, u64) {
    let mut offset: u64 = 0;
    let mut align: u64 = 1;
    for &(size, field_align) in fields {
        offset = offset.div_ceil(field_align) * field_align;
        offset += size;
        align = align.max(field_align);
    }
    (offset.div_ceil(align) * align, align)
}

pub(crate) fn field_offsets(fields: &[(u64, u64)]) -> Vec<u64> {
    let mut offset: u64 = 0;
    let mut offsets = Vec::new();
    for &(size, field_align) in fields {
        offset = offset.div_ceil(field_align) * field_align;
        offsets.push(offset);
        offset += size;
    }
    offsets
}

fn collect_defs(ty: &Ty, defs: &mut Vec<DefId>) {
    match ty {
        Ty::Adt { def, args, .. } => {
            defs.push(*def);
            for arg in args {
                collect_defs(arg, defs);
            }
        }
        Ty::Ref { ty, .. } | Ty::Nullable(ty) | Ty::Array(ty) => collect_defs(ty, defs),
        Ty::Primitive(_) | Ty::Void | Ty::Null | Ty::Param(_) | Ty::Unknown => {}
    }
}
