use std::fmt::Write;

use krelpin_ast::ast::{PrimitiveTy, ReceiverKind};
use krelpin_typeck::{LangItem, Subst, Ty};

use crate::cx::Cx;
use crate::instance::{Instance, Selector};
use crate::layout::{PtrKind, Shape, prim_llty};
use crate::rtti::RtKey;

pub(crate) struct FnCx<'c, 'a, 'tcx> {
    pub cx: &'c mut Cx<'a, 'tcx>,
    pub out: String,
    pub allocas: String,
    pub next: usize,
    pub subst: Subst,
    pub ret_ty: Ty,
    pub fail: Option<String>,
    pub borrowed_boxes: Vec<String>,
}

#[derive(Clone, Debug)]
pub(crate) struct Val {
    pub ty: Ty,
    pub v: String,
}

impl<'c, 'a, 'tcx> FnCx<'c, 'a, 'tcx> {
    pub(crate) fn new(cx: &'c mut Cx<'a, 'tcx>, subst: Subst, ret_ty: Ty) -> Self {
        FnCx {
            cx,
            out: String::new(),
            allocas: String::new(),
            next: 0,
            subst,
            ret_ty,
            fail: None,
            borrowed_boxes: Vec::new(),
        }
    }

    pub(crate) fn reg(&mut self) -> String {
        self.next += 1;
        format!("%r{}", self.next)
    }

    pub(crate) fn label(&mut self, hint: &str) -> String {
        self.next += 1;
        format!("{hint}{}", self.next)
    }

    pub(crate) fn line(&mut self, text: impl AsRef<str>) {
        self.out.push_str("  ");
        self.out.push_str(text.as_ref());
        self.out.push('\n');
    }

    pub(crate) fn start(&mut self, label: &str) {
        let _ = writeln!(self.out, "{label}:");
    }

    pub(crate) fn assign(&mut self, text: impl AsRef<str>) -> String {
        let reg = self.reg();
        self.line(format!("{reg} = {}", text.as_ref()));
        reg
    }

    pub(crate) fn gep(&mut self, struct_ll: &str, base: &str, index: usize) -> String {
        self.assign(format!(
            "getelementptr inbounds {struct_ll}, ptr {base}, i32 0, i32 {index}"
        ))
    }

    pub(crate) fn alloca(&mut self, ty: &Ty) -> String {
        let llty = self.cx.mem_llty(ty);
        self.alloca_ll(&llty)
    }

    pub(crate) fn alloca_ll(&mut self, llty: &str) -> String {
        self.next += 1;
        let name = format!("%s{}", self.next);
        let _ = writeln!(self.allocas, "  {name} = alloca {llty}, align 16");
        let _ = writeln!(self.allocas, "  store {llty} zeroinitializer, ptr {name}");
        name
    }

    pub(crate) fn sub(&self, ty: &Ty) -> Ty {
        ty.subst(&self.subst)
    }

    pub(crate) fn ll(&mut self, ty: &Ty) -> String {
        self.cx.llty(ty)
    }

    pub(crate) fn load(&mut self, ty: &Ty, addr: &str) -> String {
        let llty = self.cx.llty(ty);
        if llty == "void" {
            return String::new();
        }
        self.assign(format!("load {llty}, ptr {addr}"))
    }

    pub(crate) fn store(&mut self, ty: &Ty, value: &str, addr: &str) {
        let llty = self.cx.llty(ty);
        if llty == "void" {
            return;
        }
        self.line(format!("store {llty} {value}, ptr {addr}"));
    }

    pub(crate) fn zero(&mut self, ty: &Ty, addr: &str) {
        let llty = self.cx.llty(ty);
        if llty == "void" {
            return;
        }
        let zero = self.cx.null_value(ty);
        self.line(format!("store {llty} {zero}, ptr {addr}"));
    }

    pub(crate) fn drop_value(&mut self, value: &str, ty: &Ty) {
        if !self.cx.needs_drop(ty) {
            return;
        }
        let glue = self.cx.drop_glue(ty);
        let llty = self.cx.llty(ty);
        self.line(format!("call void {glue}({llty} {value})"));
    }

    pub(crate) fn drop_at(&mut self, ty: &Ty, addr: &str) {
        if !self.cx.needs_drop(ty) {
            return;
        }
        let old = self.load(ty, addr);
        self.drop_value(&old, ty);
        self.zero(ty, addr);
    }

    pub(crate) fn copy_value(&mut self, value: &str, ty: &Ty) -> String {
        if !self.cx.needs_drop(ty) {
            return value.to_owned();
        }
        let glue = self.cx.copy_glue(ty);
        let llty = self.cx.llty(ty);
        self.assign(format!("call {llty} {glue}({llty} {value})"))
    }

    pub(crate) fn declare(&mut self, name: &'static str, signature: &'static str) {
        self.cx.declare(name, signature);
    }

    pub(crate) fn runtime(&mut self, ret: &str, name: &'static str, args: &str) -> String {
        let signature = runtime_signature(name);
        self.declare(name, signature);
        if ret == "void" {
            self.line(format!("call void @{name}({args})"));
            String::new()
        } else {
            self.assign(format!("call {ret} @{name}({args})"))
        }
    }

    pub(crate) fn fail_label(&mut self) -> String {
        if let Some(label) = &self.fail {
            return label.clone();
        }
        let label = "fail".to_owned();
        self.fail = Some(label.clone());
        label
    }

    pub(crate) fn finish_fail(&mut self) {
        if let Some(label) = self.fail.clone() {
            self.start(&label);
            let ret = self.ret_ty.clone();
            self.ret_zero(&ret);
        }
    }

    pub(crate) fn ret_zero(&mut self, ty: &Ty) {
        let llty = self.cx.llty(ty);
        if llty == "void" {
            self.line("ret void");
        } else {
            let zero = self.cx.null_value(ty);
            self.line(format!("ret {llty} {zero}"));
        }
    }

    pub(crate) fn check_pending(&mut self, unwind: &str) {
        let pending = self.assign("load ptr, ptr @kr_pending");
        let failed = self.assign(format!("icmp ne ptr {pending}, null"));
        let ok = self.label("ok");
        self.line(format!("br i1 {failed}, label %{unwind}, label %{ok}"));
        self.start(&ok);
    }

    pub(crate) fn throw_new(&mut self, item: LangItem, message: &str, unwind: &str) {
        let text = self.cx.string_literal(message);
        self.throw_with(item, &text, unwind);
    }

    pub(crate) fn throw_with(&mut self, item: LangItem, message: &str, unwind: &str) {
        let exception = self.construct_exception(item, message);
        self.line(format!("store ptr {exception}, ptr @kr_pending"));
        self.line(format!("br label %{unwind}"));
        let dead = self.label("dead");
        self.start(&dead);
    }

    fn construct_exception(&mut self, item: LangItem, message: &str) -> String {
        let def = self.cx.lang(item);
        let ty = self.cx.tcx.self_ty(def);
        let string = self.cx.tcx.string_ty();
        let ctor = self
            .cx
            .tcx
            .sig(def)
            .ctors
            .iter()
            .find(|ctor| ctor.params.len() == 1 && self.cx.tcx.is_string(&ctor.params[0]))
            .cloned()
            .unwrap_or_else(|| panic!("`{}` takes a message", item.path()));
        let object = self.new_object(&ty, None);
        let slot = self.alloca(&ty);
        self.store(&ty, &object, &slot);
        let instance = self.cx.instance_for(&ctor, &Subst::new(), &ty);
        let id = self.cx.instance(instance);
        let name = self.cx.fn_name(id);
        let _ = string;
        self.line(format!("call void {name}(ptr {slot}, ptr {message})"));
        let object = self.load(&ty, &slot);
        self.line(format!("store ptr null, ptr {slot}"));
        object
    }

    pub(crate) fn new_object(&mut self, ty: &Ty, unwind: Option<&str>) -> String {
        let descriptor = self.cx.concrete_class(ty);
        self.cx.ensure_drop_object(ty);
        let object = self.runtime("ptr", "kr_new_object", &format!("ptr {descriptor}"));
        let Ty::Adt { def, args, .. } = ty else {
            panic!("`{ty}` is not a class");
        };
        let native_new = if self.cx.tcx.lang_items.is(*def, LangItem::Mutex) {
            Some("kr_mutex_new")
        } else if self.cx.tcx.lang_items.is(*def, LangItem::ReadWriteLock) {
            Some("kr_rwlock_new")
        } else {
            None
        };
        if let Some(native_new) = native_new {
            let mutex = self.runtime("ptr", native_new, "");
            let object_ty = self.cx.object_type(ty);
            let index = self.cx.native_index(ty, 0);
            let field = self.assign(format!(
                "getelementptr inbounds {object_ty}, ptr {object}, i32 0, i32 {index}"
            ));
            self.line(format!("store ptr {mutex}, ptr {field}"));
        }
        let fields = self.cx.class_fields(*def, args);
        let mut slot = None;
        for (index, field) in fields.iter().enumerate() {
            let Some(&body) = self.cx.field_inits.get(&(field.owner, field.name)) else {
                continue;
            };
            let owner_args = self
                .cx
                .tcx
                .upcast(*def, args, field.owner)
                .unwrap_or_default();
            let id = self.cx.instance(Instance::Body {
                body,
                args: owner_args,
            });
            let name = self.cx.fn_name(id);
            let slot = match &slot {
                Some(slot) => String::clone(slot),
                None => {
                    let created = self.alloca(ty);
                    self.store(ty, &object, &created);
                    slot = Some(created.clone());
                    created
                }
            };
            let llty = self.cx.llty(&field.ty);
            let value = self.assign(format!("call {llty} {name}(ptr {slot})"));
            if let Some(unwind) = unwind {
                let pending = self.assign("load ptr, ptr @kr_pending");
                let failed = self.assign(format!("icmp ne ptr {pending}, null"));
                let bad = self.label("initfail");
                let ok = self.label("initok");
                self.line(format!("br i1 {failed}, label %{bad}, label %{ok}"));
                self.start(&bad);
                self.drop_value(&object, ty);
                self.line(format!("store ptr null, ptr {slot}"));
                self.line(format!("br label %{unwind}"));
                self.start(&ok);
            }
            let object_ty = self.cx.object_type(ty);
            let address = self.assign(format!(
                "getelementptr inbounds {object_ty}, ptr {object}, i32 0, i32 {}",
                index + 1
            ));
            self.store(&field.ty, &value, &address);
        }
        if let Some(slot) = slot {
            self.line(format!("store ptr null, ptr {slot}"));
        }
        object
    }

    pub(crate) fn const_int(&mut self, ty: &Ty, value: i64) -> String {
        match ty {
            Ty::Primitive(PrimitiveTy::Boolean) => (value != 0).to_string(),
            Ty::Primitive(PrimitiveTy::Float | PrimitiveTy::Double) => float_const(value as f64),
            _ => value.to_string(),
        }
    }

    pub(crate) fn convert(&mut self, value: &str, from: &Ty, to: &Ty) -> String {
        if from == to {
            return value.to_owned();
        }
        if let (Ty::Ref { ty: slot, .. }, Ty::Nullable(target)) = (from, to)
            && let (Ty::Nullable(_), Ty::Ref { .. }) = (slot.as_ref(), target.as_ref())
        {
            let slot = slot.as_ref().clone();
            return self.lend_nullable_slot(value, &slot);
        }
        if let Some((from_inner, nullable)) = reference_of(from) {
            let from_inner = from_inner.clone();
            return match reference_of(to) {
                Some((to_inner, _)) if !nullable => {
                    let to_inner = to_inner.clone();
                    self.convert_reference(value, &from_inner, &to_inner)
                }
                _ if nullable => self.convert_nullable_reference(value, &from_inner, to),
                Some(_) => value.to_owned(),
                None => {
                    let loaded = self.load(&from_inner, value);
                    let copied = self.copy_value(&loaded, &from_inner);
                    self.convert(&copied, &from_inner, to)
                }
            };
        }
        let from_shape = self.cx.shape(from);
        let to_shape = self.cx.shape(to);
        match (&from_shape, &to_shape) {
            (Shape::Ptr(PtrKind::Null), _) => self.cx.null_value(to),
            (Shape::Prim(a), Shape::Prim(b)) => self.numeric(value, *a, *b),
            (Shape::Ptr(_), Shape::Ptr(_)) => value.to_owned(),
            (_, Shape::NullableValue(inner)) => {
                let inner = inner.as_ref().clone();
                if let Shape::NullableValue(from_inner) = &from_shape {
                    let from_inner = from_inner.as_ref().clone();
                    let llfrom = self.ll(from);
                    let flag = self.assign(format!("extractvalue {llfrom} {value}, 0"));
                    let payload = self.assign(format!("extractvalue {llfrom} {value}, 1"));
                    let converted = self.convert(&payload, &from_inner, &inner);
                    return self.pack_nullable(&flag, &converted, to);
                }
                let converted = self.convert(value, from, &inner);
                self.pack_nullable("true", &converted, to)
            }
            (Shape::NullableValue(inner), Shape::Ptr(_)) => {
                let inner = inner.as_ref().clone();
                let llfrom = self.ll(from);
                let flag = self.assign(format!("extractvalue {llfrom} {value}, 0"));
                let payload = self.assign(format!("extractvalue {llfrom} {value}, 1"));
                let present = self.label("box");
                let absent = self.label("nobox");
                let join = self.label("boxed");
                self.line(format!("br i1 {flag}, label %{present}, label %{absent}"));
                self.start(&present);
                let boxed = self.convert(&payload, &inner, to);
                let from_present = self.current_block_marker(&present);
                self.line(format!("br label %{join}"));
                self.start(&absent);
                self.line(format!("br label %{join}"));
                self.start(&join);
                self.assign(format!(
                    "phi ptr [ {boxed}, %{from_present} ], [ null, %{absent} ]"
                ))
            }
            (Shape::NullableValue(inner), _) => {
                let llfrom = self.ll(from);
                let payload = self.assign(format!("extractvalue {llfrom} {value}, 1"));
                let inner = inner.as_ref().clone();
                self.convert(&payload, &inner, to)
            }
            (Shape::Prim(_) | Shape::Record(..) | Shape::Enum(..), Shape::Ptr(_)) => {
                self.box_value(value, from)
            }
            (Shape::Ptr(_), Shape::Prim(_) | Shape::Record(..) | Shape::Enum(..)) => {
                self.unbox(value, to)
            }
            _ => value.to_owned(),
        }
    }

    fn lend_nullable_slot(&mut self, pointer: &str, slot: &Ty) -> String {
        if let Shape::NullableValue(_) = self.cx.shape(slot) {
            let slot_ll = self.ll(slot);
            let flag_at = self.assign(format!(
                "getelementptr inbounds {slot_ll}, ptr {pointer}, i32 0, i32 0"
            ));
            let flag = self.assign(format!("load i1, ptr {flag_at}"));
            let payload = self.assign(format!(
                "getelementptr inbounds {slot_ll}, ptr {pointer}, i32 0, i32 1"
            ));
            return self.assign(format!("select i1 {flag}, ptr {payload}, ptr null"));
        }
        let value = self.assign(format!("load ptr, ptr {pointer}"));
        let absent = self.assign(format!("icmp eq ptr {value}, null"));
        self.assign(format!("select i1 {absent}, ptr null, ptr {pointer}"))
    }

    fn convert_nullable_reference(&mut self, pointer: &str, from: &Ty, to: &Ty) -> String {
        let to_ll = self.ll(to);
        let result = self.alloca(to);
        let is_null = self.assign(format!("icmp eq ptr {pointer}, null"));
        let present = self.label("refpresent");
        let absent = self.label("refabsent");
        let done = self.label("refdone");
        self.line(format!(
            "br i1 {is_null}, label %{absent}, label %{present}"
        ));
        self.start(&present);
        let reference = Ty::Ref {
            mutable: false,
            ty: Box::new(from.clone()),
        };
        let converted = self.convert(pointer, &reference, to.non_null());
        let converted = self.convert(&converted, to.non_null(), to);
        self.line(format!("store {to_ll} {converted}, ptr {result}"));
        self.line(format!("br label %{done}"));
        self.start(&absent);
        let null = self.cx.null_value(to);
        self.line(format!("store {to_ll} {null}, ptr {result}"));
        self.line(format!("br label %{done}"));
        self.start(&done);
        let value = self.assign(format!("load {to_ll}, ptr {result}"));
        self.zero(to, &result);
        value
    }

    fn convert_reference(&mut self, pointer: &str, from: &Ty, to: &Ty) -> String {
        if from == to {
            return pointer.to_owned();
        }
        // `&&T` used as `&T` points one level too far out.
        if let (Ty::Ref { ty: inner, .. }, false) = (from, matches!(to, Ty::Ref { .. })) {
            let inner = inner.as_ref().clone();
            let loaded = self.assign(format!("load ptr, ptr {pointer}"));
            return self.convert_reference(&loaded, &inner, to);
        }
        let from_shape = self.cx.shape(from);
        let to_shape = self.cx.shape(to);
        match (&from_shape, &to_shape) {
            (Shape::Ptr(_), Shape::Ptr(_)) => pointer.to_owned(),
            (Shape::Prim(a), Shape::Prim(b)) if a == b => pointer.to_owned(),
            (Shape::Prim(_) | Shape::Record(..) | Shape::Enum(..), Shape::Ptr(_)) => {
                let descriptor = self.cx.rt_global(RtKey::Box(from.clone()));
                self.cx.ensure_drop_box(from);
                let box_ty = self.cx.box_type(from);
                let object = self.runtime("ptr", "kr_new_object", &format!("ptr {descriptor}"));
                let payload = self.assign(format!(
                    "getelementptr inbounds {box_ty}, ptr {object}, i32 0, i32 1"
                ));
                let value = self.load(from, pointer);
                self.store(from, &value, &payload);
                let slot = self.alloca_ll("ptr");
                self.line(format!("store ptr {object}, ptr {slot}"));
                self.borrowed_boxes.push(slot.clone());
                slot
            }
            (Shape::NullableValue(inner), Shape::Ptr(_)) => {
                let inner = inner.as_ref().clone();
                let nullable_ll = self.ll(from);
                let flag_addr = self.assign(format!(
                    "getelementptr inbounds {nullable_ll}, ptr {pointer}, i32 0, i32 0"
                ));
                let flag = self.assign(format!("load i1, ptr {flag_addr}"));
                let payload = self.assign(format!(
                    "getelementptr inbounds {nullable_ll}, ptr {pointer}, i32 0, i32 1"
                ));
                let slot = self.alloca_ll("ptr");
                self.line(format!("store ptr null, ptr {slot}"));
                let present = self.label("lend");
                let done = self.label("lent");
                self.line(format!("br i1 {flag}, label %{present}, label %{done}"));
                self.start(&present);
                let boxed_slot = self.convert_reference(&payload, &inner, to);
                let object = self.assign(format!("load ptr, ptr {boxed_slot}"));
                self.line(format!("store ptr {object}, ptr {slot}"));
                self.line(format!("br label %{done}"));
                self.start(&done);
                slot
            }
            (Shape::Ptr(_), Shape::Prim(_) | Shape::Record(..) | Shape::Enum(..)) => {
                let object = self.assign(format!("load ptr, ptr {pointer}"));
                let box_ty = self.cx.box_type(to);
                self.assign(format!(
                    "getelementptr inbounds {box_ty}, ptr {object}, i32 0, i32 1"
                ))
            }
            // A widened number or a value wrapped as nullable has a different
            // layout, so the borrow points at a converted copy.
            (Shape::Prim(_), Shape::Prim(_)) | (_, Shape::NullableValue(_)) => {
                let value = self.load(from, pointer);
                let converted = self.convert(&value, from, to);
                let slot = self.alloca(to);
                self.store(to, &converted, &slot);
                slot
            }
            _ => pointer.to_owned(),
        }
    }

    pub(crate) fn indirect_slot(&mut self, container: &Ty, field: &Ty, address: String) -> String {
        if self.cx.is_indirect(container, field) {
            self.assign(format!("load ptr, ptr {address}"))
        } else {
            address
        }
    }

    pub(crate) fn wrap_indirect(&mut self, container: &Ty, field: &Ty, value: &str) -> String {
        if !self.cx.is_indirect(container, field) {
            return value.to_owned();
        }
        let (size, _) = self.cx.size_align(field);
        let cell = self.runtime("ptr", "kr_alloc", &format!("i64 {size}"));
        self.store(field, value, &cell);
        cell
    }

    pub(crate) fn drop_indirect(&mut self, field: &Ty, cell: &str) {
        let present = self.assign(format!("icmp ne ptr {cell}, null"));
        let drop = self.label("cell");
        let done = self.label("celldone");
        self.line(format!("br i1 {present}, label %{drop}, label %{done}"));
        self.start(&drop);
        self.drop_at(field, cell);
        self.runtime("void", "kr_free", &format!("ptr {cell}"));
        self.line(format!("br label %{done}"));
        self.start(&done);
    }

    pub(crate) fn release_borrowed_boxes(&mut self) {
        for slot in std::mem::take(&mut self.borrowed_boxes) {
            let object = self.assign(format!("load ptr, ptr {slot}"));
            self.runtime("void", "kr_free", &format!("ptr {object}"));
            self.line(format!("store ptr null, ptr {slot}"));
        }
    }

    fn current_block_marker(&mut self, fallback: &str) -> String {
        let last = self
            .out
            .lines()
            .rev()
            .find(|line| line.ends_with(':') && !line.starts_with(' '))
            .map(|line| line.trim_end_matches(':').to_owned());
        last.unwrap_or_else(|| fallback.to_owned())
    }

    pub(crate) fn block_marker(&mut self) -> String {
        self.current_block_marker("entry")
    }

    pub(crate) fn pack_nullable(&mut self, flag: &str, value: &str, ty: &Ty) -> String {
        let llty = self.ll(ty);
        let first = self.assign(format!("insertvalue {llty} zeroinitializer, i1 {flag}, 0"));
        let Shape::NullableValue(inner) = self.cx.shape(ty) else {
            return value.to_owned();
        };
        let inner_ll = self.ll(&inner);
        self.assign(format!("insertvalue {llty} {first}, {inner_ll} {value}, 1"))
    }

    pub(crate) fn box_value(&mut self, value: &str, ty: &Ty) -> String {
        let descriptor = self.cx.rt_global(RtKey::Box(ty.clone()));
        self.cx.ensure_drop_box(ty);
        let box_ty = self.cx.box_type(ty);
        let object = self.runtime("ptr", "kr_new_object", &format!("ptr {descriptor}"));
        let payload = self.assign(format!(
            "getelementptr inbounds {box_ty}, ptr {object}, i32 0, i32 1"
        ));
        self.store(ty, value, &payload);
        object
    }

    pub(crate) fn unbox(&mut self, object: &str, ty: &Ty) -> String {
        let box_ty = self.cx.box_type(ty);
        let payload = self.assign(format!(
            "getelementptr inbounds {box_ty}, ptr {object}, i32 0, i32 1"
        ));
        let value = self.load(ty, &payload);
        self.runtime("void", "kr_free", &format!("ptr {object}"));
        value
    }

    pub(crate) fn numeric(&mut self, value: &str, from: PrimitiveTy, to: PrimitiveTy) -> String {
        use PrimitiveTy::*;
        if from == to {
            return value.to_owned();
        }
        let a = prim_llty(from);
        let b = prim_llty(to);
        let float = |p: PrimitiveTy| matches!(p, Float | Double);
        let bits = |p: PrimitiveTy| match p {
            Boolean => 1,
            Byte => 8,
            Short => 16,
            Char | Int | Float => 32,
            Long | Double => 64,
        };
        match (float(from), float(to)) {
            (false, false) => {
                if a == b {
                    return value.to_owned();
                }
                if bits(from) < bits(to) {
                    let op = if matches!(from, Boolean | Char) {
                        "zext"
                    } else {
                        "sext"
                    };
                    self.assign(format!("{op} {a} {value} to {b}"))
                } else {
                    self.assign(format!("trunc {a} {value} to {b}"))
                }
            }
            (false, true) => {
                let op = if matches!(from, Boolean | Char) {
                    "uitofp"
                } else {
                    "sitofp"
                };
                self.assign(format!("{op} {a} {value} to {b}"))
            }
            (true, false) => {
                let intrinsic = format!("llvm.fptosi.sat.{b}.{a}");
                self.cx
                    .declare_dynamic(&intrinsic, &format!("declare {b} @{intrinsic}({a})"));
                self.assign(format!("call {b} @{intrinsic}({a} {value})"))
            }
            (true, true) => {
                let op = if bits(from) < bits(to) {
                    "fpext"
                } else {
                    "fptrunc"
                };
                self.assign(format!("{op} {a} {value} to {b}"))
            }
        }
    }

    pub(crate) fn call_instance(
        &mut self,
        id: usize,
        args: &[(String, String)],
        ret: &Ty,
    ) -> String {
        let name = self.cx.fn_name(id);
        let rendered: Vec<String> = args.iter().map(|(ty, v)| format!("{ty} {v}")).collect();
        let llret = self.ll(ret);
        if llret == "void" {
            self.line(format!("call void {name}({})", rendered.join(", ")));
            String::new()
        } else {
            self.assign(format!("call {llret} {name}({})", rendered.join(", ")))
        }
    }

    pub(crate) fn virtual_fn(&mut self, object: &str, selector: usize) -> String {
        let descriptor = self.assign(format!("load ptr, ptr {object}"));
        let slot = self.assign(format!(
            "getelementptr inbounds {{ ptr, ptr, ptr, i64, ptr, i64, i64, [0 x ptr] }}, ptr \
             {descriptor}, i32 0, i32 7, i64 $slot.{selector}$"
        ));
        self.assign(format!("load ptr, ptr {slot}"))
    }

    pub(crate) fn dispatch(
        &mut self,
        selector: &Selector,
        receiver_ty: &Ty,
        receiver: &str,
        args: &[Val],
    ) -> String {
        if let Some(result) = self.dispatch_nullable(selector, receiver_ty, receiver, args) {
            return result;
        }
        let base = receiver_ty.non_null().strip_refs().non_null().clone();
        let id = self.cx.selector(selector.clone());
        let statically = self.statically_dispatched(&base);
        let mut rendered = Vec::new();
        let receiver_ll = match selector.receiver {
            ReceiverKind::Owned => self.ll(receiver_ty),
            _ => "ptr".to_owned(),
        };
        rendered.push(format!("{receiver_ll} {receiver}"));
        if statically {
            let resolved = self
                .cx
                .find_impl(&base, selector)
                .unwrap_or_else(|| panic!("`{base}` implements `{}`", selector.name));
            let instance = self.cx.resolved_instance(&resolved, &base);
            let params = self.cx.instance_params(&instance);
            if let Some(param) = params.first().cloned() {
                let converted = self.convert(receiver, receiver_ty, &param);
                let ll = self.ll(&param);
                rendered[0] = format!("{ll} {converted}");
            }
            for (index, arg) in args.iter().enumerate() {
                let param = params.get(index + 1).cloned().unwrap_or(arg.ty.clone());
                let converted = self.convert(&arg.v, &arg.ty, &param);
                let ll = self.ll(&param);
                rendered.push(format!("{ll} {converted}"));
            }
            let target_id = self.cx.instance(instance.clone());
            let ret = self.cx.instance_ret(&instance);
            let name = self.cx.fn_name(target_id);
            let llret = self.ll(&ret);
            let result = if llret == "void" {
                self.line(format!("call void {name}({})", rendered.join(", ")));
                String::new()
            } else {
                self.assign(format!("call {llret} {name}({})", rendered.join(", ")))
            };
            return self.convert(&result, &ret, &selector.ret);
        }
        let object = if matches!(selector.receiver, ReceiverKind::Owned) {
            receiver.to_owned()
        } else {
            self.assign(format!("load ptr, ptr {receiver}"))
        };
        let function = self.virtual_fn(&object, id);
        for (index, arg) in args.iter().enumerate() {
            let param = selector
                .params
                .get(index)
                .cloned()
                .unwrap_or(arg.ty.clone());
            let converted = self.convert(&arg.v, &arg.ty, &param);
            let ll = self.ll(&param);
            rendered.push(format!("{ll} {converted}"));
        }
        let llret = self.ll(&selector.ret);
        if llret == "void" {
            self.line(format!("call void {function}({})", rendered.join(", ")));
            String::new()
        } else {
            self.assign(format!("call {llret} {function}({})", rendered.join(", ")))
        }
    }

    fn dispatch_nullable(
        &mut self,
        selector: &Selector,
        receiver_ty: &Ty,
        receiver: &str,
        args: &[Val],
    ) -> Option<String> {
        let Ty::Ref { ty: slot, .. } = receiver_ty else {
            return None;
        };
        let Ty::Nullable(inner) = slot.as_ref() else {
            return None;
        };
        let name = selector.name.as_str();
        if selector.receiver != ReceiverKind::Ref || !matches!(name, "equals" | "hashCode" | "clone") {
            return None;
        }
        let slot = slot.as_ref().clone();
        let inner = inner.as_ref().clone();
        let me = self.lend_nullable_slot(receiver, &slot);
        let me_null = self.assign(format!("icmp eq ptr {me}, null"));
        let (result_ty, absent_check, other) = match name {
            "equals" => {
                let other = args.first()?;
                if !matches!(&other.ty, Ty::Ref { ty, .. } if ty.as_ref() == &slot) {
                    return None;
                }
                let you = self.lend_nullable_slot(&other.v, &slot);
                let you_null = self.assign(format!("icmp eq ptr {you}, null"));
                let either = self.assign(format!("or i1 {me_null}, {you_null}"));
                (Ty::BOOLEAN, either, Some((you, you_null)))
            }
            "hashCode" => (Ty::INT, me_null.clone(), None),
            _ => (slot.clone(), me_null.clone(), None),
        };
        let result_ll = self.ll(&result_ty);
        let result = self.alloca(&result_ty);
        let present = self.label("nonnull");
        let absent = self.label("null");
        let done = self.label("nulldone");
        self.line(format!("br i1 {absent_check}, label %{absent}, label %{present}"));
        self.start(&present);
        let value = match name {
            "equals" => {
                let (you, _) = other.clone()?;
                self.call_equals(&me, &you, &inner)
            }
            "hashCode" => self.call_hash(&me, &inner),
            _ => {
                let copy = self.call_clone(&me, &inner);
                self.convert(&copy, &inner, &slot)
            }
        };
        self.line(format!("store {result_ll} {value}, ptr {result}"));
        self.line(format!("br label %{done}"));
        self.start(&absent);
        let fallback = match name {
            "equals" => {
                let (_, you_null) = other?;
                self.assign(format!("and i1 {me_null}, {you_null}"))
            }
            "hashCode" => "0".to_owned(),
            _ => self.cx.null_value(&slot),
        };
        self.line(format!("store {result_ll} {fallback}, ptr {result}"));
        self.line(format!("br label %{done}"));
        self.start(&done);
        let loaded = self.assign(format!("load {result_ll}, ptr {result}"));
        Some(self.convert(&loaded, &result_ty, &selector.ret))
    }

    pub(crate) fn statically_dispatched(&self, base: &Ty) -> bool {
        match self.cx.shape(base) {
            Shape::Prim(_) | Shape::Record(..) | Shape::Enum(..) | Shape::NullableValue(_) => true,
            Shape::Ptr(PtrKind::String) | Shape::Ptr(PtrKind::Array) => true,
            Shape::Ptr(PtrKind::Object) => match base {
                Ty::Adt { def, .. } => {
                    let sig = self.cx.tcx.sig(*def);
                    sig.is_final && sig.kind == krelpin_typeck::AdtKind::Class
                }
                _ => false,
            },
            _ => false,
        }
    }

    pub(crate) fn object_selector(&self, name: &str, params: Vec<Ty>, ret: Ty) -> Selector {
        Selector {
            owner: self.cx.lang_ty(LangItem::Object),
            name: krelpin_span::Symbol::intern(name),
            params,
            method_args: Vec::new(),
            receiver: ReceiverKind::Ref,
            ret,
        }
    }

    pub(crate) fn interface_selector(
        &self,
        item: LangItem,
        name: &str,
        arg: &Ty,
        params: Vec<Ty>,
        ret: Ty,
    ) -> Selector {
        let def = self.cx.lang(item);
        Selector {
            owner: Ty::Adt {
                def,
                name: self.cx.tcx.ty_name(def),
                args: vec![arg.clone()],
            },
            name: krelpin_span::Symbol::intern(name),
            params,
            method_args: Vec::new(),
            receiver: ReceiverKind::Ref,
            ret,
        }
    }

    pub(crate) fn stringify(&mut self, value: &str, ty: &Ty) -> String {
        let string = self.cx.tcx.string_ty();
        match self.cx.shape(ty) {
            Shape::Prim(primitive) => self.prim_to_string(value, primitive),
            Shape::Ptr(PtrKind::String) if matches!(ty, Ty::Nullable(_)) => {
                self.stringify_nullable(value, ty)
            }
            Shape::Ptr(PtrKind::String) => self.copy_value(value, &string),
            Shape::Ptr(PtrKind::Null) => self.cx.string_literal("null"),
            Shape::Ptr(PtrKind::Ref) if matches!(ty, Ty::Nullable(_)) => {
                let inner = ty.non_null().clone();
                let is_null = self.assign(format!("icmp eq ptr {value}, null"));
                let null_label = self.label("refnull");
                let some = self.label("refsome");
                let join = self.label("refjoin");
                self.line(format!(
                    "br i1 {is_null}, label %{null_label}, label %{some}"
                ));
                self.start(&some);
                let shown = self.stringify(value, &inner);
                let from = self.block_marker();
                self.line(format!("br label %{join}"));
                self.start(&null_label);
                let null = self.cx.string_literal("null");
                self.line(format!("br label %{join}"));
                self.start(&join);
                self.assign(format!(
                    "phi ptr [ {shown}, %{from} ], [ {null}, %{null_label} ]"
                ))
            }
            Shape::Ptr(PtrKind::Ref) => {
                let Ty::Ref { ty: inner, .. } = ty else {
                    return self.cx.string_literal("null");
                };
                let inner = inner.as_ref().clone();
                if self.cx.is_ptr(&inner) {
                    let loaded = self.load(&inner, value);
                    self.stringify(&loaded, &inner)
                } else {
                    self.value_to_string(value, &inner)
                }
            }
            Shape::Ptr(_) => self.stringify_nullable(value, ty),
            Shape::Record(..) | Shape::Enum(..) => {
                let slot = self.alloca(ty);
                self.store(ty, value, &slot);
                self.value_to_string(&slot, ty)
            }
            Shape::NullableValue(inner) => {
                let inner = inner.as_ref().clone();
                let llty = self.ll(ty);
                let flag = self.assign(format!("extractvalue {llty} {value}, 0"));
                let payload = self.assign(format!("extractvalue {llty} {value}, 1"));
                let present = self.label("some");
                let absent = self.label("none");
                let join = self.label("shown");
                self.line(format!("br i1 {flag}, label %{present}, label %{absent}"));
                self.start(&present);
                let shown = self.stringify(&payload, &inner);
                let from = self.block_marker();
                self.line(format!("br label %{join}"));
                self.start(&absent);
                let null = self.cx.string_literal("null");
                self.line(format!("br label %{join}"));
                self.start(&join);
                self.assign(format!(
                    "phi ptr [ {shown}, %{from} ], [ {null}, %{absent} ]"
                ))
            }
            Shape::Void => self.cx.string_literal(""),
        }
    }

    fn stringify_nullable(&mut self, object: &str, ty: &Ty) -> String {
        let string = self.cx.tcx.string_ty();
        let is_null = self.assign(format!("icmp eq ptr {object}, null"));
        let null_label = self.label("isnull");
        let some = self.label("notnull");
        let join = self.label("joined");
        self.line(format!(
            "br i1 {is_null}, label %{null_label}, label %{some}"
        ));
        self.start(&some);
        let shown = match self.cx.shape(ty) {
            Shape::Ptr(PtrKind::String) => self.copy_value(object, &string),
            Shape::Ptr(PtrKind::Array) => {
                self.runtime("ptr", "kr_string_describe", &format!("ptr {object}"))
            }
            _ => {
                let slot = self.alloca_ll("ptr");
                self.line(format!("store ptr {object}, ptr {slot}"));
                let selector = self.object_selector("toString", Vec::new(), string.clone());
                let object_ty = self.cx.lang_ty(LangItem::Object);
                let base = ty.non_null().clone();
                let receiver_ty = Ty::Ref {
                    mutable: false,
                    ty: Box::new(if self.statically_dispatched(&base) {
                        base
                    } else {
                        object_ty
                    }),
                };
                let shown = self.dispatch(&selector, &receiver_ty, &slot, &[]);
                self.line(format!("store ptr null, ptr {slot}"));
                shown
            }
        };
        let from = self.block_marker();
        self.line(format!("br label %{join}"));
        self.start(&null_label);
        let null = self.cx.string_literal("null");
        self.line(format!("br label %{join}"));
        self.start(&join);
        self.assign(format!(
            "phi ptr [ {shown}, %{from} ], [ {null}, %{null_label} ]"
        ))
    }

    pub(crate) fn value_to_string(&mut self, address: &str, ty: &Ty) -> String {
        let string = self.cx.tcx.string_ty();
        if let Shape::Prim(primitive) = self.cx.shape(ty) {
            let value = self.load(ty, address);
            return self.prim_to_string(&value, primitive);
        }
        if self.cx.shape(ty) == Shape::Ptr(PtrKind::Ref) {
            // A reference field shows the value it points at.
            let value = self.load(ty, address);
            return self.stringify(&value, ty);
        }
        if self.cx.is_ptr(ty) {
            let value = self.load(ty, address);
            return self.stringify_nullable(&value, ty);
        }
        if let Shape::NullableValue(inner) = self.cx.shape(ty) {
            let inner = inner.as_ref().clone();
            let llty = self.ll(ty);
            let flag_addr = self.assign(format!(
                "getelementptr inbounds {llty}, ptr {address}, i32 0, i32 0"
            ));
            let flag = self.assign(format!("load i1, ptr {flag_addr}"));
            let present = self.label("some");
            let absent = self.label("none");
            let join = self.label("shown");
            self.line(format!("br i1 {flag}, label %{present}, label %{absent}"));
            self.start(&present);
            let payload = self.assign(format!(
                "getelementptr inbounds {llty}, ptr {address}, i32 0, i32 1"
            ));
            let shown = self.value_to_string(&payload, &inner);
            let from = self.block_marker();
            self.line(format!("br label %{join}"));
            self.start(&absent);
            let null = self.cx.string_literal("null");
            self.line(format!("br label %{join}"));
            self.start(&join);
            return self.assign(format!(
                "phi ptr [ {shown}, %{from} ], [ {null}, %{absent} ]"
            ));
        }
        let selector = self.object_selector("toString", Vec::new(), string);
        let receiver_ty = Ty::Ref {
            mutable: false,
            ty: Box::new(ty.clone()),
        };
        self.dispatch(&selector, &receiver_ty, address, &[])
    }

    pub(crate) fn prim_to_string(&mut self, value: &str, primitive: PrimitiveTy) -> String {
        match primitive {
            PrimitiveTy::Boolean => {
                self.runtime("ptr", "kr_string_from_bool", &format!("i1 {value}"))
            }
            PrimitiveTy::Char => {
                self.runtime("ptr", "kr_string_from_char", &format!("i32 {value}"))
            }
            PrimitiveTy::Float => {
                self.runtime("ptr", "kr_string_from_float", &format!("float {value}"))
            }
            PrimitiveTy::Double => {
                self.runtime("ptr", "kr_string_from_double", &format!("double {value}"))
            }
            PrimitiveTy::Byte | PrimitiveTy::Short | PrimitiveTy::Int | PrimitiveTy::Long => {
                let wide = self.numeric(value, primitive, PrimitiveTy::Long);
                self.runtime("ptr", "kr_string_from_long", &format!("i64 {wide}"))
            }
        }
    }

    pub(crate) fn call_equals(&mut self, a: &str, b: &str, ty: &Ty) -> String {
        if let Ty::Ref { ty: inner, .. } = ty {
            let inner = inner.as_ref().clone();
            let a = self.assign(format!("load ptr, ptr {a}"));
            let b = self.assign(format!("load ptr, ptr {b}"));
            return self.call_equals(&a, &b, &inner);
        }
        let reference = Ty::Ref {
            mutable: false,
            ty: Box::new(ty.clone()),
        };
        let selector = self.interface_selector(
            LangItem::Equatable,
            "equals",
            ty,
            vec![reference.clone()],
            Ty::BOOLEAN,
        );
        self.dispatch(
            &selector,
            &reference,
            a,
            &[Val {
                ty: reference.clone(),
                v: b.to_owned(),
            }],
        )
    }

    pub(crate) fn call_clone(&mut self, a: &str, ty: &Ty) -> String {
        let reference = Ty::Ref {
            mutable: false,
            ty: Box::new(ty.clone()),
        };
        let selector = Selector {
            owner: ty.clone(),
            name: krelpin_span::Symbol::intern("clone"),
            params: Vec::new(),
            method_args: Vec::new(),
            receiver: ReceiverKind::Ref,
            ret: ty.clone(),
        };
        self.dispatch(&selector, &reference, a, &[])
    }

    pub(crate) fn call_hash(&mut self, a: &str, ty: &Ty) -> String {
        if let Ty::Ref { ty: inner, .. } = ty {
            let inner = inner.as_ref().clone();
            let a = self.assign(format!("load ptr, ptr {a}"));
            return self.call_hash(&a, &inner);
        }
        let reference = Ty::Ref {
            mutable: false,
            ty: Box::new(ty.clone()),
        };
        let selector =
            self.interface_selector(LangItem::Hashable, "hashCode", ty, Vec::new(), Ty::INT);
        self.dispatch(&selector, &reference, a, &[])
    }
}

pub(crate) fn define(ret: &str, name: &str, params: &str, allocas: &str, body: &str) -> String {
    format!(
        "define internal {ret} {name}({params}) {{\nallocas:\n{allocas}  br label %entry\n\
         {body}}}\n"
    )
}

pub(crate) fn array_ll(elem_ll: &str) -> String {
    format!("{{ ptr, i64, [0 x {elem_ll}] }}")
}

fn reference_of(ty: &Ty) -> Option<(&Ty, bool)> {
    match ty {
        Ty::Ref { ty, .. } => Some((ty, false)),
        Ty::Nullable(inner) => match inner.as_ref() {
            Ty::Ref { ty, .. } => Some((ty, true)),
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn float_const(value: f64) -> String {
    format!("0x{:016X}", value.to_bits())
}

pub(crate) fn float32_const(value: f32) -> String {
    format!("0x{:016X}", (value as f64).to_bits())
}

pub(crate) fn runtime_signature(name: &str) -> &'static str {
    match name {
        "kr_alloc" => "declare ptr @kr_alloc(i64)",
        "kr_realloc" => "declare ptr @kr_realloc(ptr, i64)",
        "kr_free" => "declare void @kr_free(ptr)",
        "kr_new_object" => "declare ptr @kr_new_object(ptr)",
        "kr_drop_object" => "declare void @kr_drop_object(ptr)",
        "kr_instance_of" => "declare zeroext i1 @kr_instance_of(ptr, ptr)",
        "kr_string_retain" => "declare void @kr_string_retain(ptr)",
        "kr_string_release" => "declare void @kr_string_release(ptr)",
        "kr_string_concat" => "declare ptr @kr_string_concat(ptr, ptr)",
        "kr_string_length" => "declare i32 @kr_string_length(ptr)",
        "kr_string_chars" => "declare ptr @kr_string_chars(ptr, ptr)",
        "kr_string_substring" => "declare ptr @kr_string_substring(ptr, i32, i32)",
        "kr_string_index_of" => "declare i32 @kr_string_index_of(ptr, ptr)",
        "kr_string_starts_with" => "declare zeroext i1 @kr_string_starts_with(ptr, ptr)",
        "kr_string_ends_with" => "declare zeroext i1 @kr_string_ends_with(ptr, ptr)",
        "kr_string_to_upper" => "declare ptr @kr_string_to_upper(ptr)",
        "kr_string_to_lower" => "declare ptr @kr_string_to_lower(ptr)",
        "kr_string_trim" => "declare ptr @kr_string_trim(ptr)",
        "kr_string_replace" => "declare ptr @kr_string_replace(ptr, ptr, ptr)",
        "kr_string_repeat" => "declare ptr @kr_string_repeat(ptr, i32)",
        "kr_string_split" => "declare ptr @kr_string_split(ptr, ptr, ptr)",
        "kr_string_compare" => "declare i32 @kr_string_compare(ptr, ptr)",
        "kr_string_equals" => "declare zeroext i1 @kr_string_equals(ptr, ptr)",
        "kr_string_hash" => "declare i32 @kr_string_hash(ptr)",
        "kr_string_join" => "declare ptr @kr_string_join(ptr, ptr)",
        "kr_string_from_long" => "declare ptr @kr_string_from_long(i64)",
        "kr_string_from_double" => "declare ptr @kr_string_from_double(double)",
        "kr_string_from_float" => "declare ptr @kr_string_from_float(float)",
        "kr_string_from_char" => "declare ptr @kr_string_from_char(i32)",
        "kr_string_from_bool" => "declare ptr @kr_string_from_bool(i1 zeroext)",
        "kr_string_describe" => "declare ptr @kr_string_describe(ptr)",
        "kr_string_bounds" => "declare ptr @kr_string_bounds(i64, i64)",
        "kr_string_cast" => "declare ptr @kr_string_cast(ptr, ptr)",
        "kr_string_number_format" => "declare ptr @kr_string_number_format(ptr)",
        "kr_parse_long" => "declare zeroext i1 @kr_parse_long(ptr, i64, i64, ptr)",
        "kr_parse_double" => "declare zeroext i1 @kr_parse_double(ptr, ptr)",
        "kr_console_print" => "declare void @kr_console_print(ptr)",
        "kr_console_newline" => "declare void @kr_console_newline()",
        "kr_console_read_line" => "declare ptr @kr_console_read_line()",
        "kr_bridge_open" => "declare void @kr_bridge_open()",
        "kr_format_long" => "declare ptr @kr_format_long(i64, ptr)",
        "kr_builder_append" => "declare void @kr_builder_append(ptr, ptr)",
        "kr_io_last_error" => "declare ptr @kr_io_last_error()",
        "kr_io_failed" => "declare i1 @kr_io_failed()",
        "kr_io_read_file" => "declare ptr @kr_io_read_file(ptr)",
        "kr_io_write_file" => "declare i1 @kr_io_write_file(ptr, ptr, i1)",
        "kr_io_exists" => "declare i1 @kr_io_exists(ptr)",
        "kr_io_is_file" => "declare i1 @kr_io_is_file(ptr)",
        "kr_io_is_directory" => "declare i1 @kr_io_is_directory(ptr)",
        "kr_io_size" => "declare i64 @kr_io_size(ptr)",
        "kr_io_remove" => "declare i1 @kr_io_remove(ptr)",
        "kr_io_create_directories" => "declare i1 @kr_io_create_directories(ptr)",
        "kr_io_create_directory" => "declare i1 @kr_io_create_directory(ptr)",
        "kr_io_is_symlink" => "declare i1 @kr_io_is_symlink(ptr)",
        "kr_io_rename" => "declare i1 @kr_io_rename(ptr, ptr)",
        "kr_io_copy" => "declare i1 @kr_io_copy(ptr, ptr)",
        "kr_io_modified" => "declare i64 @kr_io_modified(ptr)",
        "kr_io_set_modified" => "declare zeroext i1 @kr_io_set_modified(ptr, i64)",
        "kr_io_access" => "declare zeroext i1 @kr_io_access(ptr, i32)",
        "kr_io_set_permission" => "declare zeroext i1 @kr_io_set_permission(ptr, i32, i1 zeroext)",
        "kr_io_read_bytes" => "declare ptr @kr_io_read_bytes(ptr, ptr)",
        "kr_io_write_bytes" => "declare i1 @kr_io_write_bytes(ptr, ptr, i1)",
        "kr_system_os_name" => "declare ptr @kr_system_os_name()",
        "kr_io_list" => "declare ptr @kr_io_list(ptr, ptr)",
        "kr_file_open" => "declare ptr @kr_file_open(ptr, i32)",
        "kr_net_close" => "declare void @kr_net_close(ptr)",
        "kr_net_local_addr" => "declare ptr @kr_net_local_addr(ptr)",
        "kr_net_set_timeout" => "declare zeroext i1 @kr_net_set_timeout(ptr, i64, i1 zeroext)",
        "kr_net_set_nonblocking" => "declare zeroext i1 @kr_net_set_nonblocking(ptr, i1 zeroext)",
        "kr_net_register" => "declare zeroext i1 @kr_net_register(ptr, ptr, i32, i1 zeroext, i1 zeroext, i1 zeroext)",
        "kr_net_deregister" => "declare zeroext i1 @kr_net_deregister(ptr, ptr)",
        "kr_poller_create" => "declare zeroext i1 @kr_poller_create(ptr)",
        "kr_poller_close" => "declare void @kr_poller_close(ptr)",
        "kr_poller_poll" => "declare i32 @kr_poller_poll(ptr, i64)",
        "kr_poller_token" => "declare i32 @kr_poller_token(ptr, i32)",
        "kr_poller_flags" => "declare i32 @kr_poller_flags(ptr, i32)",
        "kr_tcp_listener_bind" => "declare zeroext i1 @kr_tcp_listener_bind(ptr, ptr)",
        "kr_tcp_stream_connect" => "declare zeroext i1 @kr_tcp_stream_connect(ptr, ptr)",
        "kr_tcp_stream_accept" => "declare zeroext i1 @kr_tcp_stream_accept(ptr, ptr)",
        "kr_tcp_stream_try_accept" => "declare i32 @kr_tcp_stream_try_accept(ptr, ptr)",
        "kr_tcp_stream_start_connect" => {
            "declare zeroext i1 @kr_tcp_stream_start_connect(ptr, ptr)"
        }
        "kr_tcp_stream_finish_connect" => "declare i32 @kr_tcp_stream_finish_connect(ptr)",
        "kr_tcp_stream_try_read_line" => "declare ptr @kr_tcp_stream_try_read_line(ptr)",
        "kr_tcp_stream_at_end" => "declare zeroext i1 @kr_tcp_stream_at_end(ptr)",
        "kr_tcp_stream_try_read" => "declare ptr @kr_tcp_stream_try_read(ptr, i32, ptr)",
        "kr_tcp_stream_try_write" => "declare i32 @kr_tcp_stream_try_write(ptr, ptr, i32)",
        "kr_tcp_stream_queue_text" => "declare void @kr_tcp_stream_queue_text(ptr, ptr)",
        "kr_tcp_stream_queue_bytes" => "declare void @kr_tcp_stream_queue_bytes(ptr, ptr)",
        "kr_tcp_stream_flush" => "declare i32 @kr_tcp_stream_flush(ptr)",
        "kr_tcp_stream_queued" => "declare i64 @kr_tcp_stream_queued(ptr)",
        "kr_tcp_stream_peer_addr" => "declare ptr @kr_tcp_stream_peer_addr(ptr)",
        "kr_tcp_stream_read_line" => "declare ptr @kr_tcp_stream_read_line(ptr)",
        "kr_tcp_stream_read_all" => "declare ptr @kr_tcp_stream_read_all(ptr)",
        "kr_tcp_stream_read" => "declare ptr @kr_tcp_stream_read(ptr, i32, ptr)",
        "kr_tcp_stream_write" => "declare zeroext i1 @kr_tcp_stream_write(ptr, ptr)",
        "kr_tcp_stream_write_bytes" => "declare zeroext i1 @kr_tcp_stream_write_bytes(ptr, ptr)",
        "kr_tcp_stream_shutdown_write" => "declare zeroext i1 @kr_tcp_stream_shutdown_write(ptr)",
        "kr_tcp_stream_set_no_delay" => {
            "declare zeroext i1 @kr_tcp_stream_set_no_delay(ptr, i1 zeroext)"
        }
        "kr_udp_bind" => "declare zeroext i1 @kr_udp_bind(ptr, ptr)",
        "kr_udp_send_to" => "declare zeroext i1 @kr_udp_send_to(ptr, ptr, ptr)",
        "kr_udp_receive" => "declare ptr @kr_udp_receive(ptr, i32, ptr)",
        "kr_udp_try_send_to" => "declare i32 @kr_udp_try_send_to(ptr, ptr, ptr)",
        "kr_udp_try_receive" => "declare ptr @kr_udp_try_receive(ptr, i32, ptr)",
        "kr_udp_last_sender" => "declare ptr @kr_udp_last_sender(ptr)",
        "kr_string_bytes" => "declare ptr @kr_string_bytes(ptr, ptr)",
        "kr_string_from_utf8" => "declare ptr @kr_string_from_utf8(ptr)",
        "kr_file_write" => "declare i1 @kr_file_write(ptr, ptr)",
        "kr_file_flush" => "declare i1 @kr_file_flush(ptr)",
        "kr_file_write_bytes" => "declare i1 @kr_file_write_bytes(ptr, ptr)",
        "kr_file_read_bytes" => "declare ptr @kr_file_read_bytes(ptr, i32, ptr)",
        "kr_file_read_line" => "declare ptr @kr_file_read_line(ptr)",
        "kr_file_read_all" => "declare ptr @kr_file_read_all(ptr)",
        "kr_file_close" => "declare void @kr_file_close(ptr)",
        "kr_console_eprint" => "declare void @kr_console_eprint(ptr)",
        "kr_system_exit" => "declare void @kr_system_exit(i32) noreturn",
        "kr_system_env" => "declare ptr @kr_system_env(ptr)",
        "kr_system_working_directory" => "declare ptr @kr_system_working_directory()",
        "kr_io_canonical_path" => "declare ptr @kr_io_canonical_path(ptr)",
        "kr_process_run" => "declare i32 @kr_process_run(ptr, ptr, ptr, i1 zeroext)",
        "kr_process_captured" => "declare ptr @kr_process_captured(i1 zeroext)",
        "kr_system_millis" => "declare i64 @kr_system_millis()",
        "kr_system_nanos" => "declare i64 @kr_system_nanos()",
        "kr_system_epoch_nanos" => "declare i64 @kr_system_epoch_nanos()",
        "kr_builder_insert" => "declare i1 @kr_builder_insert(ptr, i32, ptr)",
        "kr_builder_truncate" => "declare i1 @kr_builder_truncate(ptr, i32)",
        "kr_builder_reverse" => "declare void @kr_builder_reverse(ptr)",
        "kr_builder_to_string" => "declare ptr @kr_builder_to_string(ptr)",
        "kr_builder_length" => "declare i32 @kr_builder_length(ptr)",
        "kr_builder_clear" => "declare void @kr_builder_clear(ptr)",
        "kr_builder_free" => "declare void @kr_builder_free(ptr)",
        "kr_string_trim_start" => "declare ptr @kr_string_trim_start(ptr)",
        "kr_string_trim_end" => "declare ptr @kr_string_trim_end(ptr)",
        "kr_string_char_at" => "declare i32 @kr_string_char_at(ptr, i32)",
        "kr_string_index_of_from" => "declare i32 @kr_string_index_of_from(ptr, ptr, i32)",
        "kr_string_last_index_of" => "declare i32 @kr_string_last_index_of(ptr, ptr)",
        "kr_format_double" => "declare ptr @kr_format_double(double, ptr)",
        "kr_format_text" => "declare ptr @kr_format_text(ptr, ptr)",
        "kr_bridge_receive" => "declare ptr @kr_bridge_receive()",
        "kr_bridge_send" => "declare void @kr_bridge_send(ptr)",
        "kr_bridge_escape" => "declare ptr @kr_bridge_escape(ptr)",
        "kr_bridge_unescape" => "declare ptr @kr_bridge_unescape(ptr)",
        "kr_uncaught" => "declare void @kr_uncaught(ptr, ptr)",
        "kr_char_is_digit" => "declare zeroext i1 @kr_char_is_digit(i32)",
        "kr_char_is_letter" => "declare zeroext i1 @kr_char_is_letter(i32)",
        "kr_char_is_whitespace" => "declare zeroext i1 @kr_char_is_whitespace(i32)",
        "kr_char_is_upper" => "declare zeroext i1 @kr_char_is_upper(i32)",
        "kr_char_is_lower" => "declare zeroext i1 @kr_char_is_lower(i32)",
        "kr_char_to_upper" => "declare i32 @kr_char_to_upper(i32)",
        "kr_char_to_lower" => "declare i32 @kr_char_to_lower(i32)",
        "kr_random" => "declare double @kr_random()",
        "kr_thread_spawn" => "declare ptr @kr_thread_spawn(ptr, ptr)",
        "kr_thread_join" => "declare void @kr_thread_join(ptr)",
        "kr_thread_sleep" => "declare void @kr_thread_sleep(i64)",
        "kr_mutex_new" => "declare ptr @kr_mutex_new()",
        "kr_mutex_lock" => "declare void @kr_mutex_lock(ptr)",
        "kr_mutex_unlock" => "declare void @kr_mutex_unlock(ptr)",
        "kr_mutex_free" => "declare void @kr_mutex_free(ptr)",
        "kr_mutex_wait" => "declare void @kr_mutex_wait(ptr)",
        "kr_mutex_wait_millis" => "declare zeroext i1 @kr_mutex_wait_millis(ptr, i64)",
        "kr_mutex_notify" => "declare void @kr_mutex_notify(ptr)",
        "kr_mutex_notify_all" => "declare void @kr_mutex_notify_all(ptr)",
        "kr_thread_current_id" => "declare i64 @kr_thread_current_id()",
        "kr_secure_random_fill" => "declare void @kr_secure_random_fill(ptr)",
        "kr_rwlock_new" => "declare ptr @kr_rwlock_new()",
        "kr_rwlock_read" => "declare void @kr_rwlock_read(ptr)",
        "kr_rwlock_write" => "declare void @kr_rwlock_write(ptr)",
        "kr_rwlock_unlock" => "declare void @kr_rwlock_unlock(ptr)",
        "kr_rwlock_free" => "declare void @kr_rwlock_free(ptr)",
        "kr_table_free" => "declare void @kr_table_free(ptr, ptr)",
        "kr_table_clear" => "declare void @kr_table_clear(ptr, ptr)",
        "kr_table_find" => "declare ptr @kr_table_find(ptr, ptr, ptr)",
        "kr_table_insert" => "declare ptr @kr_table_insert(ptr, ptr, ptr, ptr)",
        "kr_table_remove" => "declare zeroext i1 @kr_table_remove(ptr, ptr, ptr, ptr)",
        "kr_table_slot_count" => "declare i64 @kr_table_slot_count(ptr)",
        "kr_table_slot" => "declare ptr @kr_table_slot(ptr, ptr, i64)",
        "kr_runtime_init" => "declare void @kr_runtime_init(i32, ptr)",
        "kr_stack_guard_install" => "declare void @kr_stack_guard_install()",
        "kr_runtime_exit" => "declare void @kr_runtime_exit()",
        "kr_runtime_args" => "declare ptr @kr_runtime_args(ptr)",
        "kr_report_thread" => "declare void @kr_report_thread(ptr, ptr)",
        "kr_test_begin" => "declare void @kr_test_begin(i64)",
        "kr_test_passed" => "declare void @kr_test_passed(ptr)",
        "kr_test_failed" => "declare void @kr_test_failed(ptr, ptr, ptr)",
        "kr_test_end" => "declare i32 @kr_test_end()",
        "kr_export_failed" => "declare void @kr_export_failed(ptr, ptr)",
        "kr_once" => "declare void @kr_once(ptr, ptr)",
        _ => panic!("unknown runtime function `{name}`"),
    }
}
