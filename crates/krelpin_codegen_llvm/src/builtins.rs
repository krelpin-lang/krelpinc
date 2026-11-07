use krelpin_ast::ast::{PrimitiveTy, ReceiverKind};
use krelpin_errors::Diagnostic;
use krelpin_span::Symbol;
use krelpin_span::def_id::DefId;
use krelpin_typeck::{AdtKind, LangItem, Ty};

use crate::cx::Cx;
use crate::func::{FnCx, array_ll};
use crate::instance::{Instance, Thunk};
use crate::layout::{NetClass, PtrKind, Shape};
use crate::rtti::RtKey;

struct Builtin {
    params: Vec<Ty>,
    self_ty: Ty,
    receiver: Option<ReceiverKind>,
}

impl Builtin {
    fn arg(&self, index: usize) -> String {
        let offset = usize::from(self.receiver.is_some());
        format!("%a{}", index + offset)
    }

    fn arg_ty(&self, index: usize) -> Ty {
        let offset = usize::from(self.receiver.is_some());
        self.params[index + offset].clone()
    }
}

impl Cx<'_, '_> {
    pub(crate) fn emit_builtin(
        &mut self,
        id: usize,
        owner: DefId,
        name: Symbol,
        member: Option<u32>,
        args: &[Ty],
        self_ty: &Ty,
    ) -> String {
        let instance = Instance::Builtin {
            owner,
            name,
            member,
            args: args.to_vec(),
            self_ty: self_ty.clone(),
        };
        let method = self.builtin_method(owner, name, member);
        let params = self.instance_params(&instance);
        let ret = self.instance_ret(&instance);
        let builtin = Builtin {
            receiver: self.receiver_kind(&method),
            params: params.clone(),
            self_ty: self_ty.clone(),
        };
        let fn_name = self.fn_name(id);
        let rendered: Vec<String> = params
            .iter()
            .enumerate()
            .map(|(index, ty)| format!("{} %a{index}", self.llty(ty)))
            .collect();
        let llret = self.llty(&ret);
        let owner_name = self.tcx.sig(owner).name.name.to_string();
        let mut fx = FnCx::new(self, Default::default(), ret.clone());
        fx.start("entry");
        let handled = fx.builtin_body(owner, name.as_str(), &builtin);
        if !handled {
            fx.cx.error(Diagnostic::error(format!(
                "the code generator does not support the intrinsic `{owner_name}.{name}` yet"
            )));
            fx.ret_zero(&ret);
        }
        fx.finish_fail();
        format!(
            "define internal {llret} {fn_name}({}) {{\nallocas:\n{}  br label %entry\n{}}}\n",
            rendered.join(", "),
            fx.allocas,
            fx.out
        )
    }
}

impl FnCx<'_, '_, '_> {
    fn ret(&mut self, value: &str, ty: &Ty) {
        let ret = self.ret_ty.clone();
        let ll = self.ll(&ret);
        if ll == "void" {
            self.line("ret void");
            return;
        }
        let converted = self.convert(value, ty, &ret);
        self.line(format!("ret {ll} {converted}"));
    }

    fn this_value(&mut self, builtin: &Builtin) -> String {
        match builtin.receiver {
            Some(ReceiverKind::Owned) | None => "%a0".to_owned(),
            Some(_) => {
                let ty = builtin.self_ty.clone();
                self.load(&ty, "%a0")
            }
        }
    }

    fn builtin_body(&mut self, owner: DefId, name: &str, builtin: &Builtin) -> bool {
        let items = &self.cx.tcx.lang_items;
        let kind = self.cx.tcx.sig(owner).kind;
        if items.is(owner, LangItem::Object) && name == "toString" {
            let text = self.default_to_string(builtin);
            let string = self.cx.tcx.string_ty();
            self.ret(&text, &string);
            return true;
        }
        if items.is(owner, LangItem::Enum)
            || (kind == AdtKind::Enum && builtin.receiver.is_some())
            || (kind == AdtKind::Enum && name == "values")
            || (kind == AdtKind::Record && matches!(name, "equals" | "hashCode" | "clone"))
            || (kind == AdtKind::Record
                && builtin.receiver.is_some()
                && self
                    .cx
                    .tcx
                    .sig(owner)
                    .components
                    .contains(&Symbol::intern(name)))
        {
            return self.adt_builtin(name, builtin);
        }
        if items.is(owner, LangItem::String) {
            return self.string_builtin(name, builtin);
        }
        if items.is(owner, LangItem::Console) {
            return self.console_builtin(name, builtin);
        }
        if items.is(owner, LangItem::Math) {
            return self.math_builtin(name);
        }
        if let Some(primitive) = items.primitive_of(owner) {
            return self.primitive_builtin(primitive, name, builtin);
        }
        if items.is(owner, LangItem::Thread) {
            return self.thread_builtin(name, builtin);
        }
        if items.is(owner, LangItem::ThreadTask) {
            return self.task_builtin(name, builtin);
        }
        if items.is(owner, LangItem::MacroBridge) {
            return self.bridge_builtin(name);
        }
        if items.is(owner, LangItem::Format) {
            return self.format_builtin(name);
        }
        if items.is(owner, LangItem::StringBuilder) {
            return self.builder_builtin(name, builtin);
        }
        if items.is(owner, LangItem::System) {
            return self.system_builtin(name, builtin);
        }
        if items.is(owner, LangItem::SecureRandom) && name == "fillRaw" {
            let bytes = self.assign("load ptr, ptr %a0");
            self.runtime("void", "kr_secure_random_fill", &format!("ptr {bytes}"));
            self.line("ret void");
            return true;
        }
        if builtin.receiver.is_none()
            && builtin.params.is_empty()
            && matches!(name, "lastError" | "lastFailed")
        {
            let ret_ll = if name == "lastError" { "ptr" } else { "i1" };
            let function = if name == "lastError" {
                "kr_io_last_error"
            } else {
                "kr_io_failed"
            };
            self.runtime_call(function, ret_ll, builtin, &[]);
            return true;
        }
        if items.is(owner, LangItem::Files) {
            return self.files_builtin(name, builtin);
        }
        if items.is(owner, LangItem::Command) {
            return self.process_builtin(name, builtin);
        }
        if items.is(owner, LangItem::FileReader) || items.is(owner, LangItem::FileWriter) {
            return self.file_builtin(name, builtin);
        }
        if let Some(class) = self.cx.net_class(owner) {
            return self.net_builtin(class, name, builtin);
        }
        if items.is(owner, LangItem::AtomicInt)
            || items.is(owner, LangItem::AtomicLong)
            || items.is(owner, LangItem::AtomicBool)
        {
            return self.atomic_builtin(owner, name, builtin);
        }
        if items.is(owner, LangItem::Mutex) || items.is(owner, LangItem::MutexGuard) {
            return self.mutex_builtin(owner, name, builtin);
        }
        if items.is(owner, LangItem::ReadWriteLock)
            || items.is(owner, LangItem::ReadGuard)
            || items.is(owner, LangItem::WriteGuard)
        {
            return self.rwlock_builtin(owner, name, builtin);
        }
        if items.is(owner, LangItem::ArrayList) {
            return self.list_builtin(name, builtin);
        }
        if items.is_table(owner) {
            return self.table_builtin(owner, name, builtin);
        }
        false
    }

    /// The accessor of a record component: a copy of the component, or a
    /// reference to it when it can't be copied.
    fn record_accessor(
        &mut self,
        def: DefId,
        args: &[Ty],
        index: usize,
        builtin: &Builtin,
    ) -> bool {
        let ty = builtin.self_ty.clone();
        let fields = self.cx.record_fields(def, args);
        let field_ty = fields[index].1.clone();
        let record_ll = self.ll(&ty);
        let address = self.assign(format!(
            "getelementptr inbounds {record_ll}, ptr %a0, i32 0, i32 {index}"
        ));
        let address = self.indirect_slot(&ty, &field_ty, address);
        let ret = self.ret_ty.clone();
        if let Ty::Ref { .. } = ret {
            self.ret(&address, &ret);
        } else {
            let value = self.load(&field_ty, &address);
            let copy = self.copy_value(&value, &field_ty);
            self.ret(&copy, &field_ty);
        }
        true
    }

    fn default_to_string(&mut self, builtin: &Builtin) -> String {
        let ty = builtin.self_ty.clone();
        match self.cx.shape(&ty) {
            Shape::Prim(primitive) => {
                let value = self.load(&ty, "%a0");
                self.prim_to_string(&value, primitive)
            }
            Shape::Ptr(PtrKind::String) => {
                let value = self.load(&ty, "%a0");
                let string = self.cx.tcx.string_ty();
                self.copy_value(&value, &string)
            }
            Shape::Record(def, args) => {
                let name = self.cx.tcx.sig(def).name.name.to_string();
                let fields = self.cx.record_fields(def, &args);
                let record_ll = self.ll(&ty);
                let mut parts = Vec::new();
                for (index, (field, field_ty)) in fields.iter().enumerate() {
                    let address = self.assign(format!(
                        "getelementptr inbounds {record_ll}, ptr %a0, i32 0, i32 {index}"
                    ));
                    let address = self.indirect_slot(&ty, field_ty, address);
                    parts.push((field.to_string(), self.value_to_string(&address, field_ty)));
                }
                self.join_parts(&format!("{name}["), &parts, "]", true)
            }
            Shape::Enum(def, args) => {
                let enum_ll = self.ll(&ty);
                let tag_addr = self.assign(format!(
                    "getelementptr inbounds {enum_ll}, ptr %a0, i32 0, i32 0"
                ));
                let tag = self.assign(format!("load i32, ptr {tag_addr}"));
                let variants = self.cx.tcx.sig(def).variants.clone();
                let result = self.alloca_ll("ptr");
                let done = self.label("named");
                let mut cases = Vec::new();
                let mut blocks = Vec::new();
                for (index, _) in variants.iter().enumerate() {
                    let label = self.label("variant");
                    cases.push(format!("i32 {index}, label %{label}"));
                    blocks.push(label);
                }
                self.line(format!(
                    "switch i32 {tag}, label %{done} [ {} ]",
                    cases.join(" ")
                ));
                for (index, variant) in variants.iter().enumerate() {
                    self.start(&blocks[index]);
                    let fields = self.cx.variant_fields(def, &args, index);
                    let text = if fields.is_empty() {
                        self.cx.string_literal(variant.name.name.as_str())
                    } else {
                        let variant_ll = self.cx.variant_type(def, &args, index);
                        let mut parts = Vec::new();
                        for (position, (field, field_ty)) in fields.iter().enumerate() {
                            let address = self.assign(format!(
                                "getelementptr inbounds {variant_ll}, ptr %a0, i32 0, i32 {}",
                                position + 1
                            ));
                            let address = self.indirect_slot(&ty, field_ty, address);
                            parts.push((
                                field.to_string(),
                                self.value_to_string(&address, field_ty),
                            ));
                        }
                        self.join_parts(&format!("{}(", variant.name.name), &parts, ")", false)
                    };
                    self.line(format!("store ptr {text}, ptr {result}"));
                    self.line(format!("br label %{done}"));
                }
                self.start(&done);
                self.assign(format!("load ptr, ptr {result}"))
            }
            _ => {
                let object = self.this_value(builtin);
                self.runtime("ptr", "kr_string_describe", &format!("ptr {object}"))
            }
        }
    }

    fn join_parts(
        &mut self,
        open: &str,
        parts: &[(String, String)],
        close: &str,
        named: bool,
    ) -> String {
        let string = self.cx.tcx.string_ty();
        let mut current = self.cx.string_literal(open);
        for (index, (name, text)) in parts.iter().enumerate() {
            let prefix = match (index, named) {
                (0, true) => format!("{name}="),
                (0, false) => String::new(),
                (_, true) => format!(", {name}="),
                (_, false) => ", ".to_owned(),
            };
            if !prefix.is_empty() {
                let literal = self.cx.string_literal(&prefix);
                let joined = self.runtime(
                    "ptr",
                    "kr_string_concat",
                    &format!("ptr {current}, ptr {literal}"),
                );
                self.drop_value(&current, &string);
                current = joined;
            }
            let joined = self.runtime(
                "ptr",
                "kr_string_concat",
                &format!("ptr {current}, ptr {text}"),
            );
            self.drop_value(&current, &string);
            self.drop_value(text, &string);
            current = joined;
        }
        let literal = self.cx.string_literal(close);
        let joined = self.runtime(
            "ptr",
            "kr_string_concat",
            &format!("ptr {current}, ptr {literal}"),
        );
        self.drop_value(&current, &string);
        joined
    }

    fn adt_builtin(&mut self, name: &str, builtin: &Builtin) -> bool {
        let ty = builtin.self_ty.clone();
        if let Shape::Record(def, args) = self.cx.shape(&ty)
            && let Some(index) = self
                .cx
                .tcx
                .sig(def)
                .components
                .iter()
                .position(|c| c.as_str() == name)
        {
            return self.record_accessor(def, &args, index, builtin);
        }
        match (self.cx.shape(&ty), name) {
            (Shape::Enum(..), "ordinal") => {
                let enum_ll = self.ll(&ty);
                let tag = self.assign(format!(
                    "getelementptr inbounds {enum_ll}, ptr %a0, i32 0, i32 0"
                ));
                let value = self.assign(format!("load i32, ptr {tag}"));
                self.ret(&value, &Ty::INT);
                true
            }
            (Shape::Enum(def, _), "name") => {
                let enum_ll = self.ll(&ty);
                let tag = self.assign(format!(
                    "getelementptr inbounds {enum_ll}, ptr %a0, i32 0, i32 0"
                ));
                let tag = self.assign(format!("load i32, ptr {tag}"));
                let variants = self.cx.tcx.sig(def).variants.clone();
                let result = self.alloca_ll("ptr");
                let done = self.label("named");
                let mut cases = Vec::new();
                for (index, variant) in variants.iter().enumerate() {
                    let label = self.label("variant");
                    cases.push((index, label, variant.name.name));
                }
                let rendered: Vec<String> = cases
                    .iter()
                    .map(|(index, label, _)| format!("i32 {index}, label %{label}"))
                    .collect();
                self.line(format!(
                    "switch i32 {tag}, label %{done} [ {} ]",
                    rendered.join(" ")
                ));
                for (_, label, name) in cases {
                    self.start(&label);
                    let literal = self.cx.string_literal(name.as_str());
                    self.line(format!("store ptr {literal}, ptr {result}"));
                    self.line(format!("br label %{done}"));
                }
                self.start(&done);
                let value = self.assign(format!("load ptr, ptr {result}"));
                let string = self.cx.tcx.string_ty();
                self.ret(&value, &string);
                true
            }
            (Shape::Enum(def, args), "values") => {
                let variants = self.cx.tcx.sig(def).variants.len();
                let ret = self.ret_ty.clone();
                let array = self.new_array(&ret, &variants.to_string());
                let elem_ll = self.cx.mem_llty(&ty);
                for index in 0..variants {
                    let variant_ll = self.cx.variant_type(def, &args, index);
                    let address = self.assign(format!(
                        "getelementptr inbounds {}, ptr {array}, i32 0, i32 2, i64 {index}",
                        array_ll(&elem_ll)
                    ));
                    let tag = self.assign(format!(
                        "getelementptr inbounds {variant_ll}, ptr {address}, i32 0, i32 0"
                    ));
                    self.line(format!("store i32 {index}, ptr {tag}"));
                }
                self.ret(&array, &ret);
                true
            }
            (Shape::Enum(def, args), "equals") => {
                let (a, b) = (self.enum_tag(&ty, "%a0"), self.enum_tag(&ty, "%a1"));
                let same = self.assign(format!("icmp eq i32 {a}, {b}"));
                let result = self.alloca_ll("i1");
                self.line(format!("store i1 false, ptr {result}"));
                let fields = self.label("fields");
                let done = self.label("compared");
                self.line(format!("br i1 {same}, label %{fields}, label %{done}"));
                self.start(&fields);
                self.each_variant(
                    &ty,
                    def,
                    &args,
                    &a,
                    &done,
                    |fx, variant_ll, variant_fields| {
                        let mut equal = "true".to_owned();
                        for (position, (_, field_ty)) in variant_fields.iter().enumerate() {
                            let left = fx.variant_field(&ty, variant_ll, "%a0", position, field_ty);
                            let right =
                                fx.variant_field(&ty, variant_ll, "%a1", position, field_ty);
                            let field_equal = fx.field_equals(&left, &right, field_ty);
                            equal = fx.assign(format!("and i1 {equal}, {field_equal}"));
                        }
                        fx.line(format!("store i1 {equal}, ptr {result}"));
                    },
                );
                self.start(&done);
                let value = self.assign(format!("load i1, ptr {result}"));
                self.ret(&value, &Ty::BOOLEAN);
                true
            }
            (Shape::Enum(def, args), "hashCode") => {
                let tag = self.enum_tag(&ty, "%a0");
                let result = self.alloca_ll("i32");
                self.line(format!("store i32 {tag}, ptr {result}"));
                let done = self.label("hashed");
                self.each_variant(
                    &ty,
                    def,
                    &args,
                    &tag,
                    &done,
                    |fx, variant_ll, variant_fields| {
                        let mut hash = tag.clone();
                        for (position, (_, field_ty)) in variant_fields.iter().enumerate() {
                            let field =
                                fx.variant_field(&ty, variant_ll, "%a0", position, field_ty);
                            let field_hash = fx.field_hash(&field, field_ty);
                            let scaled = fx.assign(format!("mul i32 {hash}, 31"));
                            hash = fx.assign(format!("add i32 {scaled}, {field_hash}"));
                        }
                        fx.line(format!("store i32 {hash}, ptr {result}"));
                    },
                );
                self.start(&done);
                let value = self.assign(format!("load i32, ptr {result}"));
                self.ret(&value, &Ty::INT);
                true
            }
            (Shape::Enum(..), "compareTo") => {
                let (a, b) = (self.enum_tag(&ty, "%a0"), self.enum_tag(&ty, "%a1"));
                let less = self.assign(format!("icmp slt i32 {a}, {b}"));
                let greater = self.assign(format!("icmp sgt i32 {a}, {b}"));
                let low = self.assign(format!("select i1 {less}, i32 -1, i32 0"));
                let order = self.assign(format!("select i1 {greater}, i32 1, i32 {low}"));
                self.ret(&order, &Ty::INT);
                true
            }
            (Shape::Enum(def, args), "clone") => {
                let tag = self.enum_tag(&ty, "%a0");
                let slot = self.alloca(&ty);
                let done = self.label("cloned");
                self.each_variant(
                    &ty,
                    def,
                    &args,
                    &tag,
                    &done,
                    |fx, variant_ll, variant_fields| {
                        let tag_address = fx.assign(format!(
                            "getelementptr inbounds {variant_ll}, ptr {slot}, i32 0, i32 0"
                        ));
                        fx.line(format!("store i32 {tag}, ptr {tag_address}"));
                        for (position, (_, field_ty)) in variant_fields.iter().enumerate() {
                            let source =
                                fx.variant_field(&ty, variant_ll, "%a0", position, field_ty);
                            let value = fx.field_clone(&source, field_ty);
                            let address = fx.assign(format!(
                                "getelementptr inbounds {variant_ll}, ptr {slot}, i32 0, i32 {}",
                                position + 1
                            ));
                            if fx.cx.is_indirect(&ty, field_ty) {
                                let cell = fx.wrap_indirect(&ty, field_ty, &value);
                                fx.line(format!("store ptr {cell}, ptr {address}"));
                            } else {
                                fx.store(field_ty, &value, &address);
                            }
                        }
                    },
                );
                self.start(&done);
                let value = self.load(&ty, &slot);
                self.zero(&ty, &slot);
                self.ret(&value, &ty);
                true
            }
            (Shape::Record(def, args), "equals") => {
                let record_ll = self.ll(&ty);
                let fields = self.cx.record_fields(def, &args);
                let mut result = "true".to_owned();
                for (index, (_, field_ty)) in fields.iter().enumerate() {
                    let a = self.assign(format!(
                        "getelementptr inbounds {record_ll}, ptr %a0, i32 0, i32 {index}"
                    ));
                    let b = self.assign(format!(
                        "getelementptr inbounds {record_ll}, ptr %a1, i32 0, i32 {index}"
                    ));
                    let a = self.indirect_slot(&ty, field_ty, a);
                    let b = self.indirect_slot(&ty, field_ty, b);
                    let equal = self.field_equals(&a, &b, field_ty);
                    result = self.assign(format!("and i1 {result}, {equal}"));
                }
                self.ret(&result, &Ty::BOOLEAN);
                true
            }
            (Shape::Record(def, args), "clone") => {
                let record_ll = self.ll(&ty);
                let fields = self.cx.record_fields(def, &args);
                let mut current = "zeroinitializer".to_owned();
                for (index, (_, field_ty)) in fields.iter().enumerate() {
                    let address = self.assign(format!(
                        "getelementptr inbounds {record_ll}, ptr %a0, i32 0, i32 {index}"
                    ));
                    let address = self.indirect_slot(&ty, field_ty, address);
                    let value = self.field_clone(&address, field_ty);
                    let value = self.wrap_indirect(&ty, field_ty, &value);
                    let field_ll = self.cx.field_llty(&ty, field_ty);
                    current = self.assign(format!(
                        "insertvalue {record_ll} {current}, {field_ll} {value}, {index}"
                    ));
                }
                self.ret(&current, &ty);
                true
            }
            (Shape::Record(def, args), "hashCode") => {
                let record_ll = self.ll(&ty);
                let fields = self.cx.record_fields(def, &args);
                let mut hash = "0".to_owned();
                for (index, (_, field_ty)) in fields.iter().enumerate() {
                    let a = self.assign(format!(
                        "getelementptr inbounds {record_ll}, ptr %a0, i32 0, i32 {index}"
                    ));
                    let a = self.indirect_slot(&ty, field_ty, a);
                    let field_hash = self.field_hash(&a, field_ty);
                    let scaled = self.assign(format!("mul i32 {hash}, 31"));
                    hash = self.assign(format!("add i32 {scaled}, {field_hash}"));
                }
                self.ret(&hash, &Ty::INT);
                true
            }
            _ => false,
        }
    }

    fn nullable_parts(&mut self, address: &str, ty: &Ty) -> (String, String) {
        if matches!(self.cx.shape(ty), Shape::NullableValue(_)) {
            let ll = self.ll(ty);
            let flag_address = self.assign(format!(
                "getelementptr inbounds {ll}, ptr {address}, i32 0, i32 0"
            ));
            let flag = self.assign(format!("load i1, ptr {flag_address}"));
            let payload = self.assign(format!(
                "getelementptr inbounds {ll}, ptr {address}, i32 0, i32 1"
            ));
            (flag, payload)
        } else {
            let pointer = self.assign(format!("load ptr, ptr {address}"));
            let flag = self.assign(format!("icmp ne ptr {pointer}, null"));
            (flag, address.to_owned())
        }
    }

    fn field_equals(&mut self, a: &str, b: &str, ty: &Ty) -> String {
        if let Ty::Nullable(inner) = ty
            && !matches!(inner.as_ref(), Ty::Ref { .. })
        {
            let inner = inner.as_ref().clone();
            let (a_present, a_payload) = self.nullable_parts(a, ty);
            let (b_present, b_payload) = self.nullable_parts(b, ty);
            let result = self.alloca_ll("i1");
            let both = self.assign(format!("and i1 {a_present}, {b_present}"));
            let same_presence = self.assign(format!("icmp eq i1 {a_present}, {b_present}"));
            self.line(format!("store i1 {same_presence}, ptr {result}"));
            let compare = self.label("present");
            let done = self.label("compared");
            self.line(format!("br i1 {both}, label %{compare}, label %{done}"));
            self.start(&compare);
            let equal = self.field_equals(&a_payload, &b_payload, &inner);
            self.line(format!("store i1 {equal}, ptr {result}"));
            self.line(format!("br label %{done}"));
            self.start(&done);
            return self.assign(format!("load i1, ptr {result}"));
        }
        match self.cx.shape(ty) {
            Shape::Prim(PrimitiveTy::Float | PrimitiveTy::Double) => {
                let ll = self.ll(ty);
                let a = self.assign(format!("load {ll}, ptr {a}"));
                let b = self.assign(format!("load {ll}, ptr {b}"));
                self.assign(format!("fcmp oeq {ll} {a}, {b}"))
            }
            Shape::Prim(_) => {
                let ll = self.ll(ty);
                let a = self.assign(format!("load {ll}, ptr {a}"));
                let b = self.assign(format!("load {ll}, ptr {b}"));
                self.assign(format!("icmp eq {ll} {a}, {b}"))
            }
            _ => self.call_equals(a, b, ty),
        }
    }

    fn enum_tag(&mut self, ty: &Ty, value: &str) -> String {
        let enum_ll = self.ll(ty);
        let address = self.assign(format!(
            "getelementptr inbounds {enum_ll}, ptr {value}, i32 0, i32 0"
        ));
        self.assign(format!("load i32, ptr {address}"))
    }

    fn variant_field(
        &mut self,
        ty: &Ty,
        variant_ll: &str,
        value: &str,
        position: usize,
        field_ty: &Ty,
    ) -> String {
        let address = self.assign(format!(
            "getelementptr inbounds {variant_ll}, ptr {value}, i32 0, i32 {}",
            position + 1
        ));
        self.indirect_slot(ty, field_ty, address)
    }

    fn each_variant(
        &mut self,
        ty: &Ty,
        def: DefId,
        args: &[Ty],
        tag: &str,
        done: &str,
        mut body: impl FnMut(&mut Self, &str, &[(Symbol, Ty)]),
    ) {
        let _ = ty;
        let count = self.cx.tcx.sig(def).variants.len();
        let labels: Vec<String> = (0..count).map(|_| self.label("variant")).collect();
        let cases: Vec<String> = labels
            .iter()
            .enumerate()
            .map(|(index, label)| format!("i32 {index}, label %{label}"))
            .collect();
        self.line(format!(
            "switch i32 {tag}, label %{done} [ {} ]",
            cases.join(" ")
        ));
        for (index, label) in labels.iter().enumerate() {
            self.start(label);
            let variant_ll = self.cx.variant_type(def, args, index);
            let fields = self.cx.variant_fields(def, args, index);
            body(self, &variant_ll, &fields);
            self.line(format!("br label %{done}"));
        }
    }

    fn field_clone(&mut self, address: &str, ty: &Ty) -> String {
        match (self.cx.shape(ty), ty) {
            (Shape::Prim(_), _) => self.load(ty, address),
            (_, Ty::Ref { .. }) => self.load(ty, address),
            (_, Ty::Nullable(inner)) => {
                let inner = inner.as_ref().clone();
                let ll = self.ll(ty);
                let result = self.alloca_ll(&ll);
                let present = self.label("present");
                let absent = self.label("absent");
                let done = self.label("cloned");
                let (flag, payload) = self.nullable_parts(address, ty);
                self.line(format!("br i1 {flag}, label %{present}, label %{absent}"));
                self.start(&present);
                let cloned = self.field_clone(&payload, &inner);
                let wrapped = self.convert(&cloned, &inner, ty);
                self.line(format!("store {ll} {wrapped}, ptr {result}"));
                self.line(format!("br label %{done}"));
                self.start(&absent);
                self.line(format!("store {ll} zeroinitializer, ptr {result}"));
                self.line(format!("br label %{done}"));
                self.start(&done);
                self.assign(format!("load {ll}, ptr {result}"))
            }
            _ => self.call_clone(address, ty),
        }
    }

    fn field_hash(&mut self, a: &str, ty: &Ty) -> String {
        if let Ty::Nullable(inner) = ty
            && !matches!(inner.as_ref(), Ty::Ref { .. })
        {
            let inner = inner.as_ref().clone();
            let (present, payload) = self.nullable_parts(a, ty);
            let result = self.alloca_ll("i32");
            self.line(format!("store i32 0, ptr {result}"));
            let hash = self.label("present");
            let done = self.label("hashed");
            self.line(format!("br i1 {present}, label %{hash}, label %{done}"));
            self.start(&hash);
            let value = self.field_hash(&payload, &inner);
            self.line(format!("store i32 {value}, ptr {result}"));
            self.line(format!("br label %{done}"));
            self.start(&done);
            return self.assign(format!("load i32, ptr {result}"));
        }
        match self.cx.shape(ty) {
            Shape::Prim(primitive) => {
                let value = self.load(ty, a);
                self.prim_hash(&value, primitive)
            }
            _ => self.call_hash(a, ty),
        }
    }

    fn prim_hash(&mut self, value: &str, primitive: PrimitiveTy) -> String {
        match primitive {
            PrimitiveTy::Boolean => self.assign(format!("select i1 {value}, i32 1231, i32 1237")),
            PrimitiveTy::Byte | PrimitiveTy::Short => self.assign(format!(
                "sext {} {value} to i32",
                crate::layout::prim_llty(primitive)
            )),
            PrimitiveTy::Char | PrimitiveTy::Int => value.to_owned(),
            PrimitiveTy::Long => {
                let shifted = self.assign(format!("lshr i64 {value}, 32"));
                let mixed = self.assign(format!("xor i64 {value}, {shifted}"));
                self.assign(format!("trunc i64 {mixed} to i32"))
            }
            // Every NaN is equal to every other, so they all hash alike.
            PrimitiveTy::Float => {
                let nan = self.assign(format!("fcmp uno float {value}, {value}"));
                let bits = self.assign(format!("bitcast float {value} to i32"));
                self.assign(format!("select i1 {nan}, i32 2143289344, i32 {bits}"))
            }
            PrimitiveTy::Double => {
                let nan = self.assign(format!("fcmp uno double {value}, {value}"));
                let raw = self.assign(format!("bitcast double {value} to i64"));
                let bits = self.assign(format!(
                    "select i1 {nan}, i64 9221120237041090560, i64 {raw}"
                ));
                let shifted = self.assign(format!("lshr i64 {bits}, 32"));
                let mixed = self.assign(format!("xor i64 {bits}, {shifted}"));
                self.assign(format!("trunc i64 {mixed} to i32"))
            }
        }
    }

    fn checked_string(&mut self, value: &str, item: LangItem, message: &str) -> String {
        let failed = self.assign(format!("icmp eq ptr {value}, null"));
        let fail = self.fail_label();
        let ok = self.label("ok");
        let bad = self.label("bad");
        self.line(format!("br i1 {failed}, label %{bad}, label %{ok}"));
        self.start(&bad);
        self.throw_new(item, message, &fail);
        self.line("unreachable");
        self.start(&ok);
        value.to_owned()
    }

    fn string_builtin(&mut self, name: &str, builtin: &Builtin) -> bool {
        let string = self.cx.tcx.string_ty();
        let arg_string = |fx: &mut Self, index: usize| -> String {
            let ty = builtin.arg_ty(index);
            let arg = builtin.arg(index);
            match ty {
                Ty::Ref { .. } => fx.assign(format!("load ptr, ptr {arg}")),
                _ => arg,
            }
        };
        let release_args = |fx: &mut Self| {
            let offset = usize::from(builtin.receiver.is_some());
            for index in offset..builtin.params.len() {
                let ty = builtin.params[index].clone();
                if fx.cx.needs_drop(&ty) {
                    fx.drop_value(&format!("%a{index}"), &ty);
                }
            }
        };
        if name == "valueOf" {
            let text = self.stringify("%a0", &builtin.params[0]);
            self.drop_value("%a0", &builtin.params[0].clone());
            self.ret(&text, &string);
            return true;
        }
        if name == "fromUtf8" {
            let bytes = self.assign("load ptr, ptr %a0");
            let text = self.runtime("ptr", "kr_string_from_utf8", &format!("ptr {bytes}"));
            let ret = self.ret_ty.clone();
            self.ret(&text, &ret);
            return true;
        }
        if name == "join" {
            let joined = self.runtime("ptr", "kr_string_join", "ptr %a0, ptr %a1");
            release_args(self);
            self.ret(&joined, &string);
            return true;
        }
        let this = self.this_value(builtin);
        let result: (String, Ty) = match name {
            "length" => (
                self.runtime("i32", "kr_string_length", &format!("ptr {this}")),
                Ty::INT,
            ),
            "bytes" => {
                let array_ty = Ty::Array(Box::new(Ty::Primitive(PrimitiveTy::Byte)));
                let descriptor = self.cx.rt_global(RtKey::Array(array_ty.clone()));
                self.cx.drop_array_fn(&array_ty);
                (
                    self.runtime(
                        "ptr",
                        "kr_string_bytes",
                        &format!("ptr {this}, ptr {descriptor}"),
                    ),
                    array_ty,
                )
            }
            "chars" => {
                let array_ty = Ty::Array(Box::new(Ty::CHAR));
                let descriptor = self.cx.rt_global(RtKey::Array(array_ty.clone()));
                self.cx.drop_array_fn(&array_ty);
                (
                    self.runtime(
                        "ptr",
                        "kr_string_chars",
                        &format!("ptr {this}, ptr {descriptor}"),
                    ),
                    array_ty,
                )
            }
            "substring" => {
                let begin = builtin.arg(0);
                let end = if builtin.params.len() > 2 {
                    builtin.arg(1)
                } else {
                    self.runtime("i32", "kr_string_length", &format!("ptr {this}"))
                };
                let value = self.runtime(
                    "ptr",
                    "kr_string_substring",
                    &format!("ptr {this}, i32 {begin}, i32 {end}"),
                );
                let value = self.checked_string(
                    &value,
                    LangItem::IndexOutOfBoundsException,
                    "substring range is out of bounds",
                );
                (value, string.clone())
            }
            "indexOf" if builtin.params.len() > 2 => {
                let text = arg_string(self, 0);
                let from = builtin.arg(1);
                (
                    self.runtime(
                        "i32",
                        "kr_string_index_of_from",
                        &format!("ptr {this}, ptr {text}, i32 {from}"),
                    ),
                    Ty::INT,
                )
            }
            "indexOf" | "lastIndexOf" => {
                let text = arg_string(self, 0);
                let function = if name == "indexOf" {
                    "kr_string_index_of"
                } else {
                    "kr_string_last_index_of"
                };
                (
                    self.runtime("i32", function, &format!("ptr {this}, ptr {text}")),
                    Ty::INT,
                )
            }
            "charAt" => {
                let index = builtin.arg(0);
                let c = self.runtime(
                    "i32",
                    "kr_string_char_at",
                    &format!("ptr {this}, i32 {index}"),
                );
                let missing = self.assign(format!("icmp slt i32 {c}, 0"));
                let len = self.runtime("i32", "kr_string_length", &format!("ptr {this}"));
                self.throw_out_of_bounds(&missing, &index, &len);
                (c, Ty::CHAR)
            }
            "trimStart" | "trimEnd" => {
                let function = if name == "trimStart" {
                    "kr_string_trim_start"
                } else {
                    "kr_string_trim_end"
                };
                (
                    self.runtime("ptr", function, &format!("ptr {this}")),
                    string.clone(),
                )
            }
            "startsWith" | "endsWith" | "equals" => {
                let other = arg_string(self, 0);
                let function = match name {
                    "startsWith" => "kr_string_starts_with",
                    "endsWith" => "kr_string_ends_with",
                    _ => "kr_string_equals",
                };
                (
                    self.runtime("i1", function, &format!("ptr {this}, ptr {other}")),
                    Ty::BOOLEAN,
                )
            }
            "compareTo" => {
                let other = arg_string(self, 0);
                (
                    self.runtime(
                        "i32",
                        "kr_string_compare",
                        &format!("ptr {this}, ptr {other}"),
                    ),
                    Ty::INT,
                )
            }
            "hashCode" => (
                self.runtime("i32", "kr_string_hash", &format!("ptr {this}")),
                Ty::INT,
            ),
            "toUpperCase" => (
                self.runtime("ptr", "kr_string_to_upper", &format!("ptr {this}")),
                string.clone(),
            ),
            "toLowerCase" => (
                self.runtime("ptr", "kr_string_to_lower", &format!("ptr {this}")),
                string.clone(),
            ),
            "trim" => (
                self.runtime("ptr", "kr_string_trim", &format!("ptr {this}")),
                string.clone(),
            ),
            "replace" => {
                let target = arg_string(self, 0);
                let replacement = arg_string(self, 1);
                (
                    self.runtime(
                        "ptr",
                        "kr_string_replace",
                        &format!("ptr {this}, ptr {target}, ptr {replacement}"),
                    ),
                    string.clone(),
                )
            }
            "repeat" => {
                let count = builtin.arg(0);
                let value = self.runtime(
                    "ptr",
                    "kr_string_repeat",
                    &format!("ptr {this}, i32 {count}"),
                );
                let value = self.checked_string(
                    &value,
                    LangItem::IllegalArgumentException,
                    "repeat count is negative",
                );
                (value, string.clone())
            }
            "split" => {
                let separator = arg_string(self, 0);
                let array_ty = Ty::Array(Box::new(string.clone()));
                let descriptor = self.cx.rt_global(RtKey::Array(array_ty.clone()));
                self.cx.drop_array_fn(&array_ty);
                (
                    self.runtime(
                        "ptr",
                        "kr_string_split",
                        &format!("ptr {this}, ptr {separator}, ptr {descriptor}"),
                    ),
                    array_ty,
                )
            }
            _ => return false,
        };
        release_args(self);
        if builtin.receiver == Some(ReceiverKind::Owned) {
            self.drop_value("%a0", &string);
        }
        self.ret(&result.0, &result.1);
        true
    }

    fn console_builtin(&mut self, name: &str, builtin: &Builtin) -> bool {
        let string = self.cx.tcx.string_ty();
        match name {
            "print" | "println" => {
                if !builtin.params.is_empty() {
                    let ty = builtin.params[0].clone();
                    let text = self.stringify("%a0", &ty);
                    self.runtime("void", "kr_console_print", &format!("ptr {text}"));
                    self.drop_value(&text, &string);
                    self.drop_value("%a0", &ty);
                }
                if name == "println" {
                    self.runtime("void", "kr_console_newline", "");
                }
                self.line("ret void");
                true
            }
            "eprint" | "eprintln" => {
                if !builtin.params.is_empty() {
                    let ty = builtin.params[0].clone();
                    let text = self.stringify("%a0", &ty);
                    self.runtime("void", "kr_console_eprint", &format!("ptr {text}"));
                    self.drop_value(&text, &string);
                    self.drop_value("%a0", &ty);
                }
                if name == "eprintln" {
                    let newline = self.cx.string_literal("\n");
                    self.runtime("void", "kr_console_eprint", &format!("ptr {newline}"));
                }
                self.line("ret void");
                true
            }
            "readLine" => {
                let line = self.runtime("ptr", "kr_console_read_line", "");
                let ret = self.ret_ty.clone();
                self.ret(&line, &ret);
                true
            }
            _ => false,
        }
    }

    fn math_builtin(&mut self, name: &str) -> bool {
        let unary = |fx: &mut Self, function: &str| -> String {
            fx.cx
                .declare_dynamic(function, &format!("declare double @{function}(double)"));
            fx.assign(format!("call double @{function}(double %a0)"))
        };
        let binary = |fx: &mut Self, function: &str| -> String {
            fx.cx.declare_dynamic(
                function,
                &format!("declare double @{function}(double, double)"),
            );
            fx.assign(format!("call double @{function}(double %a0, double %a1)"))
        };
        let value = match name {
            "sqrt" => unary(self, "llvm.sqrt.f64"),
            "floor" => unary(self, "llvm.floor.f64"),
            "ceil" => unary(self, "llvm.ceil.f64"),
            "trunc" => unary(self, "llvm.trunc.f64"),
            "pow" => binary(self, "llvm.pow.f64"),
            // The C library's versions: LLVM has no intrinsics for all of
            // these on every target.
            "sin" | "cos" | "tan" | "asin" | "acos" | "atan" | "exp" | "log10" | "log2"
            | "cbrt" => unary(self, name),
            "ln" => unary(self, "log"),
            "atan2" | "hypot" => binary(self, name),
            "round" => {
                // Halfway cases round away from zero, and the conversion
                // saturates, so NaN gives 0 and infinities the extremes.
                let rounded = unary(self, "llvm.round.f64");
                let value = self.numeric(&rounded, PrimitiveTy::Double, PrimitiveTy::Long);
                self.ret(&value, &Ty::LONG);
                return true;
            }
            "random" => self.runtime("double", "kr_random", ""),
            _ => return false,
        };
        self.ret(&value, &Ty::DOUBLE);
        true
    }

    fn primitive_builtin(&mut self, primitive: PrimitiveTy, name: &str, builtin: &Builtin) -> bool {
        match name {
            "hashCode" => {
                let value = self.load(&Ty::Primitive(primitive), "%a0");
                let hash = self.prim_hash(&value, primitive);
                self.ret(&hash, &Ty::INT);
                true
            }
            "parse" => {
                let string = self.cx.tcx.string_ty();
                let ty = Ty::Primitive(primitive);
                let fail = self.fail_label();
                let (ok, value) = match primitive {
                    PrimitiveTy::Float | PrimitiveTy::Double => {
                        let out = self.alloca_ll("double");
                        let ok =
                            self.runtime("i1", "kr_parse_double", &format!("ptr %a0, ptr {out}"));
                        let value = self.assign(format!("load double, ptr {out}"));
                        let value = self.numeric(&value, PrimitiveTy::Double, primitive);
                        (ok, value)
                    }
                    _ => {
                        let (min, max) = match primitive {
                            PrimitiveTy::Byte => (i8::MIN as i64, i8::MAX as i64),
                            PrimitiveTy::Short => (i16::MIN as i64, i16::MAX as i64),
                            PrimitiveTy::Int => (i32::MIN as i64, i32::MAX as i64),
                            _ => (i64::MIN, i64::MAX),
                        };
                        let out = self.alloca_ll("i64");
                        let ok = self.runtime(
                            "i1",
                            "kr_parse_long",
                            &format!("ptr %a0, i64 {min}, i64 {max}, ptr {out}"),
                        );
                        let value = self.assign(format!("load i64, ptr {out}"));
                        let value = self.numeric(&value, PrimitiveTy::Long, primitive);
                        (ok, value)
                    }
                };
                let good = self.label("parsed");
                let bad = self.label("unparsed");
                self.line(format!("br i1 {ok}, label %{good}, label %{bad}"));
                self.start(&bad);
                let message = self.runtime("ptr", "kr_string_number_format", "ptr %a0");
                self.drop_value("%a0", &string);
                self.throw_with(LangItem::NumberFormatException, &message, &fail);
                self.line("unreachable");
                self.start(&good);
                self.drop_value("%a0", &string);
                self.ret(&value, &ty);
                true
            }
            _ if primitive == PrimitiveTy::Char => {
                let value = self.load(&Ty::CHAR, "%a0");
                let (function, ret) = match name {
                    "isDigit" => ("kr_char_is_digit", Ty::BOOLEAN),
                    "isLetter" => ("kr_char_is_letter", Ty::BOOLEAN),
                    "isWhitespace" => ("kr_char_is_whitespace", Ty::BOOLEAN),
                    "isUpperCase" => ("kr_char_is_upper", Ty::BOOLEAN),
                    "isLowerCase" => ("kr_char_is_lower", Ty::BOOLEAN),
                    "toUpperCase" => ("kr_char_to_upper", Ty::CHAR),
                    "toLowerCase" => ("kr_char_to_lower", Ty::CHAR),
                    "isLetterOrDigit" => {
                        let letter =
                            self.runtime("i1", "kr_char_is_letter", &format!("i32 {value}"));
                        let digit = self.runtime("i1", "kr_char_is_digit", &format!("i32 {value}"));
                        let either = self.assign(format!("or i1 {letter}, {digit}"));
                        self.ret(&either, &Ty::BOOLEAN);
                        return true;
                    }
                    _ => return false,
                };
                let ll = self.ll(&ret);
                let result = self.runtime(&ll, function, &format!("i32 {value}"));
                self.ret(&result, &ret);
                let _ = builtin;
                true
            }
            _ => false,
        }
    }

    fn throw_out_of_bounds(&mut self, failed: &str, index: &str, len: &str) {
        let fail = self.fail_label();
        let ok = self.label("inbounds");
        let bad = self.label("outofbounds");
        self.line(format!("br i1 {failed}, label %{bad}, label %{ok}"));
        self.start(&bad);
        let wide_index = self.assign(format!("sext i32 {index} to i64"));
        let wide_len = self.assign(format!("sext i32 {len} to i64"));
        let message = self.runtime(
            "ptr",
            "kr_string_bounds",
            &format!("i64 {wide_index}, i64 {wide_len}"),
        );
        self.throw_with(LangItem::IndexOutOfBoundsException, &message, &fail);
        self.line("unreachable");
        self.start(&ok);
    }

    fn runtime_call(
        &mut self,
        function: &'static str,
        ret_ll: &str,
        builtin: &Builtin,
        extra: &[String],
    ) {
        let mut args = Vec::new();
        for (index, param) in builtin.params.iter().enumerate() {
            let ll = self.ll(param);
            args.push(format!("{ll} %a{index}"));
        }
        args.extend(extra.iter().cloned());
        let result = self.runtime(ret_ll, function, &args.join(", "));
        for (index, param) in builtin.params.clone().iter().enumerate() {
            if self.cx.needs_drop(param) {
                self.drop_value(&format!("%a{index}"), param);
            }
        }
        if ret_ll == "void" {
            self.line("ret void");
        } else {
            let ret = self.ret_ty.clone();
            self.ret(&result, &ret);
        }
    }

    fn system_builtin(&mut self, name: &str, builtin: &Builtin) -> bool {
        match name {
            "exit" => {
                self.runtime("void", "kr_system_exit", "i32 %a0");
                self.line("unreachable");
            }
            "env" => self.runtime_call("kr_system_env", "ptr", builtin, &[]),
            "workingDirectory" => {
                self.runtime_call("kr_system_working_directory", "ptr", builtin, &[])
            }
            "currentTimeMillis" => self.runtime_call("kr_system_millis", "i64", builtin, &[]),
            "nanoTime" => self.runtime_call("kr_system_nanos", "i64", builtin, &[]),
            "currentTimeNanos" => {
                self.runtime_call("kr_system_epoch_nanos", "i64", builtin, &[])
            }
            "osName" => self.runtime_call("kr_system_os_name", "ptr", builtin, &[]),
            _ => return false,
        }
        true
    }

    fn files_builtin(&mut self, name: &str, builtin: &Builtin) -> bool {
        let (function, ret_ll) = match name {
            "readFile" => ("kr_io_read_file", "ptr"),
            "writeFile" => ("kr_io_write_file", "i1"),
            "exists" => ("kr_io_exists", "i1"),
            "isFile" => ("kr_io_is_file", "i1"),
            "isDirectory" => ("kr_io_is_directory", "i1"),
            "sizeOf" => ("kr_io_size", "i64"),
            "canonicalize" => ("kr_io_canonical_path", "ptr"),
            "remove" => ("kr_io_remove", "i1"),
            "makeDirectories" => ("kr_io_create_directories", "i1"),
            "makeDirectory" => ("kr_io_create_directory", "i1"),
            "isSymlink" => ("kr_io_is_symlink", "i1"),
            "modifiedRaw" => ("kr_io_modified", "i64"),
            "setModifiedRaw" => ("kr_io_set_modified", "i1"),
            "accessRaw" => ("kr_io_access", "i1"),
            "setPermissionRaw" => ("kr_io_set_permission", "i1"),
            "renameFile" => ("kr_io_rename", "i1"),
            "copyFile" => ("kr_io_copy", "i1"),
            "writeBytesRaw" => {
                let bytes = self.assign("load ptr, ptr %a1");
                let written = self.runtime(
                    "i1",
                    "kr_io_write_bytes",
                    &format!("ptr %a0, ptr {bytes}, i1 %a2"),
                );
                let string = self.cx.tcx.string_ty();
                self.drop_value("%a0", &string);
                let ret = self.ret_ty.clone();
                self.ret(&written, &ret);
                return true;
            }
            "readBytesRaw" => {
                let array = Ty::Array(Box::new(Ty::Primitive(PrimitiveTy::Byte)));
                let descriptor = self.cx.rt_global(RtKey::Array(array.clone()));
                self.cx.drop_array_fn(&array);
                self.runtime_call(
                    "kr_io_read_bytes",
                    "ptr",
                    builtin,
                    &[format!("ptr {descriptor}")],
                );
                return true;
            }
            "listDirectory" => {
                let array = Ty::Array(Box::new(self.cx.tcx.string_ty()));
                let descriptor = self.cx.rt_global(RtKey::Array(array.clone()));
                self.cx.drop_array_fn(&array);
                self.runtime_call("kr_io_list", "ptr", builtin, &[format!("ptr {descriptor}")]);
                return true;
            }
            _ => return false,
        };
        self.runtime_call(function, ret_ll, builtin, &[]);
        true
    }

    /// The private intrinsics of `std.process.Command`. The borrowed argument
    /// and environment arrays are passed to the runtime as the arrays.
    fn process_builtin(&mut self, name: &str, builtin: &Builtin) -> bool {
        match name {
            "runRaw" => {
                let argv = self.assign("load ptr, ptr %a0");
                let env = self.assign("load ptr, ptr %a2");
                let status = self.runtime(
                    "i32",
                    "kr_process_run",
                    &format!("ptr {argv}, ptr %a1, ptr {env}, i1 %a3"),
                );
                let directory = builtin.params[1].clone();
                self.drop_value("%a1", &directory);
                self.line(format!("ret i32 {status}"));
            }
            "capturedRaw" => {
                let text = self.runtime("ptr", "kr_process_captured", "i1 %a0");
                let ret = self.ret_ty.clone();
                self.ret(&text, &ret);
            }
            _ => return false,
        }
        true
    }

    fn file_builtin(&mut self, name: &str, builtin: &Builtin) -> bool {
        let ty = builtin.self_ty.clone();
        let string = self.cx.tcx.string_ty();
        let object = self.assign("load ptr, ptr %a0");
        let slot = self.native_addr(&object, &ty, 0);
        let handle = self.assign(format!("load ptr, ptr {slot}"));
        match name {
            "openRaw" => {
                let mode = match builtin.params.get(2) {
                    Some(_) => self.assign("select i1 %a2, i32 2, i32 1"),
                    None => "0".to_owned(),
                };
                let file = self.runtime("ptr", "kr_file_open", &format!("ptr %a1, i32 {mode}"));
                self.drop_value("%a1", &string);
                self.runtime("void", "kr_file_close", &format!("ptr {handle}"));
                self.line(format!("store ptr {file}, ptr {slot}"));
                let opened = self.assign(format!("icmp ne ptr {file}, null"));
                self.line(format!("ret i1 {opened}"));
            }
            "writeRaw" => {
                let written =
                    self.runtime("i1", "kr_file_write", &format!("ptr {handle}, ptr %a1"));
                self.drop_value("%a1", &string);
                self.line(format!("ret i1 {written}"));
            }
            "writeBytesRaw" => {
                let bytes = self.assign("load ptr, ptr %a1");
                let written = self.runtime(
                    "i1",
                    "kr_file_write_bytes",
                    &format!("ptr {handle}, ptr {bytes}"),
                );
                self.line(format!("ret i1 {written}"));
            }
            "readBytesRaw" => {
                let array = Ty::Array(Box::new(Ty::Primitive(PrimitiveTy::Byte)));
                let descriptor = self.cx.rt_global(RtKey::Array(array.clone()));
                self.cx.drop_array_fn(&array);
                let bytes = self.runtime(
                    "ptr",
                    "kr_file_read_bytes",
                    &format!("ptr {handle}, i32 %a1, ptr {descriptor}"),
                );
                let ret = self.ret_ty.clone();
                self.ret(&bytes, &ret);
            }
            "flushRaw" => {
                let flushed = self.runtime("i1", "kr_file_flush", &format!("ptr {handle}"));
                self.line(format!("ret i1 {flushed}"));
            }
            "readLineRaw" | "readAllRaw" => {
                let function = if name == "readLineRaw" {
                    "kr_file_read_line"
                } else {
                    "kr_file_read_all"
                };
                let text = self.runtime("ptr", function, &format!("ptr {handle}"));
                let ret = self.ret_ty.clone();
                self.ret(&text, &ret);
            }
            _ => return false,
        }
        true
    }

    /// The private `...Raw` intrinsics of `TcpListener`, `TcpStream`,
    /// `UdpSocket` and `Poller`. Each runtime function takes the address of
    /// the object's native slot, then the remaining arguments; a socket or
    /// poller argument is passed as its handle and a borrowed array as the
    /// array itself.
    fn net_builtin(&mut self, class: NetClass, name: &str, builtin: &Builtin) -> bool {
        let function = match (class, name) {
            (_, "localAddrRaw") => "kr_net_local_addr",
            (NetClass::Poller, "createRaw") => "kr_poller_create",
            (NetClass::Poller, "pollRaw") => "kr_poller_poll",
            (NetClass::Poller, "tokenRaw") => "kr_poller_token",
            (NetClass::Poller, "flagsRaw") => "kr_poller_flags",
            (NetClass::Poller, _) => return false,
            (_, "setTimeoutRaw") => "kr_net_set_timeout",
            (_, "setNonBlockingRaw") => "kr_net_set_nonblocking",
            (_, "registerRaw") => "kr_net_register",
            (_, "deregisterRaw") => "kr_net_deregister",
            (NetClass::Listener, "bindRaw") => "kr_tcp_listener_bind",
            (NetClass::Stream, "connectRaw") => "kr_tcp_stream_connect",
            (NetClass::Stream, "acceptRaw") => "kr_tcp_stream_accept",
            (NetClass::Stream, "tryAcceptRaw") => "kr_tcp_stream_try_accept",
            (NetClass::Stream, "startConnectRaw") => "kr_tcp_stream_start_connect",
            (NetClass::Stream, "finishConnectRaw") => "kr_tcp_stream_finish_connect",
            (NetClass::Stream, "tryReadLineRaw") => "kr_tcp_stream_try_read_line",
            (NetClass::Stream, "atEndRaw") => "kr_tcp_stream_at_end",
            (NetClass::Stream, "tryReadRaw") => "kr_tcp_stream_try_read",
            (NetClass::Stream, "tryWriteRaw") => "kr_tcp_stream_try_write",
            (NetClass::Stream, "queueRaw") => "kr_tcp_stream_queue_text",
            (NetClass::Stream, "queueBytesRaw") => "kr_tcp_stream_queue_bytes",
            (NetClass::Stream, "flushRaw") => "kr_tcp_stream_flush",
            (NetClass::Stream, "queuedRaw") => "kr_tcp_stream_queued",
            (NetClass::Stream, "peerAddrRaw") => "kr_tcp_stream_peer_addr",
            (NetClass::Stream, "readLineRaw") => "kr_tcp_stream_read_line",
            (NetClass::Stream, "readAllRaw") => "kr_tcp_stream_read_all",
            (NetClass::Stream, "readRaw") => "kr_tcp_stream_read",
            (NetClass::Stream, "writeRaw") => "kr_tcp_stream_write",
            (NetClass::Stream, "writeBytesRaw") => "kr_tcp_stream_write_bytes",
            (NetClass::Stream, "shutdownWriteRaw") => "kr_tcp_stream_shutdown_write",
            (NetClass::Stream, "setNoDelayRaw") => "kr_tcp_stream_set_no_delay",
            (NetClass::Udp, "bindRaw") => "kr_udp_bind",
            (NetClass::Udp, "sendRaw") => "kr_udp_send_to",
            (NetClass::Udp, "receiveRaw") => "kr_udp_receive",
            (NetClass::Udp, "trySendRaw") => "kr_udp_try_send_to",
            (NetClass::Udp, "tryReceiveRaw") => "kr_udp_try_receive",
            (NetClass::Udp, "lastSenderRaw") => "kr_udp_last_sender",
            _ => return false,
        };
        let ty = builtin.self_ty.clone();
        let object = self.assign("load ptr, ptr %a0");
        let slot = self.native_addr(&object, &ty, 0);
        let mut args = vec![format!("ptr {slot}")];
        let params = builtin.params.clone();
        for (index, param) in params.iter().enumerate().skip(1) {
            let value = format!("%a{index}");
            match param {
                Ty::Ref { ty: inner, .. } if self.cx.net_class_of(inner).is_some() => {
                    let other = self.assign(format!("load ptr, ptr {value}"));
                    let other_slot = self.native_addr(&other, inner, 0);
                    let handle = self.assign(format!("load ptr, ptr {other_slot}"));
                    args.push(format!("ptr {handle}"));
                }
                Ty::Ref { ty: inner, .. } if self.cx.is_ptr(inner) => {
                    let pointer = self.assign(format!("load ptr, ptr {value}"));
                    args.push(format!("ptr {pointer}"));
                }
                _ => {
                    let ll = self.ll(param);
                    args.push(format!("{ll} {value}"));
                }
            }
        }
        let ret = self.ret_ty.clone();
        if let Ty::Array(_) = ret.non_null() {
            let array = ret.non_null().clone();
            let descriptor = self.cx.rt_global(RtKey::Array(array.clone()));
            self.cx.drop_array_fn(&array);
            args.push(format!("ptr {descriptor}"));
        }
        let ret_ll = self.ll(&ret);
        let result = self.runtime(&ret_ll, function, &args.join(", "));
        for (index, param) in params.iter().enumerate().skip(1) {
            if self.cx.needs_drop(param) {
                self.drop_value(&format!("%a{index}"), param);
            }
        }
        if ret_ll == "void" {
            self.line("ret void");
        } else {
            self.ret(&result, &ret);
        }
        true
    }

    fn builder_builtin(&mut self, name: &str, builtin: &Builtin) -> bool {
        let ty = builtin.self_ty.clone();
        let string = self.cx.tcx.string_ty();
        let object = self.assign("load ptr, ptr %a0");
        let native = self.native_addr(&object, &ty, 0);
        match name {
            "append" => {
                self.runtime(
                    "void",
                    "kr_builder_append",
                    &format!("ptr {native}, ptr %a1"),
                );
                self.drop_value("%a1", &string);
                self.line("ret void");
            }
            "insert" => {
                let inserted = self.runtime(
                    "i1",
                    "kr_builder_insert",
                    &format!("ptr {native}, i32 %a1, ptr %a2"),
                );
                self.drop_value("%a2", &string);
                let failed = self.assign(format!("xor i1 {inserted}, true"));
                let len = self.runtime("i32", "kr_builder_length", &format!("ptr {native}"));
                self.throw_out_of_bounds(&failed, "%a1", &len);
                self.line("ret void");
            }
            "truncate" => {
                let len = self.runtime("i32", "kr_builder_length", &format!("ptr {native}"));
                let done = self.runtime(
                    "i1",
                    "kr_builder_truncate",
                    &format!("ptr {native}, i32 %a1"),
                );
                let failed = self.assign(format!("xor i1 {done}, true"));
                self.throw_out_of_bounds(&failed, "%a1", &len);
                self.line("ret void");
            }
            "reverse" | "clear" => {
                let function = if name == "reverse" {
                    "kr_builder_reverse"
                } else {
                    "kr_builder_clear"
                };
                self.runtime("void", function, &format!("ptr {native}"));
                self.line("ret void");
            }
            "length" => {
                let len = self.runtime("i32", "kr_builder_length", &format!("ptr {native}"));
                self.line(format!("ret i32 {len}"));
            }
            "toString" => {
                let text = self.runtime("ptr", "kr_builder_to_string", &format!("ptr {native}"));
                self.ret(&text, &string);
            }
            _ => return false,
        }
        true
    }

    fn format_builtin(&mut self, name: &str) -> bool {
        let string = self.cx.tcx.string_ty();
        let (function, value) = match name {
            "formatLong" => ("kr_format_long", "i64 %a0"),
            "formatDouble" => ("kr_format_double", "double %a0"),
            "formatText" => ("kr_format_text", "ptr %a0"),
            _ => return false,
        };
        let text = self.runtime("ptr", function, &format!("{value}, ptr %a1"));
        if name == "formatText" {
            self.drop_value("%a0", &string);
        }
        self.drop_value("%a1", &string);
        let ret = self.ret_ty.clone();
        self.ret(&text, &ret);
        true
    }

    fn bridge_builtin(&mut self, name: &str) -> bool {
        let string = self.cx.tcx.string_ty();
        match name {
            "open" => {
                self.runtime("void", "kr_bridge_open", "");
                self.line("ret void");
            }
            "receive" => {
                let line = self.runtime("ptr", "kr_bridge_receive", "");
                let ret = self.ret_ty.clone();
                self.ret(&line, &ret);
            }
            "send" => {
                self.runtime("void", "kr_bridge_send", "ptr %a0");
                self.drop_value("%a0", &string);
                self.line("ret void");
            }
            "escape" | "unescape" => {
                let function = if name == "escape" {
                    "kr_bridge_escape"
                } else {
                    "kr_bridge_unescape"
                };
                let text = self.runtime("ptr", function, "ptr %a0");
                self.drop_value("%a0", &string);
                self.ret(&text, &string);
            }
            _ => return false,
        }
        true
    }

    fn task_builtin(&mut self, name: &str, builtin: &Builtin) -> bool {
        let ty = builtin.self_ty.clone();
        let object = self.assign("load ptr, ptr %a0");
        let handle_addr = self.native_addr(&object, &ty, 0);
        let previous = self.assign(format!("load ptr, ptr {handle_addr}"));
        self.runtime("void", "kr_thread_join", &format!("ptr {previous}"));
        match name {
            "start" => {
                let self_addr = self.native_addr(&object, &ty, 1);
                self.line(format!("store ptr {object}, ptr {self_addr}"));
                let entry = self
                    .cx
                    .instance(Instance::Thunk(Thunk::ThreadEntry { runnable: ty }));
                let entry = self.cx.fn_name(entry);
                let handle = self.runtime(
                    "ptr",
                    "kr_thread_spawn",
                    &format!("ptr {entry}, ptr {self_addr}"),
                );
                self.line(format!("store ptr {handle}, ptr {handle_addr}"));
            }
            "joinRaw" => self.line(format!("store ptr null, ptr {handle_addr}")),
            _ => return false,
        }
        self.line("ret void");
        true
    }

    fn thread_builtin(&mut self, name: &str, builtin: &Builtin) -> bool {
        match name {
            "sleep" => {
                self.runtime("void", "kr_thread_sleep", "i64 %a0");
                self.line("ret void");
                true
            }
            "currentId" => {
                let id = self.runtime("i64", "kr_thread_current_id", "");
                self.line(format!("ret i64 {id}"));
                true
            }
            "start" | "join" => {
                let ty = builtin.self_ty.clone();
                let object = self.assign("load ptr, ptr %a0");
                let handle_addr = self.native_addr(&object, &ty, 0);
                if name == "start" {
                    let Ty::Adt { def, args, .. } = &ty else {
                        return false;
                    };
                    let task = krelpin_span::Symbol::intern("task");
                    let index = self.cx.field_index(&ty, *def, task);
                    let runnable = self.cx.field_ty(*def, args, task);
                    let object_ll = self.cx.object_type(&ty);
                    let task_addr = self.assign(format!(
                        "getelementptr inbounds {object_ll}, ptr {object}, i32 0, i32 {index}"
                    ));
                    let entry = self
                        .cx
                        .instance(Instance::Thunk(Thunk::ThreadEntry { runnable }));
                    let entry = self.cx.fn_name(entry);
                    let previous = self.assign(format!("load ptr, ptr {handle_addr}"));
                    self.runtime("void", "kr_thread_join", &format!("ptr {previous}"));
                    let handle = self.runtime(
                        "ptr",
                        "kr_thread_spawn",
                        &format!("ptr {entry}, ptr {task_addr}"),
                    );
                    self.line(format!("store ptr {handle}, ptr {handle_addr}"));
                } else {
                    let handle = self.assign(format!("load ptr, ptr {handle_addr}"));
                    self.runtime("void", "kr_thread_join", &format!("ptr {handle}"));
                    self.line(format!("store ptr null, ptr {handle_addr}"));
                }
                self.line("ret void");
                true
            }
            _ => false,
        }
    }

    fn atomic_builtin(&mut self, owner: DefId, name: &str, builtin: &Builtin) -> bool {
        let ty = builtin.self_ty.clone();
        let value_name = krelpin_span::Symbol::intern("value");
        let value_ty = self.cx.field_ty(owner, &[], value_name);
        let object = self.assign("load ptr, ptr %a0");
        let object_ll = self.cx.object_type(&ty);
        let index = self.cx.field_index(&ty, owner, value_name);
        let address = self.assign(format!(
            "getelementptr inbounds {object_ll}, ptr {object}, i32 0, i32 {index}"
        ));
        let boolean = value_ty == Ty::BOOLEAN;
        let ll = if boolean {
            "i8".to_owned()
        } else {
            self.ll(&value_ty)
        };
        let widen = |fx: &mut Self, value: &str| -> String {
            if boolean {
                fx.assign(format!("zext i1 {value} to i8"))
            } else {
                value.to_owned()
            }
        };
        let narrow = |fx: &mut Self, value: &str| -> String {
            if boolean {
                fx.assign(format!("trunc i8 {value} to i1"))
            } else {
                value.to_owned()
            }
        };
        match name {
            "get" => {
                let value =
                    self.assign(format!("load atomic {ll}, ptr {address} seq_cst, align 8"));
                let value = narrow(self, &value);
                self.ret(&value, &value_ty);
            }
            "set" => {
                let value = widen(self, &builtin.arg(0));
                self.line(format!(
                    "store atomic {ll} {value}, ptr {address} seq_cst, align 8"
                ));
                self.line("ret void");
            }
            "compareAndSet" => {
                let expected = widen(self, &builtin.arg(0));
                let value = widen(self, &builtin.arg(1));
                let pair = self.assign(format!(
                    "cmpxchg ptr {address}, {ll} {expected}, {ll} {value} seq_cst seq_cst"
                ));
                let swapped = self.assign(format!("extractvalue {{ {ll}, i1 }} {pair}, 1"));
                self.ret(&swapped, &Ty::BOOLEAN);
            }
            "increment" | "decrement" | "addAndGet" => {
                let delta = match name {
                    "increment" => "1".to_owned(),
                    "decrement" => "-1".to_owned(),
                    _ => builtin.arg(0),
                };
                let old = self.assign(format!("atomicrmw add ptr {address}, {ll} {delta} seq_cst"));
                let new = self.assign(format!("add {ll} {old}, {delta}"));
                self.ret(&new, &value_ty);
            }
            _ => return false,
        }
        true
    }

    fn mutex_builtin(&mut self, owner: DefId, name: &str, builtin: &Builtin) -> bool {
        let ty = builtin.self_ty.clone();
        let items = &self.cx.tcx.lang_items;
        if items.is(owner, LangItem::Mutex) && name == "lock" {
            let object = self.assign("load ptr, ptr %a0");
            let handle = self.native_addr(&object, &ty, 0);
            let handle = self.assign(format!("load ptr, ptr {handle}"));
            self.runtime("void", "kr_mutex_lock", &format!("ptr {handle}"));
            let guard_ty = self.ret_ty.clone();
            let guard = self.new_object(&guard_ty, None);
            let slot = self.native_addr(&guard, &guard_ty, 0);
            self.line(format!("store ptr {object}, ptr {slot}"));
            self.ret(&guard, &guard_ty);
            return true;
        }
        if items.is(owner, LangItem::Mutex) && matches!(name, "notify" | "notifyAll") {
            let object = self.assign("load ptr, ptr %a0");
            let handle = self.native_addr(&object, &ty, 0);
            let handle = self.assign(format!("load ptr, ptr {handle}"));
            let function = if name == "notify" {
                "kr_mutex_notify"
            } else {
                "kr_mutex_notify_all"
            };
            self.runtime("void", function, &format!("ptr {handle}"));
            self.line("ret void");
            return true;
        }
        if items.is(owner, LangItem::MutexGuard) && name == "wait" {
            let Ty::Adt { args, .. } = &ty else {
                return false;
            };
            let guard = self.assign("load ptr, ptr %a0");
            let mutex = self.native_addr(&guard, &ty, 0);
            let mutex = self.assign(format!("load ptr, ptr {mutex}"));
            let mutex_def = self.cx.lang(LangItem::Mutex);
            let mutex_ty = Ty::Adt {
                def: mutex_def,
                name: self.cx.tcx.ty_name(mutex_def),
                args: args.clone(),
            };
            let handle = self.native_addr(&mutex, &mutex_ty, 0);
            let handle = self.assign(format!("load ptr, ptr {handle}"));
            if builtin.params.len() == 1 {
                self.runtime("void", "kr_mutex_wait", &format!("ptr {handle}"));
                self.line("ret void");
            } else {
                let millis = builtin.arg(0);
                let woken = self.runtime(
                    "i1",
                    "kr_mutex_wait_millis",
                    &format!("ptr {handle}, i64 {millis}"),
                );
                self.line(format!("ret i1 {woken}"));
            }
            return true;
        }
        if items.is(owner, LangItem::MutexGuard) && matches!(name, "get" | "getMut") {
            let Ty::Adt { args, .. } = &ty else {
                return false;
            };
            let guard = self.assign("load ptr, ptr %a0");
            let mutex = self.native_addr(&guard, &ty, 0);
            let mutex = self.assign(format!("load ptr, ptr {mutex}"));
            let mutex_def = self.cx.lang(LangItem::Mutex);
            let mutex_ty = Ty::Adt {
                def: mutex_def,
                name: self.cx.tcx.ty_name(mutex_def),
                args: args.clone(),
            };
            let value = krelpin_span::Symbol::intern("value");
            let index = self.cx.field_index(&mutex_ty, mutex_def, value);
            let object_ll = self.cx.object_type(&mutex_ty);
            let address = self.assign(format!(
                "getelementptr inbounds {object_ll}, ptr {mutex}, i32 0, i32 {index}"
            ));
            self.line(format!("ret ptr {address}"));
            return true;
        }
        false
    }

    fn rwlock_builtin(&mut self, owner: DefId, name: &str, builtin: &Builtin) -> bool {
        let ty = builtin.self_ty.clone();
        let items = &self.cx.tcx.lang_items;
        if items.is(owner, LangItem::ReadWriteLock) && matches!(name, "read" | "write") {
            let object = self.assign("load ptr, ptr %a0");
            let handle = self.native_addr(&object, &ty, 0);
            let handle = self.assign(format!("load ptr, ptr {handle}"));
            let function = if name == "read" {
                "kr_rwlock_read"
            } else {
                "kr_rwlock_write"
            };
            self.runtime("void", function, &format!("ptr {handle}"));
            let guard_ty = self.ret_ty.clone();
            let guard = self.new_object(&guard_ty, None);
            let slot = self.native_addr(&guard, &guard_ty, 0);
            self.line(format!("store ptr {object}, ptr {slot}"));
            self.ret(&guard, &guard_ty);
            return true;
        }
        let is_guard =
            items.is(owner, LangItem::ReadGuard) || items.is(owner, LangItem::WriteGuard);
        if is_guard && matches!(name, "get" | "getMut") {
            let Ty::Adt { args, .. } = &ty else {
                return false;
            };
            let guard = self.assign("load ptr, ptr %a0");
            let lock = self.native_addr(&guard, &ty, 0);
            let lock = self.assign(format!("load ptr, ptr {lock}"));
            let lock_def = self.cx.lang(LangItem::ReadWriteLock);
            let lock_ty = Ty::Adt {
                def: lock_def,
                name: self.cx.tcx.ty_name(lock_def),
                args: args.clone(),
            };
            let value = krelpin_span::Symbol::intern("value");
            let index = self.cx.field_index(&lock_ty, lock_def, value);
            let object_ll = self.cx.object_type(&lock_ty);
            let address = self.assign(format!(
                "getelementptr inbounds {object_ll}, ptr {lock}, i32 0, i32 {index}"
            ));
            self.line(format!("ret ptr {address}"));
            return true;
        }
        false
    }

    fn list_builtin(&mut self, name: &str, builtin: &Builtin) -> bool {
        let ty = builtin.self_ty.clone();
        let Ty::Adt { args, .. } = &ty else {
            return false;
        };
        let elem = args[0].clone();
        let elem_ll = self.cx.mem_llty(&elem);
        let (elem_size, _) = self.cx.size_align(&elem);
        let object = self.assign("load ptr, ptr %a0");
        let data_addr = self.native_addr(&object, &ty, 0);
        let len_addr = self.native_addr(&object, &ty, 1);
        let cap_addr = self.native_addr(&object, &ty, 2);
        let len = self.assign(format!("load i64, ptr {len_addr}"));
        let fail = self.fail_label();
        let check_index = |fx: &mut Self, index: &str, inclusive: bool| -> String {
            let wide = fx.assign(format!("sext i32 {index} to i64"));
            let op = if inclusive { "ule" } else { "ult" };
            let inside = fx.assign(format!("icmp {op} i64 {wide}, {len}"));
            let ok = fx.label("inbounds");
            let bad = fx.label("outofbounds");
            fx.line(format!("br i1 {inside}, label %{ok}, label %{bad}"));
            fx.start(&bad);
            let message = fx.runtime("ptr", "kr_string_bounds", &format!("i64 {wide}, i64 {len}"));
            fx.throw_with(LangItem::IndexOutOfBoundsException, &message, &fail);
            fx.line("unreachable");
            fx.start(&ok);
            wide
        };
        let grow = |fx: &mut Self| {
            let cap = fx.assign(format!("load i64, ptr {cap_addr}"));
            let full = fx.assign(format!("icmp eq i64 {len}, {cap}"));
            let more = fx.label("grow");
            let room = fx.label("room");
            fx.line(format!("br i1 {full}, label %{more}, label %{room}"));
            fx.start(&more);
            let doubled = fx.assign(format!("mul i64 {cap}, 2"));
            let small = fx.assign(format!("icmp slt i64 {doubled}, 4"));
            let new_cap = fx.assign(format!("select i1 {small}, i64 4, i64 {doubled}"));
            let bytes = fx.assign(format!("mul i64 {new_cap}, {elem_size}"));
            let data = fx.assign(format!("load ptr, ptr {data_addr}"));
            let grown = fx.runtime("ptr", "kr_realloc", &format!("ptr {data}, i64 {bytes}"));
            fx.line(format!("store ptr {grown}, ptr {data_addr}"));
            fx.line(format!("store i64 {new_cap}, ptr {cap_addr}"));
            fx.line(format!("br label %{room}"));
            fx.start(&room);
        };
        let slot = |fx: &mut Self, index: &str| -> String {
            let data = fx.assign(format!("load ptr, ptr {data_addr}"));
            fx.assign(format!(
                "getelementptr inbounds {elem_ll}, ptr {data}, i64 {index}"
            ))
        };
        let shift = |fx: &mut Self, from: &str, to: &str, count: &str| {
            let source = slot(fx, from);
            let target = slot(fx, to);
            let bytes = fx.assign(format!("mul i64 {count}, {elem_size}"));
            fx.cx.declare_dynamic(
                "llvm.memmove.p0.p0.i64",
                "declare void @llvm.memmove.p0.p0.i64(ptr, ptr, i64, i1)",
            );
            fx.line(format!(
                "call void @llvm.memmove.p0.p0.i64(ptr {target}, ptr {source}, i64 {bytes}, i1 0)"
            ));
        };
        match name {
            "size" => {
                let value = self.assign(format!("trunc i64 {len} to i32"));
                self.ret(&value, &Ty::INT);
            }
            "get" | "getMut" => {
                let index = check_index(self, &builtin.arg(0), false);
                let address = slot(self, &index);
                self.line(format!("ret ptr {address}"));
            }
            "set" => {
                let index = check_index(self, &builtin.arg(0), false);
                let address = slot(self, &index);
                let old = self.load(&elem, &address);
                let value = self.convert(&builtin.arg(1), &builtin.arg_ty(1), &elem);
                self.store(&elem, &value, &address);
                self.ret(&old, &elem);
            }
            "add" if builtin.params.len() == 2 => {
                grow(self);
                let address = slot(self, &len);
                let value = self.convert(&builtin.arg(0), &builtin.arg_ty(0), &elem);
                self.store(&elem, &value, &address);
                let next = self.assign(format!("add i64 {len}, 1"));
                self.line(format!("store i64 {next}, ptr {len_addr}"));
                self.line("ret void");
            }
            "add" => {
                let index = check_index(self, &builtin.arg(0), true);
                grow(self);
                let after = self.assign(format!("add i64 {index}, 1"));
                let count = self.assign(format!("sub i64 {len}, {index}"));
                shift(self, &index, &after, &count);
                let address = slot(self, &index);
                let value = self.convert(&builtin.arg(1), &builtin.arg_ty(1), &elem);
                self.store(&elem, &value, &address);
                let next = self.assign(format!("add i64 {len}, 1"));
                self.line(format!("store i64 {next}, ptr {len_addr}"));
                self.line("ret void");
            }
            "remove" => {
                let index = check_index(self, &builtin.arg(0), false);
                let address = slot(self, &index);
                let old = self.load(&elem, &address);
                let after = self.assign(format!("add i64 {index}, 1"));
                let last = self.assign(format!("sub i64 {len}, 1"));
                let count = self.assign(format!("sub i64 {last}, {index}"));
                shift(self, &after, &index, &count);
                self.line(format!("store i64 {last}, ptr {len_addr}"));
                self.ret(&old, &elem);
            }
            "swap" => {
                let first = check_index(self, &builtin.arg(0), false);
                let second = check_index(self, &builtin.arg(1), false);
                let first_addr = slot(self, &first);
                let second_addr = slot(self, &second);
                let first_value = self.load(&elem, &first_addr);
                let second_value = self.load(&elem, &second_addr);
                self.store(&elem, &second_value, &first_addr);
                self.store(&elem, &first_value, &second_addr);
                self.line("ret void");
            }
            "clear" => {
                self.drop_list_elements(&object, &ty, &elem);
                self.line("ret void");
            }
            "indexOf" => {
                let counter = self.alloca_ll("i64");
                let head = self.label("search");
                let body = self.label("compare");
                let found = self.label("found");
                let next = self.label("next");
                let missing = self.label("missing");
                self.line(format!("br label %{head}"));
                self.start(&head);
                let index = self.assign(format!("load i64, ptr {counter}"));
                let more = self.assign(format!("icmp slt i64 {index}, {len}"));
                self.line(format!("br i1 {more}, label %{body}, label %{missing}"));
                self.start(&body);
                let address = slot(self, &index);
                let target = builtin.arg(0);
                let equal = self.call_equals(&address, &target, &elem);
                self.line(format!("br i1 {equal}, label %{found}, label %{next}"));
                self.start(&next);
                let following = self.assign(format!("add i64 {index}, 1"));
                self.line(format!("store i64 {following}, ptr {counter}"));
                self.line(format!("br label %{head}"));
                self.start(&found);
                let narrow = self.assign(format!("trunc i64 {index} to i32"));
                self.line(format!("ret i32 {narrow}"));
                self.start(&missing);
                self.line("ret i32 -1");
            }
            _ => return false,
        }
        true
    }

    fn table_builtin(&mut self, owner: DefId, name: &str, builtin: &Builtin) -> bool {
        let ty = builtin.self_ty.clone();
        let Ty::Adt { args, .. } = &ty else {
            return false;
        };
        let is_map = self.cx.tcx.lang_items.is_map_table(owner);
        let key = args[0].clone();
        let value = if is_map { args[1].clone() } else { Ty::Void };
        let shape = self.cx.table_shape(&key, &value);
        let entry_ll = self.cx.entry_type(&key, &value);
        let object = self.assign("load ptr, ptr %a0");
        let table = self.native_addr(&object, &ty, 0);
        let ret = self.ret_ty.clone();
        match name {
            "size" => {
                let live = self.native_addr(&object, &ty, 3);
                let live = self.assign(format!("load i64, ptr {live}"));
                let value = self.assign(format!("trunc i64 {live} to i32"));
                self.ret(&value, &Ty::INT);
            }
            "get" | "getMut" | "containsKey" | "contains" => {
                let entry = self.runtime(
                    "ptr",
                    "kr_table_find",
                    &format!("ptr {table}, ptr {shape}, ptr %a1"),
                );
                if matches!(name, "get" | "getMut") {
                    let is_null = self.assign(format!("icmp eq ptr {entry}, null"));
                    let address = self.assign(format!(
                        "getelementptr inbounds {entry_ll}, ptr {entry}, i32 0, i32 3"
                    ));
                    let result =
                        self.assign(format!("select i1 {is_null}, ptr null, ptr {address}"));
                    self.line(format!("ret ptr {result}"));
                } else {
                    let found = self.assign(format!("icmp ne ptr {entry}, null"));
                    self.ret(&found, &Ty::BOOLEAN);
                }
            }
            "put" | "add" => {
                let temp = self.alloca_ll(&entry_ll);
                let key_addr = self.assign(format!(
                    "getelementptr inbounds {entry_ll}, ptr {temp}, i32 0, i32 2"
                ));
                let key_value = self.convert("%a1", &builtin.params[1].clone(), &key);
                self.store(&key, &key_value, &key_addr);
                if is_map {
                    let value_addr = self.assign(format!(
                        "getelementptr inbounds {entry_ll}, ptr {temp}, i32 0, i32 3"
                    ));
                    let stored = self.convert("%a2", &builtin.params[2].clone(), &value);
                    self.store(&value, &stored, &value_addr);
                }
                let existed = self.alloca_ll("i1");
                self.runtime(
                    "ptr",
                    "kr_table_insert",
                    &format!("ptr {table}, ptr {shape}, ptr {temp}, ptr {existed}"),
                );
                let existed = self.assign(format!("load i1, ptr {existed}"));
                let fail = self.fail_label();
                let pending = self.assign("load ptr, ptr @kr_pending");
                let failed = self.assign(format!("icmp ne ptr {pending}, null"));
                let fine = self.label("inserted");
                let undo = self.label("undo");
                self.line(format!("br i1 {failed}, label %{undo}, label %{fine}"));
                self.start(&undo);
                self.drop_at(&key, &key_addr);
                if is_map {
                    let value_addr = self.assign(format!(
                        "getelementptr inbounds {entry_ll}, ptr {temp}, i32 0, i32 3"
                    ));
                    self.drop_at(&value, &value_addr);
                }
                self.line(format!("br label %{fail}"));
                self.start(&fine);
                let replaced = self.label("replaced");
                let fresh = self.label("fresh");
                self.line(format!(
                    "br i1 {existed}, label %{replaced}, label %{fresh}"
                ));
                self.start(&replaced);
                self.drop_at(&key, &key_addr);
                if is_map {
                    let value_addr = self.assign(format!(
                        "getelementptr inbounds {entry_ll}, ptr {temp}, i32 0, i32 3"
                    ));
                    let old = self.load(&value, &value_addr);
                    self.zero(&value, &value_addr);
                    self.ret(&old, &value);
                } else {
                    self.ret("false", &Ty::BOOLEAN);
                }
                self.start(&fresh);
                self.zero(&key, &key_addr);
                if is_map {
                    let none = self.cx.null_value(&ret);
                    let ll = self.ll(&ret);
                    self.line(format!("ret {ll} {none}"));
                } else {
                    self.ret("true", &Ty::BOOLEAN);
                }
            }
            "remove" => {
                let temp = self.alloca_ll(&entry_ll);
                let removed = self.runtime(
                    "i1",
                    "kr_table_remove",
                    &format!("ptr {table}, ptr {shape}, ptr %a1, ptr {temp}"),
                );
                let gone = self.label("removed");
                let kept = self.label("absent");
                self.line(format!("br i1 {removed}, label %{gone}, label %{kept}"));
                self.start(&gone);
                let key_addr = self.assign(format!(
                    "getelementptr inbounds {entry_ll}, ptr {temp}, i32 0, i32 2"
                ));
                self.drop_at(&key, &key_addr);
                if is_map {
                    let value_addr = self.assign(format!(
                        "getelementptr inbounds {entry_ll}, ptr {temp}, i32 0, i32 3"
                    ));
                    let old = self.load(&value, &value_addr);
                    self.zero(&value, &value_addr);
                    self.ret(&old, &value);
                } else {
                    self.ret("true", &Ty::BOOLEAN);
                }
                self.start(&kept);
                let none = self.cx.null_value(&ret);
                let ll = self.ll(&ret);
                self.line(format!("ret {ll} {none}"));
            }
            "clear" => {
                self.runtime(
                    "void",
                    "kr_table_clear",
                    &format!("ptr {table}, ptr {shape}"),
                );
                self.line("ret void");
            }
            "slotCount" => {
                let count = self.runtime("i64", "kr_table_slot_count", &format!("ptr {table}"));
                let count = self.assign(format!("trunc i64 {count} to i32"));
                self.ret(&count, &Ty::INT);
            }
            "slotAt" => {
                let index = self.assign("sext i32 %a1 to i64");
                let entry = self.runtime(
                    "ptr",
                    "kr_table_slot",
                    &format!("ptr {table}, ptr {shape}, i64 {index}"),
                );
                let is_null = self.assign(format!("icmp eq ptr {entry}, null"));
                let address = self.assign(format!(
                    "getelementptr inbounds {entry_ll}, ptr {entry}, i32 0, i32 2"
                ));
                let result = self.assign(format!("select i1 {is_null}, ptr null, ptr {address}"));
                self.line(format!("ret ptr {result}"));
            }
            "keySet" | "values" => {
                let projected = if name == "keySet" {
                    key.clone()
                } else {
                    value.clone()
                };
                let reference = Ty::Ref {
                    mutable: false,
                    ty: Box::new(projected.clone()),
                };
                let item = if name != "keySet" {
                    LangItem::ArrayList
                } else if self.cx.tcx.lang_items.is(owner, LangItem::LinkedHashMap) {
                    LangItem::LinkedHashSet
                } else {
                    LangItem::HashSet
                };
                let collection_def = self.cx.lang(item);
                let collection_ty = Ty::Adt {
                    def: collection_def,
                    name: self.cx.tcx.ty_name(collection_def),
                    args: vec![reference.clone()],
                };
                let collection = self.new_object(&collection_ty, None);
                let count = self.runtime("i64", "kr_table_slot_count", &format!("ptr {table}"));
                let counter = self.alloca_ll("i64");
                let head = self.label("walk");
                let body = self.label("visit");
                let live = self.label("live");
                let next = self.label("advance");
                let done = self.label("walked");
                self.line(format!("br label %{head}"));
                self.start(&head);
                let index = self.assign(format!("load i64, ptr {counter}"));
                let more = self.assign(format!("icmp slt i64 {index}, {count}"));
                self.line(format!("br i1 {more}, label %{body}, label %{done}"));
                self.start(&body);
                let entry = self.runtime(
                    "ptr",
                    "kr_table_slot",
                    &format!("ptr {table}, ptr {shape}, i64 {index}"),
                );
                let present = self.assign(format!("icmp ne ptr {entry}, null"));
                self.line(format!("br i1 {present}, label %{live}, label %{next}"));
                self.start(&live);
                let field = if name == "keySet" { 2 } else { 3 };
                let address = self.assign(format!(
                    "getelementptr inbounds {entry_ll}, ptr {entry}, i32 0, i32 {field}"
                ));
                let slot = self.alloca_ll("ptr");
                self.line(format!("store ptr {collection}, ptr {slot}"));
                let add = self.collection_add(&collection_ty, "add");
                let name_fn = self.cx.fn_name(add);
                if name == "keySet" {
                    self.line(format!("call i1 {name_fn}(ptr {slot}, ptr {address})"));
                } else {
                    self.line(format!("call void {name_fn}(ptr {slot}, ptr {address})"));
                }
                self.line(format!("br label %{next}"));
                self.start(&next);
                let following = self.assign(format!("add i64 {index}, 1"));
                self.line(format!("store i64 {following}, ptr {counter}"));
                self.line(format!("br label %{head}"));
                self.start(&done);
                self.ret(&collection, &collection_ty);
            }
            _ => return false,
        }
        true
    }

    fn collection_add(&mut self, collection: &Ty, name: &str) -> usize {
        let Ty::Adt { def, .. } = collection else {
            panic!("`{collection}` is not a collection");
        };
        let method = self
            .cx
            .tcx
            .sig(*def)
            .methods
            .get(&krelpin_span::Symbol::intern(name))
            .and_then(|methods| methods.iter().find(|method| method.params.len() == 1))
            .cloned()
            .unwrap_or_else(|| panic!("`{collection}` declares `{name}`"));
        let subst = match collection {
            Ty::Adt { def, args, .. } => self.cx.tcx.subst_for(*def, args),
            _ => Default::default(),
        };
        let instance = self.cx.instance_for(&method, &subst, collection);
        self.cx.instance(instance)
    }
}
