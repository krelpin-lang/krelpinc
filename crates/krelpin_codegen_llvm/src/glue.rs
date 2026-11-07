use krelpin_ast::ast::ReceiverKind;
use krelpin_typeck::{LangItem, Subst, Ty};

use crate::cx::Cx;
use crate::func::{FnCx, array_ll, define};
use crate::instance::{Instance, Selector, Thunk};
use crate::layout::{PtrKind, Shape, field_offsets, struct_layout};

impl Cx<'_, '_> {
    pub(crate) fn drop_glue(&mut self, ty: &Ty) -> String {
        match self.shape(ty) {
            Shape::Ptr(PtrKind::String) => {
                self.declare("kr_string_release", "declare void @kr_string_release(ptr)");
                return "@kr_string_release".to_owned();
            }
            Shape::Ptr(_) => {
                self.declare("kr_drop_object", "declare void @kr_drop_object(ptr)");
                return "@kr_drop_object".to_owned();
            }
            _ => {}
        }
        if let Some(name) = self.glue.get(&('d', ty.clone())) {
            return name.clone();
        }
        let name = format!("@\"drop.{}\"", self.type_key(ty));
        self.glue.insert(('d', ty.clone()), name.clone());
        let llty = self.llty(ty);
        let mut fx = FnCx::new(self, Subst::new(), Ty::Void);
        fx.start("entry");
        fx.drop_parts("%v", ty);
        fx.line("ret void");
        let body = fx.out;
        let allocas = fx.allocas;
        self.functions.push(define(
            "void",
            &name,
            &format!("{llty} %v"),
            &allocas,
            &body,
        ));
        name
    }

    pub(crate) fn copy_glue(&mut self, ty: &Ty) -> String {
        if let Some(name) = self.glue.get(&('c', ty.clone())) {
            return name.clone();
        }
        let name = format!("@\"copy.{}\"", self.type_key(ty));
        self.glue.insert(('c', ty.clone()), name.clone());
        let llty = self.llty(ty);
        let mut fx = FnCx::new(self, Subst::new(), ty.clone());
        fx.start("entry");
        fx.copy_parts("%v", ty);
        fx.line(format!("ret {llty} %v"));
        let body = fx.out;
        let allocas = fx.allocas;
        self.functions
            .push(define(&llty, &name, &format!("{llty} %v"), &allocas, &body));
        name
    }

    pub(crate) fn ensure_drop_object(&mut self, ty: &Ty) -> String {
        if let Some(name) = self.glue.get(&('o', ty.clone())) {
            return name.clone();
        }
        let name = format!("@\"dropobj.{}\"", self.type_key(ty));
        self.glue.insert(('o', ty.clone()), name.clone());
        let id = self.instance(Instance::Thunk(Thunk::DropObject(ty.clone())));
        let target = self.fn_name(id);
        self.glue.insert(('o', ty.clone()), target.clone());
        let _ = name;
        target
    }

    pub(crate) fn drop_object_fn(&mut self, ty: &Ty) -> String {
        self.ensure_drop_object(ty)
    }

    pub(crate) fn ensure_drop_box(&mut self, ty: &Ty) -> String {
        if let Some(name) = self.glue.get(&('b', ty.clone())) {
            return name.clone();
        }
        let name = format!("@\"dropbox.{}\"", self.type_key(ty));
        self.glue.insert(('b', ty.clone()), name.clone());
        let box_ty = self.box_type(ty);
        let mut fx = FnCx::new(self, Subst::new(), Ty::Void);
        fx.start("entry");
        let payload = fx.assign(format!(
            "getelementptr inbounds {box_ty}, ptr %v, i32 0, i32 1"
        ));
        fx.drop_at(ty, &payload);
        fx.runtime("void", "kr_free", "ptr %v");
        fx.line("ret void");
        let body = fx.out;
        let allocas = fx.allocas;
        self.functions
            .push(define("void", &name, "ptr %v", &allocas, &body));
        name
    }

    pub(crate) fn drop_box_fn(&mut self, ty: &Ty) -> String {
        self.ensure_drop_box(ty)
    }

    pub(crate) fn drop_array_fn(&mut self, array: &Ty) -> String {
        if let Some(name) = self.glue.get(&('a', array.clone())) {
            return name.clone();
        }
        let name = format!("@\"droparray.{}\"", self.type_key(array));
        self.glue.insert(('a', array.clone()), name.clone());
        let Ty::Array(elem) = array else {
            panic!("`{array}` is not an array");
        };
        let elem = elem.as_ref().clone();
        let elem_ll = self.mem_llty(&elem);
        let mut fx = FnCx::new(self, Subst::new(), Ty::Void);
        fx.start("entry");
        if fx.cx.needs_drop(&elem) {
            let len_addr = fx.assign("getelementptr inbounds { ptr, i64 }, ptr %v, i32 0, i32 1");
            let len = fx.assign(format!("load i64, ptr {len_addr}"));
            let counter = fx.alloca_ll("i64");
            fx.line("br label %loop");
            fx.start("loop");
            let index = fx.assign(format!("load i64, ptr {counter}"));
            let more = fx.assign(format!("icmp slt i64 {index}, {len}"));
            fx.line(format!("br i1 {more}, label %body, label %done"));
            fx.start("body");
            let address = fx.assign(format!(
                "getelementptr inbounds {}, ptr %v, i32 0, i32 2, i64 {index}",
                array_ll(&elem_ll)
            ));
            fx.drop_at(&elem, &address);
            let next = fx.assign(format!("add i64 {index}, 1"));
            fx.line(format!("store i64 {next}, ptr {counter}"));
            fx.line("br label %loop");
            fx.start("done");
        }
        fx.runtime("void", "kr_free", "ptr %v");
        fx.line("ret void");
        let body = fx.out;
        let allocas = fx.allocas;
        self.functions
            .push(define("void", &name, "ptr %v", &allocas, &body));
        name
    }

    pub(crate) fn drop_closure_fn(&mut self, index: usize) -> String {
        let name = format!("@\"dropclosure.{index}\"");
        if self.closure_drops.contains(&index) {
            return name;
        }
        self.closure_drops.insert(index);
        let closure_ty = self.closure_type(index);
        let captures = self.closures[index].captures.clone();
        let mut fx = FnCx::new(self, Subst::new(), Ty::Void);
        fx.start("entry");
        for (position, capture) in captures.iter().enumerate() {
            let address = fx.assign(format!(
                "getelementptr inbounds {closure_ty}, ptr %v, i32 0, i32 {}",
                position + 1
            ));
            fx.drop_at(capture, &address);
        }
        fx.runtime("void", "kr_free", "ptr %v");
        fx.line("ret void");
        let body = fx.out;
        let allocas = fx.allocas;
        self.functions
            .push(define("void", &name, "ptr %v", &allocas, &body));
        name
    }

    pub(crate) fn table_shape(&mut self, key: &Ty, value: &Ty) -> String {
        if let Some(name) = self.table_shapes.get(&(key.clone(), value.clone())) {
            return name.clone();
        }
        let name = format!("@\"shape.{}\"", self.table_shapes.len());
        self.table_shapes
            .insert((key.clone(), value.clone()), name.clone());
        let (entry_size, key_offset, value_offset, value_size) = self.entry_layout(key, value);
        let hash = self.instance(Instance::Thunk(Thunk::TableHash(key.clone())));
        let eq = self.instance(Instance::Thunk(Thunk::TableEq(key.clone())));
        let hash = self.fn_name(hash);
        let eq = self.fn_name(eq);
        let drop_key = if self.needs_drop(key) {
            let id = self.instance(Instance::Thunk(Thunk::TableDrop(key.clone())));
            self.fn_name(id)
        } else {
            "null".to_owned()
        };
        let drop_value = if *value != Ty::Void && self.needs_drop(value) {
            let id = self.instance(Instance::Thunk(Thunk::TableDrop(value.clone())));
            self.fn_name(id)
        } else {
            "null".to_owned()
        };
        self.globals.push(format!(
            "{name} = internal constant %KrTableShape {{ ptr {hash}, ptr {eq}, ptr {drop_key}, \
             ptr {drop_value}, i64 {entry_size}, i64 {key_offset}, i64 {value_offset}, \
             i64 {value_size} }}"
        ));
        name
    }

    pub(crate) fn entry_layout(&mut self, key: &Ty, value: &Ty) -> (u64, u64, u64, u64) {
        let key_layout = self.size_align(key);
        let value_layout = if *value == Ty::Void {
            (0, 1)
        } else {
            self.size_align(value)
        };
        let fields = [(4, 4), (4, 4), key_layout, value_layout];
        let offsets = field_offsets(&fields);
        let (size, _) = struct_layout(&fields);
        (size, offsets[2], offsets[3], value_layout.0)
    }

    pub(crate) fn entry_type(&mut self, key: &Ty, value: &Ty) -> String {
        let key_ll = self.mem_llty(key);
        if *value == Ty::Void {
            format!("{{ i32, i32, {key_ll}, {{}} }}")
        } else {
            let value_ll = self.mem_llty(value);
            format!("{{ i32, i32, {key_ll}, {value_ll} }}")
        }
    }
}

impl FnCx<'_, '_, '_> {
    pub(crate) fn drop_parts(&mut self, value: &str, ty: &Ty) {
        match self.cx.shape(ty) {
            Shape::Void | Shape::Prim(_) => {}
            Shape::Ptr(_) => self.drop_value(value, ty),
            Shape::Record(def, args) => {
                let llty = self.ll(ty);
                for (index, (_, field)) in self.cx.record_fields(def, &args).iter().enumerate() {
                    let indirect = self.cx.is_indirect(ty, field);
                    if !indirect && !self.cx.needs_drop(field) {
                        continue;
                    }
                    let part = self.assign(format!("extractvalue {llty} {value}, {index}"));
                    if indirect {
                        self.drop_indirect(field, &part);
                    } else {
                        self.drop_value(&part, field);
                    }
                }
            }
            Shape::NullableValue(inner) => {
                let inner = inner.as_ref().clone();
                let llty = self.ll(ty);
                let flag = self.assign(format!("extractvalue {llty} {value}, 0"));
                let present = self.label("present");
                let done = self.label("done");
                self.line(format!("br i1 {flag}, label %{present}, label %{done}"));
                self.start(&present);
                let payload = self.assign(format!("extractvalue {llty} {value}, 1"));
                self.drop_value(&payload, &inner);
                self.line(format!("br label %{done}"));
                self.start(&done);
            }
            Shape::Enum(def, args) => {
                let slot = self.alloca(ty);
                self.store(ty, value, &slot);
                let enum_ll = self.ll(ty);
                let tag_addr = self.assign(format!(
                    "getelementptr inbounds {enum_ll}, ptr {slot}, i32 0, i32 0"
                ));
                let tag = self.assign(format!("load i32, ptr {tag_addr}"));
                let done = self.label("done");
                let variants = self.cx.tcx.sig(def).variants.len();
                let mut cases = Vec::new();
                let mut blocks = Vec::new();
                for index in 0..variants {
                    let fields = self.cx.variant_fields(def, &args, index);
                    let droppable = fields.iter().any(|(_, field)| {
                        self.cx.is_indirect(ty, field) || self.cx.needs_drop(field)
                    });
                    if !droppable {
                        continue;
                    }
                    let label = self.label("variant");
                    cases.push(format!("i32 {index}, label %{label}"));
                    blocks.push((index, label, fields));
                }
                self.line(format!(
                    "switch i32 {tag}, label %{done} [ {} ]",
                    cases.join(" ")
                ));
                for (index, label, fields) in blocks {
                    self.start(&label);
                    let variant_ll = self.cx.variant_type(def, &args, index);
                    for (position, (_, field)) in fields.iter().enumerate() {
                        let address = self.assign(format!(
                            "getelementptr inbounds {variant_ll}, ptr {slot}, i32 0, i32 {}",
                            position + 1
                        ));
                        if self.cx.is_indirect(ty, field) {
                            let cell = self.assign(format!("load ptr, ptr {address}"));
                            self.drop_indirect(field, &cell);
                            self.line(format!("store ptr null, ptr {address}"));
                        } else {
                            self.drop_at(field, &address);
                        }
                    }
                    self.line(format!("br label %{done}"));
                }
                self.start(&done);
            }
        }
    }

    pub(crate) fn copy_parts(&mut self, value: &str, ty: &Ty) {
        match self.cx.shape(ty) {
            Shape::Ptr(PtrKind::String) => {
                self.runtime("void", "kr_string_retain", &format!("ptr {value}"));
            }
            Shape::Record(def, args) => {
                let llty = self.ll(ty);
                for (index, (_, field)) in self.cx.record_fields(def, &args).iter().enumerate() {
                    if !self.cx.needs_drop(field) {
                        continue;
                    }
                    let part = self.assign(format!("extractvalue {llty} {value}, {index}"));
                    self.copy_value(&part, field);
                }
            }
            Shape::NullableValue(inner) => {
                let inner = inner.as_ref().clone();
                let llty = self.ll(ty);
                let flag = self.assign(format!("extractvalue {llty} {value}, 0"));
                let present = self.label("present");
                let done = self.label("done");
                self.line(format!("br i1 {flag}, label %{present}, label %{done}"));
                self.start(&present);
                let payload = self.assign(format!("extractvalue {llty} {value}, 1"));
                self.copy_value(&payload, &inner);
                self.line(format!("br label %{done}"));
                self.start(&done);
            }
            Shape::Enum(def, args) => {
                let slot = self.alloca(ty);
                self.store(ty, value, &slot);
                let enum_ll = self.ll(ty);
                let tag_addr = self.assign(format!(
                    "getelementptr inbounds {enum_ll}, ptr {slot}, i32 0, i32 0"
                ));
                let tag = self.assign(format!("load i32, ptr {tag_addr}"));
                let done = self.label("done");
                let variants = self.cx.tcx.sig(def).variants.len();
                let mut cases = Vec::new();
                let mut blocks = Vec::new();
                for index in 0..variants {
                    let fields = self.cx.variant_fields(def, &args, index);
                    if !fields.iter().any(|(_, ty)| self.cx.needs_drop(ty)) {
                        continue;
                    }
                    let label = self.label("variant");
                    cases.push(format!("i32 {index}, label %{label}"));
                    blocks.push((index, label, fields));
                }
                self.line(format!(
                    "switch i32 {tag}, label %{done} [ {} ]",
                    cases.join(" ")
                ));
                for (index, label, fields) in blocks {
                    self.start(&label);
                    let variant_ll = self.cx.variant_type(def, &args, index);
                    for (position, (_, field)) in fields.iter().enumerate() {
                        let address = self.assign(format!(
                            "getelementptr inbounds {variant_ll}, ptr {slot}, i32 0, i32 {}",
                            position + 1
                        ));
                        let part = self.load(field, &address);
                        self.copy_value(&part, field);
                    }
                    self.line(format!("br label %{done}"));
                }
                self.start(&done);
            }
            _ => {}
        }
    }

    pub(crate) fn emit_drop_object(&mut self, object: &str, ty: &Ty) {
        let Ty::Adt { def, args, .. } = ty else {
            panic!("`{ty}` is not a class");
        };
        let object_ty = self.cx.object_type(ty);
        let items = &self.cx.tcx.lang_items;
        let def = *def;
        if items.is(def, LangItem::ArrayList) {
            let elem = args[0].clone();
            self.drop_list_elements(object, ty, &elem);
            let data = self.native_addr(object, ty, 0);
            let data = self.assign(format!("load ptr, ptr {data}"));
            self.runtime("void", "kr_free", &format!("ptr {data}"));
        } else if items.is_table(def) {
            let (key, value) = if items.is_map_table(def) {
                (args[0].clone(), args[1].clone())
            } else {
                (args[0].clone(), Ty::Void)
            };
            let shape = self.cx.table_shape(&key, &value);
            let table = self.native_addr(object, ty, 0);
            self.runtime(
                "void",
                "kr_table_free",
                &format!("ptr {table}, ptr {shape}"),
            );
        } else if items.is(def, LangItem::FileReader) || items.is(def, LangItem::FileWriter) {
            let handle = self.native_addr(object, ty, 0);
            let handle = self.assign(format!("load ptr, ptr {handle}"));
            self.runtime("void", "kr_file_close", &format!("ptr {handle}"));
        } else if items.is(def, LangItem::TcpListener)
            || items.is(def, LangItem::TcpStream)
            || items.is(def, LangItem::UdpSocket)
        {
            let handle = self.native_addr(object, ty, 0);
            let handle = self.assign(format!("load ptr, ptr {handle}"));
            self.runtime("void", "kr_net_close", &format!("ptr {handle}"));
        } else if items.is(def, LangItem::Poller) {
            let handle = self.native_addr(object, ty, 0);
            let handle = self.assign(format!("load ptr, ptr {handle}"));
            self.runtime("void", "kr_poller_close", &format!("ptr {handle}"));
        } else if items.is(def, LangItem::StringBuilder) {
            let builder = self.native_addr(object, ty, 0);
            self.runtime("void", "kr_builder_free", &format!("ptr {builder}"));
        } else if items.is(def, LangItem::Thread) || items.is(def, LangItem::ThreadTask) {
            let handle = self.native_addr(object, ty, 0);
            let handle = self.assign(format!("load ptr, ptr {handle}"));
            self.runtime("void", "kr_thread_join", &format!("ptr {handle}"));
        } else if items.is(def, LangItem::MutexGuard) {
            let mutex = self.native_addr(object, ty, 0);
            let mutex = self.assign(format!("load ptr, ptr {mutex}"));
            let mutex_ty = Ty::Adt {
                def: self.cx.lang(LangItem::Mutex),
                name: self.cx.tcx.ty_name(self.cx.lang(LangItem::Mutex)),
                args: args.clone(),
            };
            let handle = self.native_addr(&mutex, &mutex_ty, 0);
            let handle = self.assign(format!("load ptr, ptr {handle}"));
            self.runtime("void", "kr_mutex_unlock", &format!("ptr {handle}"));
        } else if items.is(def, LangItem::ReadGuard) || items.is(def, LangItem::WriteGuard) {
            let lock = self.native_addr(object, ty, 0);
            let lock = self.assign(format!("load ptr, ptr {lock}"));
            let lock_ty = Ty::Adt {
                def: self.cx.lang(LangItem::ReadWriteLock),
                name: self.cx.tcx.ty_name(self.cx.lang(LangItem::ReadWriteLock)),
                args: args.clone(),
            };
            let handle = self.native_addr(&lock, &lock_ty, 0);
            let handle = self.assign(format!("load ptr, ptr {handle}"));
            self.runtime("void", "kr_rwlock_unlock", &format!("ptr {handle}"));
        }
        if self.cx.tcx.closes_itself(def) {
            self.call_close(object, ty);
        }
        if items.is(def, LangItem::Mutex) {
            let handle = self.native_addr(object, ty, 0);
            let handle = self.assign(format!("load ptr, ptr {handle}"));
            self.runtime("void", "kr_mutex_free", &format!("ptr {handle}"));
        }
        if items.is(def, LangItem::ReadWriteLock) {
            let handle = self.native_addr(object, ty, 0);
            let handle = self.assign(format!("load ptr, ptr {handle}"));
            self.runtime("void", "kr_rwlock_free", &format!("ptr {handle}"));
        }
        for (index, field) in self.cx.class_fields(def, args).iter().enumerate() {
            if !self.cx.needs_drop(&field.ty) {
                continue;
            }
            let address = self.assign(format!(
                "getelementptr inbounds {object_ty}, ptr {object}, i32 0, i32 {}",
                index + 1
            ));
            self.drop_at(&field.ty, &address);
        }
        self.runtime("void", "kr_free", &format!("ptr {object}"));
    }

    fn call_close(&mut self, object: &str, ty: &Ty) {
        let slot = self.alloca_ll("ptr");
        self.line(format!("store ptr {object}, ptr {slot}"));
        let closeable = self.cx.lang(LangItem::AutoCloseable);
        let selector = Selector {
            owner: Ty::Adt {
                def: closeable,
                name: self.cx.tcx.ty_name(closeable),
                args: Vec::new(),
            },
            name: krelpin_span::Symbol::intern("close"),
            params: Vec::new(),
            method_args: Vec::new(),
            receiver: ReceiverKind::RefMut,
            ret: Ty::Void,
        };
        let receiver = Ty::Ref {
            mutable: true,
            ty: Box::new(ty.clone()),
        };
        self.dispatch(&selector, &receiver, &slot, &[]);
    }

    pub(crate) fn native_addr(&mut self, object: &str, ty: &Ty, slot: usize) -> String {
        let object_ty = self.cx.object_type(ty);
        let index = self.cx.native_index(ty, slot);
        self.assign(format!(
            "getelementptr inbounds {object_ty}, ptr {object}, i32 0, i32 {index}"
        ))
    }

    pub(crate) fn drop_list_elements(&mut self, object: &str, ty: &Ty, elem: &Ty) {
        if !self.cx.needs_drop(elem) {
            let len = self.native_addr(object, ty, 1);
            self.line(format!("store i64 0, ptr {len}"));
            return;
        }
        let elem_ll = self.cx.mem_llty(elem);
        let data = self.native_addr(object, ty, 0);
        let data = self.assign(format!("load ptr, ptr {data}"));
        let len_addr = self.native_addr(object, ty, 1);
        let len = self.assign(format!("load i64, ptr {len_addr}"));
        let counter = self.alloca_ll("i64");
        let head = self.label("droploop");
        let body = self.label("dropbody");
        let done = self.label("dropdone");
        self.line(format!("br label %{head}"));
        self.start(&head);
        let index = self.assign(format!("load i64, ptr {counter}"));
        let more = self.assign(format!("icmp slt i64 {index}, {len}"));
        self.line(format!("br i1 {more}, label %{body}, label %{done}"));
        self.start(&body);
        let address = self.assign(format!(
            "getelementptr inbounds {elem_ll}, ptr {data}, i64 {index}"
        ));
        self.drop_at(elem, &address);
        let next = self.assign(format!("add i64 {index}, 1"));
        self.line(format!("store i64 {next}, ptr {counter}"));
        self.line(format!("br label %{head}"));
        self.start(&done);
        self.line(format!("store i64 0, ptr {len_addr}"));
    }
}
