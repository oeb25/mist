use itertools::Itertools;
use mist_core::{
    hir::{
        self,
        types::{TypeProvider, TypePtr},
    },
    mir,
    util::IdxMap,
};

use crate::wasm;

#[derive(Debug, thiserror::Error)]
pub enum Error {}
type Result<T, E = Error> = std::result::Result<T, E>;

pub fn generate_module(db: &dyn crate::Db, program: hir::Program) -> Result<wasm::Module> {
    let root = program.parse(db).tree();

    // let mut builder = wasm::Module::builder();

    for &item_id in program.items(db) {
        let Some(item) = hir::item(db, &root, item_id) else { continue };
        let Some((cx, _source_map)) = hir::item_lower(db, program, item_id, item) else { continue };
        let (body, _mir_source_map) = mir::lower_item(db, cx.clone());

        FunctionLowerer::new(db, &cx, &body).generate_func();
    }

    todo!()
}

struct FunctionLowerer<'a> {
    db: &'a dyn crate::Db,
    #[allow(unused)]
    cx: &'a hir::ItemContext,
    body: &'a mir::Body,
    slots_stack_offsets: IdxMap<mir::SlotId, usize>,
}

impl<'a> FunctionLowerer<'a> {
    fn new(db: &'a dyn crate::Db, cx: &'a hir::ItemContext, body: &'a mir::Body) -> Self {
        Self {
            db,
            cx,
            body,
            slots_stack_offsets: Default::default(),
        }
    }

    fn allocate_slots<T: From<wasm::ValType>>(
        &mut self,
        offset: usize,
        slots: impl Iterator<Item = mir::SlotId>,
    ) -> Vec<T> {
        slots.fold(Vec::new(), |mut items, sid| {
            let idx = offset + items.len();
            self.slots_stack_offsets.insert(sid, idx);
            let types = self.compute_ty_layout(self.body.slot_ty(sid));
            items.extend(types.into_iter().map_into());
            items
        })
    }

    fn compute_struct_layout(&self, s: hir::Struct) -> StructLayout {
        let (layout, _) = s.fields(self.db).fold(
            (StructLayout::default(), 0),
            |(mut layout, current_offset), f| {
                layout
                    .field_offsets
                    .push((layout.types.len(), current_offset));
                let next = self.compute_ty_layout(self.body.field_ty(f));
                let size: u32 = next.iter().map(|ty| ty.num_bytes()).sum();
                let next_offset = current_offset + size;
                layout.types.extend(next);

                (layout, next_offset)
            },
        );
        layout
    }

    fn compute_ty_layout(&self, ty: TypePtr<mir::Body>) -> Vec<wasm::ValType> {
        match ty.data() {
            hir::TypeData::Ref { .. } => vec![wasm::ValType::I32],
            hir::TypeData::Primitive(p) => match p {
                hir::Primitive::Int | hir::Primitive::Bool => vec![wasm::ValType::I32],
            },
            hir::TypeData::Optional(inner) => {
                let mut layout = self.compute_ty_layout(inner);
                layout.insert(0, wasm::ValType::I32);
                layout
            }
            hir::TypeData::Struct(s) => self.compute_struct_layout(s).types,
            hir::TypeData::Range(_) => Vec::new(),
            hir::TypeData::Error
            | hir::TypeData::Void
            | hir::TypeData::Ghost(_)
            | hir::TypeData::List(_)
            | hir::TypeData::Null
            | hir::TypeData::Function { .. }
            | hir::TypeData::Free => Vec::new(),
        }
    }

    pub fn generate_func(&mut self) -> wasm::Func {
        let params = self.allocate_slots(0, self.body.params().iter().copied());
        let results = self.allocate_slots(params.len(), self.body.result_slot().into_iter());
        let locals = self.allocate_slots(params.len() + results.len(), self.body.locals());

        let type_use = wasm::TypeUse {
            type_idx: wasm::TypeIdx::Idx(0),
            params,
            results,
        };
        let instrs = vec![];
        wasm::Func {
            id: None,
            func_export: None,
            type_use,
            locals,
            instrs,
        }
    }
}

#[derive(Debug, Default)]
pub struct StructLayout {
    field_offsets: Vec<(usize, u32)>,
    types: Vec<wasm::ValType>,
}
