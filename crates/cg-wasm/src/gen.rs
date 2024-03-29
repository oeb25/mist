use itertools::Itertools;
use mist_core::{
    file::SourceFile,
    mir,
    mono::{
        self,
        types::{Adt, Type, TypeData},
    },
    types::Primitive,
    util::IdxMap,
};

use crate::wasm;

#[derive(Debug, thiserror::Error)]
pub enum Error {}
type Result<T, E = Error> = std::result::Result<T, E>;

pub fn generate_module(db: &dyn crate::Db, file: SourceFile) -> Result<wasm::Module> {
    // let mut builder = wasm::Module::builder();

    for item in mono::monomorphized_items(db, file).items(db) {
        let Some(mir) = mir::lower_item(db, item) else { continue };
        FunctionLowerer::new(db, mir.ib(db)).generate_func();
    }

    todo!()
}

struct FunctionLowerer<'a> {
    db: &'a dyn crate::Db,
    ib: &'a mir::ItemBody,
    locals_stack_offsets: IdxMap<mir::LocalId, usize>,
}

impl<'a> FunctionLowerer<'a> {
    fn new(db: &'a dyn crate::Db, ib: &'a mir::ItemBody) -> Self {
        Self { db, ib, locals_stack_offsets: Default::default() }
    }

    fn allocate_locals<T: From<wasm::ValType>>(
        &mut self,
        offset: usize,
        locals: impl Iterator<Item = mir::LocalId>,
    ) -> Vec<T> {
        locals.fold(Vec::new(), |mut items, sid| {
            let idx = offset + items.len();
            self.locals_stack_offsets.insert(sid, idx);
            let types = self.compute_ty_layout(sid.ty(self.db, self.ib));
            items.extend(types.into_iter().map_into());
            items
        })
    }

    fn compute_adt_layout(&self, adt: Adt) -> StructLayout {
        let (layout, _) = adt.fields(self.db).iter().fold(
            (StructLayout::default(), 0),
            |(mut layout, current_offset), f| {
                layout.field_offsets.push((layout.types.len(), current_offset));
                let next = self.compute_ty_layout(f.ty(self.db));
                let size: u32 = next.iter().map(|ty| ty.num_bytes()).sum();
                let next_offset = current_offset + size;
                layout.types.extend(next);

                (layout, next_offset)
            },
        );
        layout
    }

    fn compute_ty_layout(&self, ty: Type) -> Vec<wasm::ValType> {
        match ty.kind(self.db) {
            TypeData::Ref { .. } => vec![wasm::ValType::I32],
            TypeData::Primitive(p) => match p {
                Primitive::Int | Primitive::Bool => vec![wasm::ValType::I32],
            },
            TypeData::Optional(inner) => {
                let mut layout = self.compute_ty_layout(inner);
                layout.insert(0, wasm::ValType::I32);
                layout
            }
            TypeData::Adt(adt) => self.compute_adt_layout(adt).types,
            // TODO: these should perhaps be ghost, making them okay to exclude
            TypeData::Builtin(_) => Vec::new(),
            TypeData::Error
            | TypeData::Void
            | TypeData::Null
            | TypeData::Function { .. }
            | TypeData::Generic(_) => Vec::new(),
        }
    }

    pub fn generate_func(&mut self) -> wasm::Func {
        let params = self.allocate_locals(0, self.ib.params().iter().copied());
        let results = self.allocate_locals(params.len(), self.ib.result_local().into_iter());
        let locals = self.allocate_locals(params.len() + results.len(), self.ib.body_locals());

        let type_use = wasm::TypeUse { type_idx: wasm::TypeIdx::Idx(0), params, results };
        let instrs = vec![];
        wasm::Func { id: None, func_export: None, type_use, locals, instrs }
    }
}

#[derive(Debug, Default)]
pub struct StructLayout {
    field_offsets: Vec<(usize, u32)>,
    types: Vec<wasm::ValType>,
}
