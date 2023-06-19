use std::collections::{HashMap, HashSet};

use crate::{
    def::{self, Def, DefKind},
    hir::{self, ExprIdx, Param, VariableIdx},
    types::{TypeId, TypeProvider, TDK},
};

use super::{
    exprs::{ExprPtr, VariablePtr},
    types::{Adt, AdtField, FunctionType, Type, TypeData},
    Condition, Function, Item, ItemKind, MonoSourceMap, Monomorphized,
};

pub(super) struct MonoLower<'db> {
    db: &'db dyn crate::Db,
    items: HashSet<Item>,
    source_map: MonoSourceMap,
}

impl<'db> MonoLower<'db> {
    pub fn new(db: &'db dyn crate::Db) -> MonoLower<'db> {
        MonoLower { db, items: Default::default(), source_map: Default::default() }
    }
    pub fn lower_def(&mut self, def: Def) {
        let Some(cx) = def.hir(self.db).map(|hir| hir.cx(self.db)) else { return };
        let mut mdl = MonoDefLower::new(self.db, cx);

        for adt_inst in cx.ty_table().adt_instantiations() {
            let adt = mdl.lower_adt(adt_inst.adt);
            self.items.insert(Item::new(self.db, ItemKind::Adt(adt)));
        }

        match def.kind(self.db) {
            DefKind::Function(f) => {
                let fun = mdl.lower_fn(f);
                self.items.insert(Item::new(self.db, ItemKind::Function(fun)));
            }
            DefKind::TypeInvariant(_ty_inv) => {}
            // NOTE: we do nothing for these, as we only look at instantiated types
            DefKind::Struct(_) | DefKind::StructField(_) => {}
        }
    }
    pub fn finish(self) -> Monomorphized {
        Monomorphized::new(self.db, self.items.into_iter().collect(), self.source_map)
    }
}

pub(super) struct MonoDefLower<'db, 'a> {
    db: &'db dyn crate::Db,
    cx: &'a hir::ItemContext,

    adt_cache: HashMap<crate::types::Adt, Adt>,
    ty_cache: HashMap<TypeId, Type>,
}
impl<'db, 'a> MonoDefLower<'db, 'a> {
    pub(super) fn new(db: &'db dyn crate::Db, cx: &'a hir::ItemContext) -> MonoDefLower<'db, 'a> {
        MonoDefLower { db, cx, adt_cache: Default::default(), ty_cache: Default::default() }
    }
    pub(super) fn lower_var(&mut self, var: VariableIdx) -> VariablePtr {
        let ty = self.cx.var_ty(self.db, var);
        VariablePtr { def: self.cx.def(), id: var, ty: self.lower_ty(ty.id()) }
    }
    pub(super) fn lower_expr(&mut self, expr: ExprIdx) -> ExprPtr {
        let ty = self.cx.expr_ty(expr);
        ExprPtr { def: self.cx.def(), id: expr, ty: self.lower_ty(ty.id()) }
    }
    fn lower_fn(&mut self, f: def::Function) -> Function {
        let attrs = f.attrs(self.db);
        let name = f.name(self.db);
        let params = self
            .cx
            .params()
            .iter()
            .map(|param| {
                let ty = self.lower_ty(param.ty.ty(self.db));
                Param {
                    is_ghost: param.is_ghost,
                    name: VariablePtr { def: Def::new(self.db, f.into()), id: param.name, ty },
                    ty,
                }
            })
            .collect();
        let return_ty = self
            .cx
            .return_ty(self.db)
            .map(|ty| self.lower_ty(ty))
            .unwrap_or_else(|| Type::new(self.db, false, TypeData::Void));
        let conditions = self
            .cx
            .conditions()
            .map(|cond| match cond {
                hir::Condition::Requires(exprs) => {
                    Condition::Requires(exprs.iter().map(|expr| self.lower_expr(*expr)).collect())
                }
                hir::Condition::Ensures(exprs) => {
                    Condition::Ensures(exprs.iter().map(|expr| self.lower_expr(*expr)).collect())
                }
            })
            .collect();
        let body = self.cx.body_expr().map(|expr| self.lower_expr(expr));
        Function::new(self.db, attrs, name, params, return_ty, conditions, body)
    }
    pub(super) fn lower_adt(&mut self, adt: crate::types::Adt) -> Adt {
        if let Some(adt) = self.adt_cache.get(&adt).copied() {
            return adt;
        }

        let fields = self
            .cx
            .fields_of(adt)
            .into_iter()
            .map(|af| {
                let ty = self.lower_ty(self.cx.field_ty(af.into()));
                AdtField::new(self.db, af.name(self.db), ty)
            })
            .collect();

        let new_adt = Adt::new(self.db, adt.kind(), fields);
        self.adt_cache.insert(adt, new_adt);
        new_adt
    }
    pub(super) fn lower_ty(&mut self, ty: TypeId) -> Type {
        if let Some(t) = self.ty_cache.get(&ty).copied() {
            return t;
        };

        let data = ty.wrap(self.cx).data();

        let kind = match data.map(|inner| self.lower_ty(inner.id())).kind {
            TDK::Error => TypeData::Error,
            TDK::Void => TypeData::Void,
            TDK::Ref { is_mut, inner } => TypeData::Ref { is_mut, inner },
            TDK::List(inner) => TypeData::List(inner),
            TDK::Optional(inner) => TypeData::Optional(inner),
            TDK::Primitive(p) => TypeData::Primitive(p),
            TDK::Adt(adt) => TypeData::Adt(self.lower_adt(adt)),
            TDK::Null => TypeData::Null,
            TDK::Function { attrs, name: _, params, return_ty } => {
                TypeData::Function(FunctionType::new(
                    self.db,
                    attrs,
                    params.into_iter().map(|param| self.lower_ty(param.ty.ty(self.db))).collect(),
                    return_ty,
                ))
            }
            TDK::Range(inner) => TypeData::Range(inner),
            // TODO: this should not be an error i think
            TDK::Generic(_) => TypeData::Error,
            TDK::Free => TypeData::Error,
        };
        let new_ty = Type::new(self.db, data.is_ghost, kind);
        self.ty_cache.insert(ty, new_ty);
        new_ty
    }
}
