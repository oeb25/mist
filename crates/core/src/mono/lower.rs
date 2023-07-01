mod desugar;

use std::collections::HashMap;

use indexmap::IndexSet;

use crate::{
    def::{self, Def, DefKind, Name},
    hir::{self, ExprIdx, Param, VariableIdx},
    mono::exprs::VariableDeclaration,
    types::{AdtKind, BuiltinKind, TypeId, TypeProvider, TDK},
};

use super::{
    exprs::{
        Block, BuiltinExpr, Decreases, ExprData, ExprDataWrapper, ExprFunction, ExprPtr, Field,
        ForExpr, IfExpr, QuantifierOver, StatementPtr, VariablePtr, WhileExpr,
    },
    types::{Adt, AdtField, AdtFieldKind, BuiltinType, FunctionType, Type, TypeData},
    Condition, Function, Item, ItemKind, Monomorphized,
};

pub(super) struct MonoLower<'db> {
    db: &'db dyn crate::Db,
    items: IndexSet<Item>,
}

impl<'db> MonoLower<'db> {
    pub fn new(db: &'db dyn crate::Db) -> MonoLower<'db> {
        MonoLower { db, items: Default::default() }
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
        Monomorphized::new(self.db, self.items.into_iter().collect())
    }
}

pub(crate) struct MonoDefLower<'db, 'a> {
    db: &'db dyn crate::Db,
    cx: &'a hir::ItemContext,

    adt_cache: HashMap<crate::types::Adt, Adt>,
    ty_cache: HashMap<TypeId, Type>,
}
impl<'db, 'a> MonoDefLower<'db, 'a> {
    pub(crate) fn new(db: &'db dyn crate::Db, cx: &'a hir::ItemContext) -> MonoDefLower<'db, 'a> {
        MonoDefLower { db, cx, adt_cache: Default::default(), ty_cache: Default::default() }
    }
    pub(super) fn lower_var(&mut self, var: VariableIdx) -> VariablePtr {
        let ty = self.cx.var_ty(self.db, var);
        let decl = match self.cx.var_decl(var).kind() {
            crate::VariableDeclarationKind::Let { is_mut } => {
                Some(VariableDeclaration::Let { is_mut })
            }
            crate::VariableDeclarationKind::Parameter => Some(VariableDeclaration::Parameter),
            crate::VariableDeclarationKind::Function(f) => {
                Some(VariableDeclaration::Function(self.lower_fn(f)))
            }
            crate::VariableDeclarationKind::Undefined => None,
        };
        VariablePtr { def: self.cx.def(), id: var, ty: self.lower_ty(ty), decl }
    }
    pub(super) fn lower_expr(&mut self, expr_id: ExprIdx) -> ExprPtr {
        let ty = self.cx.expr_ty(expr_id);

        let expr = self.cx.expr(expr_id);

        let data = match &expr.data {
            hir::ExprData::Literal(it) => ExprData::Literal(it.clone()),
            hir::ExprData::Self_ => ExprData::Self_,
            hir::ExprData::Ident(var) => ExprData::Ident(self.lower_var(*var)),
            hir::ExprData::Block(it) => ExprData::Block(Block {
                stmts: it
                    .stmts
                    .iter()
                    .map(|stmt| StatementPtr { def: self.cx.def(), id: *stmt })
                    .collect(),
                tail_expr: it.tail_expr.map(|expr| self.lower_expr(expr)),
            }),
            hir::ExprData::Field { expr, field } => ExprData::Field {
                expr: self.lower_expr(*expr),
                field: match field {
                    crate::types::Field::AdtField(adt_field) => {
                        let adt = self.lower_adt(adt_field.adt());
                        let kind = match adt_field.kind() {
                            crate::types::AdtFieldKind::StructField(sf) => {
                                AdtFieldKind::StructField(sf)
                            }
                        };
                        let ty = self.lower_ty(adt_field.ty());
                        let adt_field =
                            AdtField::new(self.db, adt, adt_field.name(self.db), kind, ty);
                        Field::AdtField(adt, adt_field)
                    }
                    crate::types::Field::Builtin(bf) => {
                        Field::Builtin(bf.map(|ty| self.lower_ty(*ty)))
                    }
                    crate::types::Field::Undefined => Field::Undefined,
                },
            },
            hir::ExprData::Adt { adt, fields } => {
                let adt = self.lower_adt(*adt);
                ExprData::Adt {
                    adt,
                    fields: fields
                        .iter()
                        .map(|f| {
                            let ty = self.lower_ty(f.decl.ty());
                            let kind = match f.decl.kind() {
                                crate::types::AdtFieldKind::StructField(sf) => {
                                    AdtFieldKind::StructField(sf)
                                }
                            };
                            let adt_field =
                                AdtField::new(self.db, adt, f.decl.name(self.db), kind, ty);
                            (adt_field, self.lower_expr(f.value))
                        })
                        .collect(),
                }
            }
            hir::ExprData::Missing => ExprData::Missing,
            hir::ExprData::If(it) => ExprData::If(IfExpr {
                condition: self.lower_expr(it.condition),
                then_branch: self.lower_expr(it.then_branch),
                else_branch: it.else_branch.map(|expr| self.lower_expr(expr)),
            }),
            hir::ExprData::While(it) => ExprData::While(WhileExpr {
                expr: self.lower_expr(it.expr),
                invariants: it
                    .invariants
                    .iter()
                    .map(|invs| invs.iter().map(|expr| self.lower_expr(*expr)).collect())
                    .collect(),
                decreases: match it.decreases {
                    hir::Decreases::Unspecified => Decreases::Unspecified,
                    hir::Decreases::Expr(expr) => Decreases::Expr(self.lower_expr(expr)),
                    hir::Decreases::Inferred => Decreases::Inferred,
                },
                body: self.lower_expr(it.body),
            }),
            hir::ExprData::For(it) => ExprData::For(ForExpr {
                is_ghost: it.is_ghost,
                variable: self.lower_var(it.variable),
                in_expr: self.lower_expr(it.in_expr),
                invariants: it
                    .invariants
                    .iter()
                    .map(|invs| invs.iter().map(|expr| self.lower_expr(*expr)).collect())
                    .collect(),
                body: self.lower_expr(it.body),
            }),
            hir::ExprData::Call { expr, args } => {
                let expr = self.lower_expr(*expr);
                let (prefix_args, fun) = match expr.data(self.db) {
                    ExprData::Field { expr, field: Field::Builtin(bf) } if bf.is_function() => {
                        (vec![expr], ExprFunction::Builtin(bf))
                    }
                    ExprData::Ident(_) => (Vec::new(), ExprFunction::Expr(expr)),
                    _ => (Vec::new(), ExprFunction::Expr(expr)),
                };
                ExprData::Call {
                    fun,
                    args: prefix_args
                        .into_iter()
                        .chain(args.iter().map(|expr| self.lower_expr(*expr)))
                        .collect(),
                }
            }
            &hir::ExprData::Unary { op, inner } => {
                ExprData::Unary { op, inner: self.lower_expr(inner) }
            }
            &hir::ExprData::Bin { lhs, op, rhs } => {
                ExprData::Bin { lhs: self.lower_expr(lhs), op, rhs: self.lower_expr(rhs) }
            }
            &hir::ExprData::Ref { is_mut, expr } => {
                ExprData::Ref { is_mut, expr: self.lower_expr(expr) }
            }
            &hir::ExprData::Index { base, index } => {
                ExprData::Index { base: self.lower_expr(base), index: self.lower_expr(index) }
            }
            hir::ExprData::List { elems } => {
                ExprData::List { elems: elems.iter().map(|&id| self.lower_expr(id)).collect() }
            }
            hir::ExprData::Quantifier { quantifier, over, expr } => ExprData::Quantifier {
                quantifier: *quantifier,
                over: match over {
                    hir::QuantifierOver::Vars(vars) => {
                        QuantifierOver::Vars(vars.iter().map(|var| self.lower_var(*var)).collect())
                    }
                    hir::QuantifierOver::In(var, expr) => {
                        QuantifierOver::In(self.lower_var(*var), self.lower_expr(*expr))
                    }
                },
                expr: self.lower_expr(*expr),
            },
            hir::ExprData::Result => ExprData::Result,
            hir::ExprData::Range { lhs, rhs } => ExprData::Range {
                lhs: lhs.map(|it| self.lower_expr(it)),
                rhs: rhs.map(|it| self.lower_expr(it)),
            },
            hir::ExprData::Return(it) => ExprData::Return(it.map(|it| self.lower_expr(it))),
            hir::ExprData::NotNull(it) => ExprData::NotNull(self.lower_expr(*it)),
            hir::ExprData::Builtin(it) => ExprData::Builtin(match it {
                hir::BuiltinExpr::RangeMin(it) => BuiltinExpr::RangeMin(self.lower_expr(*it)),
                hir::BuiltinExpr::RangeMax(it) => BuiltinExpr::RangeMax(self.lower_expr(*it)),
                hir::BuiltinExpr::InRange(lhs, rhs) => {
                    BuiltinExpr::InRange(self.lower_expr(*lhs), self.lower_expr(*rhs))
                }
            }),
        };

        desugar::desugar_expr(
            self.db,
            ExprPtr {
                def: self.cx.def(),
                id: expr_id,
                ty: self.lower_ty(ty),
                inner_data: ExprDataWrapper::new(self.db, data),
            },
        )
    }
    fn lower_fn(&mut self, f: def::Function) -> Function {
        let attrs = f.attrs(self.db);
        let name = f.name(self.db);

        let def = Def::new(self.db, DefKind::Function(f));
        let cx = def.hir(self.db).unwrap().cx(self.db);

        let mut mdl = MonoDefLower::new(self.db, cx);

        let params = cx
            .params()
            .iter()
            .map(|param| {
                let ty = mdl.lower_ty(param.ty.ty(mdl.db));
                Param {
                    is_ghost: param.is_ghost,
                    name: VariablePtr {
                        def: Def::new(mdl.db, f.into()),
                        id: param.name,
                        ty,
                        decl: Some(VariableDeclaration::Parameter),
                    },
                    ty,
                }
            })
            .collect();
        let return_ty = cx
            .return_ty(mdl.db)
            .map(|ty| mdl.lower_ty(ty))
            .unwrap_or_else(|| Type::new(mdl.db, false, TypeData::Void));
        let conditions = cx
            .conditions()
            .map(|cond| match cond {
                hir::Condition::Requires(exprs) => {
                    Condition::Requires(exprs.iter().map(|expr| mdl.lower_expr(*expr)).collect())
                }
                hir::Condition::Ensures(exprs) => {
                    Condition::Ensures(exprs.iter().map(|expr| mdl.lower_expr(*expr)).collect())
                }
            })
            .collect();
        Function::new(mdl.db, def, attrs, name, params, return_ty, conditions)
    }

    pub(super) fn lower_builtin(
        &mut self,
        b: BuiltinKind,
        args: crate::types::GenericArgs,
    ) -> BuiltinType {
        let generic_args = args.args(self.db).iter().map(|g| self.lower_ty(*g)).collect();
        BuiltinType::new(self.db, b, generic_args)
    }
    pub(super) fn lower_adt(&mut self, adt: crate::types::Adt) -> Adt {
        if let Some(adt) = self.adt_cache.get(&adt).copied() {
            return adt;
        }

        let kind = adt.kind();
        let generic_args = adt.generic_args(self.db).map(|g| self.lower_ty(g)).collect();

        let new_adt = Adt::new(self.db, kind, generic_args);
        self.adt_cache.insert(adt, new_adt);
        new_adt
    }
    pub(crate) fn lower_ty(&mut self, ty: TypeId) -> Type {
        if let Some(t) = self.ty_cache.get(&ty).copied() {
            return t;
        };

        let data = self.cx.ty_data(ty);

        let kind = match data.map(|inner| self.lower_ty(*inner)).kind {
            TDK::Error => TypeData::Error,
            TDK::Void => TypeData::Void,
            TDK::Ref { is_mut, inner } => TypeData::Ref { is_mut, inner },
            TDK::Optional(inner) => TypeData::Optional(inner),
            TDK::Primitive(p) => TypeData::Primitive(p),
            TDK::Builtin(b, gargs) => TypeData::Builtin(self.lower_builtin(b, gargs)),
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
            TDK::Generic(g) => TypeData::Generic(g),
            TDK::Free => TypeData::Error,
        };
        let new_ty = Type::new(self.db, data.is_ghost, kind);
        self.ty_cache.insert(ty, new_ty);
        new_ty
    }

    pub(super) fn add_substitution(&mut self, id: TypeId, fixed: Type) {
        self.ty_cache.insert(id, fixed);
    }
}

#[salsa::tracked]
pub fn adt_kind_prototype_fields(db: &dyn crate::Db, def: Def) -> Vec<(Name, AdtFieldKind, Type)> {
    match def.kind(db) {
        DefKind::Struct(s) => {
            let adt_kind = AdtKind::Struct(def, s);

            let hir = def.hir(db).unwrap();
            let cx = hir.cx(db);

            let crate::types::AdtPrototype::StructPrototype(prototype) =
                cx.adt_prototype(adt_kind).unwrap();

            let mut mdl = MonoDefLower::new(db, cx);

            prototype
                .fields
                .iter()
                .map(|(sf, ty)| (sf.name(db), AdtFieldKind::StructField(*sf), mdl.lower_ty(*ty)))
                .collect()
        }
        _ => Vec::new(),
    }
}

impl Function {
    pub fn body(&self, db: &dyn crate::Db) -> Option<ExprPtr> {
        let hir = self.def(db).hir(db)?;
        let cx = hir.cx(db);
        let mut mdl = MonoDefLower::new(db, cx);
        cx.body_expr().map(|expr| mdl.lower_expr(expr))
    }
}
