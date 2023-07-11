use mist_core::{mir, mono::types::Adt, util::IdxWrap};
use silvers::{
    expression::{AbstractLocalVar, BinOp, Exp, FieldAccess, LocalVar, PermExp, QuantifierExp},
    program::{
        AnyLocalVarDecl, Domain, DomainAxiom, DomainFunc, Field, Function, LocalVarDecl, Predicate,
    },
};

use crate::{
    gen::{VExprId, ViperItem},
    mangle,
};

use super::{BodyLower, Result};

impl BodyLower<'_> {
    pub fn adt_lower(
        &mut self,
        self_local: mir::LocalId,
        adt: Adt,
        invariants: impl IntoIterator<Item = mir::BlockId>,
    ) -> Result<Vec<ViperItem<VExprId>>> {
        if adt.is_pure(self.db) {
            pure_struct(self.db, self, adt, self_local, invariants)
        } else {
            impure_struct(self.db, self, adt, self_local, invariants)
        }
    }
}

fn pure_struct(
    db: &dyn crate::Db,
    l: &mut BodyLower,
    adt: Adt,
    self_local: mir::LocalId,
    invariants: impl IntoIterator<Item = mir::BlockId>,
) -> Result<Vec<ViperItem<VExprId>>> {
    let mut viper_items = vec![];

    let self_place = self_local.place(db, l.ib);

    // TODO: is this really a good source?
    let source = mir::BlockId::from_raw(0.into());
    l.begin_scope(source, |l| {
        let mut functions = Vec::new();
        let mut axioms = Vec::new();
        let adt_ty = l.lower_type(adt.ty(db))?.vty;
        functions.push(DomainFunc {
            name: mangle::mangled_adt(db, adt) + "_unsafe_init",
            formal_args: adt
                .fields(db)
                .iter()
                .map(|f| {
                    Ok(AnyLocalVarDecl::LocalVarDecl(LocalVarDecl {
                        name: f.name(db).to_string(),
                        typ: l.lower_type(f.ty(db))?.vty,
                    }))
                })
                .collect::<Result<_>>()?,
            typ: adt_ty.clone(),
            unique: false,
            interpretation: None,
        });
        let self_decl = l.local_to_decl(self_local)?;
        let mut init_vars = vec![self_decl.clone()];
        let mut init_exps = vec![];
        let mut eq_exps = vec![];
        let tmp_var = LocalVarDecl::new("tmp".to_string(), adt_ty.clone());
        let tmp =
            l.allocs(Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(tmp_var.clone().into())));
        let first_var = LocalVarDecl::new("first".to_string(), adt_ty.clone());
        let first =
            l.allocs(Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(first_var.clone().into())));
        let second_var = LocalVarDecl::new("second".to_string(), adt_ty.clone());
        let second =
            l.allocs(Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(second_var.clone().into())));
        for (f_name, f_typ) in adt
            .fields(db)
            .into_iter()
            .map(|f| {
                let f_name = mangle::mangled_adt_field(db, adt, f);
                let f_typ = l.lower_type(f.ty(db))?.vty;
                Ok((f_name, f_typ))
            })
            .collect::<Result<Vec<_>>>()?
        {
            functions.push(DomainFunc {
                name: f_name.clone(),
                formal_args: vec![AnyLocalVarDecl::LocalVarDecl(self_decl.clone())],
                typ: f_typ.clone(),
                unique: false,
                interpretation: None,
            });

            let f_var = LocalVarDecl::new(f_name.clone() + "_", f_typ);
            let mk_field =
                |l: &mut BodyLower, c| l.allocs(Exp::new_func_app(f_name.clone(), vec![c]));
            let f_fn_tmp = mk_field(l, tmp);
            init_vars.push(f_var.clone());
            let f_exp = l.allocs(Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(f_var.into())));
            init_exps.push(l.allocs(Exp::eq_cmp(f_fn_tmp, f_exp)));

            let eq_exp = Exp::eq_cmp(mk_field(l, first), mk_field(l, second));
            eq_exps.push(l.allocs(eq_exp));
        }
        let fn_tmp_args = init_vars[1..]
            .iter()
            .map(|v| l.allocs(Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(v.clone().into()))))
            .collect();
        let fn_tmp =
            l.allocs(Exp::new_func_app(mangle::mangled_adt(db, adt) + "_unsafe_init", fn_tmp_args));
        let init_exp_body =
            init_exps.into_iter().reduce(|acc, next| l.allocs(Exp::bin(acc, BinOp::And, next)));
        if let Some(init_exp_body) = init_exp_body {
            let init_exp = l.allocs(Exp::new_let(tmp_var, fn_tmp, init_exp_body));
            axioms.push(DomainAxiom {
                name: Some(mangle::mangled_adt(db, adt) + "_init_axiom"),
                exp: l.allocs(Exp::Quantifier(QuantifierExp::Forall {
                    variables: init_vars.clone(),
                    triggers: Vec::new(),
                    exp: init_exp,
                })),
            });
        }
        let eq_exp_body =
            eq_exps.into_iter().reduce(|acc, next| l.allocs(Exp::bin(acc, BinOp::And, next)));
        if let Some(eq_exp_body) = eq_exp_body {
            let eq = l.allocs(Exp::eq_cmp(first, second));
            let eq_exp = l.allocs(Exp::eq_cmp(eq, eq_exp_body));
            axioms.push(DomainAxiom {
                name: Some(mangle::mangled_adt(db, adt) + "_eq_axiom"),
                exp: l.allocs(Exp::Quantifier(QuantifierExp::Forall {
                    variables: vec![first_var, second_var],
                    triggers: Vec::new(),
                    exp: eq_exp,
                })),
            });
        }
        let mut safe_pres = Vec::new();
        for inv in invariants {
            let inv_exp = l.pure_lower(inv)?;
            let exp = l.allocs(Exp::Quantifier(QuantifierExp::Forall {
                variables: vec![self_decl.clone()],
                triggers: Vec::new(),
                exp: inv_exp,
            }));
            axioms.push(DomainAxiom { name: None, exp });

            let safe = l.begin_scope(inv, |l| {
                for (adt_field, init_var) in adt.fields(l.db).into_iter().zip(init_vars[1..].iter())
                {
                    let field_place = self_place
                        .project_deeper(l.db, &[mir::Projection::Field(adt_field.into_field(db))]);
                    let init_exp = l.allocs(Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(
                        init_var.clone().into(),
                    )));
                    l.alias(field_place, init_exp);
                }

                l.pure_lower(inv)
            })?;
            safe_pres.push(safe);
        }
        viper_items.push(ViperItem::Domain(Domain {
            name: mangle::mangled_adt(db, adt),
            functions,
            axioms,
            typ_vars: Vec::new(),
            interpretations: None,
        }));
        let post_eq = {
            let result =
                l.allocs(Exp::AbstractLocalVar(AbstractLocalVar::Result { typ: adt_ty.clone() }));
            let eq = {
                let final_args = init_vars[1..]
                    .iter()
                    .map(|v| {
                        l.allocs(Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(
                            v.clone().into(),
                        )))
                    })
                    .collect();
                l.allocs(Exp::new_func_app(
                    mangle::mangled_adt(db, adt) + "_unsafe_init",
                    final_args,
                ))
            };
            l.allocs(Exp::eq_cmp(result, eq))
        };
        viper_items.push(ViperItem::Function(Function {
            name: mangle::mangled_adt(db, adt) + "_init",
            formal_args: init_vars[1..].to_vec(),
            typ: adt_ty,
            pres: safe_pres,
            posts: vec![post_eq],
            body: None,
        }));
        Ok(viper_items)
    })
}

fn impure_struct(
    db: &dyn crate::Db,
    l: &mut BodyLower,
    adt: Adt,
    self_local: mir::LocalId,
    invariants: impl IntoIterator<Item = mir::BlockId>,
) -> Result<Vec<ViperItem<VExprId>>> {
    let mut viper_items = Vec::new();

    // TODO: is this really a good source?
    let source = mir::BlockId::from_raw(0.into());
    l.begin_scope(source, |l| {
        let self_var = l.local_to_var(self_local)?;
        let self_var = LocalVar { name: self_var.name, typ: silvers::typ::Type::ref_() };
        let self_place = self_local.place(db, l.ib);
        let self_ = l.allocs(AbstractLocalVar::LocalVar(self_var.clone()));

        l.pre_unfolded.insert(self_place);

        let field_invs: Vec<_> = adt
            .fields(db)
            .iter()
            .map(|&f| {
                let field_ty = f.ty(db);
                let ty = l.lower_type(field_ty)?;
                let viper_field =
                    Field { name: mangle::mangled_adt_field(db, adt, f), typ: ty.vty };
                viper_items.push(ViperItem::Field(viper_field.clone()));
                let perm = l.allocs(PermExp::Full);
                let field_access = FieldAccess::new(self_, viper_field);
                let field_perm = l.allocs(field_access.clone().access_perm(perm));

                let field_ref = l.allocs(field_access.access_exp());
                Ok(if let (Some(cond), _) = l.ty_to_condition(field_ref, field_ty)? {
                    l.allocs(Exp::bin(field_perm, BinOp::And, cond))
                } else {
                    field_perm
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let inv_invs: Vec<_> =
            invariants.into_iter().map(|inv| l.pure_lower(inv)).collect::<Result<_>>()?;
        let body = field_invs
            .into_iter()
            .chain(inv_invs)
            .reduce(|acc, next| l.allocs(Exp::bin(acc, BinOp::And, next)));

        viper_items.push(ViperItem::Predicate(Predicate {
            name: mangle::mangled_adt(db, adt),
            formal_args: vec![self_var.into()],
            body,
        }));

        Ok(viper_items)
    })
}
