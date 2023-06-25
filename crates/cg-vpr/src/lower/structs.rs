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
        self_slot: mir::SlotId,
        adt: Adt,
        invariants: impl IntoIterator<Item = mir::BlockId>,
    ) -> Result<Vec<ViperItem<VExprId>>> {
        if adt.is_pure(self.db) {
            pure_struct(self.db, self, adt, self_slot, invariants)
        } else {
            impure_struct(self.db, self, adt, self_slot, invariants)
        }
    }
}

fn pure_struct(
    db: &dyn crate::Db,
    l: &mut BodyLower,
    adt: Adt,
    self_slot: mir::SlotId,
    invariants: impl IntoIterator<Item = mir::BlockId>,
) -> Result<Vec<ViperItem<VExprId>>> {
    let mut viper_items = vec![];

    let self_place = self_slot.place(db, l.ib);

    // TODO: is this really a good source?
    let source = mir::BlockId::from_raw(0.into());
    let mut functions = Vec::new();
    let mut axioms = Vec::new();
    let adt_ty = l.lower_type(adt.ty(db))?.vty;
    functions.push(DomainFunc {
        name: mangle::mangled_adt(db, adt) + "_unsafe_init",
        formal_args: adt
            .fields(db)
            .iter()
            .map(|f| Ok(AnyLocalVarDecl::UnnamedLocalVarDecl { typ: l.lower_type(f.ty(db))?.vty }))
            .collect::<Result<_>>()?,
        typ: adt_ty.clone(),
        unique: false,
        interpretation: None,
    });
    let self_decl = l.slot_to_decl(self_slot)?;
    let mut init_vars = vec![self_decl.clone()];
    let mut init_exps = vec![];
    let tmp_var = LocalVarDecl::new("tmp".to_string(), adt_ty.clone());
    let tmp =
        l.alloc(source, Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(tmp_var.clone().into())));
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

        let f_fn_tmp = l.alloc(source, Exp::new_func_app(f_name.clone(), vec![tmp]));
        let f_var = LocalVarDecl::new(f_name + "_", f_typ);
        init_vars.push(f_var.clone());
        let f_exp =
            l.alloc(source, Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(f_var.into())));
        init_exps.push(l.alloc(source, Exp::eq_cmp(f_fn_tmp, f_exp)));
    }
    let fn_tmp_args = init_vars[1..]
        .iter()
        .map(|v| {
            l.alloc(source, Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(v.clone().into())))
        })
        .collect();
    let fn_tmp = l.alloc(
        source,
        Exp::new_func_app(mangle::mangled_adt(db, adt) + "_unsafe_init", fn_tmp_args),
    );
    let init_exp_body =
        init_exps.into_iter().reduce(|acc, next| l.alloc(source, Exp::bin(acc, BinOp::And, next)));
    if let Some(init_exp_body) = init_exp_body {
        let init_exp = l.alloc(source, Exp::new_let(tmp_var, fn_tmp, init_exp_body));
        axioms.push(DomainAxiom {
            name: Some(mangle::mangled_adt(db, adt) + "_init_axiom"),
            exp: l.alloc(
                source,
                Exp::Quantifier(QuantifierExp::Forall {
                    variables: init_vars.clone(),
                    triggers: Vec::new(),
                    exp: init_exp,
                }),
            ),
        });
    }
    let mut safe_pres = Vec::new();
    for inv in invariants {
        let inv_exp = l.pure_lower(inv)?;
        let exp = l.alloc(
            inv,
            Exp::Quantifier(QuantifierExp::Forall {
                variables: vec![self_decl.clone()],
                triggers: Vec::new(),
                exp: inv_exp,
            }),
        );
        axioms.push(DomainAxiom { name: None, exp });

        let safe = l.begin_scope(|l| {
            for (adt_field, init_var) in adt.fields(l.db).into_iter().zip(init_vars[1..].iter()) {
                let field_place = self_place.project_deeper(
                    l.db,
                    &[mir::Projection::Field(
                        adt_field.into_field(db),
                        adt_field.ty(l.db).ghosted(l.db),
                    )],
                );
                let init_exp = l.alloc(
                    inv,
                    Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(init_var.clone().into())),
                );
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
        let result = l
            .alloc(source, Exp::AbstractLocalVar(AbstractLocalVar::Result { typ: adt_ty.clone() }));
        let eq = {
            let final_args = init_vars[1..]
                .iter()
                .map(|v| {
                    l.alloc(
                        source,
                        Exp::AbstractLocalVar(AbstractLocalVar::LocalVar(v.clone().into())),
                    )
                })
                .collect();
            l.alloc(
                source,
                Exp::new_func_app(mangle::mangled_adt(db, adt) + "_unsafe_init", final_args),
            )
        };
        l.alloc(source, Exp::eq_cmp(result, eq))
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
}

fn impure_struct(
    db: &dyn crate::Db,
    l: &mut BodyLower,
    adt: Adt,
    self_slot: mir::SlotId,
    invariants: impl IntoIterator<Item = mir::BlockId>,
) -> Result<Vec<ViperItem<VExprId>>> {
    let mut viper_items = Vec::new();

    // TODO: is this really a good source?
    let source = mir::BlockId::from_raw(0.into());
    let self_var = l.slot_to_var(self_slot)?;
    let self_var = LocalVar { name: self_var.name, typ: silvers::typ::Type::ref_() };
    let self_place = self_slot.place(db, l.ib);
    let self_ = l.alloc(source, AbstractLocalVar::LocalVar(self_var.clone()));

    l.pre_unfolded.insert(self_place);

    let field_invs: Vec<_> = adt
        .fields(db)
        .iter()
        .map(|&f| {
            let field_ty = f.ty(db);
            let ty = l.lower_type(field_ty)?;
            let viper_field = Field { name: mangle::mangled_adt_field(db, adt, f), typ: ty.vty };
            viper_items.push(ViperItem::Field(viper_field.clone()));
            let perm = l.alloc(source, PermExp::Full);
            let field_access = FieldAccess::new(self_, viper_field);
            let field_perm = l.alloc(source, field_access.clone().access_perm(perm));

            let field_ref = l.alloc(source, field_access.access_exp());
            Ok(if let (Some(cond), _) = l.ty_to_condition(source, field_ref, field_ty)? {
                l.alloc(source, Exp::bin(field_perm, BinOp::And, cond))
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
        .reduce(|acc, next| l.alloc(source, Exp::bin(acc, BinOp::And, next)));

    viper_items.push(ViperItem::Predicate(Predicate {
        name: mangle::mangled_adt(db, adt),
        formal_args: vec![self_var.into()],
        body,
    }));

    Ok(viper_items)
}
