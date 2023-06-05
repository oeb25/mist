use std::iter;

use mist_core::{
    def::{self, Struct, StructField},
    mir,
    types::TypeProvider,
    util::IdxWrap,
};
use silvers::{
    expression::{
        AbstractLocalVar, AccessPredicate, BinOp, Exp, FieldAccess, Literal, LocalVar, PermExp,
        PredicateAccess, PredicateAccessPredicate,
    },
    program::{Field, LocalVarDecl, Method, Predicate},
};

use crate::{
    gen::{VExprId, ViperItem},
    mangle,
};

use super::{BodyLower, Result};

impl BodyLower<'_> {
    pub fn struct_lower(
        &mut self,
        s: def::Struct,
        invariants: impl IntoIterator<Item = mir::BlockId>,
    ) -> Result<Vec<ViperItem<VExprId>>> {
        let mut viper_items = vec![];

        let source = mir::BlockId::from_raw(0.into());
        let self_slot = self.body.self_slot().expect("self slot must be set");
        let self_var = self.slot_to_var(self_slot)?;
        let self_ = self.alloc(source, AbstractLocalVar::LocalVar(self_var.clone()));
        let method_returns = LocalVar::new("res".to_string(), self_var.typ.clone());

        self.pre_unfolded.insert(self_slot.into());

        let mut field_invs = Vec::new();
        let mut method_formal_args = vec![self_var.clone().into()];

        for f in s.fields(self.db) {
            let field_ty = self.body.field_ty_ptr(f.into());
            let ty = self.lower_type(field_ty)?;
            let viper_field = Field { name: mangle::mangled_field(self.db, f), typ: ty.vty };
            viper_items.push(ViperItem::Field(viper_field.clone()));
            let perm = self.alloc(source, PermExp::Full);
            let field_access = FieldAccess::new(self_, viper_field.clone());
            let field_perm = self.alloc(source, field_access.clone().access_perm(perm));

            let field_ref = self.alloc(source, field_access.access_exp());
            field_invs.push(
                if let (Some(cond), _) = self.ty_to_condition(source, field_ref, field_ty)? {
                    self.alloc(source, Exp::bin(field_perm, BinOp::And, cond))
                } else {
                    field_perm
                },
            );
            method_formal_args
                .push(LocalVarDecl::new(format!("_{}", viper_field.name), viper_field.typ));
        }
        let inv_invs: Vec<_> =
            invariants.into_iter().map(|inv| self.pure_lower(inv)).collect::<Result<_>>()?;
        let body = field_invs
            .iter()
            .chain(inv_invs.iter())
            .copied()
            .reduce(|acc, next| self.alloc(source, Exp::bin(acc, BinOp::And, next)));

        viper_items.push(ViperItem::Predicate(Predicate {
            name: mangle::mangled_struct(self.db, s),
            formal_args: vec![self_var.into()],
            body,
        }));

        let method_pres = inv_invs;

        let full_perm = self.alloc(source, PermExp::Full);
        let method_returns_var =
            self.alloc(source, AbstractLocalVar::LocalVar(method_returns.clone()));
        let posts = vec![
            self.alloc(
                source,
                AccessPredicate::Predicate(PredicateAccessPredicate::new(
                    PredicateAccess::new(mangle::mangled_struct(self.db, s), vec![self_]),
                    full_perm,
                )),
            ),
            self.alloc(source, Exp::bin(self_, BinOp::EqCmp, method_returns_var)),
        ];

        viper_items.push(ViperItem::Method(Method {
            name: init_struct_name(self, s),
            formal_args: method_formal_args,
            formal_returns: vec![method_returns.into()],
            pres: method_pres,
            posts,
            body: None,
        }));

        Ok(viper_items)
    }
}

fn init_struct_name(b: &mut BodyLower, s: Struct) -> String {
    format!("init_{}", mangle::mangled_struct(b.db, s))
}

pub(super) fn init_struct_call(
    b: &mut BodyLower,
    inst: mir::InstructionId,
    s: Struct,
    fields: &[(StructField, mir::Operand)],
) -> Result<Exp<VExprId>> {
    let funcname = init_struct_name(b, s);
    let args = iter::once(Ok(b.alloc(inst, Literal::Null)))
        .chain(fields.iter().map(|(_, s)| b.operand_to_ref(inst, s)))
        .collect::<Result<_>>()?;
    Ok(Exp::FuncApp { funcname, args })
}
