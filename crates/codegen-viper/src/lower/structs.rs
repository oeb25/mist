use mist_core::{mir, mono::types::Adt, util::IdxWrap};
use silvers::{
    expression::{AbstractLocalVar, BinOp, Exp, FieldAccess, LocalVar, PermExp},
    program::{Field, Predicate},
};

use crate::{
    gen::{VExprId, ViperItem},
    mangle,
};

use super::{BodyLower, Result};

impl BodyLower<'_> {
    pub fn adt_lower(
        &mut self,
        adt: Adt,
        invariants: impl IntoIterator<Item = mir::BlockId>,
    ) -> Result<Vec<ViperItem<VExprId>>> {
        let mut viper_items = vec![];

        let source = mir::BlockId::from_raw(0.into());
        let self_slot = self.body.self_slot();
        let self_var = self.slot_to_var(self_slot)?;
        let self_var = LocalVar { name: self_var.name, typ: silvers::typ::Type::ref_() };
        let self_ = self.alloc(source, AbstractLocalVar::LocalVar(self_var.clone()));

        self.pre_unfolded.insert(self_slot.into());

        let field_invs: Vec<_> = adt
            .fields(self.db)
            .iter()
            .map(|&f| {
                let field_ty = f.ty(self.db);
                let ty = self.lower_type(field_ty)?;
                let viper_field =
                    Field { name: mangle::mangled_adt_field(self.db, adt, f), typ: ty.vty };
                viper_items.push(ViperItem::Field(viper_field.clone()));
                let perm = self.alloc(source, PermExp::Full);
                let field_access = FieldAccess::new(self_, viper_field);
                let field_perm = self.alloc(source, field_access.clone().access_perm(perm));

                let field_ref = self.alloc(source, field_access.access_exp());
                Ok(if let (Some(cond), _) = self.ty_to_condition(source, field_ref, field_ty)? {
                    self.alloc(source, Exp::bin(field_perm, BinOp::And, cond))
                } else {
                    field_perm
                })
            })
            .collect::<Result<Vec<_>>>()?;
        let inv_invs: Vec<_> =
            invariants.into_iter().map(|inv| self.pure_lower(inv)).collect::<Result<_>>()?;
        let body = field_invs
            .into_iter()
            .chain(inv_invs)
            .reduce(|acc, next| self.alloc(source, Exp::bin(acc, BinOp::And, next)));

        viper_items.push(ViperItem::Predicate(Predicate {
            name: mangle::mangled_adt(self.db, adt),
            formal_args: vec![self_var.into()],
            body,
        }));

        Ok(viper_items)
    }
}
