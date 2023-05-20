use mist_core::{
    hir,
    mir::{self, BlockId},
    util::IdxWrap,
};
use silvers::{
    expression::{AbstractLocalVar, BinOp, Exp, FieldAccess, PermExp},
    program::{Field, Predicate},
};

use crate::gen::{VExprId, ViperItem};

use super::{BodyLower, Result};

impl BodyLower<'_> {
    pub fn struct_lower(
        &mut self,
        s: hir::Struct,
        invariants: impl IntoIterator<Item = mir::BlockId>,
    ) -> Result<Vec<ViperItem<VExprId>>> {
        let mut viper_items = vec![];

        let source = BlockId::from_raw(0.into());
        let self_slot = self.body.self_slot().expect("self slot must be set");
        let self_var = self.slot_to_var(self_slot)?;
        let self_ = self.alloc(source, AbstractLocalVar::LocalVar(self_var.clone()));

        self.pre_unfolded.insert(self_slot.into());

        let field_invs: Vec<_> = hir::struct_fields(self.db, s)
            .into_iter()
            .map(|f| {
                let field_ty = self.cx.field_ty(&f);
                let ty = self.lower_type(field_ty)?;
                let viper_field = Field {
                    name: f.name.to_string(),
                    typ: ty.vty,
                };
                viper_items.push(ViperItem::Field(viper_field.clone()));
                let perm = self.alloc(source, PermExp::Full);
                let field_access = FieldAccess::new(self_, viper_field);
                let field_perm = self.alloc(source, field_access.clone().access_perm(perm));

                let field_ref = self.alloc(source, field_access.access_exp());
                Ok(
                    if let (Some(cond), _) = self.ty_to_condition(source, field_ref, field_ty)? {
                        self.alloc(source, Exp::bin(field_perm, BinOp::And, cond))
                    } else {
                        field_perm
                    },
                )
            })
            .collect::<Result<Vec<_>>>()?;
        let inv_invs: Vec<_> = invariants
            .into_iter()
            .map(|inv| self.pure_lower(inv))
            .collect::<Result<_>>()?;
        let body = field_invs
            .into_iter()
            .chain(inv_invs)
            .reduce(|acc, next| self.alloc(source, Exp::bin(acc, BinOp::And, next)));

        viper_items.push(ViperItem::Predicate(Predicate {
            name: s.name(self.db).to_string(),
            formal_args: vec![self_var.into()],
            body,
        }));

        Ok(viper_items)
    }
}
