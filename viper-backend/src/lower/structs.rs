use itertools::Itertools;
use mist_core::{hir, mir::BlockId, util::IdxWrap};
use silvers::{
    expression::{AbstractLocalVar, BinOp, Exp, FieldAccess, LocalVar, PermExp},
    program::{Field, Predicate},
    typ::Type as VTy,
};

use crate::gen::{VExprId, ViperItem};

use super::{BodyLower, ViperLowerError};

impl BodyLower<'_> {
    pub fn struct_lower(
        &mut self,
        s: hir::Struct,
        invariants: impl IntoIterator<Item = hir::TypeInvariant>,
    ) -> Result<Vec<ViperItem<VExprId>>, ViperLowerError> {
        let mut viper_items = vec![];

        let source = BlockId::from_raw(0.into());
        let this_var = LocalVar::new("this".to_string(), VTy::ref_());
        let this = self.alloc(source, AbstractLocalVar::LocalVar(this_var.clone()));

        let body = hir::struct_fields(self.db, s)
            .into_iter()
            .map(|f| {
                let field_ty = self.cx.field_ty(&f);
                let ty = self.lower_type(field_ty);
                let viper_field = Field {
                    name: f.name.to_string(),
                    typ: ty.vty,
                };
                viper_items.push(ViperItem::Field(viper_field.clone()));
                let perm = self.alloc(source, PermExp::Full);
                let field_access = FieldAccess::new(this, viper_field);
                let field_perm = self.alloc(source, field_access.clone().access_perm(perm));

                let field_ref = self.alloc(source, field_access.access_exp());
                if let (Some(cond), _) = self.ty_to_condition(source, field_ref, field_ty) {
                    self.alloc(source, Exp::bin(field_perm, BinOp::And, cond))
                } else {
                    field_perm
                }
            })
            .collect_vec()
            .into_iter()
            .reduce(|acc, next| self.alloc(source, Exp::bin(acc, BinOp::And, next)));

        viper_items.push(ViperItem::Predicate(Predicate {
            name: s.name(self.db).to_string(),
            formal_args: vec![this_var.into()],
            body,
        }));

        Ok(viper_items)
    }
}
