use itertools::Itertools;
use mist_core::{hir, mir::BlockId};
use silvers::{
    expression::{
        AbstractLocalVar, AccessPredicate, BinOp, Exp, FieldAccess, FieldAccessPredicate, LocalVar,
        PermExp,
    },
    program::{Field, Predicate},
    typ::Type as VTy,
};

use crate::gen::{VExpr, VExprId, ViperItem};

use super::{BodyLower, ViperLowerError};

impl BodyLower<'_> {
    pub fn struct_lower(
        &mut self,
        program: hir::Program,
        s: hir::Struct,
        invariants: impl IntoIterator<Item = hir::TypeInvariant>,
    ) -> Result<Vec<ViperItem<VExprId>>, ViperLowerError> {
        let mut viper_items = vec![];

        let source = BlockId::from_raw(0.into());
        let this_var = LocalVar::new("this".to_string(), VTy::ref_());
        let this = self.alloc(
            source,
            VExpr::new(Exp::new_abstract_local_var(AbstractLocalVar::LocalVar(
                this_var.clone(),
            ))),
        );

        let body = hir::struct_fields(self.db, program, s)
            .into_iter()
            .map(|f| {
                let ty = self.lower_type(f.ty);
                let viper_field = Field {
                    name: f.name.to_string(),
                    typ: ty.vty,
                };
                viper_items.push(ViperItem::Field(viper_field.clone()));
                let perm = self.alloc(source, VExpr::new(Exp::Perm(PermExp::Full)));
                self.alloc(
                    source,
                    VExpr::new(Exp::new_access_predicate(AccessPredicate::Field(
                        FieldAccessPredicate {
                            loc: FieldAccess {
                                rcr: this,
                                field: viper_field,
                            },
                            perm,
                        },
                    ))),
                )
            })
            .collect_vec()
            .into_iter()
            .reduce(|acc, next| self.alloc(source, VExpr::new(Exp::bin(acc, BinOp::And, next))));

        viper_items.push(ViperItem::Predicate(Predicate {
            name: s.name(self.db).to_string(),
            formal_args: vec![this_var.into()],
            body,
        }));

        Ok(viper_items)
    }
}
