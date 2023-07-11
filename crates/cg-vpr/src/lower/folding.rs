use mist_core::{mir, mono::types::Adt};
use silvers::{
    expression::{
        AbstractLocalVar, Exp, LocalVar, PermExp, PredicateAccess, PredicateAccessPredicate,
    },
    statement::Stmt,
    typ::Type as VTy,
};

use crate::{gen::VExprId, mangle};

use super::{pure::PureLowerResult, BodyLower, Result};

pub(super) fn fold_stmt(
    db: &dyn crate::Db,
    l: &mut BodyLower,
    folding: mir::Folding,
) -> Result<Option<Stmt<VExprId>>> {
    let p = match folding {
        mir::Folding::Fold { into, .. } => into,
        mir::Folding::Unfold { consume, .. } => consume,
    };
    if let Some(adt) = p.ty().ty_adt(db) {
        if !adt.is_pure(db) {
            if p.ty().is_shared_ref(db) {
                let ptr = if p.has_projection(db) {
                    l.place_to_ref(p)?
                } else {
                    let local_var = l.local_to_var(p.local())?;
                    l.allocs(AbstractLocalVar::LocalVar(local_var))
                };
                let perm = l.allocs(PermExp::Full);

                let exp = match folding {
                    mir::Folding::Fold { .. } => q_ref_fold(db, l, adt, ptr, perm),
                    mir::Folding::Unfold { .. } => q_ref_unfold(db, l, adt, ptr, perm),
                };
                return Ok(Some(Stmt::Expression(exp)));
            } else {
                let name = mangle::mangled_adt(db, adt);
                let place_ref = l.place_to_ref(p)?;
                let acc = PredicateAccessPredicate::new(
                    PredicateAccess::new(name, vec![place_ref]),
                    l.allocs(PermExp::Full),
                );

                return Ok(Some(match folding {
                    mir::Folding::Fold { .. } => Stmt::Fold { acc },
                    mir::Folding::Unfold { .. } => Stmt::Unfold { acc },
                }));
            }
        }
    }

    Ok(None)
}

pub(super) fn folding_expr(
    db: &dyn crate::Db,
    l: &mut BodyLower,
    acc: PureLowerResult,
    folding: mir::Folding,
) -> Result<PureLowerResult> {
    let unfolding_place = match folding {
        mir::Folding::Unfold { consume, .. } if !l.pre_unfolded.contains(&consume) => consume,
        _ => return Ok(acc),
    };
    match unfolding_place.ty().ty_adt(db) {
        Some(adt) if !adt.is_pure(db) => acc.try_map_exp(|exp| {
            if unfolding_place.ty().is_shared_ref(db) {
                let ptr = if unfolding_place.has_projection(db) {
                    l.place_to_ref(unfolding_place)?
                } else {
                    let local_var = l.local_to_var(unfolding_place.local())?;
                    l.allocs(AbstractLocalVar::LocalVar(local_var))
                };
                let perm = l.allocs(PermExp::Wildcard);
                Ok(q_ref_unfolding(l.db, l, adt, ptr, perm, exp))
            } else {
                let place_ref = l.place_to_ref(unfolding_place)?;
                let pred_acc = PredicateAccessPredicate::new(
                    PredicateAccess::new(mangle::mangled_adt(db, adt), vec![place_ref]),
                    l.allocs(PermExp::Wildcard),
                );

                Ok(l.allocs(Exp::new_unfolding(pred_acc, exp)))
            }
        }),
        _ => Ok(acc),
    }
}

pub(super) fn q_ref_unfolding(
    db: &dyn crate::Db,
    l: &mut BodyLower,
    adt: Adt,
    ptr: VExprId,
    _perm: VExprId,
    in_expr: VExprId,
) -> VExprId {
    let e_1 = l.allocs(Exp::Literal(silvers::expression::Literal::Int(1)));
    let e_256 = l.allocs(Exp::Literal(silvers::expression::Literal::Int(256)));
    let perm = l.allocs(Exp::Perm(PermExp::Bin {
        op: silvers::expression::PermOp::Div,
        left: Box::new(PermExp::Exp(e_1)),
        right: Box::new(PermExp::Exp(e_256)),
    }));
    let pred = l.allocs(Exp::AbstractLocalVar(silvers::expression::AbstractLocalVar::LocalVar(
        LocalVar { name: mangle::mangled_adt(db, adt), typ: VTy::ref_() },
    )));
    l.allocs(Exp::new_func_app("QRefUnfolding".to_owned(), vec![pred, ptr, perm, in_expr]))
}
fn q_ref_fold(
    db: &dyn crate::Db,
    l: &mut BodyLower,
    adt: Adt,
    ptr: VExprId,
    perm: VExprId,
) -> VExprId {
    let pred = l.allocs(Exp::AbstractLocalVar(silvers::expression::AbstractLocalVar::LocalVar(
        LocalVar { name: mangle::mangled_adt(db, adt), typ: VTy::ref_() },
    )));
    l.allocs(Exp::new_func_app("QRefFold".to_owned(), vec![pred, ptr, perm]))
}
fn q_ref_unfold(
    db: &dyn crate::Db,
    l: &mut BodyLower,
    adt: Adt,
    ptr: VExprId,
    perm: VExprId,
) -> VExprId {
    let pred = l.allocs(Exp::AbstractLocalVar(silvers::expression::AbstractLocalVar::LocalVar(
        LocalVar { name: mangle::mangled_adt(db, adt), typ: VTy::ref_() },
    )));
    l.allocs(Exp::new_func_app("QRefUnfold".to_owned(), vec![pred, ptr, perm]))
}

pub(super) fn q_ref_acc(
    db: &dyn crate::Db,
    l: &mut BodyLower,
    adt: Adt,
    ptr: VExprId,
    perm: VExprId,
) -> VExprId {
    let ptr = q_ref_strip_value(l, ptr);
    let pred = l.allocs(Exp::AbstractLocalVar(silvers::expression::AbstractLocalVar::LocalVar(
        LocalVar { name: mangle::mangled_adt(db, adt), typ: VTy::ref_() },
    )));
    l.allocs(Exp::new_func_app("QRefAcc".to_owned(), vec![pred, ptr, perm]))
}

pub(super) fn q_ref_value(l: &mut BodyLower<'_>, ptr: VExprId) -> VExprId {
    l.allocs(Exp::FuncApp { funcname: "fst".to_string(), args: vec![ptr] })
}
pub(super) fn q_ref_strip_value(l: &mut BodyLower<'_>, ptr: VExprId) -> VExprId {
    match &l.viper_body[ptr].data {
        Exp::FuncApp { funcname, args } if funcname == "fst" => args[0],
        _ => ptr,
    }
}
pub(super) fn q_ref_perm(l: &mut BodyLower<'_>, ptr: VExprId) -> VExprId {
    l.allocs(Exp::FuncApp { funcname: "snd".to_string(), args: vec![ptr] })
}
