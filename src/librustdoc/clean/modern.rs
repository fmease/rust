#![allow(dead_code)] // FIXME

use rustc_data_structures::unord::UnordSet;
use rustc_middle::ty::{self, ToPolyTraitRef, Ty, TyCtxt};
use rustc_span::symbol::kw;
use rustc_span::Span;
use thin_vec::ThinVec;

use super::{
    clean_middle_region, clean_middle_term, clean_middle_ty, clean_poly_trait_ref_with_constraints,
    projection_to_path_segment, AssocItemConstraint, AssocItemConstraintKind, GenericBound,
    WherePredicate,
};
use crate::core::DocContext;

// FIXME(return_type_notation, #123996): Support RTN.
// FIXME(async_closure): De-lower `AsyncFn*` bounds to `async Fn*` ones.

pub(super) fn clean_predicates<'tcx>(
    cx: &mut DocContext<'tcx>,
    mut predicates: Vec<(ty::Clause<'tcx>, Span)>,
) -> ThinVec<WherePredicate> {
    // FIXME: Ideally we'd only sort here if the item is an impl block (NB: def_kind() isn't reliable here
    // bc the "item_def_id" doesn't refer to an impl block if this impl was synth'ed by auto_trait).
    // FIXME: Also explain why we're doing this (at least for impls): namely `gather_explicit_predicates_of`
    // reorders preds via `cgp::setup_constraining_predicates` if it's an impl
    predicates.sort_by_key(|&(_, span)| span);

    let mut clauses = Default::default();
    let mut sized = Default::default();

    for (predicate, span) in predicates {
        group_predicate(cx.tcx, predicate, span, &mut clauses, &mut sized);
    }

    // FIXME: Explain that reason why we need to go over stuff twice is because
    // we first need to gather all projection predicates to be able to call
    // clean_poly_trait_with_constraints which requires a full set of constraints
    // NOTE: However, we might just get away with calling clean_poly_trait_ref
    // and pushing the constraints later (similar to `simplify::merge_bounds`).
    // FIXME: however, it makes things nicer actually to operate on ty:: things, not clean:: ones
    // (interned equality, etc)

    clauses
        .into_iter()
        .filter_map(|clause| match clause {
            Clause::BoundedTy { ty, bounds, .. } => clean_ty_clause(cx, ty, bounds, &mut sized),
            Clause::BoundedRe { re, bounds } => Some(clean_re_clause(re, bounds)),
        })
        .collect()
}

// FIXME: horrendous name
fn group_predicate<'tcx>(
    tcx: TyCtxt<'tcx>,
    predicate: ty::Clause<'tcx>,
    span: Span,
    clauses: &mut Vec<Clause<'tcx>>, // FIXME: ugly out param
    sized: &mut UnordSet<u32>,       // FIXME: ugly out param
) {
    let kind = predicate.kind();
    match kind.skip_binder() {
        // FIXME(fmease): Acknowledge that we intentionally ignore polarity!
        ty::ClauseKind::Trait(pred) => {
            let pred = kind.rebind(pred);
            let bounded_ty = pred.self_ty();

            match *bounded_ty.skip_binder().kind() {
                // FIXME: does this correctly deal with `Self`? I don't think so
                // FIXME: not only look for `ty::Param` but also for `ty::Alias(ty::Opaque)` (kinda)
                //        however, we don't want to handle that here, this should depend on the
                //        user (parametrization)
                ty::Param(param_ty) => {
                    if tcx.is_lang_item(pred.def_id(), rustc_hir::LangItem::Sized)
                        && param_ty.name != kw::SelfUpper
                    {
                        sized.insert(param_ty.index);
                        // FIXME: Instead of unconditionally dropping `Sized` bounds, we could make it so
                        // we only drop synthetic ones (by checking if the Span coincides with the span of
                        // the type parameter if the bounded ty is a type parameter).
                        return;
                    }
                }
                // FIXME: I don't think this can handle `Trait<AssocTy: Trait<Inner = ()>>` (namely `Inner == ()`)
                ty::Alias(ty::Projection, bounded_alias_ty) => {
                    if let Some(Clause::BoundedTy { bounds, span: clause_span, .. }) = clauses.last_mut()
                        && clause_span.contains(span) // FIXME: explainer // FIXME: this is not suffient we need to check instance_of
                        && let Some(TyBound::Trait(trait_ref, constraints)) = bounds.last_mut()
                        // FIXME: explain why skip_binder is okay here (relates to comment above)
                        && is_instance_of(tcx, trait_ref.skip_binder(), bounded_alias_ty.trait_ref(tcx))
                    {
                        // FIXME: ^ support constraints on this bound ^^'
                        let bound = pred.to_poly_trait_ref();
                        let bounded_alias_ty = pred.rebind(bounded_alias_ty);

                        if let Some(Constraint::Bounds(alias_ty, alias_bounds)) = constraints.last_mut()
                            // FIXME: Audit (do we need to use is_instance of)
                            && *alias_ty == bounded_alias_ty
                        {
                            alias_bounds.push(bound);
                        } else {
                            constraints.push(Constraint::Bounds(bounded_alias_ty, vec![bound]));
                        }
                        return;
                    }
                }
                _ => {}
            }

            // FIXME: Skip `Destruct` here
            //     // `T: ~const Destruct` is hidden because `T: Destruct` is a no-op.
            //     // FIXME(effects) check constness
            //     if tcx.is_lang_item(pred.def_id(), hir::LangItem::Destruct) {
            //         return None;
            //     }

            let bound = TyBound::Trait(pred.to_poly_trait_ref(), Vec::new());

            if let Some(Clause::BoundedTy { ty, bounds, .. }) = clauses.last_mut()
                && *ty == bounded_ty // FIXME: explain why `==` is okay here
            {
                bounds.push(bound);
            } else {
                clauses.push(Clause::BoundedTy { ty: bounded_ty, bounds: vec![bound], span });
            }
        }
        ty::ClauseKind::Projection(pred) => {
            // FIXME: explain why `no_bound_vars` is not correct here (I think)
            // FIXME: Add note: Projections don't support binders (yet).
            //        Would be (surface) `T: Trait<for<'a> T<'a> = &'a ()>`
            //        (contrary to `for<'a> T: ...` or `T: for<'a> ...`)
            // assert!(kind.bound_vars().is_empty());

            // FIXME: explain why it's fine to ignre polarity
            if let Some(Clause::BoundedTy { bounds, .. }) = clauses.last_mut()
                && let Some(TyBound::Trait(trait_ref, constraints)) = bounds.last_mut()
                // FIXME: Explain why this seems to be necessary
                && is_instance_of(tcx, trait_ref.skip_binder(), pred.projection_term.trait_ref(tcx))
            {
                // FIXME: explain why skip_binder is okay here (relates to comment above)
                // FIXME: explain why this holds
                // FIXME: this no longer holds
                // debug_assert!(is_instance_of(tcx, trait_ref.skip_binder(), pred.projection_term.trait_ref(tcx)));

                constraints.push(Constraint::Equality(kind.rebind(pred)));
            } else {
                // FIXME: Explainer (synthetic `-> ()` has same span as trait ref, therefore they don't get placed after it).
                // FIXME: make this more robust by also checking that the trait ref is a fn-family trait ref (incl. async ones)
                // debug_assert_eq!(pred.term.as_type(), Some(tcx.types.unit));

                // FIXME: Explainer why it's fine to drop things
                // FIXME: however, make sure that `auto_trait.rs` actually conforms to the scheme
            }
        }
        ty::ClauseKind::RegionOutlives(ty::OutlivesPredicate(bounded_re, bound)) => {
            if let Some(Clause::BoundedRe { re, bounds }) = clauses.last_mut()
                && *re == bounded_re
            {
                bounds.push(bound);
            } else {
                clauses.push(Clause::BoundedRe { re: bounded_re, bounds: vec![bound] });
            }
        }
        // FIXME: We also need to look for Alias(Projection): 'a to be able to resugar
        //        associated type bounds of the form `Trait<AssocTy: 'a>`
        ty::ClauseKind::TypeOutlives(ty::OutlivesPredicate(bounded_ty, bound)) => {
            let bounded_ty = kind.rebind(bounded_ty);
            if let Some(Clause::BoundedTy { ty, bounds, .. }) = clauses.last_mut()
                && *ty == bounded_ty // FIXME: explain why `==` is okay here
            {
                bounds.push(TyBound::Outlives(bound));
            } else {
                clauses.push(Clause::BoundedTy { ty: bounded_ty, bounds: vec![TyBound::Outlives(bound)], span });
            }
        }
        ty::ClauseKind::ConstArgHasType(_, _)
        | ty::ClauseKind::WellFormed(_)
        // FIXME(fmease): Check if we need to reify this for GCEs
        | ty::ClauseKind::ConstEvaluatable(_) => {}
    }
}

fn clean_ty_clause<'tcx>(
    cx: &mut DocContext<'tcx>,
    bounded_ty: ty::Binder<'tcx, Ty<'tcx>>,
    bounds: Vec<TyBound<'tcx>>,
    sized: &mut UnordSet<u32>,
) -> Option<super::WherePredicate> {
    let mut bounds: Vec<_> = bounds.into_iter().map(|bound| clean_ty_bound(cx, bound)).collect();

    if let ty::Param(param_ty) = bounded_ty.skip_binder().kind()
        && param_ty.name != kw::SelfUpper
        // FIXME: HACK
        && sized.insert(param_ty.index)
    {
        bounds.push(GenericBound::maybe_sized(cx));
    }

    if bounds.is_empty() {
        // FIXME: We might want to keep `where T:` (user-written) (Wf).
        // However, we do need to skip here due to Sized/?Sized logic
        return None;
    }

    Some(WherePredicate::BoundPredicate {
        ty: clean_middle_ty(bounded_ty, cx, None, None),
        bounds,
        bound_params: Vec::new(), // FIXME: reconstruct outer binder
    })
}

fn clean_ty_bound<'tcx>(cx: &mut DocContext<'tcx>, bound: TyBound<'tcx>) -> GenericBound {
    match bound {
        // FIXME: filter out non-const Destruct
        TyBound::Trait(trait_ref, constraints) => {
            let constraints = constraints
                .into_iter()
                .map(|constraint| clean_assoc_item_constraint(cx, constraint))
                .collect();

            clean_poly_trait_ref_with_constraints(cx, trait_ref, constraints)
        }
        TyBound::Outlives(bound) => {
            // FIXME: expect instead of unwrap
            GenericBound::Outlives(clean_middle_region(bound).unwrap())
        }
    }
}

fn clean_assoc_item_constraint<'tcx>(
    cx: &mut DocContext<'tcx>,
    constraint: Constraint<'tcx>,
) -> AssocItemConstraint {
    match constraint {
        Constraint::Equality(proj_pred) => AssocItemConstraint {
            assoc: projection_to_path_segment(
                // FIXME: This needs to be made resilient for `AliasTerm`s that are associated consts.
                proj_pred.map_bound(|pred| pred.projection_term.expect_ty(cx.tcx)),
                cx,
            ),
            kind: AssocItemConstraintKind::Equality {
                term: clean_middle_term(proj_pred.term(), cx),
            },
        },
        Constraint::Bounds(alias_ty, bounds) => AssocItemConstraint {
            assoc: projection_to_path_segment(alias_ty, cx),
            kind: AssocItemConstraintKind::Bound {
                bounds: bounds
                    .into_iter()
                    // FIXME: support for nested constraints
                    .map(|bound| clean_poly_trait_ref_with_constraints(cx, bound, ThinVec::new()))
                    .collect(),
            },
        },
    }
}

fn clean_re_clause<'tcx>(
    bounded_re: ty::Region<'tcx>,
    bounds: Vec<ty::Region<'tcx>>,
) -> WherePredicate {
    WherePredicate::RegionPredicate {
        lifetime: clean_middle_region(bounded_re).unwrap(), // FIXME: expect
        // FIXME: expect
        bounds: bounds
            .into_iter()
            .map(|bound| GenericBound::Outlives(clean_middle_region(bound).unwrap()))
            .collect(),
    }
}

// FIXME: it's not really a "Bound" bc we duplicate self_ty for poly trait preds
// more appropriately, it's type-reindexed preds, kinda
// FIXME: explain that we have intermediary because relating clean types is slow and imprecise etc.
enum Clause<'tcx> {
    BoundedTy { ty: ty::Binder<'tcx, Ty<'tcx>>, bounds: Vec<TyBound<'tcx>>, span: Span }, // maybe record "outer bound var candidates"
    BoundedRe { re: ty::Region<'tcx>, bounds: Vec<ty::Region<'tcx>> },
}

enum TyBound<'tcx> {
    Trait(ty::PolyTraitRef<'tcx>, Vec<Constraint<'tcx>>),
    Outlives(ty::Region<'tcx>),
}

// FIXME: bad name
enum Constraint<'tcx> {
    Equality(ty::Binder<'tcx, ty::ProjectionPredicate<'tcx>>),
    Bounds(ty::Binder<'tcx, ty::AliasTy<'tcx>>, Vec<ty::PolyTraitRef<'tcx>>),
}

// FIXME(fmease): Better name
// FIXME(fmease): Docs
fn is_instance_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    child: ty::TraitRef<'tcx>,
    trait_: ty::TraitRef<'tcx>,
) -> bool {
    if child == trait_ {
        return true;
    }

    debug_assert!(tcx.generics_of(child.def_id).has_self);

    // FIXME: these are not the elaborated ones, can you find an example where this matters?
    tcx.explicit_super_predicates_of(child.def_id)
        .predicates
        .iter()
        .filter_map(|(pred, _)| {
            let ty::ClauseKind::Trait(pred) = pred.kind().skip_binder() else {
                return None;
            };
            if pred.trait_ref.self_ty() != tcx.types.self_param {
                return None;
            }

            Some(ty::EarlyBinder::bind(pred.trait_ref).instantiate(tcx, child.args))
        })
        .any(|child| is_instance_of(tcx, child, trait_))
}
