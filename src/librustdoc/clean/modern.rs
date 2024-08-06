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

// FIXME: experiment
pub(super) trait CleanPredicate<'tcx> {
    fn elide_sized_bound_on(&mut self, ty: ty::Binder<'tcx, Ty<'tcx>>) -> bool;
}

////////////// FIXME: temporary location

#[derive(Default)]
pub(super) struct WhereClause {
    pub(super) sized: UnordSet<u32>,
}

impl<'tcx> CleanPredicate<'tcx> for WhereClause {
    fn elide_sized_bound_on(&mut self, ty: ty::Binder<'tcx, Ty<'tcx>>) -> bool {
        if let ty::Param(param_ty) = *ty.skip_binder().kind()
            && param_ty.name != kw::SelfUpper
        {
            self.sized.insert(param_ty.index);
            return true;
        }
        false
    }
}

#[derive(Default)]
pub(super) struct Apit {
    sized: bool,
}

impl<'tcx> CleanPredicate<'tcx> for Apit {
    fn elide_sized_bound_on(&mut self, ty: ty::Binder<'tcx, Ty<'tcx>>) -> bool {
        if let ty::Param(_) = ty.skip_binder().kind() {
            self.sized = true;
            return true;
        }
        false
    }
}

#[derive(Default)]
pub(super) struct OpaqueTy {
    sized: bool,
}

impl<'tcx> CleanPredicate<'tcx> for OpaqueTy {
    fn elide_sized_bound_on(&mut self, ty: ty::Binder<'tcx, Ty<'tcx>>) -> bool {
        // FIXME: is this correct?
        if let ty::Alias(ty::Opaque, _) = ty.skip_binder().kind() {
            eprintln!("HIT!");
            self.sized = true;
            return true;
        }
        false
    }
}

//////////////

// FIXME: we overflow the stack on RPITITs :(

// FIXME: We 'need' to support arbitrarily nested ATBs
//        like `A<T: B<U: C>>`

pub(super) fn clean_predicates<'tcx, C: CleanPredicate<'tcx>>(
    cx: &mut DocContext<'tcx>,
    mut predicates: Vec<(ty::Clause<'tcx>, Span)>,
    cleaner: &mut C,
) -> ThinVec<WherePredicate> {
    // FIXME: Ideally we'd only sort here if the item is an impl block (NB: def_kind() isn't reliable here
    // bc the "item_def_id" doesn't refer to an impl block if this impl was synth'ed by auto_trait).
    // FIXME: Also explain why we're doing this (at least for impls): namely `gather_explicit_predicates_of`
    // reorders preds via `cgp::setup_constraining_predicates` if it's an impl
    predicates.sort_by_key(|&(_, span)| span);

    let mut clauses = Default::default();

    for (predicate, span) in predicates {
        group_predicate(cx.tcx, predicate, span, &mut clauses, cleaner);
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
            Clause::BoundedTy { ty, bounds, .. } => clean_ty_clause(cx, ty, bounds, cleaner),
            Clause::BoundedRe { re, bounds } => Some(clean_re_clause(re, bounds)),
        })
        .collect()
}

// FIXME: horrendous name
fn group_predicate<'tcx, C: CleanPredicate<'tcx>>(
    tcx: TyCtxt<'tcx>,
    predicate: ty::Clause<'tcx>,
    span: Span,
    clauses: &mut Vec<Clause<'tcx>>, // FIXME: ugly out param
    cleaner: &mut C,
) {
    let kind = predicate.kind();
    match kind.skip_binder() {
        // FIXME(fmease): Acknowledge that we intentionally ignore polarity!
        ty::ClauseKind::Trait(pred) => {
            let pred = kind.rebind(pred);
            let bounded_ty = pred.self_ty();

            // FIXME: properly implement this
            if tcx.is_lang_item(pred.def_id(), rustc_hir::LangItem::Sized)
                && cleaner.elide_sized_bound_on(bounded_ty)
            {
                // FIXME: Instead of unconditionally dropping `Sized` bounds, we could make it so
                // we only drop synthetic ones (by checking if the Span coincides with the span of
                // the type parameter if the bounded ty is a type parameter).
                // FIXME: Add back explainer about implicit Sized from mod simplify
                return;
            }

            // FIXME: I don't think this can handle `Trait<AssocTy: Trait<Inner = ()>>` (namely `Inner == ()`)
            // FIXME: does this scale to assoc tys? we might want to allow the caller to specify
            // the "base bounded ty" (Param for Normal&APIT, Alias(Opaque) for RPIT(IT?), Alias(Projection) for assoc ty item bounds)
            if let ty::Alias(ty::Projection, alias_ty) = *bounded_ty.skip_binder().kind()
                && let Some(Clause::BoundedTy { bounds, span: clause_span, .. }) = clauses.last_mut()
                && clause_span.contains(span) // FIXME: explainer
                && let Some(Bound::Trait(trait_ref, constraints)) = bounds.last_mut()
                // FIXME: explain why skip_binder is okay here (relates to comment above)
                && is_instance_of(tcx, trait_ref.skip_binder(), alias_ty.trait_ref(tcx))
            {
                // FIXME: support constraints on this bound
                let bound = Bound::Trait(pred.to_poly_trait_ref(), Vec::new());
                let bounded_alias_ty = pred.rebind(alias_ty);

                if let Some(Constraint::Bounds(alias_ty, alias_bounds)) = constraints.last_mut()
                    // FIXME: Audit (do we need to use is_instance of)
                    && *alias_ty == bounded_alias_ty //FIXME bad naming left<->right (both are bounded)
                {
                    alias_bounds.push(bound);
                } else {
                    constraints.push(Constraint::Bounds(bounded_alias_ty, vec![bound]));
                }
                return;
            }

            // FIXME: Skip `Destruct` here
            //     // `T: ~const Destruct` is hidden because `T: Destruct` is a no-op.
            //     // FIXME(effects) check constness
            //     if tcx.is_lang_item(pred.def_id(), hir::LangItem::Destruct) {
            //         return None;
            //     }

            let bound = Bound::Trait(pred.to_poly_trait_ref(), Vec::new());

            if let Some(Clause::BoundedTy { ty, bounds, .. }) = clauses.last_mut()
                && *ty == bounded_ty // FIXME: explain why `==` is okay here
            {
                bounds.push(bound);
            } else {
                clauses.push(Clause::BoundedTy { ty: bounded_ty, bounds: vec![bound], span });
            }
        }
        ty::ClauseKind::Projection(pred) => {
            // FIXME: explain why it's fine to ignore polarity
            if let Some(Clause::BoundedTy { bounds, .. }) = clauses.last_mut()
                && let Some(Bound::Trait(trait_ref, constraints)) = bounds.last_mut()
                // FIXME: Explain why this seems to be necessary
                // FIXME: is skip_binder ok?? feels fishy
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

            if let ty::Alias(ty::Projection, alias_ty) = *bounded_ty.skip_binder().kind()
                && let Some(Clause::BoundedTy { bounds, span: clause_span, .. }) = clauses.last_mut()
                && clause_span.contains(span) // FIXME: explainer
                && let Some(Bound::Trait(trait_ref, constraints)) = bounds.last_mut()
                // FIXME: explain why skip_binder is okay here (relates to comment above)
                && is_instance_of(tcx, trait_ref.skip_binder(), alias_ty.trait_ref(tcx))
            {
                let bound = Bound::Outlives(bound);
                let bounded_alias_ty = bounded_ty.rebind(alias_ty);

                if let Some(Constraint::Bounds(alias_ty, alias_bounds)) = constraints.last_mut()
                    // FIXME: Audit (do we need to use is_instance of)
                    && *alias_ty == bounded_alias_ty //FIXME bad naming left<->right (both are bounded)
                {
                    alias_bounds.push(bound);
                } else {
                    constraints.push(Constraint::Bounds(bounded_alias_ty, vec![bound]));
                }
                return;
            }

            if let Some(Clause::BoundedTy { ty, bounds, .. }) = clauses.last_mut()
                && *ty == bounded_ty // FIXME: explain why `==` is okay here
            {
                bounds.push(Bound::Outlives(bound));
            } else {
                clauses.push(Clause::BoundedTy { ty: bounded_ty, bounds: vec![Bound::Outlives(bound)], span });
            }
        }
        ty::ClauseKind::ConstArgHasType(_, _)
        | ty::ClauseKind::WellFormed(_)
        // FIXME(fmease): Check if we need to reify this for GCEs
        | ty::ClauseKind::ConstEvaluatable(_) => {}
    }
}

fn clean_ty_clause<'tcx, C: CleanPredicate<'tcx>>(
    cx: &mut DocContext<'tcx>,
    bounded_ty: ty::Binder<'tcx, Ty<'tcx>>,
    bounds: Vec<Bound<'tcx>>,
    _cleaner: &mut C, // FIXME
) -> Option<super::WherePredicate> {
    let bounds: Vec<_> = bounds.into_iter().map(|bound| clean_bound(cx, bound)).collect();

    // FIXME: doing this in here isn't great... bc this leads to duplicate efforts
    // if we don't have any preds (e.g., `X<T: ?Sized>`) where we need to go through all
    // "generics" "anyway" (NB: this module doesn't have a notion of "generics"!!!)
    // if let ty::Param(param_ty) = bounded_ty.skip_binder().kind()
    //     && param_ty.name != kw::SelfUpper
    //     // FIXME: HACK
    //     && sized.insert(param_ty.index)
    // {
    //     bounds.push(GenericBound::maybe_sized(cx));
    // }

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

fn clean_bound<'tcx>(cx: &mut DocContext<'tcx>, bound: Bound<'tcx>) -> GenericBound {
    match bound {
        // FIXME: filter out non-const Destruct
        Bound::Trait(trait_ref, constraints) => {
            let constraints = constraints
                .into_iter()
                .map(|constraint| clean_assoc_item_constraint(cx, constraint))
                .collect();

            clean_poly_trait_ref_with_constraints(cx, trait_ref, constraints)
        }
        Bound::Outlives(bound) => {
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
                bounds: bounds.into_iter().map(|bound| clean_bound(cx, bound)).collect(),
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
    BoundedTy { ty: ty::Binder<'tcx, Ty<'tcx>>, bounds: Vec<Bound<'tcx>>, span: Span }, // maybe record "outer bound var candidates"
    BoundedRe { re: ty::Region<'tcx>, bounds: Vec<ty::Region<'tcx>> },
}

enum Bound<'tcx> {
    Trait(ty::PolyTraitRef<'tcx>, Vec<Constraint<'tcx>>),
    Outlives(ty::Region<'tcx>),
}

// FIXME: bad name, I guess
enum Constraint<'tcx> {
    Equality(ty::Binder<'tcx, ty::ProjectionPredicate<'tcx>>),
    Bounds(ty::Binder<'tcx, ty::AliasTy<'tcx>>, Vec<Bound<'tcx>>),
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
