//! Simplification of where-clauses and parameter bounds into a prettier and
//! more canonical form.
//!
//! Currently all cross-crate-inlined function use `rustc_middle::ty` to reconstruct
//! the AST (e.g., see all of `clean::inline`), but this is not always a
//! non-lossy transformation. The current format of storage for where-clauses
//! for functions and such is simply a list of predicates. One example of this
//! is that the AST predicate of: `where T: Trait<Foo = Bar>` is encoded as:
//! `where T: Trait, <T as Trait>::Foo = Bar`.
//!
//! This module attempts to reconstruct the original where and/or parameter
//! bounds by special casing scenarios such as these. Fun!

use thin_vec::ThinVec;

use crate::clean;

/// Move bounds that are (likely) directly attached to generic parameters from the where-clause to
/// the respective parameter.
///
/// There is no guarantee that this is what the user actually wrote but we have no way of knowing.
// FIXME(fmease): It'd make a lot of sense to just incorporate this logic into `clean_ty_generics`
// making every of its users benefit from it.
pub(crate) fn move_bounds_to_generic_parameters(generics: &mut clean::Generics) {
    use clean::types::*;

    let mut where_predicates = ThinVec::new();
    for mut pred in generics.where_predicates.drain(..) {
        if let WherePredicate::BoundPredicate { ty: Generic(arg), bounds, .. } = &mut pred
            && let Some(GenericParamDef {
                kind: GenericParamDefKind::Type { bounds: param_bounds, .. },
                ..
            }) = generics.params.iter_mut().find(|param| &param.name == arg)
        {
            param_bounds.extend(bounds.drain(..));
        } else if let WherePredicate::RegionPredicate { lifetime: Lifetime(arg), bounds } =
            &mut pred
            && let Some(GenericParamDef {
                kind: GenericParamDefKind::Lifetime { outlives: param_bounds },
                ..
            }) = generics.params.iter_mut().find(|param| &param.name == arg)
        {
            param_bounds.extend(bounds.drain(..).map(|bound| match bound {
                GenericBound::Outlives(lifetime) => lifetime,
                _ => unreachable!(),
            }));
        } else {
            where_predicates.push(pred);
        }
    }
    generics.where_predicates = where_predicates;
}
