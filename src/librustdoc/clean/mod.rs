//! This module defines the primary IR[^1] used in rustdoc together with the procedures that
//! transform rustc data types into it.
//!
//! This IR — commonly referred to as the *cleaned AST* — is modeled after the [AST][ast].
//!
//! There are two kinds of transformation — *cleaning* — procedures:
//!
//! 1. Cleans [HIR][hir] types. Used for user-written code and inlined local re-exports
//!    both found in the local crate. These are defined in module [`local`].
//! 2. Cleans [`rustc_middle::ty`] types. Used for inlined cross-crate re-exports and anything
//!    output by the trait solver (e.g., when synthesizing blanket and auto-trait impls).
//!    They are defined in this module.
//!
//! Their name is prefixed by `clean_`.
//!
//! Both the HIR and the `rustc_middle::ty` IR are quite removed from the source code.
//! The cleaned AST on the other hand is closer to it which simplifies the rendering process.
//! Furthermore, operating on a single IR instead of two avoids duplicating efforts down the line.
//!
//! This IR is consumed by both the HTML and the JSON backend.
//!
//! [^1]: Intermediate representation.

mod auto_trait;
mod blanket_impl;
pub(crate) mod cfg;
pub(crate) mod inline;
pub(crate) mod local;
mod render_macro_matchers;
mod simplify;
pub(crate) mod types;
pub(crate) mod utils;

use rustc_ast as ast;
use rustc_ast::token::{Token, TokenKind};
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexSet};
use rustc_errors::FatalError;
use rustc_hir as hir;
use rustc_hir::def::{CtorKind, DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::metadata::Reexport;
use rustc_middle::middle::resolve_bound_vars as rbv;
use rustc_middle::ty::GenericArgsRef;
use rustc_middle::ty::TypeVisitableExt;
use rustc_middle::ty::{self, AdtKind, Ty, TyCtxt};
use rustc_middle::{bug, span_bug};
use rustc_span::symbol::{kw, sym, Symbol};
use rustc_trait_selection::traits::wf::object_region_bounds;

use std::assert_matches::debug_assert_matches;
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::mem;
use thin_vec::{thin_vec, ThinVec};

use crate::core::DocContext;
use crate::formats::item_type::ItemType;
use crate::visit_ast::Module as DocModule;

use utils::*;

pub(crate) use self::types::*;
pub(crate) use self::utils::{krate, register_res, synthesize_auto_trait_and_blanket_impls};

// FIXME: move into local?
pub(crate) fn clean_doc_module<'tcx>(doc: &DocModule<'tcx>, cx: &mut DocContext<'tcx>) -> Item {
    let mut items: Vec<Item> = vec![];
    let mut inserted = FxHashSet::default();
    items.extend(doc.foreigns.iter().map(|(item, renamed)| {
        let item = local::clean_foreign_item(cx, item, *renamed);
        if let Some(name) = item.name
            && (cx.render_options.document_hidden || !item.is_doc_hidden())
        {
            inserted.insert((item.type_(), name));
        }
        item
    }));
    items.extend(doc.mods.iter().filter_map(|x| {
        if !inserted.insert((ItemType::Module, x.name)) {
            return None;
        }
        let item = clean_doc_module(x, cx);
        if !cx.render_options.document_hidden && item.is_doc_hidden() {
            // Hidden modules are stripped at a later stage.
            // If a hidden module has the same name as a visible one, we want
            // to keep both of them around.
            inserted.remove(&(ItemType::Module, x.name));
        }
        Some(item)
    }));

    // Split up imports from all other items.
    //
    // This covers the case where somebody does an import which should pull in an item,
    // but there's already an item with the same namespace and same name. Rust gives
    // priority to the not-imported one, so we should, too.
    items.extend(doc.items.values().flat_map(|(item, renamed, import_id)| {
        // First, lower everything other than glob imports.
        if matches!(item.kind, hir::ItemKind::Use(_, hir::UseKind::Glob)) {
            return Vec::new();
        }
        let v = local::clean_item(cx, item, *renamed, *import_id);
        for item in &v {
            if let Some(name) = item.name
                && (cx.render_options.document_hidden || !item.is_doc_hidden())
            {
                inserted.insert((item.type_(), name));
            }
        }
        v
    }));
    items.extend(doc.inlined_foreigns.iter().flat_map(|((_, renamed), (res, local_import_id))| {
        let Some(def_id) = res.opt_def_id() else { return Vec::new() };
        let name = renamed.unwrap_or_else(|| cx.tcx.item_name(def_id));
        let import = cx.tcx.hir().expect_item(*local_import_id);
        match import.kind {
            hir::ItemKind::Use(path, kind) => {
                let hir::UsePath { segments, span, .. } = *path;
                let path = hir::Path { segments, res: *res, span };
                local::clean_use_statement_inner(
                    import,
                    name,
                    &path,
                    kind,
                    cx,
                    &mut Default::default(),
                )
            }
            _ => unreachable!(),
        }
    }));
    items.extend(doc.items.values().flat_map(|(item, renamed, _)| {
        // Now we actually lower the imports, skipping everything else.
        if let hir::ItemKind::Use(path, hir::UseKind::Glob) = item.kind {
            let name = renamed.unwrap_or_else(|| cx.tcx.hir().name(item.hir_id()));
            local::clean_use_statement(item, name, path, hir::UseKind::Glob, cx, &mut inserted)
        } else {
            // skip everything else
            Vec::new()
        }
    }));

    // determine if we should display the inner contents or
    // the outer `mod` item for the source code.

    let span = Span::new({
        let where_outer = doc.where_outer(cx.tcx);
        let sm = cx.sess().source_map();
        let outer = sm.lookup_char_pos(where_outer.lo());
        let inner = sm.lookup_char_pos(doc.where_inner.lo());
        if outer.file.start_pos == inner.file.start_pos {
            // mod foo { ... }
            where_outer
        } else {
            // mod foo; (and a separate SourceFile for the contents)
            doc.where_inner
        }
    });

    let kind = ModuleItem(Module { items, span });
    generate_item_with_correct_attrs(
        cx,
        kind,
        doc.def_id.to_def_id(),
        doc.name,
        doc.import_id,
        doc.renamed,
    )
}

fn is_glob_import(tcx: TyCtxt<'_>, import_id: LocalDefId) -> bool {
    if let hir::Node::Item(item) = tcx.hir_node_by_def_id(import_id)
        && let hir::ItemKind::Use(_, use_kind) = item.kind
    {
        use_kind == hir::UseKind::Glob
    } else {
        false
    }
}

fn generate_item_with_correct_attrs(
    cx: &mut DocContext<'_>,
    kind: ItemKind,
    def_id: DefId,
    name: Symbol,
    import_id: Option<LocalDefId>,
    renamed: Option<Symbol>,
) -> Item {
    let target_attrs = inline::load_attrs(cx, def_id);
    let attrs = if let Some(import_id) = import_id {
        // glob reexports are treated the same as `#[doc(inline)]` items.
        //
        // For glob re-exports the item may or may not exist to be re-exported (potentially the cfgs
        // on the path up until the glob can be removed, and only cfgs on the globbed item itself
        // matter), for non-inlined re-exports see #85043.
        let is_inline = inline::load_attrs(cx, import_id.to_def_id())
            .lists(sym::doc)
            .get_word_attr(sym::inline)
            .is_some()
            || (is_glob_import(cx.tcx, import_id)
                && (cx.render_options.document_hidden || !cx.tcx.is_doc_hidden(def_id)));
        let mut attrs = get_all_import_attributes(cx, import_id, def_id, is_inline);
        add_without_unwanted_attributes(&mut attrs, target_attrs, is_inline, None);
        attrs
    } else {
        // We only keep the item's attributes.
        target_attrs.iter().map(|attr| (Cow::Borrowed(attr), None)).collect()
    };

    let cfg = attrs.cfg(cx.tcx, &cx.cache.hidden_cfg);
    let attrs = Attributes::from_ast_iter(attrs.iter().map(|(attr, did)| (&**attr, *did)), false);

    let name = renamed.or(Some(name));
    let mut item = Item::from_def_id_and_attrs_and_parts(def_id, name, kind, Box::new(attrs), cfg);
    item.inline_stmt_id = import_id.map(|local| local.to_def_id());
    item
}

pub(crate) fn clean_trait_ref_with_constraints<'tcx>(
    cx: &mut DocContext<'tcx>,
    trait_ref: ty::PolyTraitRef<'tcx>,
    constraints: ThinVec<AssocItemConstraint>,
) -> Path {
    let kind = cx.tcx.def_kind(trait_ref.def_id()).into();
    if !matches!(kind, ItemType::Trait | ItemType::TraitAlias) {
        span_bug!(cx.tcx.def_span(trait_ref.def_id()), "`TraitRef` had unexpected kind {kind:?}");
    }
    inline::record_extern_fqn(cx, trait_ref.def_id(), kind);
    let path =
        clean_path(cx, trait_ref.def_id(), true, constraints, trait_ref.map_bound(|tr| tr.args));

    debug!(?trait_ref);

    path
}

fn clean_poly_trait_ref_with_constraints<'tcx>(
    cx: &mut DocContext<'tcx>,
    poly_trait_ref: ty::PolyTraitRef<'tcx>,
    constraints: ThinVec<AssocItemConstraint>,
) -> GenericBound {
    GenericBound::TraitBound(
        PolyTrait {
            trait_: clean_trait_ref_with_constraints(cx, poly_trait_ref, constraints),
            generic_params: clean_bound_vars(poly_trait_ref.bound_vars()),
        },
        hir::TraitBoundModifier::None,
    )
}

pub(crate) fn clean_const<'tcx>(
    constant: ty::Binder<'tcx, ty::Const<'tcx>>,
    _cx: &mut DocContext<'tcx>,
) -> Constant {
    // FIXME: instead of storing the stringified expression, store `self` directly instead.
    Constant { kind: ConstantKind::TyConst { expr: constant.skip_binder().to_string().into() } }
}

pub(crate) fn clean_region<'tcx>(region: ty::Region<'tcx>) -> Option<Lifetime> {
    match *region {
        ty::ReStatic => Some(Lifetime::statik()),
        _ if !region.has_name() => None,
        ty::ReBound(_, ty::BoundRegion { kind: ty::BrNamed(_, name), .. }) => Some(Lifetime(name)),
        ty::ReEarlyParam(ref data) => Some(Lifetime(data.name)),
        ty::ReBound(..)
        | ty::ReLateParam(..)
        | ty::ReVar(..)
        | ty::ReError(_)
        | ty::RePlaceholder(..)
        | ty::ReErased => {
            debug!("cannot clean region {region:?}");
            None
        }
    }
}

pub(crate) fn clean_predicate<'tcx>(
    predicate: ty::Clause<'tcx>,
    cx: &mut DocContext<'tcx>,
) -> Option<WherePredicate> {
    let bound_predicate = predicate.kind();
    match bound_predicate.skip_binder() {
        ty::ClauseKind::Trait(pred) => clean_poly_trait_predicate(bound_predicate.rebind(pred), cx),
        ty::ClauseKind::RegionOutlives(pred) => clean_region_outlives_predicate(pred),
        ty::ClauseKind::TypeOutlives(pred) => {
            clean_type_outlives_predicate(bound_predicate.rebind(pred), cx)
        }
        ty::ClauseKind::Projection(pred) => {
            Some(clean_projection_predicate(bound_predicate.rebind(pred), cx))
        }
        // FIXME(generic_const_exprs): should this do something?
        ty::ClauseKind::ConstEvaluatable(..)
        | ty::ClauseKind::WellFormed(..)
        | ty::ClauseKind::ConstArgHasType(..) => None,
    }
}

fn clean_poly_trait_predicate<'tcx>(
    pred: ty::PolyTraitPredicate<'tcx>,
    cx: &mut DocContext<'tcx>,
) -> Option<WherePredicate> {
    // `T: ~const Destruct` is hidden because `T: Destruct` is a no-op.
    // FIXME(effects) check constness
    if Some(pred.skip_binder().def_id()) == cx.tcx.lang_items().destruct_trait() {
        return None;
    }

    let poly_trait_ref = pred.map_bound(|pred| pred.trait_ref);
    Some(WherePredicate::BoundPredicate {
        ty: clean_ty(poly_trait_ref.self_ty(), cx, None, None),
        bounds: vec![clean_poly_trait_ref_with_constraints(cx, poly_trait_ref, ThinVec::new())],
        bound_params: Vec::new(),
    })
}

fn clean_region_outlives_predicate<'tcx>(
    pred: ty::RegionOutlivesPredicate<'tcx>,
) -> Option<WherePredicate> {
    let ty::OutlivesPredicate(a, b) = pred;

    Some(WherePredicate::RegionPredicate {
        lifetime: clean_region(a).expect("failed to clean lifetime"),
        bounds: vec![GenericBound::Outlives(clean_region(b).expect("failed to clean bounds"))],
    })
}

fn clean_type_outlives_predicate<'tcx>(
    pred: ty::Binder<'tcx, ty::TypeOutlivesPredicate<'tcx>>,
    cx: &mut DocContext<'tcx>,
) -> Option<WherePredicate> {
    let ty::OutlivesPredicate(ty, lt) = pred.skip_binder();

    Some(WherePredicate::BoundPredicate {
        ty: clean_ty(pred.rebind(ty), cx, None, None),
        bounds: vec![GenericBound::Outlives(clean_region(lt).expect("failed to clean lifetimes"))],
        bound_params: Vec::new(),
    })
}

fn clean_term<'tcx>(term: ty::Binder<'tcx, ty::Term<'tcx>>, cx: &mut DocContext<'tcx>) -> Term {
    match term.skip_binder().unpack() {
        ty::TermKind::Ty(ty) => Term::Type(clean_ty(term.rebind(ty), cx, None, None)),
        ty::TermKind::Const(c) => Term::Constant(clean_const(term.rebind(c), cx)),
    }
}

fn clean_projection_predicate<'tcx>(
    pred: ty::Binder<'tcx, ty::ProjectionPredicate<'tcx>>,
    cx: &mut DocContext<'tcx>,
) -> WherePredicate {
    WherePredicate::EqPredicate {
        lhs: clean_projection(
            pred.map_bound(|p| {
                // FIXME: This needs to be made resilient for `AliasTerm`s that
                // are associated consts.
                p.projection_term.expect_ty(cx.tcx)
            }),
            cx,
            None,
        ),
        rhs: clean_term(pred.map_bound(|p| p.term), cx),
    }
}

fn clean_projection<'tcx>(
    ty: ty::Binder<'tcx, ty::AliasTy<'tcx>>,
    cx: &mut DocContext<'tcx>,
    def_id: Option<DefId>,
) -> Type {
    if cx.tcx.is_impl_trait_in_trait(ty.skip_binder().def_id) {
        let bounds = cx
            .tcx
            .explicit_item_bounds(ty.skip_binder().def_id)
            .iter_instantiated_copied(cx.tcx, ty.skip_binder().args)
            .map(|(pred, _)| pred)
            .collect::<Vec<_>>();
        return clean_opaque_bounds(cx, bounds);
    }

    let trait_ = clean_trait_ref_with_constraints(
        cx,
        ty.map_bound(|ty| ty.trait_ref(cx.tcx)),
        ThinVec::new(),
    );
    let self_type = clean_ty(ty.map_bound(|ty| ty.self_ty()), cx, None, None);
    let self_def_id = if let Some(def_id) = def_id {
        cx.tcx.opt_parent(def_id).or(Some(def_id))
    } else {
        self_type.def_id(&cx.cache)
    };
    let should_show_cast = compute_should_show_cast(self_def_id, &trait_, &self_type);
    Type::QPath(Box::new(QPathData {
        assoc: projection_to_path_segment(ty, cx),
        should_show_cast,
        self_type,
        trait_: Some(trait_),
    }))
}

// FIXME: maybe move to utils?
fn compute_should_show_cast(self_def_id: Option<DefId>, trait_: &Path, self_type: &Type) -> bool {
    !trait_.segments.is_empty()
        && self_def_id
            .zip(Some(trait_.def_id()))
            .map_or(!self_type.is_self_type(), |(id, trait_)| id != trait_)
}

fn projection_to_path_segment<'tcx>(
    ty: ty::Binder<'tcx, ty::AliasTy<'tcx>>,
    cx: &mut DocContext<'tcx>,
) -> PathSegment {
    let def_id = ty.skip_binder().def_id;
    let item = cx.tcx.associated_item(def_id);
    let generics = cx.tcx.generics_of(def_id);
    PathSegment {
        name: item.name,
        args: GenericArgs::AngleBracketed {
            args: clean_generic_args(
                cx,
                ty.map_bound(|ty| &ty.args[generics.parent_count..]),
                false,
                def_id,
            )
            .into(),
            constraints: Default::default(),
        },
    }
}

fn clean_generic_param_def<'tcx>(
    def: &ty::GenericParamDef,
    defaults: ParamDefaults,
    cx: &mut DocContext<'tcx>,
) -> GenericParamDef {
    let (name, kind) = match def.kind {
        ty::GenericParamDefKind::Lifetime => {
            (def.name, GenericParamDefKind::Lifetime { outlives: ThinVec::new() })
        }
        ty::GenericParamDefKind::Type { has_default, synthetic, .. } => {
            let default = if let ParamDefaults::Yes = defaults
                && has_default
            {
                Some(clean_ty(
                    ty::Binder::dummy(cx.tcx.type_of(def.def_id).instantiate_identity()),
                    cx,
                    Some(def.def_id),
                    None,
                ))
            } else {
                None
            };
            (
                def.name,
                GenericParamDefKind::Type {
                    bounds: ThinVec::new(), // These are filled in from the where-clauses.
                    default: default.map(Box::new),
                    synthetic,
                },
            )
        }
        ty::GenericParamDefKind::Const { has_default, is_host_effect } => (
            def.name,
            GenericParamDefKind::Const {
                ty: Box::new(clean_ty(
                    ty::Binder::dummy(
                        cx.tcx
                            .type_of(def.def_id)
                            .no_bound_vars()
                            .expect("const parameter types cannot be generic"),
                    ),
                    cx,
                    Some(def.def_id),
                    None,
                )),
                default: if let ParamDefaults::Yes = defaults
                    && has_default
                {
                    Some(Box::new(
                        cx.tcx.const_param_default(def.def_id).instantiate_identity().to_string(),
                    ))
                } else {
                    None
                },
                is_host_effect,
            },
        ),
    };

    GenericParamDef { name, def_id: def.def_id, kind }
}

/// Whether to clean generic parameter defaults or not.
enum ParamDefaults {
    Yes,
    No,
}

fn clean_generics<'tcx>(
    cx: &mut DocContext<'tcx>,
    gens: &ty::Generics,
    preds: ty::GenericPredicates<'tcx>,
) -> Generics {
    // Don't populate `cx.impl_trait_bounds` before cleaning where clauses,
    // since `clean_predicate` would consume them.
    let mut impl_trait = BTreeMap::<u32, Vec<GenericBound>>::default();

    let params: ThinVec<_> = gens
        .own_params
        .iter()
        .filter(|param| match param.kind {
            ty::GenericParamDefKind::Lifetime => !param.is_anonymous_lifetime(),
            ty::GenericParamDefKind::Type { synthetic, .. } => {
                if param.name == kw::SelfUpper {
                    debug_assert_eq!(param.index, 0);
                    return false;
                }
                if synthetic {
                    impl_trait.insert(param.index, vec![]);
                    return false;
                }
                true
            }
            ty::GenericParamDefKind::Const { is_host_effect, .. } => !is_host_effect,
        })
        .map(|param| clean_generic_param_def(param, ParamDefaults::Yes, cx))
        .collect();

    // param index -> [(trait DefId, associated type name & generics, term)]
    let mut impl_trait_proj =
        FxHashMap::<u32, Vec<(DefId, PathSegment, ty::Binder<'_, ty::Term<'_>>)>>::default();

    let where_predicates = preds
        .predicates
        .iter()
        .flat_map(|(pred, _)| {
            let mut projection = None;
            let param_idx = (|| {
                let bound_p = pred.kind();
                match bound_p.skip_binder() {
                    ty::ClauseKind::Trait(pred) => {
                        if let ty::Param(param) = pred.self_ty().kind() {
                            return Some(param.index);
                        }
                    }
                    ty::ClauseKind::TypeOutlives(ty::OutlivesPredicate(ty, _reg)) => {
                        if let ty::Param(param) = ty.kind() {
                            return Some(param.index);
                        }
                    }
                    ty::ClauseKind::Projection(p) => {
                        if let ty::Param(param) = p.projection_term.self_ty().kind() {
                            projection = Some(bound_p.rebind(p));
                            return Some(param.index);
                        }
                    }
                    _ => (),
                }

                None
            })();

            if let Some(param_idx) = param_idx
                && let Some(bounds) = impl_trait.get_mut(&param_idx)
            {
                let pred = clean_predicate(*pred, cx)?;

                bounds.extend(pred.get_bounds().into_iter().flatten().cloned());

                if let Some(proj) = projection
                    && let lhs = clean_projection(
                        proj.map_bound(|p| {
                            // FIXME: This needs to be made resilient for `AliasTerm`s that
                            // are associated consts.
                            p.projection_term.expect_ty(cx.tcx)
                        }),
                        cx,
                        None,
                    )
                    && let Some((_, trait_did, name)) = lhs.projection()
                {
                    impl_trait_proj.entry(param_idx).or_default().push((
                        trait_did,
                        name,
                        proj.map_bound(|p| p.term),
                    ));
                }

                return None;
            }

            Some(pred)
        })
        .collect::<Vec<_>>();

    for (idx, mut bounds) in impl_trait {
        let mut has_sized = false;
        bounds.retain(|b| {
            if b.is_sized_bound(cx) {
                has_sized = true;
                false
            } else {
                true
            }
        });
        if !has_sized {
            bounds.push(GenericBound::maybe_sized(cx));
        }

        // Move trait bounds to the front.
        bounds.sort_by_key(|b| !b.is_trait_bound());

        // Add back a `Sized` bound if there are no *trait* bounds remaining (incl. `?Sized`).
        // Since all potential trait bounds are at the front we can just check the first bound.
        if bounds.first().map_or(true, |b| !b.is_trait_bound()) {
            bounds.insert(0, GenericBound::sized(cx));
        }

        if let Some(proj) = impl_trait_proj.remove(&idx) {
            for (trait_did, name, rhs) in proj {
                let rhs = clean_term(rhs, cx);
                simplify::merge_bounds(cx, &mut bounds, trait_did, name, &rhs);
            }
        }

        cx.impl_trait_bounds.insert(idx.into(), bounds);
    }

    // Now that `cx.impl_trait_bounds` is populated, we can process
    // remaining predicates which could contain `impl Trait`.
    let where_predicates =
        where_predicates.into_iter().flat_map(|p| clean_predicate(*p, cx)).collect();

    let mut generics = Generics { params, where_predicates };
    simplify::sized_bounds(cx, &mut generics);
    generics.where_predicates = simplify::where_clauses(cx, generics.where_predicates);
    generics
}

// FIXME: maybe move to utils?
fn clean_ty_alias_inner_type<'tcx>(
    ty: Ty<'tcx>,
    cx: &mut DocContext<'tcx>,
    ret: &mut Vec<Item>,
) -> Option<TypeAliasInnerType> {
    let ty::Adt(adt_def, args) = ty.kind() else {
        return None;
    };

    if !adt_def.did().is_local() {
        cx.with_param_env(adt_def.did(), |cx| {
            inline::build_impls(cx, adt_def.did(), None, ret);
        });
    }

    Some(if adt_def.is_enum() {
        let variants: rustc_index::IndexVec<_, _> = adt_def
            .variants()
            .iter()
            .map(|variant| clean_variant_def_with_args(variant, args, cx))
            .collect();

        if !adt_def.did().is_local() {
            inline::record_extern_fqn(cx, adt_def.did(), ItemType::Enum);
        }

        TypeAliasInnerType::Enum {
            variants,
            is_non_exhaustive: adt_def.is_variant_list_non_exhaustive(),
        }
    } else {
        let variant = adt_def
            .variants()
            .iter()
            .next()
            .unwrap_or_else(|| bug!("a struct or union should always have one variant def"));

        let fields: Vec<_> =
            clean_variant_def_with_args(variant, args, cx).kind.inner_items().cloned().collect();

        if adt_def.is_struct() {
            if !adt_def.did().is_local() {
                inline::record_extern_fqn(cx, adt_def.did(), ItemType::Struct);
            }
            TypeAliasInnerType::Struct { ctor_kind: variant.ctor_kind(), fields }
        } else {
            if !adt_def.did().is_local() {
                inline::record_extern_fqn(cx, adt_def.did(), ItemType::Union);
            }
            TypeAliasInnerType::Union { fields }
        }
    })
}

fn clean_poly_fn_sig<'tcx>(
    cx: &mut DocContext<'tcx>,
    did: Option<DefId>,
    sig: ty::PolyFnSig<'tcx>,
) -> FnDecl {
    let mut names = did.map_or(&[] as &[_], |did| cx.tcx.fn_arg_names(did)).iter();

    // We assume all empty tuples are default return type. This theoretically can discard `-> ()`,
    // but shouldn't change any code meaning.
    let mut output = clean_ty(sig.output(), cx, None, None);

    // If the return type isn't an `impl Trait`, we can safely assume that this
    // function isn't async without needing to execute the query `asyncness` at
    // all which gives us a noticeable performance boost.
    if let Some(did) = did
        && let Type::ImplTrait(_) = output
        && cx.tcx.asyncness(did).is_async()
    {
        output = output.sugared_async_return_type();
    }

    FnDecl {
        output,
        c_variadic: sig.skip_binder().c_variadic,
        inputs: Arguments {
            values: sig
                .inputs()
                .iter()
                .map(|t| Argument {
                    type_: clean_ty(t.map_bound(|t| *t), cx, None, None),
                    name: names
                        .next()
                        .map(|i| i.name)
                        .filter(|i| !i.is_empty())
                        .unwrap_or(kw::Underscore),
                    is_const: false,
                })
                .collect(),
        },
    }
}

pub(crate) fn clean_assoc_item<'tcx>(
    assoc_item: &ty::AssocItem,
    cx: &mut DocContext<'tcx>,
) -> Item {
    let tcx = cx.tcx;
    let kind = match assoc_item.kind {
        ty::AssocKind::Const => {
            let ty = Box::new(clean_ty(
                ty::Binder::dummy(tcx.type_of(assoc_item.def_id).instantiate_identity()),
                cx,
                Some(assoc_item.def_id),
                None,
            ));

            let mut generics = clean_generics(
                cx,
                tcx.generics_of(assoc_item.def_id),
                tcx.explicit_predicates_of(assoc_item.def_id),
            );
            simplify::move_bounds_to_generic_parameters(&mut generics);

            let provided = match assoc_item.container {
                ty::ImplContainer => true,
                ty::TraitContainer => tcx.defaultness(assoc_item.def_id).has_value(),
            };
            if provided {
                AssocConstItem(generics, ty, ConstantKind::Extern { def_id: assoc_item.def_id })
            } else {
                TyAssocConstItem(generics, ty)
            }
        }
        ty::AssocKind::Fn => {
            let mut item = inline::build_function(cx, assoc_item.def_id);

            if assoc_item.fn_has_self_parameter {
                let self_ty = match assoc_item.container {
                    ty::ImplContainer => {
                        tcx.type_of(assoc_item.container_id(tcx)).instantiate_identity()
                    }
                    ty::TraitContainer => tcx.types.self_param,
                };
                let self_arg_ty =
                    tcx.fn_sig(assoc_item.def_id).instantiate_identity().input(0).skip_binder();
                if self_arg_ty == self_ty {
                    item.decl.inputs.values[0].type_ = Generic(kw::SelfUpper);
                } else if let ty::Ref(_, ty, _) = *self_arg_ty.kind() {
                    if ty == self_ty {
                        match item.decl.inputs.values[0].type_ {
                            BorrowedRef { ref mut type_, .. } => **type_ = Generic(kw::SelfUpper),
                            _ => unreachable!(),
                        }
                    }
                }
            }

            let provided = match assoc_item.container {
                ty::ImplContainer => true,
                ty::TraitContainer => assoc_item.defaultness(tcx).has_value(),
            };
            if provided {
                let defaultness = match assoc_item.container {
                    ty::ImplContainer => Some(assoc_item.defaultness(tcx)),
                    ty::TraitContainer => None,
                };
                MethodItem(item, defaultness)
            } else {
                TyMethodItem(item)
            }
        }
        ty::AssocKind::Type => {
            let my_name = assoc_item.name;

            fn param_eq_arg(param: &GenericParamDef, arg: &GenericArg) -> bool {
                match (&param.kind, arg) {
                    (GenericParamDefKind::Type { .. }, GenericArg::Type(Type::Generic(ty)))
                        if *ty == param.name =>
                    {
                        true
                    }
                    (GenericParamDefKind::Lifetime { .. }, GenericArg::Lifetime(Lifetime(lt)))
                        if *lt == param.name =>
                    {
                        true
                    }
                    (GenericParamDefKind::Const { .. }, GenericArg::Const(c)) => match &c.kind {
                        ConstantKind::TyConst { expr } => **expr == *param.name.as_str(),
                        _ => false,
                    },
                    _ => false,
                }
            }

            let mut predicates = tcx.explicit_predicates_of(assoc_item.def_id).predicates;
            if let ty::TraitContainer = assoc_item.container {
                let bounds =
                    tcx.explicit_item_bounds(assoc_item.def_id).instantiate_identity_iter_copied();
                predicates = tcx.arena.alloc_from_iter(bounds.chain(predicates.iter().copied()));
            }
            let mut generics = clean_generics(
                cx,
                tcx.generics_of(assoc_item.def_id),
                ty::GenericPredicates { parent: None, predicates },
            );
            simplify::move_bounds_to_generic_parameters(&mut generics);

            if let ty::TraitContainer = assoc_item.container {
                // Move bounds that are (likely) directly attached to the associated type
                // from the where-clause to the associated type.
                // There is no guarantee that this is what the user actually wrote but we have
                // no way of knowing.
                let mut bounds: Vec<GenericBound> = Vec::new();
                generics.where_predicates.retain_mut(|pred| match *pred {
                    WherePredicate::BoundPredicate {
                        ty:
                            QPath(box QPathData {
                                ref assoc,
                                ref self_type,
                                trait_: Some(ref trait_),
                                ..
                            }),
                        bounds: ref mut pred_bounds,
                        ..
                    } => {
                        if assoc.name != my_name {
                            return true;
                        }
                        if trait_.def_id() != assoc_item.container_id(tcx) {
                            return true;
                        }
                        match *self_type {
                            Generic(ref s) if *s == kw::SelfUpper => {}
                            _ => return true,
                        }
                        match &assoc.args {
                            GenericArgs::AngleBracketed { args, constraints } => {
                                if !constraints.is_empty()
                                    || generics
                                        .params
                                        .iter()
                                        .zip(args.iter())
                                        .any(|(param, arg)| !param_eq_arg(param, arg))
                                {
                                    return true;
                                }
                            }
                            GenericArgs::Parenthesized { .. } => {
                                // The only time this happens is if we're inside the rustdoc for Fn(),
                                // which only has one associated type, which is not a GAT, so whatever.
                            }
                        }
                        bounds.extend(mem::replace(pred_bounds, Vec::new()));
                        false
                    }
                    _ => true,
                });
                // Our Sized/?Sized bound didn't get handled when creating the generics
                // because we didn't actually get our whole set of bounds until just now
                // (some of them may have come from the trait). If we do have a sized
                // bound, we remove it, and if we don't then we add the `?Sized` bound
                // at the end.
                match bounds.iter().position(|b| b.is_sized_bound(cx)) {
                    Some(i) => {
                        bounds.remove(i);
                    }
                    None => bounds.push(GenericBound::maybe_sized(cx)),
                }

                if tcx.defaultness(assoc_item.def_id).has_value() {
                    AssocTypeItem(
                        Box::new(TypeAlias {
                            type_: clean_ty(
                                ty::Binder::dummy(
                                    tcx.type_of(assoc_item.def_id).instantiate_identity(),
                                ),
                                cx,
                                Some(assoc_item.def_id),
                                None,
                            ),
                            generics,
                            inner_type: None,
                            item_type: None,
                        }),
                        bounds,
                    )
                } else {
                    TyAssocTypeItem(generics, bounds)
                }
            } else {
                AssocTypeItem(
                    Box::new(TypeAlias {
                        type_: clean_ty(
                            ty::Binder::dummy(
                                tcx.type_of(assoc_item.def_id).instantiate_identity(),
                            ),
                            cx,
                            Some(assoc_item.def_id),
                            None,
                        ),
                        generics,
                        inner_type: None,
                        item_type: None,
                    }),
                    // Associated types inside trait or inherent impls are not allowed to have
                    // item bounds. Thus we don't attempt to move any bounds there.
                    Vec::new(),
                )
            }
        }
    };

    Item::from_def_id_and_parts(assoc_item.def_id, Some(assoc_item.name), kind, cx)
}

/// Returns `None` if the type could not be normalized
// FIXME: maybe move to util?
fn normalize<'tcx>(
    cx: &mut DocContext<'tcx>,
    ty: ty::Binder<'tcx, Ty<'tcx>>,
) -> Option<ty::Binder<'tcx, Ty<'tcx>>> {
    // HACK: low-churn fix for #79459 while we wait for a trait normalization fix
    if !cx.tcx.sess.opts.unstable_opts.normalize_docs {
        return None;
    }

    use rustc_middle::traits::ObligationCause;
    use rustc_trait_selection::infer::TyCtxtInferExt;
    use rustc_trait_selection::traits::query::normalize::QueryNormalizeExt;

    // Try to normalize `<X as Y>::T` to a type
    let infcx = cx.tcx.infer_ctxt().build();
    let normalized = infcx
        .at(&ObligationCause::dummy(), cx.param_env)
        .query_normalize(ty)
        .map(|resolved| infcx.resolve_vars_if_possible(resolved.value));
    match normalized {
        Ok(normalized_value) => {
            debug!("normalized {ty:?} to {normalized_value:?}");
            Some(normalized_value)
        }
        Err(err) => {
            debug!("failed to normalize {ty:?}: {err:?}");
            None
        }
    }
}

fn clean_trait_object_lifetime_bound<'tcx>(
    region: ty::Region<'tcx>,
    container: Option<ContainerTy<'_, 'tcx>>,
    preds: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> Option<Lifetime> {
    if can_elide_trait_object_lifetime_bound(region, container, preds, tcx) {
        return None;
    }

    // Since there is a semantic difference between an implicitly elided (i.e. "defaulted") object
    // lifetime and an explicitly elided object lifetime (`'_`), we intentionally don't hide the
    // latter contrary to `clean_region`.
    match *region {
        ty::ReStatic => Some(Lifetime::statik()),
        ty::ReEarlyParam(region) if region.name != kw::Empty => Some(Lifetime(region.name)),
        ty::ReBound(_, ty::BoundRegion { kind: ty::BrNamed(_, name), .. }) if name != kw::Empty => {
            Some(Lifetime(name))
        }
        ty::ReEarlyParam(_)
        | ty::ReBound(..)
        | ty::ReLateParam(_)
        | ty::ReVar(_)
        | ty::RePlaceholder(_)
        | ty::ReErased
        | ty::ReError(_) => None,
    }
}

fn can_elide_trait_object_lifetime_bound<'tcx>(
    region: ty::Region<'tcx>,
    container: Option<ContainerTy<'_, 'tcx>>,
    preds: &'tcx ty::List<ty::PolyExistentialPredicate<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> bool {
    // Below we quote extracts from https://doc.rust-lang.org/reference/lifetime-elision.html#default-trait-object-lifetimes

    // > If the trait object is used as a type argument of a generic type then the containing type is
    // > first used to try to infer a bound.
    let default = container
        .map_or(ObjectLifetimeDefault::Empty, |container| container.object_lifetime_default(tcx));

    // > If there is a unique bound from the containing type then that is the default
    // If there is a default object lifetime and the given region is lexically equal to it, elide it.
    match default {
        ObjectLifetimeDefault::Static => return *region == ty::ReStatic,
        // FIXME(fmease): Don't compare lexically but respect de Bruijn indices etc. to handle shadowing correctly.
        ObjectLifetimeDefault::Arg(default) => return region.get_name() == default.get_name(),
        // > If there is more than one bound from the containing type then an explicit bound must be specified
        // Due to ambiguity there is no default trait-object lifetime and thus elision is impossible.
        // Don't elide the lifetime.
        ObjectLifetimeDefault::Ambiguous => return false,
        // There is no meaningful bound. Further processing is needed...
        ObjectLifetimeDefault::Empty => {}
    }

    // > If neither of those rules apply, then the bounds on the trait are used:
    match *object_region_bounds(tcx, preds) {
        // > If the trait has no lifetime bounds, then the lifetime is inferred in expressions
        // > and is 'static outside of expressions.
        // FIXME: If we are in an expression context (i.e. fn bodies and const exprs) then the default is
        // `'_` and not `'static`. Only if we are in a non-expression one, the default is `'static`.
        // Note however that at the time of this writing it should be fine to disregard this subtlety
        // as we neither render const exprs faithfully anyway (hiding them in some places or using `_` instead)
        // nor show the contents of fn bodies.
        [] => *region == ty::ReStatic,
        // > If the trait is defined with a single lifetime bound then that bound is used.
        // > If 'static is used for any lifetime bound then 'static is used.
        // FIXME(fmease): Don't compare lexically but respect de Bruijn indices etc. to handle shadowing correctly.
        [object_region] => object_region.get_name() == region.get_name(),
        // There are several distinct trait regions and none are `'static`.
        // Due to ambiguity there is no default trait-object lifetime and thus elision is impossible.
        // Don't elide the lifetime.
        _ => false,
    }
}

#[derive(Debug)]
pub(crate) enum ContainerTy<'a, 'tcx> {
    Ref(ty::Region<'tcx>),
    Regular {
        ty: DefId,
        /// The arguments *have* to contain an arg for the self type if the corresponding generics
        /// contain a self type.
        args: ty::Binder<'tcx, &'a [ty::GenericArg<'tcx>]>,
        arg: usize,
    },
}

impl<'tcx> ContainerTy<'_, 'tcx> {
    fn object_lifetime_default(self, tcx: TyCtxt<'tcx>) -> ObjectLifetimeDefault<'tcx> {
        match self {
            Self::Ref(region) => ObjectLifetimeDefault::Arg(region),
            Self::Regular { ty: container, args, arg: index } => {
                let (DefKind::Struct
                | DefKind::Union
                | DefKind::Enum
                | DefKind::TyAlias
                | DefKind::Trait) = tcx.def_kind(container)
                else {
                    return ObjectLifetimeDefault::Empty;
                };

                let generics = tcx.generics_of(container);
                debug_assert_eq!(generics.parent_count, 0);

                let param = generics.own_params[index].def_id;
                let default = tcx.object_lifetime_default(param);
                match default {
                    rbv::ObjectLifetimeDefault::Param(lifetime) => {
                        // The index is relative to the parent generics but since we don't have any,
                        // we don't need to translate it.
                        let index = generics.param_def_id_to_index[&lifetime];
                        let arg = args.skip_binder()[index as usize].expect_region();
                        ObjectLifetimeDefault::Arg(arg)
                    }
                    rbv::ObjectLifetimeDefault::Empty => ObjectLifetimeDefault::Empty,
                    rbv::ObjectLifetimeDefault::Static => ObjectLifetimeDefault::Static,
                    rbv::ObjectLifetimeDefault::Ambiguous => ObjectLifetimeDefault::Ambiguous,
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum ObjectLifetimeDefault<'tcx> {
    Empty,
    Static,
    Ambiguous,
    Arg(ty::Region<'tcx>),
}

#[instrument(level = "trace", skip(cx), ret)]
pub(crate) fn clean_ty<'tcx>(
    bound_ty: ty::Binder<'tcx, Ty<'tcx>>,
    cx: &mut DocContext<'tcx>,
    parent_def_id: Option<DefId>,
    container: Option<ContainerTy<'_, 'tcx>>,
) -> Type {
    let bound_ty = normalize(cx, bound_ty).unwrap_or(bound_ty);
    match *bound_ty.skip_binder().kind() {
        ty::Never => Primitive(PrimitiveType::Never),
        ty::Bool => Primitive(PrimitiveType::Bool),
        ty::Char => Primitive(PrimitiveType::Char),
        ty::Int(int_ty) => Primitive(int_ty.into()),
        ty::Uint(uint_ty) => Primitive(uint_ty.into()),
        ty::Float(float_ty) => Primitive(float_ty.into()),
        ty::Str => Primitive(PrimitiveType::Str),
        ty::Slice(ty) => Slice(Box::new(clean_ty(bound_ty.rebind(ty), cx, None, None))),
        ty::Pat(ty, pat) => Type::Pat(
            Box::new(clean_ty(bound_ty.rebind(ty), cx, None, None)),
            format!("{pat:?}").into_boxed_str(),
        ),
        ty::Array(ty, mut n) => {
            n = n.normalize(cx.tcx, ty::ParamEnv::reveal_all());
            let n = print_const(cx, n);
            Array(Box::new(clean_ty(bound_ty.rebind(ty), cx, None, None)), n.into())
        }
        ty::RawPtr(ty, mutbl) => {
            RawPointer(mutbl, Box::new(clean_ty(bound_ty.rebind(ty), cx, None, None)))
        }
        ty::Ref(r, ty, mutbl) => BorrowedRef {
            lifetime: clean_region(r),
            mutability: mutbl,
            type_: Box::new(clean_ty(bound_ty.rebind(ty), cx, None, Some(ContainerTy::Ref(r)))),
        },
        ty::FnDef(..) | ty::FnPtr(_) => {
            // FIXME: should we merge the outer and inner binders somehow?
            let sig = bound_ty.skip_binder().fn_sig(cx.tcx);
            let decl = clean_poly_fn_sig(cx, None, sig);
            let generic_params = clean_bound_vars(sig.bound_vars());

            BareFunction(Box::new(BareFunctionDecl {
                safety: sig.safety(),
                generic_params,
                decl,
                abi: sig.abi(),
            }))
        }
        ty::Adt(def, args) => {
            let did = def.did();
            let kind = match def.adt_kind() {
                AdtKind::Struct => ItemType::Struct,
                AdtKind::Union => ItemType::Union,
                AdtKind::Enum => ItemType::Enum,
            };
            inline::record_extern_fqn(cx, did, kind);
            let path = clean_path(cx, did, false, ThinVec::new(), bound_ty.rebind(args));
            Type::Path { path }
        }
        ty::Foreign(did) => {
            inline::record_extern_fqn(cx, did, ItemType::ForeignType);
            let path = clean_path(
                cx,
                did,
                false,
                ThinVec::new(),
                ty::Binder::dummy(ty::GenericArgs::empty()),
            );
            Type::Path { path }
        }
        ty::Dynamic(obj, ref reg, _) => {
            // HACK: pick the first `did` as the `did` of the trait object. Someone
            // might want to implement "native" support for marker-trait-only
            // trait objects.
            let mut dids = obj.auto_traits();
            let did = obj
                .principal_def_id()
                .or_else(|| dids.next())
                .unwrap_or_else(|| panic!("found trait object `{bound_ty:?}` with no traits?"));
            let args = match obj.principal() {
                Some(principal) => principal.map_bound(|p| p.args),
                // marker traits have no args.
                _ => ty::Binder::dummy(ty::GenericArgs::empty()),
            };

            inline::record_extern_fqn(cx, did, ItemType::Trait);

            let lifetime = clean_trait_object_lifetime_bound(*reg, container, obj, cx.tcx);

            let mut bounds = dids
                .map(|did| {
                    let empty = ty::Binder::dummy(ty::GenericArgs::empty());
                    let path = clean_path(cx, did, false, ThinVec::new(), empty);
                    inline::record_extern_fqn(cx, did, ItemType::Trait);
                    PolyTrait { trait_: path, generic_params: Vec::new() }
                })
                .collect::<Vec<_>>();

            let bindings = obj
                .projection_bounds()
                .map(|pb| AssocItemConstraint {
                    assoc: projection_to_path_segment(
                        pb.map_bound(|pb| {
                            pb
                                // HACK(compiler-errors): Doesn't actually matter what self
                                // type we put here, because we're only using the GAT's args.
                                .with_self_ty(cx.tcx, cx.tcx.types.self_param)
                                .projection_term
                                // FIXME: This needs to be made resilient for `AliasTerm`s
                                // that are associated consts.
                                .expect_ty(cx.tcx)
                        }),
                        cx,
                    ),
                    kind: AssocItemConstraintKind::Equality {
                        term: clean_term(pb.map_bound(|pb| pb.term), cx),
                    },
                })
                .collect();

            let late_bound_regions: FxIndexSet<_> = obj
                .iter()
                .flat_map(|pred| pred.bound_vars())
                .filter_map(|var| match var {
                    ty::BoundVariableKind::Region(ty::BrNamed(def_id, name))
                        if name != kw::UnderscoreLifetime =>
                    {
                        Some(GenericParamDef::lifetime(def_id, name))
                    }
                    _ => None,
                })
                .collect();
            let late_bound_regions = late_bound_regions.into_iter().collect();

            let path = clean_path(cx, did, false, bindings, args);
            bounds.insert(0, PolyTrait { trait_: path, generic_params: late_bound_regions });

            DynTrait(bounds, lifetime)
        }
        ty::Tuple(t) => {
            Tuple(t.iter().map(|t| clean_ty(bound_ty.rebind(t), cx, None, None)).collect())
        }

        ty::Alias(ty::Projection, data) => {
            clean_projection(bound_ty.rebind(data), cx, parent_def_id)
        }

        ty::Alias(ty::Inherent, alias_ty) => {
            let def_id = alias_ty.def_id;
            let alias_ty = bound_ty.rebind(alias_ty);
            let self_type = clean_ty(alias_ty.map_bound(|ty| ty.self_ty()), cx, None, None);

            Type::QPath(Box::new(QPathData {
                assoc: PathSegment {
                    name: cx.tcx.associated_item(def_id).name,
                    args: GenericArgs::AngleBracketed {
                        args: clean_generic_args(
                            cx,
                            alias_ty.map_bound(|ty| ty.args.as_slice()),
                            true,
                            def_id,
                        )
                        .into(),
                        constraints: Default::default(),
                    },
                },
                should_show_cast: false,
                self_type,
                trait_: None,
            }))
        }

        ty::Alias(ty::Weak, data) => {
            if cx.tcx.features().lazy_type_alias {
                // Weak type alias `data` represents the `type X` in `type X = Y`. If we need `Y`,
                // we need to use `type_of`.
                let path =
                    clean_path(cx, data.def_id, false, ThinVec::new(), bound_ty.rebind(data.args));
                Type::Path { path }
            } else {
                let ty = cx.tcx.type_of(data.def_id).instantiate(cx.tcx, data.args);
                clean_ty(bound_ty.rebind(ty), cx, None, None)
            }
        }

        ty::Param(ref p) => {
            if let Some(bounds) = cx.impl_trait_bounds.remove(&p.index.into()) {
                ImplTrait(bounds)
            } else {
                Generic(p.name)
            }
        }

        ty::Bound(_, ref ty) => match ty.kind {
            ty::BoundTyKind::Param(_, name) => Generic(name),
            ty::BoundTyKind::Anon => panic!("unexpected anonymous bound type variable"),
        },

        ty::Alias(ty::Opaque, ty::AliasTy { def_id, args, .. }) => {
            // If it's already in the same alias, don't get an infinite loop.
            if cx.current_type_aliases.contains_key(&def_id) {
                let path = clean_path(cx, def_id, false, ThinVec::new(), bound_ty.rebind(args));
                Type::Path { path }
            } else {
                *cx.current_type_aliases.entry(def_id).or_insert(0) += 1;
                // Grab the "TraitA + TraitB" from `impl TraitA + TraitB`,
                // by looking up the bounds associated with the def_id.
                let bounds = cx
                    .tcx
                    .explicit_item_bounds(def_id)
                    .iter_instantiated_copied(cx.tcx, args)
                    .map(|(bound, _)| bound)
                    .collect::<Vec<_>>();
                let ty = clean_opaque_bounds(cx, bounds);
                if let Some(count) = cx.current_type_aliases.get_mut(&def_id) {
                    *count -= 1;
                    if *count == 0 {
                        cx.current_type_aliases.remove(&def_id);
                    }
                }
                ty
            }
        }

        ty::Closure(..) => panic!("Closure"),
        ty::CoroutineClosure(..) => panic!("CoroutineClosure"),
        ty::Coroutine(..) => panic!("Coroutine"),
        ty::Placeholder(..) => panic!("Placeholder"),
        ty::CoroutineWitness(..) => panic!("CoroutineWitness"),
        ty::Infer(..) => panic!("Infer"),
        ty::Error(_) => FatalError.raise(),
    }
}

fn clean_opaque_bounds<'tcx>(cx: &mut DocContext<'tcx>, bounds: Vec<ty::Clause<'tcx>>) -> Type {
    let mut has_sized = false;
    let mut bounds = bounds
        .iter()
        .filter_map(|bound| {
            let bound_predicate = bound.kind();
            let trait_ref = match bound_predicate.skip_binder() {
                ty::ClauseKind::Trait(tr) => bound_predicate.rebind(tr.trait_ref),
                ty::ClauseKind::TypeOutlives(ty::OutlivesPredicate(_ty, reg)) => {
                    return clean_region(reg).map(GenericBound::Outlives);
                }
                _ => return None,
            };

            if let Some(sized) = cx.tcx.lang_items().sized_trait()
                && trait_ref.def_id() == sized
            {
                has_sized = true;
                return None;
            }

            let bindings: ThinVec<_> = bounds
                .iter()
                .filter_map(|bound| {
                    if let ty::ClauseKind::Projection(proj) = bound.kind().skip_binder() {
                        if proj.projection_term.trait_ref(cx.tcx) == trait_ref.skip_binder() {
                            Some(AssocItemConstraint {
                                assoc: projection_to_path_segment(
                                    // FIXME: This needs to be made resilient for `AliasTerm`s that
                                    // are associated consts.
                                    bound.kind().rebind(proj.projection_term.expect_ty(cx.tcx)),
                                    cx,
                                ),
                                kind: AssocItemConstraintKind::Equality {
                                    term: clean_term(bound.kind().rebind(proj.term), cx),
                                },
                            })
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                })
                .collect();

            Some(clean_poly_trait_ref_with_constraints(cx, trait_ref, bindings))
        })
        .collect::<Vec<_>>();

    if !has_sized {
        bounds.push(GenericBound::maybe_sized(cx));
    }

    // Move trait bounds to the front.
    bounds.sort_by_key(|b| !b.is_trait_bound());

    // Add back a `Sized` bound if there are no *trait* bounds remaining (incl. `?Sized`).
    // Since all potential trait bounds are at the front we can just check the first bound.
    if bounds.first().map_or(true, |b| !b.is_trait_bound()) {
        bounds.insert(0, GenericBound::sized(cx));
    }

    ImplTrait(bounds)
}

pub(crate) fn clean_field<'tcx>(field: &ty::FieldDef, cx: &mut DocContext<'tcx>) -> Item {
    clean_field_with_def_id(
        field.did,
        field.name,
        clean_ty(
            ty::Binder::dummy(cx.tcx.type_of(field.did).instantiate_identity()),
            cx,
            Some(field.did),
            None,
        ),
        cx,
    )
}

// FIXME: maybe move to utils?
pub(crate) fn clean_field_with_def_id(
    def_id: DefId,
    name: Symbol,
    ty: Type,
    cx: &mut DocContext<'_>,
) -> Item {
    Item::from_def_id_and_parts(def_id, Some(name), StructFieldItem(ty), cx)
}

pub(crate) fn clean_variant_def<'tcx>(variant: &ty::VariantDef, cx: &mut DocContext<'tcx>) -> Item {
    let discriminant = match variant.discr {
        ty::VariantDiscr::Explicit(def_id) => Some(Discriminant { expr: None, value: def_id }),
        ty::VariantDiscr::Relative(_) => None,
    };

    let kind = match variant.ctor_kind() {
        Some(CtorKind::Const) => VariantKind::CLike,
        Some(CtorKind::Fn) => {
            VariantKind::Tuple(variant.fields.iter().map(|field| clean_field(field, cx)).collect())
        }
        None => VariantKind::Struct(VariantStruct {
            fields: variant.fields.iter().map(|field| clean_field(field, cx)).collect(),
        }),
    };

    Item::from_def_id_and_parts(
        variant.def_id,
        Some(variant.name),
        VariantItem(Variant { kind, discriminant }),
        cx,
    )
}

pub(crate) fn clean_variant_def_with_args<'tcx>(
    variant: &ty::VariantDef,
    args: &GenericArgsRef<'tcx>,
    cx: &mut DocContext<'tcx>,
) -> Item {
    let discriminant = match variant.discr {
        ty::VariantDiscr::Explicit(def_id) => Some(Discriminant { expr: None, value: def_id }),
        ty::VariantDiscr::Relative(_) => None,
    };

    use rustc_middle::traits::ObligationCause;
    use rustc_trait_selection::infer::TyCtxtInferExt;
    use rustc_trait_selection::traits::query::normalize::QueryNormalizeExt;

    let infcx = cx.tcx.infer_ctxt().build();
    let kind = match variant.ctor_kind() {
        Some(CtorKind::Const) => VariantKind::CLike,
        Some(CtorKind::Fn) => VariantKind::Tuple(
            variant
                .fields
                .iter()
                .map(|field| {
                    let ty = cx.tcx.type_of(field.did).instantiate(cx.tcx, args);

                    // normalize the type to only show concrete types
                    // note: we do not use try_normalize_erasing_regions since we
                    // do care about showing the regions
                    let ty = infcx
                        .at(&ObligationCause::dummy(), cx.param_env)
                        .query_normalize(ty)
                        .map(|normalized| normalized.value)
                        .unwrap_or(ty);

                    clean_field_with_def_id(
                        field.did,
                        field.name,
                        clean_ty(ty::Binder::dummy(ty), cx, Some(field.did), None),
                        cx,
                    )
                })
                .collect(),
        ),
        None => VariantKind::Struct(VariantStruct {
            fields: variant
                .fields
                .iter()
                .map(|field| {
                    let ty = cx.tcx.type_of(field.did).instantiate(cx.tcx, args);

                    // normalize the type to only show concrete types
                    // note: we do not use try_normalize_erasing_regions since we
                    // do care about showing the regions
                    let ty = infcx
                        .at(&ObligationCause::dummy(), cx.param_env)
                        .query_normalize(ty)
                        .map(|normalized| normalized.value)
                        .unwrap_or(ty);

                    clean_field_with_def_id(
                        field.did,
                        field.name,
                        clean_ty(ty::Binder::dummy(ty), cx, Some(field.did), None),
                        cx,
                    )
                })
                .collect(),
        }),
    };

    Item::from_def_id_and_parts(
        variant.def_id,
        Some(variant.name),
        VariantItem(Variant { kind, discriminant }),
        cx,
    )
}

pub(crate) fn reexport_chain<'tcx>(
    tcx: TyCtxt<'tcx>,
    import_def_id: LocalDefId,
    target_def_id: DefId,
) -> &'tcx [Reexport] {
    for child in tcx.module_children_local(tcx.local_parent(import_def_id)) {
        if child.res.opt_def_id() == Some(target_def_id)
            && child.reexport_chain.first().and_then(|r| r.id()) == Some(import_def_id.to_def_id())
        {
            return &child.reexport_chain;
        }
    }
    &[]
}

/// Collect attributes from the whole import chain.
fn get_all_import_attributes<'hir>(
    cx: &mut DocContext<'hir>,
    import_def_id: LocalDefId,
    target_def_id: DefId,
    is_inline: bool,
) -> Vec<(Cow<'hir, ast::Attribute>, Option<DefId>)> {
    let mut attrs = Vec::new();
    let mut first = true;
    for def_id in reexport_chain(cx.tcx, import_def_id, target_def_id)
        .iter()
        .flat_map(|reexport| reexport.id())
    {
        let import_attrs = inline::load_attrs(cx, def_id);
        if first {
            // This is the "original" reexport so we get all its attributes without filtering them.
            attrs = import_attrs.iter().map(|attr| (Cow::Borrowed(attr), Some(def_id))).collect();
            first = false;
        // We don't add attributes of an intermediate re-export if it has `#[doc(hidden)]`.
        } else if cx.render_options.document_hidden || !cx.tcx.is_doc_hidden(def_id) {
            add_without_unwanted_attributes(&mut attrs, import_attrs, is_inline, Some(def_id));
        }
    }
    attrs
}

fn filter_tokens_from_list(
    args_tokens: &TokenStream,
    should_retain: impl Fn(&TokenTree) -> bool,
) -> Vec<TokenTree> {
    let mut tokens = Vec::with_capacity(args_tokens.len());
    let mut skip_next_comma = false;
    for token in args_tokens.trees() {
        match token {
            TokenTree::Token(Token { kind: TokenKind::Comma, .. }, _) if skip_next_comma => {
                skip_next_comma = false;
            }
            token if should_retain(token) => {
                skip_next_comma = false;
                tokens.push(token.clone());
            }
            _ => {
                skip_next_comma = true;
            }
        }
    }
    tokens
}

fn filter_doc_attr_ident(ident: Symbol, is_inline: bool) -> bool {
    if is_inline {
        ident == sym::hidden || ident == sym::inline || ident == sym::no_inline
    } else {
        ident == sym::cfg
    }
}

/// Remove attributes from `normal` that should not be inherited by `use` re-export.
/// Before calling this function, make sure `normal` is a `#[doc]` attribute.
fn filter_doc_attr(normal: &mut ast::NormalAttr, is_inline: bool) {
    match normal.item.args {
        ast::AttrArgs::Delimited(ref mut args) => {
            let tokens = filter_tokens_from_list(&args.tokens, |token| {
                !matches!(
                    token,
                    TokenTree::Token(
                        Token {
                            kind: TokenKind::Ident(
                                ident,
                                _,
                            ),
                            ..
                        },
                        _,
                    ) if filter_doc_attr_ident(*ident, is_inline),
                )
            });
            args.tokens = TokenStream::new(tokens);
        }
        ast::AttrArgs::Empty | ast::AttrArgs::Eq(..) => {}
    }
}

/// When inlining items, we merge their attributes (and all the reexports attributes too) with the
/// final reexport. For example:
///
/// ```ignore (just an example)
/// #[doc(hidden, cfg(feature = "foo"))]
/// pub struct Foo;
///
/// #[doc(cfg(feature = "bar"))]
/// #[doc(hidden, no_inline)]
/// pub use Foo as Foo1;
///
/// #[doc(inline)]
/// pub use Foo2 as Bar;
/// ```
///
/// So `Bar` at the end will have both `cfg(feature = "...")`. However, we don't want to merge all
/// attributes so we filter out the following ones:
/// * `doc(inline)`
/// * `doc(no_inline)`
/// * `doc(hidden)`
fn add_without_unwanted_attributes<'hir>(
    attrs: &mut Vec<(Cow<'hir, ast::Attribute>, Option<DefId>)>,
    new_attrs: &'hir [ast::Attribute],
    is_inline: bool,
    import_parent: Option<DefId>,
) {
    for attr in new_attrs {
        if matches!(attr.kind, ast::AttrKind::DocComment(..)) {
            attrs.push((Cow::Borrowed(attr), import_parent));
            continue;
        }
        let mut attr = attr.clone();
        match attr.kind {
            ast::AttrKind::Normal(ref mut normal) => {
                if let [ident] = &*normal.item.path.segments {
                    let ident = ident.ident.name;
                    if ident == sym::doc {
                        filter_doc_attr(normal, is_inline);
                        attrs.push((Cow::Owned(attr), import_parent));
                    } else if is_inline || ident != sym::cfg {
                        // If it's not a `cfg()` attribute, we keep it.
                        attrs.push((Cow::Owned(attr), import_parent));
                    }
                }
            }
            _ => unreachable!(),
        }
    }
}

fn clean_path<'tcx>(
    cx: &mut DocContext<'tcx>,
    did: DefId,
    has_self: bool,
    constraints: ThinVec<AssocItemConstraint>,
    args: ty::Binder<'tcx, GenericArgsRef<'tcx>>,
) -> Path {
    let def_kind = cx.tcx.def_kind(did);
    let name = cx.tcx.opt_item_name(did).unwrap_or(kw::Empty);
    Path {
        res: Res::Def(def_kind, did),
        segments: thin_vec![PathSegment {
            name,
            args: clean_generic_args_with_constraints(cx, did, has_self, constraints, args),
        }],
    }
}

fn clean_generic_args<'tcx>(
    cx: &mut DocContext<'tcx>,
    args: ty::Binder<'tcx, &'tcx [ty::GenericArg<'tcx>]>,
    mut has_self: bool,
    owner: DefId,
) -> Vec<GenericArg> {
    let (args, bound_vars) = (args.skip_binder(), args.bound_vars());
    if args.is_empty() {
        // Fast path which avoids executing the query `generics_of`.
        return Vec::new();
    }

    // If the container is a trait object type, the arguments won't contain the self type but the
    // generics of the corresponding trait will. In such a case, prepend a dummy self type in order
    // to align the arguments and parameters for the iteration below and to enable us to correctly
    // instantiate the generic parameter default later.
    let generics = cx.tcx.generics_of(owner);
    let args = if !has_self && generics.parent.is_none() && generics.has_self {
        has_self = true;
        [cx.tcx.types.trait_object_dummy_self.into()]
            .into_iter()
            .chain(args.iter().copied())
            .collect::<Vec<_>>()
            .into()
    } else {
        std::borrow::Cow::from(args)
    };

    let mut elision_has_failed_once_before = false;
    let clean_arg = |(index, &arg): (usize, &ty::GenericArg<'tcx>)| {
        // Elide the self type.
        if has_self && index == 0 {
            return None;
        }

        // Elide internal host effect args.
        let param = generics.param_at(index, cx.tcx);
        if param.is_host_effect() {
            return None;
        }

        let arg = ty::Binder::bind_with_vars(arg, bound_vars);

        // Elide arguments that coincide with their default.
        if !elision_has_failed_once_before && let Some(default) = param.default_value(cx.tcx) {
            let default = default.instantiate(cx.tcx, args.as_ref());
            if can_elide_generic_arg(arg, arg.rebind(default)) {
                return None;
            }
            elision_has_failed_once_before = true;
        }

        match arg.skip_binder().unpack() {
            ty::GenericArgKind::Lifetime(lt) => {
                Some(GenericArg::Lifetime(clean_region(lt).unwrap_or(Lifetime::elided())))
            }
            ty::GenericArgKind::Type(ty) => Some(GenericArg::Type(clean_ty(
                arg.rebind(ty),
                cx,
                None,
                Some(crate::clean::ContainerTy::Regular {
                    ty: owner,
                    args: arg.rebind(args.as_ref()),
                    arg: index,
                }),
            ))),
            ty::GenericArgKind::Const(ct) => {
                Some(GenericArg::Const(Box::new(clean_const(arg.rebind(ct), cx))))
            }
        }
    };

    let offset = if has_self { 1 } else { 0 };
    let mut clean_args = Vec::with_capacity(args.len().saturating_sub(offset));
    clean_args.extend(args.iter().enumerate().rev().filter_map(clean_arg));
    clean_args.reverse();
    clean_args
}

/// Check if the generic argument `actual` coincides with the `default` and can therefore be elided.
///
/// This uses a very conservative approach for performance and correctness reasons, meaning for
/// several classes of terms it claims that they cannot be elided even if they theoretically could.
/// This is absolutely fine since it mostly concerns edge cases.
fn can_elide_generic_arg<'tcx>(
    actual: ty::Binder<'tcx, ty::GenericArg<'tcx>>,
    default: ty::Binder<'tcx, ty::GenericArg<'tcx>>,
) -> bool {
    debug_assert_matches!(
        (actual.skip_binder().unpack(), default.skip_binder().unpack()),
        (ty::GenericArgKind::Lifetime(_), ty::GenericArgKind::Lifetime(_))
            | (ty::GenericArgKind::Type(_), ty::GenericArgKind::Type(_))
            | (ty::GenericArgKind::Const(_), ty::GenericArgKind::Const(_))
    );

    // In practice, we shouldn't have any inference variables at this point.
    // However to be safe, we bail out if we do happen to stumble upon them.
    if actual.has_infer() || default.has_infer() {
        return false;
    }

    // Since we don't properly keep track of bound variables in rustdoc (yet), we don't attempt to
    // make any sense out of escaping bound variables. We simply don't have enough context and it
    // would be incorrect to try to do so anyway.
    if actual.has_escaping_bound_vars() || default.has_escaping_bound_vars() {
        return false;
    }

    // Theoretically we could now check if either term contains (non-escaping) late-bound regions or
    // projections, relate the two using an `InferCtxt` and check if the resulting obligations hold.
    // Having projections means that the terms can potentially be further normalized thereby possibly
    // revealing that they are equal after all. Regarding late-bound regions, they could to be
    // liberated allowing us to consider more types to be equal by ignoring the names of binders
    // (e.g., `for<'a> TYPE<'a>` and `for<'b> TYPE<'b>`).
    //
    // However, we are mostly interested in “reeliding” generic args, i.e., eliding generic args that
    // were originally elided by the user and later filled in by the compiler contrary to eliding
    // arbitrary generic arguments if they happen to semantically coincide with the default (of course,
    // we cannot possibly distinguish these two cases). Therefore and for performance reasons, it
    // suffices to only perform a syntactic / structural check by comparing the memory addresses of
    // the interned arguments.
    actual.skip_binder() == default.skip_binder()
}

fn clean_generic_args_with_constraints<'tcx>(
    cx: &mut DocContext<'tcx>,
    did: DefId,
    has_self: bool,
    constraints: ThinVec<AssocItemConstraint>,
    ty_args: ty::Binder<'tcx, GenericArgsRef<'tcx>>,
) -> GenericArgs {
    let args = clean_generic_args(cx, ty_args.map_bound(|args| &args[..]), has_self, did);

    if cx.tcx.fn_trait_kind_from_def_id(did).is_some() {
        let ty = ty_args
            .iter()
            .nth(if has_self { 1 } else { 0 })
            .unwrap()
            .map_bound(|arg| arg.expect_ty());
        let inputs =
            // The trait's first substitution is the one after self, if there is one.
            match ty.skip_binder().kind() {
                ty::Tuple(tys) => tys.iter().map(|t| clean_ty(ty.rebind(t), cx, None, None)).collect::<Vec<_>>().into(),
                _ => return GenericArgs::AngleBracketed { args: args.into(), constraints },
            };
        let output = constraints.into_iter().next().and_then(|binding| match binding.kind {
            AssocItemConstraintKind::Equality { term: Term::Type(ty) }
                if ty != Type::Tuple(Vec::new()) =>
            {
                Some(Box::new(ty))
            }
            _ => None,
        });
        GenericArgs::Parenthesized { inputs, output }
    } else {
        GenericArgs::AngleBracketed { args: args.into(), constraints }
    }
}

fn clean_bound_vars<'tcx>(
    bound_vars: &'tcx ty::List<ty::BoundVariableKind>,
) -> Vec<GenericParamDef> {
    bound_vars
        .into_iter()
        .filter_map(|var| match var {
            ty::BoundVariableKind::Region(ty::BrNamed(def_id, name))
                if name != kw::UnderscoreLifetime =>
            {
                Some(GenericParamDef::lifetime(def_id, name))
            }
            ty::BoundVariableKind::Ty(ty::BoundTyKind::Param(def_id, name)) => {
                Some(GenericParamDef {
                    name,
                    def_id,
                    kind: GenericParamDefKind::Type {
                        bounds: ThinVec::new(),
                        default: None,
                        synthetic: false,
                    },
                })
            }
            // FIXME(non_lifetime_binders): Support higher-ranked const parameters.
            ty::BoundVariableKind::Const => None,
            _ => None,
        })
        .collect()
}
