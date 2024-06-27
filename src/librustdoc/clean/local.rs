use rustc_ast as ast;
use rustc_attr as attr;
use rustc_data_structures::fx::{FxHashSet, FxIndexMap, IndexEntry};
use rustc_errors::{codes::*, struct_span_code_err};
use rustc_hir as hir;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, DefIdMap, DefIdSet, LocalDefId, LOCAL_CRATE};
use rustc_hir::PredicateOrigin;
use rustc_hir_analysis::lower_ty;
use rustc_middle::bug;
use rustc_middle::middle::resolve_bound_vars as rbv;
use rustc_middle::ty;
use rustc_middle::ty::TypeVisitableExt;
use rustc_span::hygiene::{AstPass, MacroKind};
use rustc_span::symbol::{kw, sym, Ident, Symbol};
use rustc_span::ExpnKind;

use thin_vec::ThinVec;

use crate::core::DocContext;
use crate::formats::item_type::ItemType;

use super::{
    inline,
    types::*,
    utils::{self, *},
};

fn clean_args_from_types_and_body_id<'tcx>(
    cx: &mut DocContext<'tcx>,
    types: &[hir::Ty<'tcx>],
    body_id: hir::BodyId,
) -> Arguments {
    let body = cx.tcx.hir().body(body_id);

    Arguments {
        values: types
            .iter()
            .enumerate()
            .map(|(i, ty)| Argument {
                name: name_from_pat(body.params[i].pat),
                type_: clean_ty(ty, cx),
                is_const: false,
            })
            .collect(),
    }
}

fn clean_args_from_types_and_names<'tcx>(
    cx: &mut DocContext<'tcx>,
    types: &[hir::Ty<'tcx>],
    names: &[Ident],
) -> Arguments {
    Arguments {
        values: types
            .iter()
            .enumerate()
            .map(|(i, ty)| Argument {
                type_: clean_ty(ty, cx),
                name: names
                    .get(i)
                    .map(|ident| ident.name)
                    .filter(|ident| !ident.is_empty())
                    .unwrap_or(kw::Underscore),
                is_const: false,
            })
            .collect(),
    }
}

fn clean_assoc_item_constraint<'tcx>(
    constraint: &hir::AssocItemConstraint<'tcx>,
    cx: &mut DocContext<'tcx>,
) -> AssocItemConstraint {
    AssocItemConstraint {
        assoc: PathSegment {
            name: constraint.ident.name,
            args: clean_generic_args(constraint.gen_args, cx),
        },
        kind: match constraint.kind {
            hir::AssocItemConstraintKind::Equality { ref term } => {
                AssocItemConstraintKind::Equality { term: clean_term(term, cx) }
            }
            hir::AssocItemConstraintKind::Bound { bounds } => AssocItemConstraintKind::Bound {
                bounds: bounds.iter().filter_map(|b| clean_generic_bound(b, cx)).collect(),
            },
        },
    }
}

fn clean_bare_fn_ty<'tcx>(
    bare_fn: &hir::BareFnTy<'tcx>,
    cx: &mut DocContext<'tcx>,
) -> BareFunctionDecl {
    let (generic_params, decl) = enter_impl_trait(cx, |cx| {
        // NOTE: generics must be cleaned before args
        let generic_params = bare_fn
            .generic_params
            .iter()
            .filter(|p| !is_elided_lifetime(p))
            .map(|x| clean_generic_param(cx, None, x))
            .collect();
        let args = clean_args_from_types_and_names(cx, bare_fn.decl.inputs, bare_fn.param_names);
        let decl = clean_fn_decl_with_args(cx, bare_fn.decl, None, args);
        (generic_params, decl)
    });
    BareFunctionDecl { safety: bare_fn.safety, abi: bare_fn.abi, decl, generic_params }
}

fn clean_const_arg<'tcx>(constant: &hir::ConstArg<'_>, _cx: &mut DocContext<'tcx>) -> Constant {
    Constant { kind: ConstantKind::Anonymous { body: constant.value.body } }
}

fn clean_extern_crate<'tcx>(
    krate: &hir::Item<'tcx>,
    name: Symbol,
    orig_name: Option<Symbol>,
    cx: &mut DocContext<'tcx>,
) -> Vec<Item> {
    // this is the ID of the `extern crate` statement
    let cnum = cx.tcx.extern_mod_stmt_cnum(krate.owner_id.def_id).unwrap_or(LOCAL_CRATE);
    // this is the ID of the crate itself
    let crate_def_id = cnum.as_def_id();
    let attrs = cx.tcx.hir().attrs(krate.hir_id());
    let ty_vis = cx.tcx.visibility(krate.owner_id);
    let please_inline = ty_vis.is_public()
        && attrs.iter().any(|a| {
            a.has_name(sym::doc)
                && match a.meta_item_list() {
                    Some(l) => attr::list_contains_name(&l, sym::inline),
                    None => false,
                }
        })
        && !cx.output_format.is_json();

    let krate_owner_def_id = krate.owner_id.to_def_id();
    if please_inline {
        if let Some(items) = inline::try_inline(
            cx,
            Res::Def(DefKind::Mod, crate_def_id),
            name,
            Some((attrs, Some(krate_owner_def_id))),
            &mut Default::default(),
        ) {
            return items;
        }
    }

    vec![Item::from_def_id_and_parts(
        krate_owner_def_id,
        Some(name),
        ExternCrateItem { src: orig_name },
        cx,
    )]
}

fn clean_field<'tcx>(field: &hir::FieldDef<'tcx>, cx: &mut DocContext<'tcx>) -> Item {
    super::clean_field_with_def_id(
        field.def_id.to_def_id(),
        field.ident.name,
        clean_ty(field.ty, cx),
        cx,
    )
}

fn clean_fn_decl_with_args<'tcx>(
    cx: &mut DocContext<'tcx>,
    decl: &hir::FnDecl<'tcx>,
    header: Option<&hir::FnHeader>,
    args: Arguments,
) -> FnDecl {
    let mut output = match decl.output {
        hir::FnRetTy::Return(typ) => clean_ty(typ, cx),
        hir::FnRetTy::DefaultReturn(..) => Type::Tuple(Vec::new()),
    };
    if let Some(header) = header
        && header.is_async()
    {
        output = output.sugared_async_return_type();
    }
    FnDecl { inputs: args, output, c_variadic: decl.c_variadic }
}

fn clean_fn_or_proc_macro<'tcx>(
    item: &hir::Item<'tcx>,
    sig: &hir::FnSig<'tcx>,
    generics: &hir::Generics<'tcx>,
    body_id: hir::BodyId,
    name: &mut Symbol,
    cx: &mut DocContext<'tcx>,
) -> ItemKind {
    let attrs = cx.tcx.hir().attrs(item.hir_id());
    let macro_kind = attrs.iter().find_map(|a| {
        if a.has_name(sym::proc_macro) {
            Some(MacroKind::Bang)
        } else if a.has_name(sym::proc_macro_derive) {
            Some(MacroKind::Derive)
        } else if a.has_name(sym::proc_macro_attribute) {
            Some(MacroKind::Attr)
        } else {
            None
        }
    });
    match macro_kind {
        Some(kind) => clean_proc_macro(item, name, kind, cx),
        None => {
            let mut func = clean_fn(cx, sig, generics, FunctionArgs::Body(body_id));
            clean_legacy_const_generics(&mut func, attrs);
            FunctionItem(func)
        }
    }
}

fn clean_fn<'tcx>(
    cx: &mut DocContext<'tcx>,
    sig: &hir::FnSig<'tcx>,
    generics: &hir::Generics<'tcx>,
    args: FunctionArgs<'tcx>,
) -> Box<Function> {
    let (generics, decl) = enter_impl_trait(cx, |cx| {
        // NOTE: generics must be cleaned before args
        let generics = clean_generics(generics, cx);
        let args = match args {
            FunctionArgs::Body(body_id) => {
                clean_args_from_types_and_body_id(cx, sig.decl.inputs, body_id)
            }
            FunctionArgs::Names(names) => {
                clean_args_from_types_and_names(cx, sig.decl.inputs, names)
            }
        };
        let decl = clean_fn_decl_with_args(cx, sig.decl, Some(&sig.header), args);
        (generics, decl)
    });
    Box::new(Function { decl, generics })
}

pub(super) fn clean_foreign_item<'tcx>(
    cx: &mut DocContext<'tcx>,
    item: &hir::ForeignItem<'tcx>,
    renamed: Option<Symbol>,
) -> Item {
    let def_id = item.owner_id.to_def_id();
    cx.with_param_env(def_id, |cx| {
        let kind = match item.kind {
            hir::ForeignItemKind::Fn(decl, names, generics, safety) => {
                let (generics, decl) = enter_impl_trait(cx, |cx| {
                    // NOTE: generics must be cleaned before args
                    let generics = clean_generics(generics, cx);
                    let args = clean_args_from_types_and_names(cx, decl.inputs, names);
                    let decl = clean_fn_decl_with_args(cx, decl, None, args);
                    (generics, decl)
                });
                ForeignFunctionItem(Box::new(Function { decl, generics }), safety)
            }
            hir::ForeignItemKind::Static(ty, mutability, safety) => ForeignStaticItem(
                Static { type_: clean_ty(ty, cx), mutability, expr: None },
                safety,
            ),
            hir::ForeignItemKind::Type => ForeignTypeItem,
        };

        Item::from_def_id_and_parts(
            item.owner_id.def_id.to_def_id(),
            Some(renamed.unwrap_or(item.ident.name)),
            kind,
            cx,
        )
    })
}

fn clean_generic_args<'tcx>(
    generic_args: &hir::GenericArgs<'tcx>,
    cx: &mut DocContext<'tcx>,
) -> GenericArgs {
    // FIXME(return_type_notation): Fix RTN parens rendering
    if let Some((inputs, output)) = generic_args.paren_sugar_inputs_output() {
        let inputs = inputs.iter().map(|x| clean_ty(x, cx)).collect::<Vec<_>>().into();
        let output = match output.kind {
            hir::TyKind::Tup(&[]) => None,
            _ => Some(Box::new(clean_ty(output, cx))),
        };
        GenericArgs::Parenthesized { inputs, output }
    } else {
        let args = generic_args
            .args
            .iter()
            .filter_map(|arg| {
                Some(match arg {
                    hir::GenericArg::Lifetime(lt) if !lt.is_anonymous() => {
                        GenericArg::Lifetime(clean_lifetime(*lt, cx))
                    }
                    hir::GenericArg::Lifetime(_) => GenericArg::Lifetime(Lifetime::elided()),
                    hir::GenericArg::Type(ty) => GenericArg::Type(clean_ty(ty, cx)),
                    // Checking for `is_desugared_from_effects` on the `AnonConst` not only accounts for the case
                    // where the argument is `host` but for all possible cases (e.g., `true`, `false`).
                    hir::GenericArg::Const(hir::ConstArg {
                        is_desugared_from_effects: true,
                        ..
                    }) => {
                        return None;
                    }
                    hir::GenericArg::Const(ct) => {
                        GenericArg::Const(Box::new(clean_const_arg(ct, cx)))
                    }
                    hir::GenericArg::Infer(_inf) => GenericArg::Infer,
                })
            })
            .collect::<Vec<_>>()
            .into();
        let constraints = generic_args
            .constraints
            .iter()
            .map(|c| clean_assoc_item_constraint(c, cx))
            .collect::<ThinVec<_>>();
        GenericArgs::AngleBracketed { args, constraints }
    }
}

fn clean_generic_bound<'tcx>(
    bound: &hir::GenericBound<'tcx>,
    cx: &mut DocContext<'tcx>,
) -> Option<GenericBound> {
    Some(match *bound {
        hir::GenericBound::Outlives(lt) => GenericBound::Outlives(clean_lifetime(lt, cx)),
        hir::GenericBound::Trait(ref t, modifier) => {
            // `T: ~const Destruct` is hidden because `T: Destruct` is a no-op.
            if modifier == hir::TraitBoundModifier::MaybeConst
                && cx.tcx.lang_items().destruct_trait() == Some(t.trait_ref.trait_def_id().unwrap())
            {
                return None;
            }

            GenericBound::TraitBound(clean_poly_trait_ref(t, cx), modifier)
        }
        // FIXME(precise_capturing): Implement rustdoc support
        hir::GenericBound::Use(..) => return None,
    })
}

fn clean_generic_param<'tcx>(
    cx: &mut DocContext<'tcx>,
    generics: Option<&hir::Generics<'tcx>>,
    param: &hir::GenericParam<'tcx>,
) -> GenericParamDef {
    let (name, kind) = match param.kind {
        hir::GenericParamKind::Lifetime { .. } => {
            let outlives = if let Some(generics) = generics {
                generics
                    .outlives_for_param(param.def_id)
                    .filter(|bp| !bp.in_where_clause)
                    .flat_map(|bp| bp.bounds)
                    .map(|bound| match bound {
                        hir::GenericBound::Outlives(lt) => clean_lifetime(lt, cx),
                        _ => panic!(),
                    })
                    .collect()
            } else {
                ThinVec::new()
            };
            (param.name.ident().name, GenericParamDefKind::Lifetime { outlives })
        }
        hir::GenericParamKind::Type { ref default, synthetic } => {
            let bounds = if let Some(generics) = generics {
                generics
                    .bounds_for_param(param.def_id)
                    .filter(|bp| bp.origin != PredicateOrigin::WhereClause)
                    .flat_map(|bp| bp.bounds)
                    .filter_map(|x| clean_generic_bound(x, cx))
                    .collect()
            } else {
                ThinVec::new()
            };
            (
                param.name.ident().name,
                GenericParamDefKind::Type {
                    bounds,
                    default: default.map(|t| clean_ty(t, cx)).map(Box::new),
                    synthetic,
                },
            )
        }
        hir::GenericParamKind::Const { ty, default, is_host_effect } => (
            param.name.ident().name,
            GenericParamDefKind::Const {
                ty: Box::new(clean_ty(ty, cx)),
                default: default
                    .map(|ct| Box::new(ty::Const::from_anon_const(cx.tcx, ct.def_id).to_string())),
                is_host_effect,
            },
        ),
    };

    GenericParamDef { name, def_id: param.def_id.to_def_id(), kind }
}

pub(super) fn clean_generics<'tcx>(
    gens: &hir::Generics<'tcx>,
    cx: &mut DocContext<'tcx>,
) -> Generics {
    let impl_trait_params = gens
        .params
        .iter()
        .filter(|param| is_impl_trait(param))
        .map(|param| {
            let param = clean_generic_param(cx, Some(gens), param);
            match param.kind {
                GenericParamDefKind::Lifetime { .. } => unreachable!(),
                GenericParamDefKind::Type { ref bounds, .. } => {
                    cx.impl_trait_bounds.insert(param.def_id.into(), bounds.to_vec());
                }
                GenericParamDefKind::Const { .. } => unreachable!(),
            }
            param
        })
        .collect::<Vec<_>>();

    let mut bound_predicates = FxIndexMap::default();
    let mut region_predicates = FxIndexMap::default();
    let mut eq_predicates = ThinVec::default();
    for pred in gens.predicates.iter().filter_map(|x| clean_where_predicate(x, cx)) {
        match pred {
            WherePredicate::BoundPredicate { ty, bounds, bound_params } => {
                match bound_predicates.entry(ty) {
                    IndexEntry::Vacant(v) => {
                        v.insert((bounds, bound_params));
                    }
                    IndexEntry::Occupied(mut o) => {
                        // we merge both bounds.
                        for bound in bounds {
                            if !o.get().0.contains(&bound) {
                                o.get_mut().0.push(bound);
                            }
                        }
                        for bound_param in bound_params {
                            if !o.get().1.contains(&bound_param) {
                                o.get_mut().1.push(bound_param);
                            }
                        }
                    }
                }
            }
            WherePredicate::RegionPredicate { lifetime, bounds } => {
                match region_predicates.entry(lifetime) {
                    IndexEntry::Vacant(v) => {
                        v.insert(bounds);
                    }
                    IndexEntry::Occupied(mut o) => {
                        // we merge both bounds.
                        for bound in bounds {
                            if !o.get().contains(&bound) {
                                o.get_mut().push(bound);
                            }
                        }
                    }
                }
            }
            WherePredicate::EqPredicate { lhs, rhs } => {
                eq_predicates.push(WherePredicate::EqPredicate { lhs, rhs });
            }
        }
    }

    let mut params = ThinVec::with_capacity(gens.params.len());
    // In this loop, we gather the generic parameters (`<'a, B: 'a>`) and check if they have
    // bounds in the where predicates. If so, we move their bounds into the where predicates
    // while also preventing duplicates.
    for p in gens.params.iter().filter(|p| !is_impl_trait(p) && !is_elided_lifetime(p)) {
        let mut p = clean_generic_param(cx, Some(gens), p);
        match &mut p.kind {
            GenericParamDefKind::Lifetime { ref mut outlives } => {
                if let Some(region_pred) = region_predicates.get_mut(&Lifetime(p.name)) {
                    // We merge bounds in the `where` clause.
                    for outlive in outlives.drain(..) {
                        let outlive = GenericBound::Outlives(outlive);
                        if !region_pred.contains(&outlive) {
                            region_pred.push(outlive);
                        }
                    }
                }
            }
            GenericParamDefKind::Type { bounds, synthetic: false, .. } => {
                if let Some(bound_pred) = bound_predicates.get_mut(&Type::Generic(p.name)) {
                    // We merge bounds in the `where` clause.
                    for bound in bounds.drain(..) {
                        if !bound_pred.0.contains(&bound) {
                            bound_pred.0.push(bound);
                        }
                    }
                }
            }
            GenericParamDefKind::Type { .. } | GenericParamDefKind::Const { .. } => {
                // nothing to do here.
            }
        }
        params.push(p);
    }
    params.extend(impl_trait_params);

    Generics {
        params,
        where_predicates: bound_predicates
            .into_iter()
            .map(|(ty, (bounds, bound_params))| WherePredicate::BoundPredicate {
                ty,
                bounds,
                bound_params,
            })
            .chain(
                region_predicates
                    .into_iter()
                    .map(|(lifetime, bounds)| WherePredicate::RegionPredicate { lifetime, bounds }),
            )
            .chain(eq_predicates)
            .collect(),
    }
}

fn clean_impl<'tcx>(
    impl_: &hir::Impl<'tcx>,
    def_id: LocalDefId,
    cx: &mut DocContext<'tcx>,
) -> Vec<Item> {
    let tcx = cx.tcx;
    let mut ret = Vec::new();
    let trait_ = impl_.of_trait.as_ref().map(|t| clean_trait_ref(t, cx));
    let items = impl_
        .items
        .iter()
        .map(|ii| clean_impl_item(tcx.hir().impl_item(ii.id), cx))
        .collect::<Vec<_>>();

    // If this impl block is an implementation of the Deref trait, then we
    // need to try inlining the target's inherent impl blocks as well.
    if trait_.as_ref().map(|t| t.def_id()) == tcx.lang_items().deref_trait() {
        build_deref_target_impls(cx, &items, &mut ret);
    }

    let for_ = clean_ty(impl_.self_ty, cx);
    let type_alias =
        for_.def_id(&cx.cache).and_then(|alias_def_id: DefId| match tcx.def_kind(alias_def_id) {
            DefKind::TyAlias => Some(super::clean_middle_ty(
                ty::Binder::dummy(tcx.type_of(def_id).instantiate_identity()),
                cx,
                Some(def_id.to_def_id()),
                None,
            )),
            _ => None,
        });
    let mut make_item = |trait_: Option<Path>, for_: Type, items: Vec<Item>| {
        let kind = ImplItem(Box::new(Impl {
            safety: impl_.safety,
            generics: clean_generics(impl_.generics, cx),
            trait_,
            for_,
            items,
            polarity: tcx.impl_polarity(def_id),
            kind: if utils::has_doc_flag(tcx, def_id.to_def_id(), sym::fake_variadic) {
                ImplKind::FakeVariadic
            } else {
                ImplKind::Normal
            },
        }));
        Item::from_def_id_and_parts(def_id.to_def_id(), None, kind, cx)
    };
    if let Some(type_alias) = type_alias {
        ret.push(make_item(trait_.clone(), type_alias, items.clone()));
    }
    ret.push(make_item(trait_, for_, items));
    ret
}

pub(super) fn clean_impl_item<'tcx>(
    impl_: &hir::ImplItem<'tcx>,
    cx: &mut DocContext<'tcx>,
) -> Item {
    let local_did = impl_.owner_id.to_def_id();
    cx.with_param_env(local_did, |cx| {
        let inner = match impl_.kind {
            hir::ImplItemKind::Const(ty, expr) => {
                let generics = clean_generics(impl_.generics, cx);
                let default = ConstantKind::Local { def_id: local_did, body: expr };
                AssocConstItem(generics, Box::new(clean_ty(ty, cx)), default)
            }
            hir::ImplItemKind::Fn(ref sig, body) => {
                let m = clean_fn(cx, sig, impl_.generics, FunctionArgs::Body(body));
                let defaultness = cx.tcx.defaultness(impl_.owner_id);
                MethodItem(m, Some(defaultness))
            }
            hir::ImplItemKind::Type(hir_ty) => {
                let type_ = clean_ty(hir_ty, cx);
                let generics = clean_generics(impl_.generics, cx);
                let item_type = super::clean_middle_ty(
                    ty::Binder::dummy(lower_ty(cx.tcx, hir_ty)),
                    cx,
                    None,
                    None,
                );
                AssocTypeItem(
                    Box::new(TypeAlias {
                        type_,
                        generics,
                        inner_type: None,
                        item_type: Some(item_type),
                    }),
                    Vec::new(),
                )
            }
        };

        Item::from_def_id_and_parts(local_did, Some(impl_.ident.name), inner, cx)
    })
}

pub(super) fn clean_item<'tcx>(
    cx: &mut DocContext<'tcx>,
    item: &hir::Item<'tcx>,
    renamed: Option<Symbol>,
    import_id: Option<LocalDefId>,
) -> Vec<Item> {
    use hir::ItemKind;

    let def_id = item.owner_id.to_def_id();
    let mut name = renamed.unwrap_or_else(|| cx.tcx.hir().name(item.hir_id()));
    cx.with_param_env(def_id, |cx| {
        let kind = match item.kind {
            ItemKind::Static(ty, mutability, body_id) => {
                StaticItem(Static { type_: clean_ty(ty, cx), mutability, expr: Some(body_id) })
            }
            ItemKind::Const(ty, generics, body_id) => ConstantItem(
                clean_generics(generics, cx),
                Box::new(clean_ty(ty, cx)),
                Constant { kind: ConstantKind::Local { body: body_id, def_id } },
            ),
            ItemKind::OpaqueTy(ref ty) => OpaqueTyItem(OpaqueTy {
                bounds: ty.bounds.iter().filter_map(|x| clean_generic_bound(x, cx)).collect(),
                generics: clean_generics(ty.generics, cx),
            }),
            ItemKind::TyAlias(hir_ty, generics) => {
                *cx.current_type_aliases.entry(def_id).or_insert(0) += 1;
                let rustdoc_ty = clean_ty(hir_ty, cx);
                let type_ = super::clean_middle_ty(
                    ty::Binder::dummy(lower_ty(cx.tcx, hir_ty)),
                    cx,
                    None,
                    None,
                );
                let generics = clean_generics(generics, cx);
                if let Some(count) = cx.current_type_aliases.get_mut(&def_id) {
                    *count -= 1;
                    if *count == 0 {
                        cx.current_type_aliases.remove(&def_id);
                    }
                }

                let ty = cx.tcx.type_of(def_id).instantiate_identity();

                let mut ret = Vec::new();
                let inner_type = super::clean_ty_alias_inner_type(ty, cx, &mut ret);

                ret.push(super::generate_item_with_correct_attrs(
                    cx,
                    TypeAliasItem(Box::new(TypeAlias {
                        generics,
                        inner_type,
                        type_: rustdoc_ty,
                        item_type: Some(type_),
                    })),
                    item.owner_id.def_id.to_def_id(),
                    name,
                    import_id,
                    renamed,
                ));
                return ret;
            }
            ItemKind::Enum(ref def, generics) => EnumItem(Enum {
                variants: def.variants.iter().map(|v| clean_variant(v, cx)).collect(),
                generics: clean_generics(generics, cx),
            }),
            ItemKind::TraitAlias(generics, bounds) => TraitAliasItem(TraitAlias {
                generics: clean_generics(generics, cx),
                bounds: bounds.iter().filter_map(|x| clean_generic_bound(x, cx)).collect(),
            }),
            ItemKind::Union(ref variant_data, generics) => UnionItem(Union {
                generics: clean_generics(generics, cx),
                fields: variant_data.fields().iter().map(|x| clean_field(x, cx)).collect(),
            }),
            ItemKind::Struct(ref variant_data, generics) => StructItem(Struct {
                ctor_kind: variant_data.ctor_kind(),
                generics: clean_generics(generics, cx),
                fields: variant_data.fields().iter().map(|x| clean_field(x, cx)).collect(),
            }),
            ItemKind::Impl(impl_) => return clean_impl(impl_, item.owner_id.def_id, cx),
            ItemKind::Macro(ref macro_def, MacroKind::Bang) => {
                let ty_vis = cx.tcx.visibility(def_id);
                MacroItem(Macro {
                    // FIXME this shouldn't be false
                    source: display_macro_source(cx, name, macro_def, def_id, ty_vis, false),
                })
            }
            ItemKind::Macro(_, macro_kind) => clean_proc_macro(item, &mut name, macro_kind, cx),
            // proc macros can have a name set by attributes
            ItemKind::Fn(ref sig, generics, body_id) => {
                clean_fn_or_proc_macro(item, sig, generics, body_id, &mut name, cx)
            }
            ItemKind::Trait(_, _, generics, bounds, item_ids) => {
                let items = item_ids
                    .iter()
                    .map(|ti| clean_trait_item(cx.tcx.hir().trait_item(ti.id), cx))
                    .collect();

                TraitItem(Box::new(Trait {
                    def_id,
                    items,
                    generics: clean_generics(generics, cx),
                    bounds: bounds.iter().filter_map(|x| clean_generic_bound(x, cx)).collect(),
                }))
            }
            ItemKind::ExternCrate(orig_name) => {
                return clean_extern_crate(item, name, orig_name, cx);
            }
            ItemKind::Use(path, kind) => {
                return clean_use_statement(item, name, path, kind, cx, &mut FxHashSet::default());
            }
            _ => unreachable!("not yet converted"),
        };

        vec![super::generate_item_with_correct_attrs(
            cx,
            kind,
            item.owner_id.def_id.to_def_id(),
            name,
            import_id,
            renamed,
        )]
    })
}

/// This is needed to make it more "readable" when documenting functions using
/// `rustc_legacy_const_generics`. More information in
/// <https://github.com/rust-lang/rust/issues/83167>.
fn clean_legacy_const_generics(func: &mut Function, attrs: &[ast::Attribute]) {
    for meta_item_list in attrs
        .iter()
        .filter(|a| a.has_name(sym::rustc_legacy_const_generics))
        .filter_map(|a| a.meta_item_list())
    {
        for (pos, literal) in meta_item_list.iter().filter_map(|meta| meta.lit()).enumerate() {
            match literal.kind {
                ast::LitKind::Int(a, _) => {
                    let gen = func.generics.params.remove(0);
                    if let GenericParamDef {
                        name,
                        kind: GenericParamDefKind::Const { ty, .. },
                        ..
                    } = gen
                    {
                        func.decl
                            .inputs
                            .values
                            .insert(a.get() as _, Argument { name, type_: *ty, is_const: true });
                    } else {
                        panic!("unexpected non const in position {pos}");
                    }
                }
                _ => panic!("invalid arg index"),
            }
        }
    }
}

fn clean_lifetime<'tcx>(lifetime: &hir::Lifetime, cx: &mut DocContext<'tcx>) -> Lifetime {
    if let Some(
        rbv::ResolvedArg::EarlyBound(did)
        | rbv::ResolvedArg::LateBound(_, _, did)
        | rbv::ResolvedArg::Free(_, did),
    ) = cx.tcx.named_bound_var(lifetime.hir_id)
        && let Some(lt) = cx.args.get(&did).and_then(|arg| arg.as_lt())
    {
        return lt.clone();
    }
    Lifetime(lifetime.ident.name)
}

fn clean_path<'tcx>(path: &hir::Path<'tcx>, cx: &mut DocContext<'tcx>) -> Path {
    Path {
        res: path.res,
        segments: path.segments.iter().map(|x| clean_path_segment(x, cx)).collect(),
    }
}

fn clean_path_segment<'tcx>(
    path: &hir::PathSegment<'tcx>,
    cx: &mut DocContext<'tcx>,
) -> PathSegment {
    PathSegment { name: path.ident.name, args: clean_generic_args(path.args(), cx) }
}

fn clean_poly_trait_ref<'tcx>(
    poly_trait_ref: &hir::PolyTraitRef<'tcx>,
    cx: &mut DocContext<'tcx>,
) -> PolyTrait {
    PolyTrait {
        trait_: clean_trait_ref(&poly_trait_ref.trait_ref, cx),
        generic_params: poly_trait_ref
            .bound_generic_params
            .iter()
            .filter(|p| !is_elided_lifetime(p))
            .map(|x| clean_generic_param(cx, None, x))
            .collect(),
    }
}

fn clean_proc_macro<'tcx>(
    item: &hir::Item<'tcx>,
    name: &mut Symbol,
    kind: MacroKind,
    cx: &mut DocContext<'tcx>,
) -> ItemKind {
    let attrs = cx.tcx.hir().attrs(item.hir_id());
    if kind == MacroKind::Derive
        && let Some(derive_name) = attrs.lists(sym::proc_macro_derive).find_map(|mi| mi.ident())
    {
        *name = derive_name.name;
    }

    let mut helpers = Vec::new();
    for mi in attrs.lists(sym::proc_macro_derive) {
        if !mi.has_name(sym::attributes) {
            continue;
        }

        if let Some(list) = mi.meta_item_list() {
            for inner_mi in list {
                if let Some(ident) = inner_mi.ident() {
                    helpers.push(ident.name);
                }
            }
        }
    }
    ProcMacroItem(ProcMacro { kind, helpers })
}

fn clean_qpath<'tcx>(hir_ty: &hir::Ty<'tcx>, cx: &mut DocContext<'tcx>) -> Type {
    let hir::Ty { hir_id, span, ref kind } = *hir_ty;
    let hir::TyKind::Path(qpath) = kind else { unreachable!() };

    match qpath {
        hir::QPath::Resolved(None, path) => {
            if let Res::Def(DefKind::TyParam, did) = path.res {
                if let Some(new_ty) = cx.args.get(&did).and_then(|p| p.as_ty()).cloned() {
                    return new_ty;
                }
                if let Some(bounds) = cx.impl_trait_bounds.remove(&did.into()) {
                    return ImplTrait(bounds);
                }
            }

            if let Some(expanded) = maybe_expand_private_type_alias(cx, path) {
                expanded
            } else {
                // First we check if it's a private re-export.
                let path = if let Some(path) = first_non_private(cx, hir_id, &path) {
                    path
                } else {
                    clean_path(path, cx)
                };
                resolve_type(cx, path)
            }
        }
        hir::QPath::Resolved(Some(qself), p) => {
            // Try to normalize `<X as Y>::T` to a type
            let ty = lower_ty(cx.tcx, hir_ty);
            // `hir_to_ty` can return projection types with escaping vars for GATs, e.g. `<() as Trait>::Gat<'_>`
            if !ty.has_escaping_bound_vars()
                && let Some(normalized_value) = super::normalize(cx, ty::Binder::dummy(ty))
            {
                return super::clean_middle_ty(normalized_value, cx, None, None);
            }

            let trait_segments = &p.segments[..p.segments.len() - 1];
            let trait_def = cx.tcx.associated_item(p.res.def_id()).container_id(cx.tcx);
            let trait_ = self::Path {
                res: Res::Def(DefKind::Trait, trait_def),
                segments: trait_segments.iter().map(|x| clean_path_segment(x, cx)).collect(),
            };
            register_res(cx, trait_.res);
            let self_def_id = DefId::local(qself.hir_id.owner.def_id.local_def_index);
            let self_type = clean_ty(qself, cx);
            let should_show_cast =
                super::compute_should_show_cast(Some(self_def_id), &trait_, &self_type);
            Type::QPath(Box::new(QPathData {
                assoc: clean_path_segment(p.segments.last().expect("segments were empty"), cx),
                should_show_cast,
                self_type,
                trait_: Some(trait_),
            }))
        }
        hir::QPath::TypeRelative(qself, segment) => {
            let ty = lower_ty(cx.tcx, hir_ty);
            let self_type = clean_ty(qself, cx);

            let (trait_, should_show_cast) = match ty.kind() {
                ty::Alias(ty::Projection, proj) => {
                    let res = Res::Def(DefKind::Trait, proj.trait_ref(cx.tcx).def_id);
                    let trait_ = clean_path(&hir::Path { span, res, segments: &[] }, cx);
                    register_res(cx, trait_.res);
                    let self_def_id = res.opt_def_id();
                    let should_show_cast =
                        super::compute_should_show_cast(self_def_id, &trait_, &self_type);

                    (Some(trait_), should_show_cast)
                }
                ty::Alias(ty::Inherent, _) => (None, false),
                // Rustdoc handles `ty::Error`s by turning them into `Type::Infer`s.
                ty::Error(_) => return Type::Infer,
                _ => bug!("clean: expected associated type, found `{ty:?}`"),
            };

            Type::QPath(Box::new(QPathData {
                assoc: clean_path_segment(segment, cx),
                should_show_cast,
                self_type,
                trait_,
            }))
        }
        hir::QPath::LangItem(..) => bug!("clean: requiring documentation of lang item"),
    }
}

fn clean_term<'tcx>(term: &hir::Term<'tcx>, cx: &mut DocContext<'tcx>) -> Term {
    match term {
        hir::Term::Ty(ty) => Term::Type(clean_ty(ty, cx)),
        hir::Term::Const(c) => Term::Constant(super::clean_middle_const(
            ty::Binder::dummy(ty::Const::from_anon_const(cx.tcx, c.def_id)),
            cx,
        )),
    }
}

fn clean_trait_item<'tcx>(trait_item: &hir::TraitItem<'tcx>, cx: &mut DocContext<'tcx>) -> Item {
    let local_did = trait_item.owner_id.to_def_id();
    cx.with_param_env(local_did, |cx| {
        let inner = match trait_item.kind {
            hir::TraitItemKind::Const(ty, Some(default)) => {
                let generics = enter_impl_trait(cx, |cx| clean_generics(trait_item.generics, cx));
                AssocConstItem(
                    generics,
                    Box::new(clean_ty(ty, cx)),
                    ConstantKind::Local { def_id: local_did, body: default },
                )
            }
            hir::TraitItemKind::Const(ty, None) => {
                let generics = enter_impl_trait(cx, |cx| clean_generics(trait_item.generics, cx));
                TyAssocConstItem(generics, Box::new(clean_ty(ty, cx)))
            }
            hir::TraitItemKind::Fn(ref sig, hir::TraitFn::Provided(body)) => {
                let m = clean_fn(cx, sig, trait_item.generics, FunctionArgs::Body(body));
                MethodItem(m, None)
            }
            hir::TraitItemKind::Fn(ref sig, hir::TraitFn::Required(names)) => {
                let m = clean_fn(cx, sig, trait_item.generics, FunctionArgs::Names(names));
                TyMethodItem(m)
            }
            hir::TraitItemKind::Type(bounds, Some(default)) => {
                let generics = enter_impl_trait(cx, |cx| clean_generics(trait_item.generics, cx));
                let bounds = bounds.iter().filter_map(|x| clean_generic_bound(x, cx)).collect();
                let item_type = super::clean_middle_ty(
                    ty::Binder::dummy(lower_ty(cx.tcx, default)),
                    cx,
                    None,
                    None,
                );
                AssocTypeItem(
                    Box::new(TypeAlias {
                        type_: clean_ty(default, cx),
                        generics,
                        inner_type: None,
                        item_type: Some(item_type),
                    }),
                    bounds,
                )
            }
            hir::TraitItemKind::Type(bounds, None) => {
                let generics = enter_impl_trait(cx, |cx| clean_generics(trait_item.generics, cx));
                let bounds = bounds.iter().filter_map(|x| clean_generic_bound(x, cx)).collect();
                TyAssocTypeItem(generics, bounds)
            }
        };
        Item::from_def_id_and_parts(local_did, Some(trait_item.ident.name), inner, cx)
    })
}

fn clean_trait_ref<'tcx>(trait_ref: &hir::TraitRef<'tcx>, cx: &mut DocContext<'tcx>) -> Path {
    let path = clean_path(trait_ref.path, cx);
    register_res(cx, path.res);
    path
}

pub(super) fn clean_ty<'tcx>(ty: &hir::Ty<'tcx>, cx: &mut DocContext<'tcx>) -> Type {
    use rustc_hir::*;

    match ty.kind {
        TyKind::Never => Primitive(PrimitiveType::Never),
        TyKind::Ptr(ref m) => RawPointer(m.mutbl, Box::new(clean_ty(m.ty, cx))),
        TyKind::Ref(ref l, ref m) => {
            let lifetime = if l.is_anonymous() { None } else { Some(clean_lifetime(*l, cx)) };
            BorrowedRef { lifetime, mutability: m.mutbl, type_: Box::new(clean_ty(m.ty, cx)) }
        }
        TyKind::Slice(ty) => Slice(Box::new(clean_ty(ty, cx))),
        TyKind::Pat(ty, pat) => Type::Pat(Box::new(clean_ty(ty, cx)), format!("{pat:?}").into()),
        TyKind::Array(ty, ref length) => {
            let length = match length {
                hir::ArrayLen::Infer(..) => "_".to_string(),
                hir::ArrayLen::Body(anon_const) => {
                    // NOTE(min_const_generics): We can't use `const_eval_poly` for constants
                    // as we currently do not supply the parent generics to anonymous constants
                    // but do allow `ConstKind::Param`.
                    //
                    // `const_eval_poly` tries to first substitute generic parameters which
                    // results in an ICE while manually constructing the constant and using `eval`
                    // does nothing for `ConstKind::Param`.
                    let ct = ty::Const::from_anon_const(cx.tcx, anon_const.def_id);
                    let param_env = cx.tcx.param_env(anon_const.def_id);
                    print_const(cx, ct.normalize(cx.tcx, param_env))
                }
            };

            Array(Box::new(clean_ty(ty, cx)), length.into())
        }
        TyKind::Tup(tys) => Tuple(tys.iter().map(|ty| clean_ty(ty, cx)).collect()),
        TyKind::OpaqueDef(item_id, _, _) => {
            let item = cx.tcx.hir().item(item_id);
            if let hir::ItemKind::OpaqueTy(ref ty) = item.kind {
                ImplTrait(ty.bounds.iter().filter_map(|x| clean_generic_bound(x, cx)).collect())
            } else {
                unreachable!()
            }
        }
        TyKind::Path(_) => clean_qpath(ty, cx),
        TyKind::TraitObject(bounds, ref lifetime, _) => {
            let bounds = bounds.iter().map(|bound| clean_poly_trait_ref(bound, cx)).collect();
            let lifetime =
                if !lifetime.is_elided() { Some(clean_lifetime(*lifetime, cx)) } else { None };
            DynTrait(bounds, lifetime)
        }
        TyKind::BareFn(barefn) => BareFunction(Box::new(clean_bare_fn_ty(barefn, cx))),
        // Rustdoc handles `TyKind::Err`s by turning them into `Type::Infer`s.
        TyKind::Infer | TyKind::Err(_) | TyKind::Typeof(..) | TyKind::InferDelegation(..) => Infer,
        TyKind::AnonAdt(..) => {
            unimplemented!("Anonymous structs or unions are not supported yet")
        }
    }
}

pub(super) fn clean_use_statement<'tcx>(
    import: &hir::Item<'tcx>,
    name: Symbol,
    path: &hir::UsePath<'tcx>,
    kind: hir::UseKind,
    cx: &mut DocContext<'tcx>,
    inlined_names: &mut FxHashSet<(ItemType, Symbol)>,
) -> Vec<Item> {
    let mut items = Vec::new();
    let hir::UsePath { segments, ref res, span } = *path;
    for &res in res {
        let path = hir::Path { segments, res, span };
        items.append(&mut clean_use_statement_inner(import, name, &path, kind, cx, inlined_names));
    }
    items
}

pub(super) fn clean_use_statement_inner<'tcx>(
    import: &hir::Item<'tcx>,
    name: Symbol,
    path: &hir::Path<'tcx>,
    kind: hir::UseKind,
    cx: &mut DocContext<'tcx>,
    inlined_names: &mut FxHashSet<(ItemType, Symbol)>,
) -> Vec<Item> {
    if should_ignore_res(path.res) {
        return Vec::new();
    }
    // We need this comparison because some imports (for std types for example)
    // are "inserted" as well but directly by the compiler and they should not be
    // taken into account.
    if import.span.ctxt().outer_expn_data().kind == ExpnKind::AstPass(AstPass::StdImports) {
        return Vec::new();
    }

    let visibility = cx.tcx.visibility(import.owner_id);
    let attrs = cx.tcx.hir().attrs(import.hir_id());
    let inline_attr = attrs.lists(sym::doc).get_word_attr(sym::inline);
    let pub_underscore = visibility.is_public() && name == kw::Underscore;
    let current_mod = cx.tcx.parent_module_from_def_id(import.owner_id.def_id);
    let import_def_id = import.owner_id.def_id.to_def_id();

    // The parent of the module in which this import resides. This
    // is the same as `current_mod` if that's already the top
    // level module.
    let parent_mod = cx.tcx.parent_module_from_def_id(current_mod.to_local_def_id());

    // This checks if the import can be seen from a higher level module.
    // In other words, it checks if the visibility is the equivalent of
    // `pub(super)` or higher. If the current module is the top level
    // module, there isn't really a parent module, which makes the results
    // meaningless. In this case, we make sure the answer is `false`.
    let is_visible_from_parent_mod =
        visibility.is_accessible_from(parent_mod, cx.tcx) && !current_mod.is_top_level_module();

    if pub_underscore && let Some(ref inline) = inline_attr {
        struct_span_code_err!(
            cx.tcx.dcx(),
            inline.span(),
            E0780,
            "anonymous imports cannot be inlined"
        )
        .with_span_label(import.span, "anonymous import")
        .emit();
    }

    // We consider inlining the documentation of `pub use` statements, but we
    // forcefully don't inline if this is not public or if the
    // #[doc(no_inline)] attribute is present.
    // Don't inline doc(hidden) imports so they can be stripped at a later stage.
    let mut denied = cx.output_format.is_json()
        || !(visibility.is_public()
            || (cx.render_options.document_private && is_visible_from_parent_mod))
        || pub_underscore
        || attrs.iter().any(|a| {
            a.has_name(sym::doc)
                && match a.meta_item_list() {
                    Some(l) => {
                        attr::list_contains_name(&l, sym::no_inline)
                            || attr::list_contains_name(&l, sym::hidden)
                    }
                    None => false,
                }
        });

    // Also check whether imports were asked to be inlined, in case we're trying to re-export a
    // crate in Rust 2018+
    let path = clean_path(path, cx);
    let inner = if kind == hir::UseKind::Glob {
        if !denied {
            let mut visited = DefIdSet::default();
            if let Some(items) = inline::try_inline_glob(
                cx,
                path.res,
                current_mod,
                &mut visited,
                inlined_names,
                import,
            ) {
                return items;
            }
        }
        Import::new_glob(resolve_use_source(cx, path), true)
    } else {
        if inline_attr.is_none()
            && let Res::Def(DefKind::Mod, did) = path.res
            && !did.is_local()
            && did.is_crate_root()
        {
            // if we're `pub use`ing an extern crate root, don't inline it unless we
            // were specifically asked for it
            denied = true;
        }
        if !denied
            && let Some(mut items) = inline::try_inline(
                cx,
                path.res,
                name,
                Some((attrs, Some(import_def_id))),
                &mut Default::default(),
            )
        {
            items.push(Item::from_def_id_and_parts(
                import_def_id,
                None,
                ImportItem(Import::new_simple(name, resolve_use_source(cx, path), false)),
                cx,
            ));
            return items;
        }
        Import::new_simple(name, resolve_use_source(cx, path), true)
    };

    vec![Item::from_def_id_and_parts(import_def_id, None, ImportItem(inner), cx)]
}

fn clean_variant<'tcx>(variant: &hir::Variant<'tcx>, cx: &mut DocContext<'tcx>) -> Item {
    let kind = VariantItem(clean_variant_data(&variant.data, &variant.disr_expr, cx));
    Item::from_def_id_and_parts(variant.def_id.to_def_id(), Some(variant.ident.name), kind, cx)
}

fn clean_variant_data<'tcx>(
    variant: &hir::VariantData<'tcx>,
    disr_expr: &Option<&hir::AnonConst>,
    cx: &mut DocContext<'tcx>,
) -> Variant {
    let discriminant = disr_expr
        .map(|disr| Discriminant { expr: Some(disr.body), value: disr.def_id.to_def_id() });

    let kind = match variant {
        hir::VariantData::Struct { fields, .. } => VariantKind::Struct(VariantStruct {
            fields: fields.iter().map(|x| clean_field(x, cx)).collect(),
        }),
        hir::VariantData::Tuple(..) => {
            VariantKind::Tuple(variant.fields().iter().map(|x| clean_field(x, cx)).collect())
        }
        hir::VariantData::Unit(..) => VariantKind::CLike,
    };

    Variant { discriminant, kind }
}

fn clean_where_predicate<'tcx>(
    predicate: &hir::WherePredicate<'tcx>,
    cx: &mut DocContext<'tcx>,
) -> Option<WherePredicate> {
    if !predicate.in_where_clause() {
        return None;
    }
    Some(match *predicate {
        hir::WherePredicate::BoundPredicate(ref wbp) => {
            let bound_params = wbp
                .bound_generic_params
                .iter()
                .map(|param| clean_generic_param(cx, None, param))
                .collect();
            WherePredicate::BoundPredicate {
                ty: clean_ty(wbp.bounded_ty, cx),
                bounds: wbp.bounds.iter().filter_map(|x| clean_generic_bound(x, cx)).collect(),
                bound_params,
            }
        }

        hir::WherePredicate::RegionPredicate(ref wrp) => WherePredicate::RegionPredicate {
            lifetime: clean_lifetime(wrp.lifetime, cx),
            bounds: wrp.bounds.iter().filter_map(|x| clean_generic_bound(x, cx)).collect(),
        },

        hir::WherePredicate::EqPredicate(ref wrp) => WherePredicate::EqPredicate {
            lhs: clean_ty(wrp.lhs_ty, cx),
            rhs: clean_ty(wrp.rhs_ty, cx).into(),
        },
    })
}

/// The goal of this function is to return the first `Path` which is not private (ie not private
/// or `doc(hidden)`). If it's not possible, it'll return the "end type".
///
/// If the path is not a re-export or is public, it'll return `None`.
fn first_non_private<'tcx>(
    cx: &mut DocContext<'tcx>,
    hir_id: hir::HirId,
    path: &hir::Path<'tcx>,
) -> Option<Path> {
    let target_def_id = path.res.opt_def_id()?;
    let (parent_def_id, ident) = match &path.segments {
        [] => return None,
        // Relative paths are available in the same scope as the owner.
        [leaf] => (cx.tcx.local_parent(hir_id.owner.def_id), leaf.ident),
        // So are self paths.
        [parent, leaf] if parent.ident.name == kw::SelfLower => {
            (cx.tcx.local_parent(hir_id.owner.def_id), leaf.ident)
        }
        // Crate paths are not. We start from the crate root.
        [parent, leaf] if matches!(parent.ident.name, kw::Crate | kw::PathRoot) => {
            (LOCAL_CRATE.as_def_id().as_local()?, leaf.ident)
        }
        [parent, leaf] if parent.ident.name == kw::Super => {
            let parent_mod = cx.tcx.parent_module(hir_id);
            if let Some(super_parent) = cx.tcx.opt_local_parent(parent_mod.to_local_def_id()) {
                (super_parent, leaf.ident)
            } else {
                // If we can't find the parent of the parent, then the parent is already the crate.
                (LOCAL_CRATE.as_def_id().as_local()?, leaf.ident)
            }
        }
        // Absolute paths are not. We start from the parent of the item.
        [.., parent, leaf] => (parent.res.opt_def_id()?.as_local()?, leaf.ident),
    };
    // First we try to get the `DefId` of the item.
    for child in
        cx.tcx.module_children_local(parent_def_id).iter().filter(move |c| c.ident == ident)
    {
        if let Res::Def(DefKind::Ctor(..), _) | Res::SelfCtor(..) = child.res {
            continue;
        }

        if let Some(def_id) = child.res.opt_def_id()
            && target_def_id == def_id
        {
            let mut last_path_res = None;
            'reexps: for reexp in child.reexport_chain.iter() {
                if let Some(use_def_id) = reexp.id()
                    && let Some(local_use_def_id) = use_def_id.as_local()
                    && let hir::Node::Item(item) = cx.tcx.hir_node_by_def_id(local_use_def_id)
                    && !item.ident.name.is_empty()
                    && let hir::ItemKind::Use(path, _) = item.kind
                {
                    for res in &path.res {
                        if let Res::Def(DefKind::Ctor(..), _) | Res::SelfCtor(..) = res {
                            continue;
                        }
                        if (cx.render_options.document_hidden ||
                            !cx.tcx.is_doc_hidden(use_def_id)) &&
                            // We never check for "cx.render_options.document_private"
                            // because if a re-export is not fully public, it's never
                            // documented.
                            cx.tcx.local_visibility(local_use_def_id).is_public()
                        {
                            break 'reexps;
                        }
                        last_path_res = Some((path, res));
                        continue 'reexps;
                    }
                }
            }
            if !child.reexport_chain.is_empty() {
                // So in here, we use the data we gathered from iterating the reexports. If
                // `last_path_res` is set, it can mean two things:
                //
                // 1. We found a public reexport.
                // 2. We didn't find a public reexport so it's the "end type" path.
                if let Some((new_path, _)) = last_path_res {
                    return Some(first_non_private_clean_path(
                        cx,
                        path,
                        new_path.segments,
                        new_path.span,
                    ));
                }
                // If `last_path_res` is `None`, it can mean two things:
                //
                // 1. The re-export is public, no need to change anything, just use the path as is.
                // 2. Nothing was found, so let's just return the original path.
                return None;
            }
        }
    }
    None
}

fn first_non_private_clean_path<'tcx>(
    cx: &mut DocContext<'tcx>,
    path: &hir::Path<'tcx>,
    new_path_segments: &'tcx [hir::PathSegment<'tcx>],
    new_path_span: rustc_span::Span,
) -> Path {
    let new_hir_path =
        hir::Path { segments: new_path_segments, res: path.res, span: new_path_span };
    let mut new_clean_path = clean_path(&new_hir_path, cx);
    // In here we need to play with the path data one last time to provide it the
    // missing `args` and `res` of the final `Path` we get, which, since it comes
    // from a re-export, doesn't have the generics that were originally there, so
    // we add them by hand.
    if let Some(path_last) = path.segments.last().as_ref()
        && let Some(new_path_last) = new_clean_path.segments[..].last_mut()
        && let Some(path_last_args) = path_last.args.as_ref()
        && path_last.args.is_some()
    {
        assert!(new_path_last.args.is_empty());
        new_path_last.args = clean_generic_args(path_last_args, cx);
    }
    new_clean_path
}

/// This can happen for `async fn`, e.g. `async fn f<'_>(&'_ self)`.
///
/// See `lifetime_to_generic_param` in `rustc_ast_lowering` for more information.
fn is_elided_lifetime(param: &hir::GenericParam<'_>) -> bool {
    matches!(
        param.kind,
        hir::GenericParamKind::Lifetime { kind: hir::LifetimeParamKind::Elided(_) }
    )
}

/// Synthetic type-parameters are inserted after normal ones.
/// In order for normal parameters to be able to refer to synthetic ones,
/// scans them first.
fn is_impl_trait(param: &hir::GenericParam<'_>) -> bool {
    match param.kind {
        hir::GenericParamKind::Type { synthetic, .. } => synthetic,
        _ => false,
    }
}

fn maybe_expand_private_type_alias<'tcx>(
    cx: &mut DocContext<'tcx>,
    path: &hir::Path<'tcx>,
) -> Option<Type> {
    let Res::Def(DefKind::TyAlias, def_id) = path.res else { return None };
    // Substitute private type aliases
    let def_id = def_id.as_local()?;
    let alias = if !cx.cache.effective_visibilities.is_exported(cx.tcx, def_id.to_def_id())
        && !cx.current_type_aliases.contains_key(&def_id.to_def_id())
    {
        &cx.tcx.hir().expect_item(def_id).kind
    } else {
        return None;
    };
    let hir::ItemKind::TyAlias(ty, generics) = alias else { return None };

    let provided_params = &path.segments.last().expect("segments were empty");
    let mut args = DefIdMap::default();
    let generic_args = provided_params.args();

    let mut indices: hir::GenericParamCount = Default::default();
    for param in generics.params.iter() {
        match param.kind {
            hir::GenericParamKind::Lifetime { .. } => {
                let mut j = 0;
                let lifetime = generic_args.args.iter().find_map(|arg| match arg {
                    hir::GenericArg::Lifetime(lt) => {
                        if indices.lifetimes == j {
                            return Some(lt);
                        }
                        j += 1;
                        None
                    }
                    _ => None,
                });
                if let Some(lt) = lifetime {
                    let lt = if !lt.is_anonymous() {
                        clean_lifetime(lt, cx)
                    } else {
                        Lifetime::elided()
                    };
                    args.insert(param.def_id.to_def_id(), GenericArg::Lifetime(lt));
                }
                indices.lifetimes += 1;
            }
            hir::GenericParamKind::Type { ref default, .. } => {
                let mut j = 0;
                let type_ = generic_args.args.iter().find_map(|arg| match arg {
                    hir::GenericArg::Type(ty) => {
                        if indices.types == j {
                            return Some(*ty);
                        }
                        j += 1;
                        None
                    }
                    _ => None,
                });
                if let Some(ty) = type_.or(*default) {
                    args.insert(param.def_id.to_def_id(), GenericArg::Type(clean_ty(ty, cx)));
                }
                indices.types += 1;
            }
            // FIXME(#82852): Instantiate const parameters.
            hir::GenericParamKind::Const { .. } => {}
        }
    }

    Some(cx.enter_alias(args, def_id.to_def_id(), |cx| {
        cx.with_param_env(def_id.to_def_id(), |cx| clean_ty(&ty, cx))
    }))
}

enum FunctionArgs<'tcx> {
    Body(hir::BodyId),
    Names(&'tcx [Ident]),
}
