use crate::clean::utils::print_const_expr;
use crate::formats::{cache::Cache, item_type::ItemType};
use crate::html::{escape::Escape, format::Buffer};
use rustc_hir::def::{CtorKind, DefKind};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::interpret::{AllocRange, ConstValue, Scalar};
use rustc_middle::mir::ConstantKind;
use rustc_middle::ty::{self, util::is_doc_hidden};
use rustc_middle::ty::{Const, ConstInt, DefIdTree, FieldDef, ParamConst, ScalarInt};
use rustc_middle::ty::{Ty, TyCtxt, TypeVisitable, Visibility};
use rustc_target::abi::Size;
use std::fmt::Write;

// FIXME: respect `Buffer.for_html`

const DEPTH_LIMIT: u32 = 2;
const DEPTH_ELLIPSIS_HTML: &str = r#"<span class="ellipsis">…</span>"#;
const LENGTH_ELLIPSIS_HTML: &str = r#"<span class="ellipsis">………</span>"#;

#[derive(Clone, Copy)]
pub(crate) enum Renderer<'a, 'tcx> {
    PlainText { tcx: TyCtxt<'tcx>, cache: &'a Cache },
    Html { cx: &'a super::Context<'tcx> },
}

impl<'a, 'tcx> Renderer<'a, 'tcx> {
    fn buffer(&self) -> Buffer {
        match self {
            Self::PlainText { .. } => Buffer::new(),
            Self::Html { .. } => Buffer::html(),
        }
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        match self {
            Self::PlainText { tcx, .. } => *tcx,
            Self::Html { cx } => cx.tcx(),
        }
    }

    fn cache(&self) -> &Cache {
        match self {
            Self::PlainText { cache, .. } => cache,
            Self::Html { cx } => &cx.shared.cache,
        }
    }
}

pub(crate) fn eval_and_render_const(def_id: DefId, renderer: Renderer<'_, '_>) -> Option<String> {
    let value = renderer.tcx().const_eval_poly(def_id).ok()?;
    let mut buffer = renderer.buffer();
    render_const_value(&mut buffer, value, renderer.tcx().type_of(def_id), renderer, 0);
    Some(buffer.into_inner())
}

fn render_constant_kind<'tcx>(
    buffer: &mut Buffer,
    ct: ConstantKind<'tcx>,
    renderer: Renderer<'_, 'tcx>,
    depth: u32,
) {
    if depth > DEPTH_LIMIT {
        write!(buffer, "{DEPTH_ELLIPSIS_HTML}");
        return;
    }

    match ct {
        ConstantKind::Ty(ct) => render_const(buffer, ct, renderer),
        ConstantKind::Val(ct, ty) => render_const_value(buffer, ct, ty, renderer, depth),
    }
}

fn render_const<'tcx>(buffer: &mut Buffer, ct: Const<'tcx>, renderer: Renderer<'_, 'tcx>) {
    let tcx = renderer.tcx();

    match ct.kind() {
        ty::ConstKind::Unevaluated(ty::Unevaluated { def, promoted: Some(promoted), .. }) => {
            render_path(buffer, def.did, renderer);
            write!(buffer, "::{:?}", promoted);
        }
        ty::ConstKind::Unevaluated(ty::Unevaluated { def, promoted: None, .. }) => {
            match tcx.def_kind(def.did) {
                DefKind::Static(..) | DefKind::Const | DefKind::AssocConst => {
                    render_path(buffer, def.did, renderer)
                }
                _ => {
                    write!(
                        buffer,
                        "{}",
                        match def.as_local() {
                            Some(def) => {
                                let hir_id = tcx.hir().local_def_id_to_hir_id(def.did);
                                let body_id = tcx.hir().body_owned_by(hir_id);
                                print_const_expr(tcx, body_id)
                            }
                            None => {
                                crate::clean::inline::print_inlined_const(tcx, def.did)
                            }
                        }
                    );
                }
            }
        }
        ty::ConstKind::Param(ParamConst { name, .. }) => write!(buffer, "{}", name),
        ty::ConstKind::Value(value) => render_valtree(buffer, value, ct.ty()),
        ty::ConstKind::Infer(_)
        | ty::ConstKind::Bound(..)
        | ty::ConstKind::Placeholder(_)
        | ty::ConstKind::Error(_) => write!(buffer, "_"),
    }
}

fn render_const_value<'tcx>(
    buffer: &mut Buffer,
    ct: ConstValue<'tcx>,
    ty: Ty<'tcx>,
    renderer: Renderer<'_, 'tcx>,
    depth: u32,
) {
    let tcx = renderer.tcx();
    // FIXME: The code inside `rustc_middle::mir::pretty_print_const` does this.
    //        Do we need to do this, too? Why (not)?
    // let ct = tcx.lift(ct).unwrap();
    // let ty = tcx.lift(ty).unwrap();
    let u8_type = tcx.types.u8;

    match (ct, ty.kind()) {
        (ConstValue::Slice { data, start, end }, ty::Ref(_, inner, _)) => {
            match inner.kind() {
                ty::Slice(t) if *t == u8_type => {
                    // The `inspect` here is okay since we checked the bounds, and there are
                    // no relocations (we have an active slice reference here). We don't use
                    // this result to affect interpreter execution.
                    let byte_str =
                        data.inner().inspect_with_uninit_and_ptr_outside_interpreter(start..end);
                    render_byte_str(buffer, byte_str);
                }
                ty::Str => {
                    // The `inspect` here is okay since we checked the bounds, and there are no
                    // relocations (we have an active `str` reference here). We don't use this
                    // result to affect interpreter execution.
                    let slice =
                        data.inner().inspect_with_uninit_and_ptr_outside_interpreter(start..end);

                    // FIXME: What should the actual limit be?
                    //        Should it depend on the nesting level?
                    const LENGTH_LIMIT: usize = 80;

                    if slice.len() > LENGTH_LIMIT {
                        write!(buffer, r#""{LENGTH_ELLIPSIS_HTML}""#);
                    } else {
                        // FIXME: Somehow avoid creating those intermediate Strings
                        write!(
                            buffer,
                            "{}",
                            Escape(&format!("{:?}", String::from_utf8_lossy(slice)))
                        );
                    }
                }
                _ => {
                    // FIXME: Actually print the contents of the slice smh.
                    write!(buffer, "_");
                }
            }
        }
        (ConstValue::ByRef { alloc, offset }, ty::Array(t, n)) if *t == u8_type => {
            let n = n.kind().try_to_bits(tcx.data_layout.pointer_size).unwrap();
            // cast is ok because we already checked for pointer size (32 or 64 bit) above
            let range = AllocRange { start: offset, size: Size::from_bytes(n) };
            let byte_str = alloc.inner().get_bytes(&tcx, range).unwrap();
            write!(buffer, "*");
            render_byte_str(buffer, byte_str);
        }

        // Aggregates.
        //
        // NB: the `has_param_types_or_consts` check ensures that we can use
        // the `destructure_const` query with an empty `ty::ParamEnv` without
        // introducing ICEs (e.g. via `layout_of`) from missing bounds.
        // E.g. `transmute([0usize; 2]): (u8, *mut T)` needs to know `T: Sized`
        // to be able to destructure the tuple into `(0u8, *mut T)
        (_, ty::Array(..) | ty::Tuple(..) | ty::Adt(..)) if !ty.has_param_types_or_consts() => {
            // FIXME: The code inside `rustc_middle::mir::pretty_print_const` does this.
            //        Do we need to do this, too? Why (not)?
            // let ct = tcx.lift(ct).unwrap();
            // let ty = tcx.lift(ty).unwrap();
            let Some(contents) = tcx.try_destructure_mir_constant(
                ty::ParamEnv::reveal_all().and(ConstantKind::Val(ct, ty))
            ) else {
                return write!(buffer, "_");
            };

            // FIXME: What should the actual limit be? Should it depend on the nesting level?
            const LENGTH_LIMIT: usize = 12;
            let mut fields = contents.fields.iter().copied();

            // FIXME: (Maybe) try to print larger structs etc. across multiple lines
            //        just like rustfmt would do.
            match *ty.kind() {
                ty::Array(..) => {
                    write!(buffer, "[");

                    if contents.fields.len() > LENGTH_LIMIT {
                        write!(buffer, "{LENGTH_ELLIPSIS_HTML}");
                    } else if let Some(first) = fields.next() {
                        render_constant_kind(buffer, first, renderer, depth + 1);
                        for field in fields {
                            buffer.write_str(", ");
                            render_constant_kind(buffer, field, renderer, depth + 1);
                        }
                    }

                    write!(buffer, "]");
                }
                ty::Tuple(..) => {
                    write!(buffer, "(");

                    if let Some(first) = fields.next() {
                        render_constant_kind(buffer, first, renderer, depth + 1);
                        for field in fields {
                            buffer.write_str(", ");
                            render_constant_kind(buffer, field, renderer, depth + 1);
                        }
                    }
                    if contents.fields.len() == 1 {
                        write!(buffer, ",");
                    }

                    write!(buffer, ")");
                }
                // FIXME: Is this case actually reachable in normal code? This case is blindly
                //        copied from `rustc_middle::mir::pretty_print_const`.
                ty::Adt(def, _) if def.variants().is_empty() => write!(buffer, "_"),
                ty::Adt(def, _) => {
                    let should_hide = |field: &FieldDef| {
                        // FIXME: Should I use `cache.access_levels.is_public(did)` here instead?
                        is_doc_hidden(tcx, field.did)
                            && !(renderer.cache().document_hidden && field.did.is_local())
                            || field.vis != Visibility::Public
                                && !(renderer.cache().document_private && field.did.is_local())
                    };

                    let variant_idx =
                        contents.variant.expect("destructed const of adt without variant idx");
                    let variant_def = &def.variant(variant_idx);
                    render_path(buffer, variant_def.def_id, renderer);

                    match variant_def.ctor_kind {
                        CtorKind::Const => {}
                        CtorKind::Fn => {
                            write!(buffer, "(");

                            let mut first = true;
                            for (field_def, field) in std::iter::zip(&variant_def.fields, fields) {
                                if !first {
                                    write!(buffer, ", ");
                                }
                                first = false;

                                if should_hide(field_def) {
                                    write!(buffer, "_");
                                    continue;
                                }

                                render_constant_kind(buffer, field, renderer, depth + 1);
                            }

                            // FIXME: Should we print something (not `..` though!) if the type
                            //        is non-local and `#[non_exhaustive]`?

                            write!(buffer, ")");
                        }
                        CtorKind::Fictive => {
                            write!(buffer, " {{ ");

                            let mut first = true;
                            let mut did_hide_fields = false;
                            for (field_def, field) in std::iter::zip(&variant_def.fields, fields) {
                                if should_hide(field_def) {
                                    did_hide_fields = true;
                                    continue;
                                }

                                if !first {
                                    write!(buffer, ", ");
                                }
                                first = false;

                                // FIXME: Avoid rightward drift.
                                match renderer {
                                    // FIXME: implement plain-text fmt'ting
                                    Renderer::PlainText { .. } => todo!(),
                                    Renderer::Html { cx } => match super::href(field_def.did, cx) {
                                        Ok((mut url, ..)) => {
                                            write!(url, "#").unwrap();
                                            let parent_id = tcx.parent(field_def.did);
                                            if tcx.def_kind(parent_id) == DefKind::Variant {
                                                write!(
                                                    url,
                                                    "{}.{}.field",
                                                    ItemType::Variant,
                                                    tcx.item_name(parent_id)
                                                )
                                            } else {
                                                write!(url, "{}", ItemType::StructField)
                                            }
                                            .unwrap();

                                            write!(url, ".{}", field_def.name).unwrap();

                                            write!(
                                                buffer,
                                                r#"<a class="{}" href="{}" title="field {}">{}</a>"#,
                                                ItemType::StructField,
                                                url,
                                                field_def.name,
                                                field_def.name,
                                            )
                                        }
                                        Err(_) => write!(buffer, "{}", field_def.name),
                                    },
                                }

                                write!(buffer, ": ");

                                render_constant_kind(buffer, field, renderer, depth + 1);
                            }

                            // FIXME: Should we print ellipses (`..`) if the type is
                            //        non-local and `#[non_exhaustive]`?
                            if did_hide_fields {
                                if !first {
                                    write!(buffer, ", ");
                                }
                                write!(buffer, "..");
                            }

                            write!(buffer, " }}");
                        }
                    }
                }
                _ => unreachable!(),
            }
        }

        (ConstValue::Scalar(scalar), _) => render_const_scalar(buffer, scalar, ty),
        // FIXME: Useful?
        (ConstValue::ZeroSized, ty::FnDef(d, _)) => render_path(buffer, *d, renderer),

        // FIXME: Print aggregates that contain type or const parameters.
        _ => write!(buffer, "_"),
    }
}

fn render_valtree<'tcx>(buffer: &mut Buffer, _valtree: ty::ValTree<'tcx>, _ty: Ty<'tcx>) {
    // FIXME: Actually adopt the code from
    //        rustc_middle::ty::print::pretty::PrettyPrinter::pretty_print_const_valtree
    //        (if this is actually reachable)
    write!(buffer, "_");
}

fn render_path<'tcx>(buffer: &mut Buffer, def_id: DefId, renderer: Renderer<'_, 'tcx>) {
    match renderer {
        // FIXME: Implement plain-text fmt'ing
        Renderer::PlainText { .. } => todo!(),
        Renderer::Html { cx } => {
            let tcx = cx.tcx();

            if let Ok((mut url, item_type, path)) = super::href(def_id, cx) {
                let mut needs_fragment = true;
                let item_type = match tcx.def_kind(def_id) {
                    DefKind::AssocFn => match tcx.associated_item(def_id).defaultness.has_value() {
                        true => ItemType::Method,
                        false => ItemType::TyMethod,
                    },
                    DefKind::AssocTy => ItemType::AssocType,
                    DefKind::AssocConst => ItemType::AssocConst,
                    DefKind::Variant => ItemType::Variant,
                    _ => {
                        needs_fragment = false;
                        item_type
                    }
                };

                let name = tcx.item_name(def_id);
                let mut path = super::join_with_double_colon(&path);

                if needs_fragment {
                    write!(url, "#{}.{}", item_type, name).unwrap();
                    write!(path, "::{}", name).unwrap();
                }

                write!(
                    buffer,
                    r#"<a class="{}" href="{}" title="{} {}">{}</a>"#,
                    item_type, url, item_type, path, name,
                );
            } else {
                write!(buffer, "{}", tcx.item_name(def_id));
            }
        }
    }
}

fn render_byte_str(buffer: &mut Buffer, byte_str: &[u8]) {
    // FIXME: What should the actual limit be? Should it depend on the nesting level?
    const LENGTH_LIMIT: usize = 80;

    buffer.write_str("b\"");

    if byte_str.len() > LENGTH_LIMIT {
        write!(buffer, "{LENGTH_ELLIPSIS_HTML}");
    } else {
        for &char in byte_str {
            for char in std::ascii::escape_default(char) {
                // FIXME: Somehow write this in a nicer way. This looks horrendous!
                write!(buffer, "{}", Escape(&char::from(char).to_string()));
            }
        }
    }

    buffer.write_str("\"");
}

fn render_const_scalar<'tcx>(buffer: &mut Buffer, scalar: Scalar, ty: Ty<'tcx>) {
    match scalar {
        // FIXME: Should we actually attempt to render pointers properly? Would it make any sense?
        Scalar::Ptr(..) => write!(buffer, "_"),
        Scalar::Int(int) => render_const_scalar_int(buffer, int, ty),
    }
}

fn render_const_scalar_int<'tcx>(buffer: &mut Buffer, int: ScalarInt, ty: Ty<'tcx>) {
    extern crate rustc_apfloat;
    use rustc_apfloat::ieee::{Double, Single};

    match ty.kind() {
        ty::Bool if int == ScalarInt::FALSE => write!(buffer, "false"),
        ty::Bool if int == ScalarInt::TRUE => write!(buffer, "true"),

        ty::Float(ty::FloatTy::F32) => {
            write!(buffer, "{}", Single::try_from(int).unwrap())
        }
        ty::Float(ty::FloatTy::F64) => {
            write!(buffer, "{}", Double::try_from(int).unwrap())
        }

        ty::Uint(_) | ty::Int(_) => {
            let int =
                ConstInt::new(int, matches!(ty.kind(), ty::Int(_)), ty.is_ptr_sized_integral());
            write!(buffer, "{:?}", int)
        }
        ty::Char if char::try_from(int).is_ok() => {
            write!(buffer, "{:?}", char::try_from(int).unwrap())
        }
        _ => write!(buffer, "_"),
    }
}
