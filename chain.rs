#![allow(dead_code)]
#![feature(custom_inner_attributes)]
#![rustfmt::skip]

#[cfg(any())]
mod with_args {

mod module { pub trait A<X> { type T; } }
trait B<X>: module::A<(X,)> { type T; }
trait C<X>: B<(X,)> {}

//fn f(_: impl C<bool> + B<(bool,), T = ()> + module::A<((bool,)), T = ()>) {}
fn f(_: impl C<bool, T = ()>) {}

}

#[cfg(any())]
mod without_args_and_padded {

trait A { type T; }
trait B: A { type T; }
trait C: B { type PadLeft; type PadRight; }

//fn f(_: impl C + B<T = ()> + A<T = ()>) {}
// fn f(_: impl C<T = ()>) {}
fn f(_: impl C<PadLeft = (), T = (), PadRight = ()>) {}
}

#[cfg(any())]
mod gat {
    // FIXME: if the arity of the two assoc tys differ, then what happens?

    trait A { type T<Q, K>; }
    trait B: A { type T<Q>; }
    trait C: B {}

    // fn f(_: impl C + B<T<i32> = ()> + A<T<i32> = ()>) {}
    fn f(_: impl C<T<i32> = ()>) {}
}

#[cfg(any())]
mod super_with_projs {
    trait A { type T; type Unrelated; }
    trait K { type T; }
    // Explainer: It's possible that we have
    // ambiguous assoc item constraints despite all but one already
    // being constrained, lol.
    trait B: A<Unrelated = String> + K<T = u32> {} // NOTE: not mentioning Unrelated in the sugg is perfect!!

    // fn t(_: impl B<> + A<T = ()>) {}
    fn f(_: impl B<T = ()>) {}
    // fn sugg(_: impl B<> + K<T = ()> + A<T = ()>) {} // FIXME: incorrect sugg
    //                     //^^^^^^^^^ we should skip this smh
}

// Here, the ident is ambiguous in the toplevel traitref but
// all assoc item candidates are constrained already meaning
// `disambiguated_bounds` will be empty once we filter out
// already-constrained bounds. therefore we need to emit a
// different suggestion: namely only remove!!!
// SOLUTION: repl `if d_bounds.empty.not { let constr=constr.unwrap`
//               ---> `iflet Some(constr) = constr { [[only sugg removal]]`
#[cfg(any())]
mod super_with_exhaustive_projs {
    trait A0 { type T; }
    trait A1 { type T; }
    trait B: A0<T = i32> + A1<T = u32> {} // NOTE: not mentioning Unrelated in the sugg is perfect!!

    // fn t(_: impl B) {}
    fn f(_: impl B<T = ()>) {}
    // fn sugg(_: impl B<> + A0<T = ()> + A<T = ()>) {} // FIXME: incorrect sugg
}

#[cfg(any())]
mod paren_sugar {
    trait A { type Output; }
    /*tmp*/trait FnOnce_ { type Output; }
    // BIG NOTE!!!! Unrelated to paren_sugar: It's possible that we have
    // ambiguous assoc item constraints despite all but one already
    // being constrained, lol.
    trait B: A + FnOnce() {}

    // Actually, the suggestion: "impl B + A<Output = ()>" is correct lol!!!!
    // nice!
    // fn t(_: impl B + A<Output = ()>) {}
    // fn f(_: impl B<Output = ()>) {}
}

// Making sure we print for<> binders
#[cfg(any())]
mod higher_rank {
    trait A<'a> {type T;}
    trait B<'a> {type T;}
    trait C: for<'a> A<'a> + for<'r> B<'r> {}

    fn f(_: impl C<T = ()>) {}
}

#[cfg(any())]
mod atb {

trait A { type T; }
trait B: A { type T; }
trait C: B { }

// FIXME: (minor) doesn't sugg anything
// fn t(_: impl C + B<T: Copy> + A<T: Copy>) {}
fn f(_: impl C<T: Copy>) {}
}

// FIXME: Macros!!!!
