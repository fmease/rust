// check-pass
// compile-flags: --crate-type=lib -Ztrait-solver=next

#![feature(non_lifetime_binders)]
//~^ WARN the feature `non_lifetime_binders` is incomplete

pub fn f<T>() where for<U> (T, U): Copy {}
