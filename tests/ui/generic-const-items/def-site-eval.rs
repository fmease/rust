//! Test that we only evaluate free const items (their def site to be clear)
//! whose generics don't require monomorphization.
#![feature(generic_const_items)]
#![allow(incomplete_features)]

//@ revisions: fail pass
//@[pass] build-pass (we require monomorphization)

const _<_T>: () = panic!();
const _<const _N: usize>: () = panic!();

#[cfg(fail)]
const _<'_a>: () = panic!(); //[fail]~ ERROR evaluation of constant value failed

fn main() {}
