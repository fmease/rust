#![feature(generic_consts, trivial_bounds)]
#![allow(incomplete_features, dead_code, trivial_bounds)]

// FIXME(generic_consts): This looks like a compiler bug to me, is it one though?
// I expected that we wouldn't emit any errors.
// I thought we'd skip the evaluation of consts whose bounds don't hold.

const UNUSED: () = ()
where
    String: Copy;
//~^^^ ERROR evaluation of constant value failed

fn main() {}
