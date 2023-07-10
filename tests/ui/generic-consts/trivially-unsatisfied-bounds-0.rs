#![feature(generic_consts, trivial_bounds)]
#![allow(incomplete_features)]

// Ensure that we check if trivial bounds on consts hold or not.

const UNUSABLE: () = ()
where
    String: Copy;

fn main() {
    let _ = UNUSABLE; //~ ERROR the trait bound `String: Copy` is not satisfied
}
