#![feature(generic_consts)]
#![allow(incomplete_features)]

// Check that we deny lifetime elision inside where-clauses of consts.
// FIXME(generic_consts): Are there other places we should check?

const K<T>: () = ()
where
    &T: Copy; //~ ERROR `&` without an explicit lifetime name cannot be used here

fn main() {}
