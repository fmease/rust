// FIXME(fmease): #prMergeBlocker This leads to a stack overflow in the compiler!
// Detect this during normalization / const evaluation and report a cycle error instead.

// ignore-test

#![feature(generic_consts)]
#![allow(incomplete_features)]

const RECUR<T>: () = RECUR::<(T,)>;

fn main() {
    let _ = RECUR::<()>;
}
