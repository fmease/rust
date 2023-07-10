#![feature(generic_consts)]
#![allow(incomplete_features, dead_code)]

// FIXME(generic_consts): Is this the expected behavior? CC #110590
// check-pass

trait Foo {
    const BAR: bool
    where
        Self: Sized;
}

fn foo(_: &dyn Foo) {}

fn main() {}
