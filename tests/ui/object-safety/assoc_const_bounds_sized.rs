#![feature(generic_consts)]
#![allow(incomplete_features, dead_code)]

// FIXME(generic_consts): Is this the expected behavior? #110590 #112319
// check-pass

trait Foo {
    const BAR: bool
    where
        Self: Sized;
}

fn foo(_: &dyn Foo) {}

fn main() {}
