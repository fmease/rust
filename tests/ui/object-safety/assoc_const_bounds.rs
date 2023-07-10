#![feature(generic_consts)]
#![allow(incomplete_features, dead_code)]

// FIXME(generic_consts): Is this the expected behavior? CC #110590
// check-pass

trait Foo<T> {
    const BAR: bool
    where
        Self: Sized;
}

trait Cake {}
impl Cake for () {}

fn foo(_: &dyn Foo<()>) {}
fn bar(_: &dyn Foo<i32>) {}

fn main() {}
