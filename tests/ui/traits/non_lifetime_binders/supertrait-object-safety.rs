// compile-flags: -Ztrait-solver=next

#![feature(non_lifetime_binders)]
//~^ WARN the feature `non_lifetime_binders` is incomplete

trait Foo: for<T> Bar<T> {}

trait Bar<T: ?Sized> {
    fn method(&self) {}
}

fn needs_bar(x: &(impl Bar<i32> + ?Sized)) {
    x.method();
}

impl Foo for () {}

impl<T: ?Sized> Bar<T> for () {}

fn main() {
    let x: &dyn Foo = &();
    //~^ ERROR the type `&dyn Foo` is not well-formed
    //~| ERROR mismatched types
    needs_bar(x);
    //~^ ERROR the type `&dyn Foo` is not well-formed
    //~| ERROR the type `dyn Foo` is not well-formed
    //~| ERROR the trait bound `dyn Foo: Bar<i32>` is not satisfied
}
