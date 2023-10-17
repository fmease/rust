// compile-flags: -Ztrait-solver=next

#![feature(non_lifetime_binders)]
//~^ WARN is incomplete and may not be safe

pub fn foo()
where
    for<V> V: Sized,
{
}

pub fn bar()
where
    for<V> V: IntoIterator,
{
}

fn main() {
    foo();

    bar();
    //~^ ERROR the trait bound `V: IntoIterator` is not satisfied
}
