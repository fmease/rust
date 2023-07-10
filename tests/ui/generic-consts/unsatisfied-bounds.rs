#![feature(generic_consts)]
#![allow(incomplete_features)]

// Ensure that we check if bounds on consts hold or not.

use std::convert::Infallible;

const C<T: Copy>: () = ();

const K<T>: () = ()
where
    Infallible: From<T>;

const Q<'a, T: 'a>: () = ();

trait Trait<P> {
    const A: u32
    where
        P: Copy;

    const B<T>: u32
    where
        Infallible: From<T>;
}

impl<P> Trait<P> for () {
    const A: u32 = 0;
    const B<T>: u32 = 1;
}

fn main() {
    let () = C::<String>; //~ ERROR the trait bound `String: Copy` is not satisfied
    let () = K::<()>; //~ ERROR the trait bound `Infallible: From<()>` is not satisfied
    let _ = <() as Trait<Vec<u8>>>::A; //~ ERROR the trait bound `Vec<u8>: Copy` is not satisfied
    let _ = <() as Trait<&'static str>>::B::<()>; //~ ERROR the trait bound `Infallible: From<()>` is not satisfied
}
