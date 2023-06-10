// FIXME: polish this up

pub trait Tr {
    const K<T>: i32;
    //~^ ERROR generic consts are experimental
}

const K<T>: i32 = 0;
//~^ ERROR generic consts are experimental

const E<>: i32 = 0;
//~^ ERROR generic consts are experimental

macro_rules! discard {
    ($item:item) => {}
}

discard! { const FREE<T>: () = (); }
//~^ ERROR generic consts are experimental

discard! { impl () { const ASSOC<const N: ()>: () = (); } }
//~^ ERROR generic consts are experimental

fn main() {}
