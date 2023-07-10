pub trait Trait<A> {
    const ONE<T>: i32;
    //~^ ERROR generic consts are experimental

    const TWO: ()
    where
        A: Copy;
    //~^^ ERROR generic consts are experimental
}

const CONST<T>: i32 = 0;
//~^ ERROR generic consts are experimental

const EMPTY<>: i32 = 0;
//~^ ERROR generic consts are experimental

const TRUE: () = ()
where
    String: Clone;
//~^^ ERROR generic consts are experimental

// Ensure that we flag generic consts inside macro calls as well:

macro_rules! discard {
    ($item:item) => {}
}

discard! { const FREE<T>: () = (); }
//~^ ERROR generic consts are experimental

discard! { impl () { const ASSOC<const N: ()>: () = (); } }
//~^ ERROR generic consts are experimental

discard! { impl () { const ASSOC: i32 = 0 where String: Copy; } }
//~^ ERROR generic consts are experimental

fn main() {}
