struct S;

impl S {
    static fn f() {}
    //~^ ERROR expected identifier, found keyword `fn`
    //~| ERROR expected one of `:`, `;`, `<`, `=`, or `where`
    //~| ERROR missing type for `static` item
    // FIXME(generic_consts): `<` and `where` now being in the list of expected tokens isn't great.
}

fn main() {}
