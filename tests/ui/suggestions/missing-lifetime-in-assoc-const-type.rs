trait ZstAssert: Sized {
    const A: &str = ""; //~ ERROR missing lifetime specifier
    const B: S = S { s: &() }; //~ ERROR missing lifetime specifier
    const C: &'_ str = ""; //~ ERROR missing lifetime specifier
    const D: T = T { a: &(), b: &() }; //~ ERROR missing lifetime specifier
    // FIXME(generic_consts): We should only suggest adding lifetime parameters to assoc consts if
    // the feature `generic_consts` is enabled. If it isn't, suggest adding it to the trait.
}

struct S<'a> {
    s: &'a (),
}
struct T<'a, 'b> {
    a: &'a (),
    b: &'b (),
}

fn main() {}
