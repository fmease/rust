#![feature(generic_consts)]
#![allow(incomplete_features)]

// Check that we emit a *hard* error for generic parameter defaults on free const items since we are
// not limited by backward compatibility.
// FIXME(default_type_parameter_fallback): Consider reallowing them once they work properly.

const NONE<T = ()>: Option<T> = None::<T>; //~ ERROR defaults for type parameters are only allowed

fn main() {
    let _ = NONE;
}
