#![feature(generic_consts)]
#![allow(incomplete_features)]

const NONE<T>: Option<T> = None::<T>;

fn main() {
    let _ = NONE; //~ ERROR type annotations needed
}
