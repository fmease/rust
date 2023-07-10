// check-pass

// Test that we can call methods from const trait impls from inside of generic consts.

#![feature(generic_consts, const_trait_impl)]
#![allow(incomplete_features)]
#![crate_type = "lib"]

const CREATE<T: ~const Create>: T = T::create();

pub const K0: i32 = CREATE::<i32>;
pub const K1: i32 = CREATE; // arg inferred

#[const_trait]
trait Create {
    fn create() -> Self;
}

impl const Create for i32 {
    fn create() -> i32 {
        4096
    }
}
