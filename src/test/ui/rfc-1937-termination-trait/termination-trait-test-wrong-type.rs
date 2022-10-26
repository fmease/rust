// compile-flags: --test

use std::num::ParseFloatError;

#[test]
fn can_parse_zero_as_f32() -> Result<f32, ParseFloatError> {
    //~^ ERROR the trait bound `f32: Termination` is not satisfied
    //~| ERROR the trait bound `f32: Termination` is not satisfied
    "0".parse()
}
