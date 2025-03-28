//@ known-bug: rust-lang/rust#129095
//@ compile-flags: -Zmir-enable-passes=+GVN -Zmir-enable-passes=+Inline -Zvalidate-mir

#![feature(adt_const_params, unsized_const_params)]
#![allow(incomplete_features)]

pub fn function_with_bytes<const BYTES: &'static [u8; 4]>() -> &'static [u8] {
    BYTES
}

pub fn main() {
    assert_eq!(function_with_bytes::<b"AAAAA">(), &[0x41, 0x41, 0x41, 0x41]);
}
