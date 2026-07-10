#![no_std]

extern crate alloc;
#[cfg(test)]
extern crate std;

mod input_v1;
mod structural_v1;

pub use input_v1::*;
pub use structural_v1::*;
