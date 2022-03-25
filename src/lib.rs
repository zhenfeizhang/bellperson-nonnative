#![feature(hash_raw_entry)]
#![feature(test)]

extern crate bellperson;
extern crate bincode;
extern crate derivative;
extern crate ff;
extern crate flate2;
extern crate fnv;
extern crate gmp_mpfr_sys;
extern crate rand;
extern crate rayon;
extern crate rug;
extern crate serde;
extern crate sha2;
extern crate test;

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;
extern crate byteorder;

#[macro_use]
pub mod util;
pub mod mp;

use bellperson::SynthesisError;
trait OptionExt<T> {
    fn grab(&self) -> Result<&T, SynthesisError>;
    fn grab_mut(&mut self) -> Result<&mut T, SynthesisError>;
}

impl<T> OptionExt<T> for Option<T> {
    fn grab(&self) -> Result<&T, SynthesisError> {
        self.as_ref().ok_or(SynthesisError::AssignmentMissing)
    }
    fn grab_mut(&mut self) -> Result<&mut T, SynthesisError> {
        self.as_mut().ok_or(SynthesisError::AssignmentMissing)
    }
}
