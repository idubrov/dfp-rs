use std::fmt;

#[derive(PartialEq)]
pub struct Bits<T: fmt::LowerHex>(pub T);

impl<T: fmt::LowerHex> fmt::Debug for Bits<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[{:x}]", self.0)
    }
}
