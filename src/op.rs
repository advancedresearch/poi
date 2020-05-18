/// Binary operation on functions.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Op {
    /// Function composition `f . g`
    Compose,
    /// Path `f[g]`
    Path,
    /// Apply function to some argument.
    Apply,
    /// Constrain function input.
    Constrain,
}
