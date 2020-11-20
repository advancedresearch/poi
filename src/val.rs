use std::fmt;

/// Value.
#[derive(Clone, PartialEq, PartialOrd, Debug)]
pub enum Value {
    /// A boolean value.
    Bool(bool),
    /// A f64 value.
    F64(f64),
}

impl fmt::Display for Value {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> std::result::Result<(), fmt::Error> {
        use Value::*;

        match self {
            Bool(v) => write!(w, "{}", v)?,
            F64(v) => write!(w, "{}", v)?,
        }
        Ok(())
    }
}
