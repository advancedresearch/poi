use super::*;

/// Standard library knowledge base.
pub fn std() -> Vec<Knowledge> {
    match parse_data_str(include_str!("../assets/std.md"), &[]) {
        Ok(ParseData::Knowledge(k)) => k,
        Ok(ParseData::Expr(_)) => panic!("Expected knowledge, found expression"),
        Err(err) => panic!("ERROR:\n{}", err),
    }
}
