use poi::prelude::*;

fn main() {
    let ref std = std();

    assert_eq!(path(And, Not).reduce_all(std), Or.into());
    assert_eq!(path(Or, Not).reduce_all(std), And.into());
    assert_eq!(path(Xor, Not).reduce_all(std), Eqb.into());
    assert_eq!(path(Eqb, Not).reduce_all(std), Xor.into());
    assert_eq!(path(Nand, Not).reduce_all(std), Nor.into());
    assert_eq!(path(Nor, Not).reduce_all(std), Nand.into());

    assert_eq!(comp(Not, Nand).reduce_all(std), And.into());
    assert_eq!(comp(Not, Nor).reduce_all(std), Or.into());
    assert_eq!(comp(Not, And).reduce_all(std), Nand.into());
    assert_eq!(comp(Not, Or).reduce_all(std), Nor.into());
}
