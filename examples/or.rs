use poi::prelude::*;

fn main() {
    let ref std = std();

    // or(true, true) = true
    let a = app(Or, (true, true)).reduce_all(std);

    // or(true)(true) = true
    let a = a.inline(&Or, std).unwrap().reduce_all(std);
    assert_eq!(a, true.into());
}
