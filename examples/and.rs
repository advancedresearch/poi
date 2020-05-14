use poi::prelude::*;

fn main() {
    let ref std = std();

    // and(true, true) = true
    let a = app(And, (true, true)).reduce_all(std);

    // and(true)(true) = true
    let a = a.inline(&And, std).unwrap().reduce_all(std);
    assert_eq!(a, true.into());
}
