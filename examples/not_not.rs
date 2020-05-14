use poi::*;
use poi::prelude::*;

fn main() {
    let ref std = std();

    // (not . not)(false) = false
    let a = app(comp(Not, Not), false);
    let a = a.reduce(std).unwrap().0;
    let a = a.inline(&Idb, std).unwrap();
    let a = a.reduce(std).unwrap().0;
    assert_eq!(a, false.into());

    // (not . not)(true) = true
    let a = app(comp(Not, Not), true);
    let a = a.reduce(std).unwrap().0;
    let a = a.inline(&Idb, std).unwrap();
    let a = a.reduce(std).unwrap().0;
    assert_eq!(a, true.into());
}
