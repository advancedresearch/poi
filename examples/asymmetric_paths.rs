use poi::prelude::*;

fn main() {
    let ref std = std();

    // `if(a, b)[not -> id]`
    let a = path(_if("a", "b"), (Not, Id)).reduce_all(std);
    assert_eq!(a, _if("b", "a"));

    let a = path("f", (Id, Not)).reduce_all(std);
    assert_eq!(a, comp(Not, "f"));

    // `f[not] => f[not -> id][id -> not]`
    let a = path("f", Not).reduce(std).unwrap().0;
    assert_eq!(a, path(path("f", (Not, Id)), (Id, Not)));

    let a = comp(Not, path(_if("a", "b"), Not)).reduce_all(std);
    assert_eq!(a, _if("b", "a"));
}
