use poi::prelude::*;

fn main() {
    test("source/and_not.txt", path(And, Not));
    test("source/or_not.txt", path(Or, Not));
    test("source/and_true.txt", app(And, true));
    test("source/and_false.txt", app(And, false));
}

fn test(file: &str, e: Expr) {
    let a: Expr = parse(file, &[]).map_err(|err| panic!("{}", err)).unwrap();
    assert_eq!(a, e);
}
