use poi::prelude::*;

fn main() {
    test_binary(And, |a, b| a && b);
    test_binary(Or, |a, b| a || b);
    test_binary(Eqb, |a, b| a == b);
    test_binary(Xor, |a, b| a ^ b);
    test_binary(Nand, |a, b| !(a && b));
    test_binary(Nor, |a, b| !(a || b));
    test_binary(Exc, |a, b| a && !b);
    test_binary(Imply, |a, b| !a || b);
    test_binary(Fstb, |a, _| a);
    test_binary(Sndb, |_, b| b);
}

pub fn test_binary(sym: Symbol, f: fn(bool, bool) -> bool) {
    let ref std = std();
    let cases = &[
        (false, false),
        (false, true),
        (true, false),
        (true, true)
    ];
    for case in cases {
        let r = f(case.0, case.1);
        let a = app(sym.clone(), (case.0, case.1)).eval(std).unwrap();
        assert_eq!(a, r.into());
    }
}
