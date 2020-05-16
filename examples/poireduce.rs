use poi::*;

fn main() {
    println!("=== Poi Reduce 0.2 ===");
    println!("Type `help` for more information.");
    let ref std = std();

    let mut prev_expr: Option<Expr> = None;
    loop {
        use std::io::{self, Write};

        print!("> ");
        let mut input = String::new();
        io::stdout().flush().unwrap();
        match io::stdin().read_line(&mut input) {
            Ok(_) => {}
            Err(_) => {
                println!("ERROR: Could not read input");
                continue;
            }
        };

        let mut inlined = false;
        match input.trim() {
            "help" => {
                print_help();
                continue;
            }
            "help eqv" => {
                print_help_eqv();
                continue;
            }
            "help asym" => {
                print_help_asym();
                continue;
            }
            "help dom" => {
                print_help_dom();
                continue;
            }
            "inline all" => {
                if let Some(expr) = &prev_expr {
                    prev_expr = Some(match expr.inline_all(std) {
                        Ok(x) => {
                            inlined = true;
                            x
                        }
                        Err(err) => {
                            println!("ERROR: {:?}", err);
                            continue;
                        }
                    });
                } else {
                    println!("ERROR: No previous expression");
                    continue;
                }
            }
            "bye" => break,
            _ => {}
        }

        let mut expr = if inlined {prev_expr.unwrap()} else {
                match parse_str(&input) {
                    Ok(expr) => expr,
                    Err(err) => {
                        println!("ERROR:\n{}", err);
                        continue;
                    }
                }
            };
        println!("{}", expr);
        loop {
            if let Ok((nexpr, i)) = expr.reduce(std) {
                if nexpr == expr {break};
                expr = nexpr;
                println!("{}\t\t\t( {} )", expr, std[i]);
            } else {
                break;
            }
        }

        let equivalences = expr.equivalences(std);
        for i in 0..equivalences.len() {
            let j = equivalences[i].1;
            println!("<=>  {}\t\t( {} )", equivalences[i].0, std[j]);
        }

        prev_expr = Some(expr);
    }
}

fn print_help() {
    println!("=== Poi Reduce Help ===");
    println!("Made by Sven Nilsen, 2020");
    println!("");
    println!("Poi is based on the theory of path semantics:");
    println!("https://github.com/advancedresearch/path_semantics");
    println!("");
    println!("Special commands:");
    println!("- bye            quits the program");
    println!("- inline all     inlines all definitions from previous expression");
    println!("- help asym      more help about asymmetric paths");
    println!("- help eqv       more help about equivalent expressions");
    println!("- help dom       more help about domains and partial functions");
    println!("");
    println!("Type in an expression in path semantics, e.g. `and[not]`");
}

fn print_help_eqv() {
    println!("=== Equivalent Expressions ===");
    println!("");
    println!("When the expression can not be reduced further,");
    println!("a list of equivalent expressions are displayed.");
    println!("");
    println!("For example, type `(len . concat)(a, b)` and you will get the suggestion");
    println!("`<=>  add((len · fst)(a)(b), (len · snd)(a)(b))`");
    println!("Copy-paste this as the new input and it will reduce to `add(len(a))(len(b))`.");
}

fn print_help_asym() {
    println!("=== Asymmetric Paths ===");
    println!("");
    println!("You can write asymmetric paths, e.g. `not . and[not x id -> id]`.");
    println!("This will reduce to `and[not ⨯ id → not]`.");
}

fn print_help_dom() {
    println!("=== Domains and Partial Functions ===");
    println!("");
    println!("A partial function is a function where the input is constrained in some way.");
    println!("According to Path Semantics, this changes the identity of the function.");
    println!("Therefore, one should think about partial functions as 'different' functions.");
    println!("");
    println!("For example: `and(a, a)`. Type it and see what happens.");
    println!("");
    println!("In `and(a, a)`, the input of `and` is constrained implicitly.");
    println!("Poi reduces this first to `and{{eq}}(a)(a)` by adding `eq` as domain constraint.");
    println!("This turns `and` into a partial function `and{{eqb}}`.");
    println!("");
    println!("Now, the identity of the `and` function has changed into another function.");
    println!("Poi uses the rule `and{{eq}} => fstb` to reduce this expression further.");
    println!("In the end, the expression `and(a, a)` is reduced to just `a`.");
}
