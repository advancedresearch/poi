use poi::*;

fn main() {
    println!("=== Poi Reduce 0.1 ===");
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
    println!("");
    println!("Type in an expression in path semantics, e.g. `and[not]`");
}
