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
            "help" => {print_help(); continue}
            "help eqv" => {print_help_eqv(); continue}
            "help asym" => {print_help_asym(); continue}
            "help dom" => {print_help_dom(); continue}
            "help triv" => {print_help_triv(); continue}
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

fn print_help() {print!("{}", include_str!("../assets/help.txt"))}
fn print_help_eqv() {print!("{}", include_str!("../assets/help-eqv.txt"))}
fn print_help_asym() {print!("{}", include_str!("../assets/help-asym.txt"))}
fn print_help_dom() {print!("{}", include_str!("../assets/help-dom.txt"))}
fn print_help_triv() {print!("{}", include_str!("../assets/help-triv.txt"))}
