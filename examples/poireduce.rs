use poi::*;

fn main() {
    println!("=== Poi Reduce 0.1 ===");
    println!("Type `help` for more information.");
    let ref std = std();

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

        match input.trim() {
            "help" => {
                print_help();
                continue;
            }
            "bye" => break,
            _ => {}
        }

        let mut expr = match parse_str(&input) {
            Ok(expr) => expr,
            Err(err) => {
                println!("ERROR:\n{}", err);
                continue;
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
    }
}

fn print_help() {
    println!("=== Poi Reduce Help ===");
    println!("Made by Sven Nilsen, 2020");
    println!("");
    println!("Poi is based on the theory of path semantics:");
    println!("https://github.com/advancedresearch/path_semantics");
    println!("");
    println!("Type in an expression in path semantics, e.g. `and[not]`");
}
