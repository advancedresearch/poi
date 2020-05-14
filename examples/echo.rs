use poi::*;

fn main() {
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

        let expr = match parse_str(&input) {
            Ok(expr) => expr,
            Err(err) => {
                println!("ERROR:\n{}", err);
                continue;
            }
        };
        println!("{}", expr);
        println!("{:?}", expr);
    }
}
