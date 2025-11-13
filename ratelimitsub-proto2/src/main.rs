use std::env;
mod streamrate;
mod parse;


// Test string: (|| 10/5 12/4) <: (. (|| 300/50 40/10 50/5) 2/1)
fn main() {
    let args: Vec<String> = env::args().collect();
    let (left, right) = parse::parse(&args[1]);
    if streamrate::stream_sub(&left, &right) {
        println!("{} is true", args[0])
    } else {
         println!("{} is false", args[0])
    }
}
