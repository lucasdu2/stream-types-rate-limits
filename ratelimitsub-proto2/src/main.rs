use std::env;
mod streamrate;
mod parse;

fn main() {
    let args: Vec<String> = env::args().collect();
    let (left, right) = parse::parse(&args[0]);
    if streamrate::stream_sub(&left, &right) {
        println!("{} is true", args[0])
    } else {
         println!("{} is false", args[0])
    }
}
