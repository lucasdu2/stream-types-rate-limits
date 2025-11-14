use std::env;
mod streamrate;
mod parse;


// Test string: (|| 10/5 12/4) <: (. (|| 300/50 40/10 50/5) 2/1)
// Test string:
// (. (|| 10000/234090980909790 100/30) (|| (. 10/5 35209890/1090809383) (. 109/9898 190987/4545 7676/257890176)))
fn main() {
    let args: Vec<String> = env::args().collect();
    let (left, right) = parse::parse(&args[1]);
    if streamrate::stream_sub(&left, &right) {
        println!("{} is true", args[1])
    } else {
         println!("{} is false", args[1])
    }
}
