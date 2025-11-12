use std::str;
use crate::streamrate::StreamRate;
use crate::streamrate::Rate;

// (. 10/5 (| 45/5 50/100 6000/1000))
// This is more like a Scheme/Lisp s-expr parser.
// I should learn how to write a real parser at some point, hopefully soon.
// This is very hacky, but it's OK for now.

enum ExprOp {
    Zero,
    Sum,
    Par,
    Concat,
}

// TODO
fn parse_chunk(chunk: &str) -> StreamRate {

}

fn get_next_parenthesized_chunk<'a>(
    s: &'a str,
    s_iter: &mut str::CharIndices,
    start_idx: usize
) -> &'a str {
    let error_prefix = "parsing error:";
    // We only call this function when we've discovered an open parenthesis.
    let mut open_parens = 1;
    loop {
        match s_iter.next() {
            Some(c_tuple) => {
                match c_tuple {
                    (i, ')') => {
                        open_parens -= 1;
                        if open_parens == 0 {
                            // We don't want i+1 as the last index, since we
                            // want to remove the trailing ) anyway.
                            break &s[start_idx..i]
                        } else {
                            continue
                        }
                    },
                    (_, '(') => {
                        open_parens += 1; continue
                    }
                    (_, _) => continue
                }
            },
            None => {
                if open_parens == 0 {
                    break &s[start_idx..]
                } else {
                    panic!("{} unclosed parentheses", error_prefix)
                }
            }
        }
    }
}

fn chunk_one_level(s: &str) -> (ExprOp, Vec<&str>) {
    let error_prefix = "parsing error:";
    let mut chunked: Vec<&str> = Vec::new();
    let s_trim = s.trim();
    let mut s_trim_iter = s_trim.char_indices();
    let mut outer_open_parens = 0;
    match s_trim_iter.next() {
        Some(c_tuple) => {
            let (_, c) = c_tuple;
            match c {
                '(' => outer_open_parens += 1,
                _ => panic!("{} expression must begin with (", error_prefix)
            }
        }
        None => return (ExprOp::Zero, chunked) // Just return empty Vec
    };
    // Find operator...
    let op: ExprOp = loop {
        match s_trim_iter.next() {
            Some(c_tuple) => {
                match c_tuple {
                    (_, ' ') | (_, '\t') => continue,
                    (_, '.') => break ExprOp::Concat,
                    (_, '|') => {
                        match s_trim_iter.next() {
                            Some(c_tuple) => {
                                match c_tuple {
                                    (_, '|') => break ExprOp::Par,
                                    (_, _) =>
                                        panic!("{} | should be ||", error_prefix),
                                }
                            }
                            None => panic!("{} | should be ||", error_prefix),

                        }
                    },
                    (_, '+') => break ExprOp::Sum,
                    (_, _) => panic!("{} open parenthesis must be followed by operator",
                                     error_prefix),
                }
            },
            None => {
                panic!("{} no operator found for expression", error_prefix)
            }
        }
    };
    let mut active_range = false;
    let mut active_start = 0;
    let mut active_end = 0;
    loop {
        match s_trim_iter.next() {
            Some(c_tuple) => {
                match c_tuple {
                    (i, '0'..='9') | (i, '/') => {
                        if active_range {
                            active_end = i
                        } else {
                            active_range = true;
                            active_start = i
                        }
                    },
                    (_, ' ') | (_, '\t') => {
                        if active_range {
                            active_range = false;
                            chunked.push(&s[active_start..(active_end + 1)])
                        }
                    },
                    (i, '(') => {
                        if active_range {
                            active_range = false;
                            chunked.push(&s[active_start..(active_end + 1)])
                        };
                        let pchunk = get_next_parenthesized_chunk(s, &mut s_trim_iter,  i);
                        chunked.push(pchunk)
                    },
                    (_, ')') => {
                        outer_open_parens -= 1;
                        if active_range {
                            active_range = false;
                            chunked.push(&s[active_start..(active_end + 1)])
                        };
                        if outer_open_parens == 0 {
                            // Just stop parsing when our initial open parenthesis
                            // gets closed (anything afterwards will just be ignored).
                            break
                        }
                    }
                    (i, c) => {
                        panic!("{} did not expect {} at character {}",
                               error_prefix, c, i)
                    }
                }
            },
            None => {
                if outer_open_parens == 0 {
                    break
                } else {
                    panic!("{} expression not closed with )", error_prefix)
                }
            }
        }
    }
    return (op, chunked)
}

fn generate_streamrate_rec(eo: ExprOp, v: Vec<&str>) -> Option<StreamRate> {
    if v.len() == 0 {
        None
    } else {
        match eo {
            ExprOp::Sum => {
                let hd = v.get(0);
                let tl = v.get(1..);
                // TODO
                Some(StreamRate::Sum(v.get(0)))
            }
        }
    }
}
fn generate_streamrate(eo: ExprOp, v: Vec<&str>) -> StreamRate {
    let error_prefix = "parsing error:";
    if v.len() == 0 {
        panic!("{} no subexpressions after operator", error_prefix)
    };
    generate_streamrate_rec(eo, v)
}

fn parse_side(s: &str) -> StreamRate {
    let error_prefix = "parsing error:";
    match chunk_one_level(s) {
        (ExprOp::Zero, _) => panic!("{} stream rate expression is empty", error_prefix),
        (ExprOp::Par, v) => {

        },
        (ExprOp::Sum, v) => (),
        (ExprOp::Concat, v) => (),
    }
}

pub fn parse(full_sub_str: &String) -> (StreamRate, StreamRate) {
    let mut split_sides = full_sub_str.split("<:");
    let left = match split_sides.next() {
         None => panic!("wtf!"), Some(r) => parse_side(&r),}; let right = match split_sides.next() {
        None => panic!("wtf!"),
        Some(r) => parse_side(&r),
    };
    (left, right)
}
