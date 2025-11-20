use crate::streamrate::Rate;
use crate::streamrate::StreamRate;
use std::str;

// (. 10/5 (| 45/5 50/100 6000/1000))
// This is more like a Scheme/Lisp s-expr parser.
// I should learn how to write a real parser at some point, hopefully soon.
// This is very hacky, but it's OK for now.

#[derive(Debug)]
enum ExprOp {
    None,
    Sum,
    Par,
    Concat,
}

fn get_next_parenthesized_chunk<'a>(
    s: &'a str,
    s_iter: &mut str::CharIndices,
    start_idx: usize,
) -> &'a str {
    let error_prefix = "parsing error:";
    match s.get(start_idx..start_idx + 1) {
        // TODO: OK, well to start: the start index is not actually a (, despite
        // us directly making sure that this is the case at the call site...
        None => panic!("wtf!"),
        Some(c) => match c {
            "(" => (),
            _ => panic!("first character of parenthesized chunk should be ("),
        },
    }
    // We only call this function when we've discovered an open parenthesis.
    let mut open_parens = 1;
    loop {
        match s_iter.next() {
            Some(c_tuple) => {
                match c_tuple {
                    (i, ')') => {
                        open_parens -= 1;
                        if open_parens == 0 {
                            // We want the i+1, since we want the trailing ).
                            break &s[start_idx..i + 2];
                        } else {
                            continue;
                        }
                    }
                    (_, '(') => {
                        open_parens += 1;
                        continue;
                    }
                    (_, _) => continue,
                }
            }
            None => {
                if open_parens == 0 {
                    break &s[start_idx..];
                } else {
                    panic!("{} unclosed parentheses", error_prefix)
                }
            }
        }
    }
}

fn chunk_one_level(s: &str) -> (ExprOp, Vec<&str>) {
    // TODO: Handle case where it's just 1 raw rate with no operators.
    let error_prefix = "parsing error:";
    let mut chunked: Vec<&str> = Vec::new();
    let s_trim = s.trim();
    let mut s_trim_iter = s_trim.char_indices();
    let mut outer_open_parens = 0;
    let mut active_range = false;
    let mut active_start = 0;
    let mut active_end = 0;
    loop {
        match s_trim_iter.next() {
            // NOTE: This sort of ends up being the same code that gets raw
            // rate type strings later in this function, but formatted
            // slightly differently, i.e. we directly pattern match on the
            // tuple later on, whereas here we pattern match on the char part
            // exclusively. I guess I could unify this later with some nicer
            // abstractions, but...it's fine for now.
            Some(c_tuple) => {
                let (i, c) = c_tuple;
                match c {
                    '(' => {
                        outer_open_parens += 1;
                        break;
                    }
                    // Must be a single raw rate, otherwise panic.
                    '0'..='9' | '/' => {
                        if active_range {
                            active_end = i
                        } else {
                            active_range = true;
                            active_start = i
                        }
                    }
                    _ => {
                        panic!(
                            "{} expression must either begin with ( or be a \
                                single raw rate",
                            error_prefix
                        )
                    }
                }
            }
            None => {
                if active_range {
                    chunked.push(s);
                    return (ExprOp::None, chunked);
                } else {
                    return (ExprOp::None, chunked); // Just return empty Vec
                }
            }
        }
    }
    // Find operator...
    let op: ExprOp = loop {
        match s_trim_iter.next() {
            Some(c_tuple) => match c_tuple {
                (_, ' ') | (_, '\t') => continue,
                (_, '.') => break ExprOp::Concat,
                (_, '|') => match s_trim_iter.next() {
                    Some(c_tuple) => match c_tuple {
                        (_, '|') => break ExprOp::Par,
                        (_, _) => panic!("{} | should be ||", error_prefix),
                    },
                    None => panic!("{} | should be ||", error_prefix),
                },
                (_, '+') => break ExprOp::Sum,
                (_, _) => panic!(
                    "{} open parenthesis must be followed by operator",
                    error_prefix
                ),
            },
            None => {
                panic!("{} no operator found for expression", error_prefix)
            }
        }
    };

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
                    }
                    (_, ' ') | (_, '\t') => {
                        if active_range {
                            active_range = false;
                            chunked.push(&s_trim[active_start..(active_end + 1)])
                        }
                    }
                    (i, '(') => {
                        if active_range {
                            active_range = false;
                            chunked.push(&s_trim[active_start..(active_end + 1)])
                        };
                        let pchunk = get_next_parenthesized_chunk(s, &mut s_trim_iter, i);
                        chunked.push(pchunk)
                    }
                    (_, ')') => {
                        outer_open_parens -= 1;
                        if active_range {
                            active_range = false;
                            chunked.push(&s_trim[active_start..(active_end + 1)])
                        };
                        if outer_open_parens == 0 {
                            // Just stop parsing when our initial open parenthesis
                            // gets closed (anything afterwards will just be ignored).
                            break;
                        }
                    }
                    (i, c) => {
                        panic!("{} did not expect {} at character {}", error_prefix, c, i)
                    }
                }
            }
            None => {
                if outer_open_parens == 0 {
                    break;
                } else {
                    panic!("{} expression not closed with )", error_prefix)
                }
            }
        }
    }
    return (op, chunked);
}

fn parse_chunk(chunk: &str) -> StreamRate {
    match chunk.get(0..1) {
        Some("(") => parse_side(chunk),
        Some(_) => {
            let mut rate_parts = chunk.split('/');
            let ev_count: usize = match rate_parts.next() {
                None => panic!("raw rate must have form n/t"),
                Some(e) => match e.parse::<usize>() {
                    Err(err) => panic!("raw rate event count is ill formed: {}", err),
                    Ok(r) => r,
                },
            };
            let win_size: usize = match rate_parts.next() {
                None => panic!("raw rate must have form n/t"),
                Some(e) => match e.parse::<usize>() {
                    Err(err) => panic!("raw rate window size is  ill formed: {}", err),
                    Ok(r) => r,
                },
            };
            StreamRate::Raw(Rate {
                events: ev_count,
                window: win_size,
            })
        }
        None => panic!("passed empty chunk to parse_chunk"),
    }
}

fn generate_streamrate_rec(eo: &ExprOp, v: Vec<&str>) -> Option<StreamRate> {
    match v.len() {
        0 => None,
        1 => {
            // This unwrap is guaranteed to be safe.
            Some(parse_chunk(v.get(0).unwrap().trim()))
        }
        _ => {
            let hd_parsed = parse_chunk(v.get(0).unwrap().trim());
            // This unwrap should also be guaranteed to be safe, although it's a
            // bit harder to reason about and prove. Basically, the case analysis
            // here makes it so.
            let tl_parsed = generate_streamrate_rec(eo, v.get(1..).unwrap().to_vec()).unwrap();
            match eo {
                ExprOp::None => None,
                ExprOp::Sum => Some(StreamRate::Sum(Box::new(hd_parsed), Box::new(tl_parsed))),
                ExprOp::Concat => {
                    Some(StreamRate::Concat(Box::new(hd_parsed), Box::new(tl_parsed)))
                }
                ExprOp::Par => Some(StreamRate::Par(Box::new(hd_parsed), Box::new(tl_parsed))),
            }
        }
    }
}
fn generate_streamrate(eo: &ExprOp, v: Vec<&str>) -> StreamRate {
    let error_prefix = "parsing error:";
    if v.len() == 0 {
        panic!("{} no subexpressions after operator", error_prefix)
    };
    match generate_streamrate_rec(&eo, v) {
        None => panic!("{} no subexpressions after operator", error_prefix),
        Some(sr) => sr,
    }
}

fn parse_side(s: &str) -> StreamRate {
    let error_prefix = "parsing error:";
    match chunk_one_level(s) {
        (ExprOp::None, v) => {
            match v.len() {
                0 => panic!("{} stream rate expression is empty", error_prefix),
                // If just a single raw rate, directly generate StreamRate
                1 => parse_chunk(v[0]),
                _ => panic!(
                    "{} only single raw rate allowed if no operator",
                    error_prefix
                ),
            }
        }
        (eo, v) => generate_streamrate(&eo, v),
    }
}

pub fn parse(full_sub_str: &String) -> (StreamRate, StreamRate) {
    let mut split_sides = full_sub_str.split("<:");
    let left = match split_sides.next() {
        None => panic!("wtf!"),
        Some(r) => parse_side(&r.trim()),
    };
    let right = match split_sides.next() {
        None => panic!("wtf!"),
        Some(r) => parse_side(&r.trim()),
    };
    // TODO: Remove or comment out after testing.
    // dbg!(left.clone());
    // dbg!(right.clone());
    (left, right)
}
