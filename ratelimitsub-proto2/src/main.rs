#[derive(Copy, Clone, Debug, PartialEq)]
struct Rate {
    events: usize,
    window: usize,
}

// TODO: Later on, make this an actual type and not just a type alias.
type RateRefine = Vec<Rate>;

// TODO: You may be able to model refinements this way too, with StreamTy just
// being base stream types.
// enum RateTy {
//     Stream(StreamTy),
//     RateRf(Box<RateTy>, Rate),
// }

#[derive(Clone, Debug)]
enum StreamTy {
    Int(RateRefine),
    Sum(Box<StreamTy>, Box<StreamTy>, RateRefine),
    Par(Box<StreamTy>, Box<StreamTy>, RateRefine),
    Concat(Box<StreamTy>, Box<StreamTy>, RateRefine),
    Star(Box<StreamTy>, RateRefine),
}

fn uniform_rate_sub(rate1: &Rate, rate2: &Rate) -> bool {
    if rate2.window <= rate1.window {
        rate1.events <= rate2.events
    } else {
        let bound = rate2.events / (rate2.window).div_ceil(rate1.window);
        rate1.events <= bound
    }
}

fn uniform_refine_sub(refine1: &RateRefine, refine2: &RateRefine) -> bool {
    let check_rate_sub = |rate1: &Rate| -> bool {
        for rate2 in refine2 {
            if uniform_rate_sub(rate1, rate2) {
                return true;
            }
        }
        false
    };
    for rate1 in refine1 {
        if !check_rate_sub(rate1) {
            return false;
        }
    }
    true
}

fn can_erase(single_rate: &Rate, full_refine: &RateRefine) -> bool {
    for in_r in full_refine {
        if uniform_rate_sub(in_r, single_rate) {
            return true;
        }
    }
    false
}

fn merge_refine(inner_refine: &RateRefine, outer_refine: &RateRefine) -> RateRefine {
    // TODO: Let's remove this clone somehow. Later!
    let mut new_refine = inner_refine.clone();
    for out_r in outer_refine {
        if !can_erase(out_r, inner_refine) {
            new_refine.push(*out_r)
        };
    }
    new_refine
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_uniform_rate_sub() {
        let rate1 = Rate {
            events: 10,
            window: 3,
        };
        let rate2 = Rate {
            events: 12,
            window: 4,
        };
        let check = uniform_rate_sub(&rate1, &rate2);
        assert_eq!(check, false);
    }

    #[test]
    fn test_can_erase() {
        let single_rate: Rate = Rate {
            events: 10,
            window: 3,
        };
        let full_refine: RateRefine = vec![Rate {
            events: 12,
            window: 4,
        }];
        assert_eq!(can_erase(&single_rate, &full_refine), false);
    }

    #[test]
    fn test_merge_refine_1() {
        let inner_refine: RateRefine = vec![Rate {
            events: 10,
            window: 3,
        }];
        let outer_refine: RateRefine = vec![Rate {
            events: 12,
            window: 4,
        }];
        let merged: RateRefine = merge_refine(&inner_refine, &outer_refine);
        assert_eq!(
            merged,
            vec![
                Rate {
                    events: 10,
                    window: 3
                },
                Rate {
                    events: 12,
                    window: 4
                }
            ]
        );
    }

    #[test]
    fn test_merge_refine_2() {
        let inner_refine: RateRefine = vec![Rate {
            events: 10,
            window: 3,
        }];
        let outer_refine: RateRefine = vec![
            Rate {
                events: 12,
                window: 4,
            },
            Rate {
                events: 20,
                window: 6,
            },
            Rate {
                events: 50,
                window: 4,
            },
        ];
        let merged: RateRefine = merge_refine(&inner_refine, &outer_refine);
        assert_eq!(
            merged,
            vec![
                Rate {
                    events: 10,
                    window: 3
                },
                Rate {
                    events: 12,
                    window: 4
                }
            ]
        );
    }
}

fn check_subtype(s1: &StreamTy, s2: &StreamTy) -> bool {
    match (s1, s2) {
        (StreamTy::Int(refine1), StreamTy::Int(refine2)) => uniform_refine_sub(refine1, refine2),
        (StreamTy::Sum(s1, s2, refine1), StreamTy::Sum(t1, t2, refine2)) => {
            // TODO: Either need to figure out how to nicely pattern match on
            // empty vectors or re-do the implementation a bit to run the push
            // in (or "normalize") operation as part of check_subtype.
            uniform_refine_sub(refine1, refine2) && check_subtype(s1, t1) && check_subtype(s2, t2)
        }
        _ => false,
    };
    false
}

fn main() {
    println!("Hello, world!");
}
