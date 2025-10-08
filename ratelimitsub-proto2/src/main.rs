#[derive(Copy, Clone, Debug, PartialEq)]
struct Rate {
    events: usize,
    // TODO: We may be able to allow real-valued windows here without any issue,
    // but first get something working with integer-valued windows.
    window: usize,
}

// TODO: Later on, make these actual types and not just a type aliases.
type OrRate = Vec<Rate>;
type RateRefine = Vec<OrRate>;

#[derive(Clone, Debug)]
enum StreamTy {
    Base(RateRefine),
    Sum(Box<StreamTy>, Box<StreamTy>, RateRefine),
    Par(Box<StreamTy>, Box<StreamTy>, RateRefine),
    Concat(Box<StreamTy>, Box<StreamTy>, RateRefine),
    Star(Box<StreamTy>, RateRefine),
}
// NOTE: + should just be a logical or --- add this to our lattice, and we can
// do way with any notion of max or min.
// NOTE: One way to do things is just to reduce everything first-order, i.e.
// only bare rates connected with AND, OR. Then can solve for entailment. There
// may be no way to do this without resorting to symbolic values and an SMT solver,
// but I think we may be able to get away with heuristics for now.
// NOTE: Even if we must resort to symbolic values, we may be able to constrain
// the search space even further by bounding it with the window sizes in the
// entailment we are trying to prove.
// NOTE: Reducing everything to first-order using aggressive heuristics might
// be the simple, if very crude, first thing you can try. Trying to delegate
// things to an SMT solver or more fine-grained heuristics for an exact answer
// is a good next step.
// The below is for our manual (i.e. non-SMT) heuristic solution.
// NOTE: Perhaps LHS should be in disjunctive normal form, RHS should be in
// conjunctive normal form: then we need to check that every clause on the LHS
// implies all clauses on the RHS for entailment.

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

fn uniform_rate_max(rate1: &Rate, rate2: &Rate) -> Rate {
    if uniform_rate_sub(rate1, rate2) {
        *rate2
    } else if uniform_rate_sub(rate2, rate1) {
        *rate1
    } else {
        // NOTE: Semantically speaking, if the window sizes are equal then the
        // rates will certainly be directly comparable (so should be handled in
        // the prior two if-else clauses). That case actually should never get
        // to this point.
        if rate1.window <= rate2.window {
            let ratio_ceil = (rate2.window).div_ceil(rate1.window);
            let convert_n1 = rate1.events * ratio_ceil;
            if convert_n1 > rate2.events {
                Rate{events: convert_n1, window: rate2.window}
            } else {
                // NOTE: The logic here is basically that, in the case the above
                // conversion doesn't give us a supertype/upper bound, then we
                // want to take an upper bound with the window size of rate1.
                // This should *always* be the rate below. Why? If rate2.window
                // is bigger than rate1.window, the only way for the direct
                // comparison to not work is if rate2.events is also greater
                // than rate1.events (otherwise, rate1 is definitely a supertype
                // of rate2). When converting rate2 to rate1's window size,
                // since rate2's window is bigger than rate1, we end up with
                // the rate below (by our subtyping rules for getting a
                // supertype). rate2.events is already guaranteed to be greater
                // than rate1.events, so the below is immediately an upper bound
                // on both. QED. (handwavingly speaking)
                Rate{events: rate2.events, window: rate1.window}
            }
        } else {
            let ratio_ceil = (rate1.window).div_ceil(rate2.window);
            let convert_n2 = rate2.events * ratio_ceil;
            if convert_n2 > rate1.events {
                Rate{events: convert_n2, window: rate1.window}
            } else {
                Rate{events: rate1.events, window: rate2.window}
            }
        }
    }
}
// NOTE: This is also imprecise. We are actually able to get a fully precise
// least upper bound by simply taking the conjunction of the two rates. However,
// this doesn't play well with the way we end up doing the subtyping check, so
// we just do this as a hack for now. This prototype will also end up being
// mostly thrown away (since our current rate typing system seems sort of seems
// fundamentally messed up), so it's OK. This is just to get a bit more practice
// with Rust and have something to build from.
fn uniform_rate_min(rate1: &Rate, rate2: &Rate) -> Rate {
    if uniform_rate_sub(rate1, rate2) {
        *rate1
    } else if uniform_rate_sub(rate2, rate1) {
        *rate2
    } else {
        if rate1.window <= rate2.window {
            let ratio_ceil = (rate2.window).div_ceil(rate1.window);
            let convert_n2 = rate2.events / ratio_ceil;
            if convert_n2 < rate1.events {
                Rate{events: convert_n2, window: rate1.window}
            } else {
                Rate{events: rate1.events, window: rate1.window}
            }
        } else {
            let ratio_ceil = (rate1.window).div_ceil(rate2.window);
            let convert_n1 = rate1.events / ratio_ceil;
            if convert_n1 < rate2.events {
                Rate{events: convert_n1, window: rate2.window}
            } else {
                Rate{events: rate2.events, window: rate2.window}
            }
        }
    }
}
fn uniform_refine_collapse_max(refine: &RateRefine) -> Rate {
    let zero = Rate{events: 0, window: 1};
    refine.iter().fold(zero, |acc: Rate, x: &Rate| uniform_rate_max(&acc, x))
}

fn uniform_refine_max() {}

fn uniform_refine_collapse_min(refine1: &RateRefine, refine2: &RateRefine) -> RateRefine {

}
fn uniform_refine_min() {}

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
            // For empty vectors, just use an if statement in the branch
            uniform_refine_sub(refine1, refine2) && check_subtype(s1, t1) && check_subtype(s2, t2)
        }
        _ => false,
    };
    false
}

fn main() {
    println!("Hello, world!");
}
