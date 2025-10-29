use crate::z3::Solver;
use crate::z3::SatResult;
use crate::z3::Ast;

#[derive(Clone, Debug, PartialEq, Eq)]
struct Rate {
    // NOTE: We may be able to allow real-valued windows here without any issue,
    // but first get something working with integer-valued windows.
    events: usize,
    window: usize,
}

// enum CoreRate {
//     Single(Rate),
//     Par(Vec<Rate>),
//     LConcat(Box<CoreRate>, Box<CoreRate>),
// }

// enum NormBARate {
//     Core(CoreRate),
//     Or(Box<NormBARate>, Box<NormBARate>),
//     And(Box<NormBARate>, Box<NormBARate>),
// }

#[derive(Clone, Debug, PartialEq, Eq)]
enum BARate {
    Sym(SymRate),
    Raw(Rate),
    Par(Box<BARate>, Box<BARate>),
    // NOTE: We should always immediately collapse Concats on the LHS of a
    // potential subtyping relation when both elements are Raw. This case is
    // really only for the scenario where one (or both!) sides of the Concat
    // are ParSum (since our current set of rules can't immediately reduce this
    // form of rate type until abstraction/SMT solving time).
    LConcat(Box<BARate>, Box<BARate>),
    Or(Box<BARate>, Box<BARate>),
    And(Box<BARate>, Box<BARate>)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum StreamRate {
    Raw(Rate),
    Sum(Box<StreamRate>, Box<StreamRate>),
    Par(Box<StreamRate>, Box<StreamRate>),
    Concat(Box<StreamRate>, Box<StreamRate>),
}

#[derive(Clone, Debug)]
enum SubRel {
    LHS,
    RHS,
}

// NOTE: This function has side effects: it mutates a Solver.
// TODO: Is there a way to recursively build our constraints, or should we just
// flatten the recursive structure into, say, Vecs, and then just loop imperatively
// over that?
struct SymRate {
    // Symbolic rate variables
    events: Ast::Int,
    window: Ast::Int,
    // Metadata for "global" constraint generation
    max_window: usize,
    min_window: usize,
    seen_windows: Vec<usize>,
}

fn rate_symbolize(rate: &BARate, rel: &SubRel, mut s: &Solver) -> SymRate {
    match rate {
        BARate::Sym(s) => s,
        BARate::Raw(r) => {
            // TODO: Wouldn't we want to this case to just directly encode the
            // exact concrete raw event and window values?
            let sym_raw_n = Ast::Int.fresh_const("n");
            let sym_raw_t = Ast::Int.fresh_const("t");
            let Rate {events: n, window: t} = r;
            match rel {
                // Would be nice to have an automated way to take high-level
                // rules and automatically compile them to these SMT assertions.
                // I'm pretty worried that my hand-compilation here is going to
                // be subtly wrong.
                SubRel::LHS => {
                    s.assert((&sym_raw_t.leq(t)).implies(&sym_raw_n.eq(n)));
                    s.assert((&sym_raw_t.ge(t)).implies(
                        ((&sym_raw_t % t).eq(0)).ite(
                            &sym_raw_n.eq(n * (&sym_raw_t / t)),
                            &sym_raw_n.eq(n * ((&sym_raw_t / t)) + 1))));
                },
                SubRel::RHS => {
                    s.assert((&sym_raw_t.geq(t)).implies(&syn_raw_n.eq(n)));
                    s.assert((&sym_raw_t.le(t)).implies(
                        ((t % &sym_raw_t).eq(0)).ite(
                            ((n % (t / &sym_raw_t)).eq(0)).ite(
                                &sym_raw_n.eq(n / (t / &sym_raw_t)),
                                &sym_raw_n.eq((n / (t / &sym_raw_t)) + 1)
                            ),
                            ((n % ((t / &sym_raw_t) + 1)).eq(0)).ite(
                                &sym_raw_n.eq(n / ((t / &sym_raw_t) + 1)),
                                &sym_raw_n.eq((n / ((t / &sym_raw_t) + 1)) + 1)
                            )
                        )
                    ))
                },
            };
            return SymRate {
                events: sym_raw_n,
                window: sym_raw_t,
                max_window: t,
                min_window: t,
                seen_windows: vec![t]
            }
        },
        BARate::Par(left, right) => {
            let sym_par_n = Ast::Int.fresh_const("n");
            let sym_par_t = Ast::Int.fresh_const("t");
            let left_sym = rate_symbolize(left, rel, s);
            let RateSym {
                events: l_sym_n,
                window: l_sym_t,
                max_window: l_max_window,
                min_window: l_min_window,
                seen_windows: l_seen_windows,
            } = left_sym;
            let right_sym = rate_symbolize(right, rel, s);
            let RateSym {
                events: r_sym_n,
                window: r_sym_t,
                max_window: r_max_window,
                min_window: r_min_window,
                seen_windows: r_seen_windows,
            } = right_sym;
            // If symbolic windows on left and right hand sides are equal, then
            // we can immediately just sum events.
            s.assert((&l_sym_t.eq(&r_sym_t)).implies(
                &sym_par_t.eq(&l_sym_t).and(&sym_par_n.eq(&l_sym_n + &r_sym_n))
            ));
            // New symbolic window for parallel must be equal to one of the
            // existing left or right symbolic windows.
            s.assert((&sym_par_t.eq(&l_sym_t)).or(&sym_par_t.eq(&r_sym_t)));
            // Otherwise, we have some sub/super-type specific (i.e. left and
            // right hand side specific) rules for conversion to a common
            // window size.
            match rel {
                SubRel::LHS => {
                    s.assert((&l_sym_t.lt(&r_sym_t)).implies(
                        ((&sym_par_t.eq(&l_sym_t)).implies(
                            // Convert RHS symbolic rate to supertype with
                            // window size l_sym_t
                        )).and(
                            // Convert LHS symbolic rate to supertype with
                            // window size r_sym_t
                            ((&sym_par_t.eq(&r_sym_t)).implies(
                            ))
                        )
                    ));
                    s.assert((&l_sym_t.gt(&r_sym_t)).implies(

                    ));
                },
                SubRel::RHS => {

                },
            }
        }
    }
}
fn rate_sub_symbolize(rate1: &BARate, rate2: &BARate, mut s: &Solver) {
    match (rate1, rate2) {
        // TODO: We probably just want to call rate_symbolize here on each side
        // and then do the stuff that involves the actual subtyping comparison
        // between both sides, i.e. coalescing all the seen windows, min and max
        // windows, and then adding the global constraints involving everything
        // in the subtyping relation to the solver.
        (BARate::Raw(r), BARate::Par(left, right)) => {
            let sym_raw_n = Ast::Int.fresh_const("n");
            let sym_raw_t = Ast::Int.fresh_const("t");
            let Rate {events: n, window: t} = r;
            // Constraints for LHS
            s.assert((&sym_raw_t.leq(t)).implies(&sym_raw_n.eq(n)));
            s.assert((&sym_raw_t.ge(t)).implies(
                ((&sym_raw_t % t).eq(0)).ite(
                    &sym_raw_n.eq(n * (&sym_raw_t / t)))));
            // Constraints for RHS
            let
            s.assert();
            //
        },
        (BARate::Par(left, right), BARate::Raw(r)) => (),
        (BARate::Raw(r), BARate::LConcat(left, right)) => (),
        (BARate::LConcat(left, right), BARate::Raw(r)) => (),
        (BARate::LConcat(l1, r1), BARate::Par(l2, r2)) => (),
        (BARate::Par(l1, r1), BARate::Par(l2, r2)) => (),
        // NOTE: We should never hit this if the reduction fixpoint to a normal
        // form works as expected and, more generally, all functions prior to
        // this function in the call stack work as expected.
        (_, _) => panic!("Unexpected type!")
    }
}

// Construct SMT constraints and solve.
fn rate_sub_solve(rate1: &BARate, rate2: &BARate) -> bool {
    let mut solver = Solver::new();
    rate_sub_symbolize(rate1, rate2, solver);
    match solver.check() {
        // TODO: It would be nice to produce a model in this case.
        SatResult::Sat => true,
        SatResult::Unsat | SatResult::Unknown => false
    }
}

fn rate_sub(rate1: &BARate, rate2: &BARate) -> bool {
    match (rate1, rate2) {
        (BARate::Raw(Rate { events: e1, window: w1 }),
         BARate::Raw(Rate { events: e2, window: w2 })) =>
            if w2 <= w1 {
                e1 <= e2
            } else {
                let bound = e2 / w2.div_ceil(*w1);
                *e1 <= bound
            },
        (r1, r2) => rate_sub_solve(r1, r2)
    }
}

fn ba_rate_sub(ba_rate1: &BARate, ba_rate2: &BARate) -> bool {
    match (ba_rate1, ba_rate2) {
        (r, BARate::Or(bar1, bar2)) => {
            ba_rate_sub(r, bar1) || ba_rate_sub(r, bar2)
        },
        (BARate::Or(bar1, bar2), r) => {
            ba_rate_sub(bar1, r) || ba_rate_sub(bar2, r)
        },
        (r, BARate::And(bar1, bar2)) => {
            ba_rate_sub(r, bar1) && ba_rate_sub(r, bar2)
        }
        (BARate::And(bar1, bar2), r) => {
            ba_rate_sub(bar1, r) && ba_rate_sub(bar2, r)
        },
        (r1, r2) => {
            rate_sub(r1, r2)
        },
    }
}

fn convert_to_ba(sr: &StreamRate, rel: &SubRel) -> BARate {
    match sr {
        StreamRate::Raw(r) => BARate::Raw(r.clone()),
        StreamRate::Sum(box_sr1, box_sr2) => {
            match rel {
                SubRel::LHS => {
                    BARate::Or(Box::new(convert_to_ba(box_sr1, rel)),
                               Box::new(convert_to_ba(box_sr2, rel)))
                },
                SubRel::RHS => {
                    BARate::And(Box::new(convert_to_ba(box_sr1, rel)),
                                Box::new(convert_to_ba(box_sr2, rel)))
                }
            }
        },
        StreamRate::Par(box_sr1, box_sr2) => {
            BARate::Par(Box::new(convert_to_ba(box_sr1, rel)),
                        Box::new(convert_to_ba(box_sr2, rel)))
        },
        StreamRate::Concat(box_sr1, box_sr2) => {
            match rel {
                SubRel::LHS => {
                    BARate::LConcat(Box::new(convert_to_ba(box_sr1, rel)),
                                    Box::new(convert_to_ba(box_sr2, rel)))
                },
                SubRel::RHS => {
                    BARate::And(Box::new(convert_to_ba(box_sr1, rel)),
                                Box::new(convert_to_ba(box_sr2, rel)))
                    }
            }
        },
    }
}

// NOTE: The second return value is a bool indicating whether the reduction step
// actually changed the BARate. This is used in fixpoint computation, i.e. we
// stop when the BARate rewrites stop changing.
fn reduce_ba(bar: BARate) -> (BARate, bool) {
     match bar {
         BARate::Sym(_) => (bar, false),
         BARate::Raw(_) => (bar, false),
         BARate::Par(bar1, bar2) => {
            match (*bar1, *bar2) {
                // (S1 OR S2) || S3 <=> (S1 || S3) OR (S2 || S3)
                (BARate::Or(left, right), b) | (b, BARate::Or(left, right)) => {
                    (BARate::Or(
                        Box::new(BARate::Par(left, Box::new(b.clone()))),
                        Box::new(BARate::Par(right, Box::new(b.clone())))),
                    true)
                },
                // (S1 AND S2) || S3 <=> (S1 || S3) AND (S2 || S3)
                (BARate::And(left, right), b) | (b, BARate::And(left, right)) => {
                    (BARate::And(
                        Box::new(BARate::Par(left, Box::new(b.clone()))),
                        Box::new(BARate::Par(right, Box::new(b.clone())))),
                    true)
                },
                (b1, b2) => {
                    let (reduced_b1, has_change1) = reduce_ba(b1);
                    let (reduced_b2, has_change2) = reduce_ba(b2);
                    match (has_change1, has_change2) {
                        (false, false) => {
                            (BARate::Par(
                                Box::new(reduced_b1),
                                Box::new(reduced_b2)),
                             false)
                        },
                        (_, _) => {
                            (BARate::Par(
                                Box::new(reduced_b1),
                                Box::new(reduced_b2)),
                             true)
                        }
                    }
                }
            }
        },
        BARate::LConcat(bar1, bar2) => {
            match (*bar1, *bar2) {
                 // (S1 OR S2) . S3 <=> (S1 . S3) OR (S2 . S3)
                (BARate::Or(left, right), b) | (b, BARate::Or(left, right)) => {
                    (BARate::Or(
                        Box::new(BARate::Par(left, Box::new(b.clone()))),
                        Box::new(BARate::Par(right, Box::new(b.clone())))),
                    true)
                },
                // (S1 AND S2) . S3 <=> (S1 . S3) AND (S2 . S3)
                (BARate::And(left, right), b) | (b, BARate::And(left, right)) => {
                    (BARate::And(
                        Box::new(BARate::Par(left, Box::new(b.clone()))),
                        Box::new(BARate::Par(right, Box::new(b.clone())))),
                    true)
                },
                (b1, b2) => {
                    let (reduced_b1, has_change1) = reduce_ba(b1);
                    let (reduced_b2, has_change2) = reduce_ba(b2);
                    match (has_change1, has_change2) {
                        (false, false) => {
                            (BARate::LConcat(
                                Box::new(reduced_b1),
                                Box::new(reduced_b2)),
                             false)
                        },
                        (_, _) => {
                            (BARate::LConcat(
                                Box::new(reduced_b1),
                                Box::new(reduced_b2)),
                             true)
                        }
                    }
                }
            }
        }
        BARate::Or(bar1, bar2) => {
            let (reduced_b1, has_change1) = reduce_ba(*bar1);
            let (reduced_b2, has_change2) = reduce_ba(*bar2);
            match (has_change1, has_change2) {
                (false, false) => {
                    (BARate::Or(
                        Box::new(reduced_b1),
                        Box::new(reduced_b2)),
                      false)
                },
                (_, _) => {
                    (BARate::Or(
                        Box::new(reduced_b1),
                        Box::new(reduced_b2)),
                      true)
                }
            }
        }
        BARate::And(bar1, bar2) => {
            let (reduced_b1, has_change1) = reduce_ba(*bar1);
            let (reduced_b2, has_change2) = reduce_ba(*bar2);
            match (has_change1, has_change2) {
                (false, false) => {
                    (BARate::And(
                        Box::new(reduced_b1),
                        Box::new(reduced_b2)),
                      false)
                },
                (_, _) => {
                    (BARate::And(
                        Box::new(reduced_b1),
                        Box::new(reduced_b2)),
                      true)
                }
            }
        }
    }
}

// NOTE/TODO: Should prove termination, just for sanity. Should also prove
// existence and structure of normal form.
fn reduce_ba_fixpoint(bar: BARate) -> BARate {
    let (reduced, has_change) = reduce_ba(bar);
    if has_change {
        reduce_ba_fixpoint(reduced)
    } else {
        reduced
    }
}

// fn normalize_ba(bar: BARate) -> NormBARate {
//     // TODO: Placeholder function for converting a fully reduce BARate to a
//     // NormBARate type, throwing an error if BARate is not actually fully
//     // reduced to normal form.
//     NormBARate::Core(CoreRate::Single(Rate{events: 10, window: 10}))
// }

fn stream_sub(sr1: &StreamRate, sr2: &StreamRate) -> bool {
    let norm_ba_lhs = reduce_ba_fixpoint(convert_to_ba(sr1, &SubRel::LHS));
    let norm_ba_rhs = reduce_ba_fixpoint(convert_to_ba(sr2, &SubRel::RHS));
    ba_rate_sub(&norm_ba_lhs, &norm_ba_rhs)
}

fn main() {
    println!("Hello, world!");
}

#[cfg(test)]
mod tests {
    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    // TODO: Consider using a property based testing library here to at least
    // test termination on generated BARates.
    #[test]
    fn test_reduce_ba_fixpoint() {
        let testba1 = BARate::Raw(Rate{events: 10, window: 20});
        assert_eq!(reduce_ba_fixpoint(testba1), BARate::Raw(Rate{events: 10, window: 20}));
        let testba2 = BARate::Par(
            Box::new(BARate::Or(
                Box::new(BARate::Raw(Rate{events: 10, window: 20})),
                Box::new(BARate::Raw(Rate{events: 50, window: 55})))),
            Box::new(BARate::And(
                Box::new(BARate::Raw(Rate{events: 30, window: 5})),
                Box::new(BARate::Raw(Rate{events: 1000, window: 5})))));
        assert_eq!(reduce_ba_fixpoint(testba2),
                   BARate::Or(
                       Box::new(BARate::And(
                           Box::new(BARate::Par(
                               Box::new(BARate::Raw(Rate{events: 30, window: 5})),
                               Box::new(BARate::Raw(Rate{events: 10, window: 20})))),
                           Box::new(BARate::Par(
                               Box::new(BARate::Raw(Rate{events: 1000, window: 5})),
                               Box::new(BARate::Raw(Rate{events: 10, window: 20})))))),
                       Box::new(BARate::And(
                           Box::new(BARate::Par(
                               Box::new(BARate::Raw(Rate{events: 30, window: 5})),
                               Box::new(BARate::Raw(Rate{events: 50, window: 55})))),
                           Box::new(BARate::Par(
                               Box::new(BARate::Raw(Rate{events: 1000, window: 5})),
                               Box::new(BARate::Raw(Rate{events: 50, window: 55}))))))));
    }

}
