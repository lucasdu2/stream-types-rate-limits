// use z3::ast::Ast;
use z3::SatResult;
use z3::Solver;
use z3::ast::Bool;
use z3::ast::Int;

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
    And(Box<BARate>, Box<BARate>),
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
#[derive(Clone, Debug, PartialEq, Eq)]
struct SymRate {
    // Symbolic rate variables
    events: Int,
    window: Int,
    // Metadata for "global" constraint generation
    max_window: usize,
    min_window: usize,
    seen_concrete_windows: Vec<usize>,
    seen_symbolic_windows: Vec<Int>,
}

// Two helper functions to take max, min of two usizes
fn max(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
}
fn min(a: usize, b: usize) -> usize {
    if a < b { a } else { b }
}

fn rate_symbolize(rate: &BARate, rel: &SubRel, s: &Solver) -> Vec<SymRate> {
    match rate {
        BARate::Sym(s) => vec![s.clone()],
        BARate::Raw(r) => {
            let sym_raw_n = Int::fresh_const("n");
            let sym_raw_t = Int::fresh_const("t");
            let Rate {
                events: usize_n,
                window: usize_t,
            } = r;
            let n = Int::from_u64(*usize_n as u64);
            let t = Int::from_u64(*usize_t as u64);
            match rel {
                // Would be nice to have an automated way to take high-level
                // rules and automatically compile them to these SMT assertions.
                // I'm pretty worried that my hand-compilation here is going to
                // be subtly wrong.
                SubRel::LHS => {
                    s.assert((sym_raw_t.le(&t)).implies(sym_raw_n.eq(&n)));
                    s.assert((sym_raw_t.ge(&t)).implies(((&sym_raw_t % &t).eq(0)).ite(
                        &sym_raw_n.eq(&n * (&sym_raw_t / &t)),
                        &sym_raw_n.eq(&n * (&sym_raw_t / &t) + 1),
                    )));
                }
                SubRel::RHS => {
                    s.assert((sym_raw_t.ge(&t)).implies(sym_raw_n.eq(&n)));
                    s.assert((sym_raw_t.le(&t)).implies(((&t % &sym_raw_t).eq(0)).ite(
                        &(((&n % (&t / &sym_raw_t)).eq(0)).ite(
                            &sym_raw_n.eq(&n / (&t / &sym_raw_t)),
                            &sym_raw_n.eq((&n / (&t / &sym_raw_t)) + 1),
                        )),
                        &(((&n % ((&t / &sym_raw_t) + 1)).eq(0)).ite(
                            &sym_raw_n.eq(&n / ((&t / &sym_raw_t) + 1)),
                            &sym_raw_n.eq((&n / ((&t / &sym_raw_t) + 1)) + 1),
                        )),
                    )))
                }
            };
            return vec![SymRate {
                events: sym_raw_n,
                window: sym_raw_t,
                max_window: *usize_t,
                min_window: *usize_t,
                seen_concrete_windows: vec![*usize_t],
                seen_symbolic_windows: Vec::new(),
            }];
        }
        BARate::Par(left, right) => {
            let left_sym = rate_symbolize(left, rel, s);
            let right_sym = rate_symbolize(right, rel, s);
            let mut return_sym: Vec<SymRate> = Vec::new();
            for lsym in left_sym.iter() {
                for rsym in right_sym.iter() {
                    let sym_par_n = Int::fresh_const("n");
                    let sym_par_t = Int::fresh_const("t");
                    let SymRate {
                        events: l_sym_n,
                        window: l_sym_t,
                        max_window: l_max_window,
                        min_window: l_min_window,
                        seen_concrete_windows: l_seen_concrete_windows,
                        seen_symbolic_windows: l_seen_symbolic_windows,
                    } = lsym;
                    let SymRate {
                        events: r_sym_n,
                        window: r_sym_t,
                        max_window: r_max_window,
                        min_window: r_min_window,
                        seen_concrete_windows: r_seen_concrete_windows,
                        seen_symbolic_windows: r_seen_symbolic_windows,
                    } = rsym;
                    // If symbolic windows on left and right hand sides are equal, then
                    // we can immediately just sum events.
                    s.assert((l_sym_t.eq(r_sym_t)).implies(Bool::and(&[
                        sym_par_t.eq(l_sym_t),
                        sym_par_n.eq(l_sym_n + r_sym_n),
                    ])));
                    // New symbolic window for parallel must be equal to one of the
                    // existing left or right symbolic windows.
                    s.assert(Bool::or(&[sym_par_t.eq(l_sym_t), sym_par_t.eq(r_sym_t)]));
                    // Otherwise, we have some sub/super-type specific (i.e. left and
                    // right hand side specific) rules for conversion to a common
                    // window size.
                    match rel {
                        SubRel::LHS => {
                            // l_sym_t < r_sym_t
                            s.assert((l_sym_t.lt(r_sym_t)).implies(Bool::and(&[
                                ((sym_par_t.eq(l_sym_t)).implies(
                                    // Convert RHS symbolic rate to supertype with
                                    // window size l_sym_t
                                    sym_par_n.eq(l_sym_n + r_sym_n),
                                )),
                                // Convert LHS symbolic rate to supertype with
                                // window size r_sym_t
                                ((sym_par_t.eq(r_sym_t)).implies(sym_par_n.eq(r_sym_n
                                    + ((r_sym_t % l_sym_t).eq(0)).ite(
                                        &(l_sym_n * (r_sym_t / l_sym_t)),
                                        &(l_sym_n * ((r_sym_t / l_sym_t) + 1)),
                                    )))),
                            ])));
                            // l_sym_t > r_sym_t
                            // TODO: There might at least be a way to factor out this
                            // particular reasoning into a function and then just call it
                            // each time we need it, i.e. something like:
                            // symbolize_window_change(smaller_w: ..., larger_w:...)
                            // Specifically the window change reasoning with all the
                            // annoying-to-type ceiling and floor cases.
                            s.assert((&l_sym_t.gt(r_sym_t)).implies(Bool::and(&[
                                (sym_par_t.eq(l_sym_t)).implies(
                                    // Convert RHS symbolic rate to supertype with
                                    // window size l_sym_t
                                    sym_par_n.eq(l_sym_n
                                        + (&(l_sym_t % r_sym_t).eq(0)).ite(
                                            &(r_sym_n * (l_sym_t / r_sym_t)),
                                            &(r_sym_n * ((l_sym_t / r_sym_t) + 1)),
                                        )),
                                ),
                                // Convert LHS symbolic rate to supertype with
                                // window size r_sym_t
                                (sym_par_t.eq(r_sym_t)).implies(sym_par_n.eq(l_sym_n + r_sym_n)),
                            ])));
                        }
                        SubRel::RHS => {
                            // l_sym_t < r_sym_t
                            s.assert((&l_sym_t.lt(r_sym_t)).implies(Bool::and(&[
                                ((sym_par_t.eq(l_sym_t)).implies(
                                    // Convert RHS symbolic rate to subtype with
                                    // window size l_sym_t
                                    sym_par_n.eq(l_sym_n
                                        + ((r_sym_t % l_sym_t).eq(0)).ite(
                                            &(((r_sym_n % (r_sym_t / l_sym_t)).eq(0)).ite(
                                                &(r_sym_n / (r_sym_t / l_sym_t)),
                                                &(r_sym_n / ((r_sym_t / l_sym_t) + 1)),
                                            )),
                                            &(((r_sym_n % ((r_sym_t / l_sym_t) + 1)).eq(0)).ite(
                                                &(r_sym_n / ((r_sym_t / l_sym_t) + 1)),
                                                &((r_sym_n / ((r_sym_t / l_sym_t) + 1)) + 1),
                                            )),
                                        )),
                                )),
                                // Convert LHS symbolic rate to subtype with
                                // window size r_sym_t
                                (sym_par_t.eq(r_sym_t)).implies(sym_par_n.eq(l_sym_n + r_sym_n)),
                            ])));
                            // l_sym_t > r_sym_t
                            s.assert((&l_sym_t.gt(r_sym_t)).implies(Bool::and(&[
                                (sym_par_t.eq(l_sym_t)).implies(
                                    // Convert RHS symbolic rate to subtype with
                                    // window size l_sym_t
                                    sym_par_n.eq(l_sym_n + r_sym_n),
                                ),
                                (sym_par_t.eq(r_sym_t)).implies(
                                    // Convert LHS symbolic rate to subtype with
                                    // window size r_sym_t
                                    sym_par_n.eq(r_sym_n
                                        + ((l_sym_t % r_sym_t).eq(0)).ite(
                                            &(((l_sym_n % (l_sym_t / r_sym_t)).eq(0)).ite(
                                                &(l_sym_n / (l_sym_t / r_sym_t)),
                                                &(l_sym_n / ((l_sym_t / r_sym_t) + 1)),
                                            )),
                                            &(((l_sym_n % ((l_sym_t / r_sym_t) + 1)).eq(0)).ite(
                                                &(l_sym_n / ((l_sym_t / r_sym_t) + 1)),
                                                &((l_sym_n / ((l_sym_t / r_sym_t) + 1)) + 1),
                                            )),
                                        )),
                                ),
                            ])));
                        }
                    };
                    // More imperative stuff that I don't like, but I don't know
                    // how to use RCs yet so it's OK.
                    let mut all_seen_concrete_windows = Vec::new();
                    all_seen_concrete_windows.extend_from_slice(&l_seen_concrete_windows[..]);
                    all_seen_concrete_windows.extend_from_slice(&r_seen_concrete_windows[..]);
                    let mut all_seen_symbolic_windows = Vec::new();
                    all_seen_symbolic_windows.extend_from_slice(&l_seen_symbolic_windows[..]);
                    all_seen_symbolic_windows.extend_from_slice(&r_seen_symbolic_windows[..]);
                    let par_rate_sym = SymRate {
                        events: sym_par_n,
                        window: sym_par_t,
                        max_window: max(*l_max_window, *r_max_window),
                        min_window: min(*l_min_window, *r_min_window),
                        seen_concrete_windows: all_seen_concrete_windows,
                        seen_symbolic_windows: all_seen_symbolic_windows,
                    };
                    return_sym.push(par_rate_sym);
                }
            }
            return return_sym;
        }
        BARate::LConcat(left, right) => {
            // NOTE: rel here should only be SubRel::LHS. Again, it would be
            // nice to prove this in the code itself, but I'll just write this
            // note here now to call this out.
            let left_sym = rate_symbolize(left, rel, s);
            let right_sym = rate_symbolize(right, rel, s);
            // OK, I've succumbed here to writing very imperative code. There
            // might be a way to recover a more functional style, although it
            // might not be super nice in Rust.
            let mut return_sym: Vec<SymRate> = Vec::new();
            for lsym in left_sym.iter() {
                for rsym in right_sym.iter() {
                    let SymRate {
                        events: l_sym_n,
                        window: l_sym_t,
                        max_window: l_max_window,
                        min_window: l_min_window,
                        seen_concrete_windows: l_seen_concrete_windows,
                        seen_symbolic_windows: l_seen_symbolic_windows,
                    } = lsym;
                    let SymRate {
                        events: r_sym_n,
                        window: r_sym_t,
                        max_window: r_max_window,
                        min_window: r_min_window,
                        seen_concrete_windows: r_seen_concrete_windows,
                        seen_symbolic_windows: r_seen_symbolic_windows,
                    } = rsym;
                    let cross_sym_n = Int::fresh_const("n");
                    let cross_sym_t = Int::fresh_const("t");
                    // Add constraints for crossover period
                    s.assert(&cross_sym_n.eq(l_sym_n + r_sym_n));
                    s.assert(&cross_sym_t.eq(l_sym_t + r_sym_t));
                    // More imperative stuff that I don't like, but I don't know
                    // how to use RCs yet so it's OK.
                    // TODO: This is copy-pasted from above; there definitely
                    // is opportunity here to better abstract and modularize
                    // the code.
                    let mut all_seen_concrete_windows = Vec::new();
                    all_seen_concrete_windows.extend_from_slice(&l_seen_concrete_windows[..]);
                    all_seen_concrete_windows.extend_from_slice(&r_seen_concrete_windows[..]);
                    let mut all_seen_symbolic_windows = Vec::new();
                    all_seen_symbolic_windows.extend_from_slice(&l_seen_symbolic_windows[..]);
                    all_seen_symbolic_windows.extend_from_slice(&r_seen_symbolic_windows[..]);
                    all_seen_symbolic_windows.push(cross_sym_t.clone());
                    let cross_rate_sym = SymRate {
                        events: cross_sym_n,
                        window: cross_sym_t,
                        max_window: max(*l_max_window, *r_max_window),
                        min_window: min(*l_min_window, *r_min_window),
                        seen_concrete_windows: all_seen_concrete_windows,
                        // Add the symbolic window generated by the crossover
                        // region to the set of seen symbolic windows for use
                        // in the overall subtyping constraint as a possible
                        // common window size. It's actually unclear to me if
                        // this is necessary, or if we can get away with just
                        // tracking concrete window sizes, but I'll probably
                        // need to prove this. I do suspect right now that it
                        // is necessary, so I'm including it here.
                        seen_symbolic_windows: all_seen_symbolic_windows,
                    };
                    return_sym.push(lsym.clone());
                    return_sym.push(cross_rate_sym);
                    return_sym.push(rsym.clone());
                }
            }
            return return_sym;
        }
        _ => {
            // This is where I wish we could prove this statement in the code
            // instead of just throwing an exception. Maybe if I designed the
            // types a bit better, it would help...but I think this is where
            // dependent types would be very nice.
            panic!("Unexpected type constructor: And, Or should not appear here.")
        }
    }
}

fn rate_sub_symbolize(rate1: &BARate, rate2: &BARate, s: &Solver) {
    // TODO: We probably just want to call rate_symbolize here on each side
    // and then do the stuff that involves the actual subtyping comparison
    // between both sides, i.e. coalescing all the seen windows, min and max
    // windows, and then adding the global constraints involving everything
    // in the subtyping relation to the solver.
    let left_rate_sym = rate_symbolize(rate1, &SubRel::LHS, s);
    let right_rate_sym = rate_symbolize(rate2, &SubRel::RHS, s);
    // Coalesce and add final constraints
    for lsym in left_rate_sym.iter() {
        for rsym in right_rate_sym.iter() {
            let SymRate {
                events: l_sym_n,
                window: l_sym_t,
                max_window: l_max_window,
                min_window: l_min_window,
                seen_concrete_windows: l_seen_concrete_windows,
                seen_symbolic_windows: l_seen_symbolic_windows,
            } = lsym;
            let SymRate {
                events: r_sym_n,
                window: r_sym_t,
                max_window: r_max_window,
                min_window: r_min_window,
                seen_concrete_windows: r_seen_concrete_windows,
                seen_symbolic_windows: r_seen_symbolic_windows,
            } = rsym;
            s.assert(&l_sym_t.eq(r_sym_t));
            let overall_max_window = max(*l_max_window, *r_max_window);
            let overall_min_window = min(*l_min_window, *r_min_window);
            s.assert(&l_sym_t.le(Int::from_u64(overall_max_window as u64)));
            s.assert(&l_sym_t.ge(Int::from_u64(overall_min_window as u64)));
            s.assert(&l_sym_n.le(r_sym_n));
            // TODO: Add constraints for possible window sizes --- must be one
            // of seen concrete windows or seen symbolic windows.
            // TODO: This is copy-pasted from above; there definitely
            // is opportunity here to better abstract and modularize
            // the code.
            let mut all_seen_concrete_windows = Vec::new();
            all_seen_concrete_windows.extend_from_slice(&l_seen_concrete_windows[..]);
            all_seen_concrete_windows.extend_from_slice(&r_seen_concrete_windows[..]);
            let mut all_seen_symbolic_windows = Vec::new();
            all_seen_symbolic_windows.extend_from_slice(&l_seen_symbolic_windows[..]);
            all_seen_symbolic_windows.extend_from_slice(&r_seen_symbolic_windows[..]);
            // NOTE: How do we do polymorphism in Rust?
            // We could probably construct a variant type for generic windows,
            // i.e. concrete or symbolic, and then do stuff on that type.
            let concrete_window_eq = |cw: usize| -> Bool { l_sym_t.eq(Int::from_u64(cw as u64)) };
            let symbolic_window_eq = |sw: Int| -> Bool { l_sym_t.eq(sw) };
            let mut all_window_constraints: Vec<Bool> = Vec::new();
            let mut concrete_window_constraints = all_seen_concrete_windows
                .into_iter()
                .map(concrete_window_eq)
                .collect();
            let mut symbolic_window_constraints = all_seen_symbolic_windows
                .into_iter()
                .map(symbolic_window_eq)
                .collect();
            all_window_constraints.append(&mut concrete_window_constraints);
            all_window_constraints.append(&mut symbolic_window_constraints);
            s.assert(Bool::or(&all_window_constraints[..]));
        }
    }
}

// Construct SMT constraints and solve.
fn rate_sub_solve(rate1: &BARate, rate2: &BARate) -> bool {
    let solver = Solver::new();
    rate_sub_symbolize(rate1, rate2, &solver);
    match solver.check() {
        // TODO: It would be nice to produce a model in this case.
        SatResult::Sat => true,
        SatResult::Unsat | SatResult::Unknown => false,
    }
}

fn rate_sub(rate1: &BARate, rate2: &BARate) -> bool {
    match (rate1, rate2) {
        (
            BARate::Raw(Rate {
                events: e1,
                window: w1,
            }),
            BARate::Raw(Rate {
                events: e2,
                window: w2,
            }),
        ) => {
            if w2 <= w1 {
                e1 <= e2
            } else {
                let bound = e2 / w2.div_ceil(*w1);
                *e1 <= bound
            }
        }
        (r1, r2) => rate_sub_solve(r1, r2),
    }
}

fn ba_rate_sub(ba_rate1: &BARate, ba_rate2: &BARate) -> bool {
    match (ba_rate1, ba_rate2) {
        (r, BARate::Or(bar1, bar2)) => ba_rate_sub(r, bar1) || ba_rate_sub(r, bar2),
        (BARate::Or(bar1, bar2), r) => ba_rate_sub(bar1, r) || ba_rate_sub(bar2, r),
        (r, BARate::And(bar1, bar2)) => ba_rate_sub(r, bar1) && ba_rate_sub(r, bar2),
        (BARate::And(bar1, bar2), r) => ba_rate_sub(bar1, r) && ba_rate_sub(bar2, r),
        (r1, r2) => rate_sub(r1, r2),
    }
}

fn convert_to_ba(sr: &StreamRate, rel: &SubRel) -> BARate {
    match sr {
        StreamRate::Raw(r) => BARate::Raw(r.clone()),
        StreamRate::Sum(box_sr1, box_sr2) => match rel {
            SubRel::LHS => BARate::Or(
                Box::new(convert_to_ba(box_sr1, rel)),
                Box::new(convert_to_ba(box_sr2, rel)),
            ),
            SubRel::RHS => BARate::And(
                Box::new(convert_to_ba(box_sr1, rel)),
                Box::new(convert_to_ba(box_sr2, rel)),
            ),
        },
        StreamRate::Par(box_sr1, box_sr2) => BARate::Par(
            Box::new(convert_to_ba(box_sr1, rel)),
            Box::new(convert_to_ba(box_sr2, rel)),
        ),
        StreamRate::Concat(box_sr1, box_sr2) => match rel {
            SubRel::LHS => BARate::LConcat(
                Box::new(convert_to_ba(box_sr1, rel)),
                Box::new(convert_to_ba(box_sr2, rel)),
            ),
            SubRel::RHS => BARate::And(
                Box::new(convert_to_ba(box_sr1, rel)),
                Box::new(convert_to_ba(box_sr2, rel)),
            ),
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
                (BARate::Or(left, right), b) | (b, BARate::Or(left, right)) => (
                    BARate::Or(
                        Box::new(BARate::Par(left, Box::new(b.clone()))),
                        Box::new(BARate::Par(right, Box::new(b.clone()))),
                    ),
                    true,
                ),
                // (S1 AND S2) || S3 <=> (S1 || S3) AND (S2 || S3)
                (BARate::And(left, right), b) | (b, BARate::And(left, right)) => (
                    BARate::And(
                        Box::new(BARate::Par(left, Box::new(b.clone()))),
                        Box::new(BARate::Par(right, Box::new(b.clone()))),
                    ),
                    true,
                ),
                (b1, b2) => {
                    let (reduced_b1, has_change1) = reduce_ba(b1);
                    let (reduced_b2, has_change2) = reduce_ba(b2);
                    match (has_change1, has_change2) {
                        (false, false) => (
                            BARate::Par(Box::new(reduced_b1), Box::new(reduced_b2)),
                            false,
                        ),
                        (_, _) => (
                            BARate::Par(Box::new(reduced_b1), Box::new(reduced_b2)),
                            true,
                        ),
                    }
                }
            }
        }
        BARate::LConcat(bar1, bar2) => {
            match (*bar1, *bar2) {
                // (S1 OR S2) . S3 <=> (S1 . S3) OR (S2 . S3)
                (BARate::Or(left, right), b) | (b, BARate::Or(left, right)) => (
                    BARate::Or(
                        Box::new(BARate::Par(left, Box::new(b.clone()))),
                        Box::new(BARate::Par(right, Box::new(b.clone()))),
                    ),
                    true,
                ),
                // (S1 AND S2) . S3 <=> (S1 . S3) AND (S2 . S3)
                (BARate::And(left, right), b) | (b, BARate::And(left, right)) => (
                    BARate::And(
                        Box::new(BARate::Par(left, Box::new(b.clone()))),
                        Box::new(BARate::Par(right, Box::new(b.clone()))),
                    ),
                    true,
                ),
                (b1, b2) => {
                    let (reduced_b1, has_change1) = reduce_ba(b1);
                    let (reduced_b2, has_change2) = reduce_ba(b2);
                    match (has_change1, has_change2) {
                        (false, false) => (
                            BARate::LConcat(Box::new(reduced_b1), Box::new(reduced_b2)),
                            false,
                        ),
                        (_, _) => (
                            BARate::LConcat(Box::new(reduced_b1), Box::new(reduced_b2)),
                            true,
                        ),
                    }
                }
            }
        }
        BARate::Or(bar1, bar2) => {
            let (reduced_b1, has_change1) = reduce_ba(*bar1);
            let (reduced_b2, has_change2) = reduce_ba(*bar2);
            match (has_change1, has_change2) {
                (false, false) => (
                    BARate::Or(Box::new(reduced_b1), Box::new(reduced_b2)),
                    false,
                ),
                (_, _) => (BARate::Or(Box::new(reduced_b1), Box::new(reduced_b2)), true),
            }
        }
        BARate::And(bar1, bar2) => {
            let (reduced_b1, has_change1) = reduce_ba(*bar1);
            let (reduced_b2, has_change2) = reduce_ba(*bar2);
            match (has_change1, has_change2) {
                (false, false) => (
                    BARate::And(Box::new(reduced_b1), Box::new(reduced_b2)),
                    false,
                ),
                (_, _) => (
                    BARate::And(Box::new(reduced_b1), Box::new(reduced_b2)),
                    true,
                ),
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
        let testba1 = BARate::Raw(Rate {
            events: 10,
            window: 20,
        });
        assert_eq!(
            reduce_ba_fixpoint(testba1),
            BARate::Raw(Rate {
                events: 10,
                window: 20
            })
        );
        let testba2 = BARate::Par(
            Box::new(BARate::Or(
                Box::new(BARate::Raw(Rate {
                    events: 10,
                    window: 20,
                })),
                Box::new(BARate::Raw(Rate {
                    events: 50,
                    window: 55,
                })),
            )),
            Box::new(BARate::And(
                Box::new(BARate::Raw(Rate {
                    events: 30,
                    window: 5,
                })),
                Box::new(BARate::Raw(Rate {
                    events: 1000,
                    window: 5,
                })),
            )),
        );
        assert_eq!(
            reduce_ba_fixpoint(testba2),
            BARate::Or(
                Box::new(BARate::And(
                    Box::new(BARate::Par(
                        Box::new(BARate::Raw(Rate {
                            events: 30,
                            window: 5
                        })),
                        Box::new(BARate::Raw(Rate {
                            events: 10,
                            window: 20
                        }))
                    )),
                    Box::new(BARate::Par(
                        Box::new(BARate::Raw(Rate {
                            events: 1000,
                            window: 5
                        })),
                        Box::new(BARate::Raw(Rate {
                            events: 10,
                            window: 20
                        }))
                    ))
                )),
                Box::new(BARate::And(
                    Box::new(BARate::Par(
                        Box::new(BARate::Raw(Rate {
                            events: 30,
                            window: 5
                        })),
                        Box::new(BARate::Raw(Rate {
                            events: 50,
                            window: 55
                        }))
                    )),
                    Box::new(BARate::Par(
                        Box::new(BARate::Raw(Rate {
                            events: 1000,
                            window: 5
                        })),
                        Box::new(BARate::Raw(Rate {
                            events: 50,
                            window: 55
                        }))
                    ))
                ))
            )
        );
    }
}
