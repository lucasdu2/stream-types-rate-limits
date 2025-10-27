#[derive(Clone, Debug, PartialEq)]
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

#[derive(Clone, Debug)]
enum BARate {
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

#[derive(Clone, Debug)]
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

fn rate_sub(rate1: &CoreRate, rate2: &CoreRate) -> bool {
    match (rate1, rate2) {
        (CoreRate::Single(Rate { events: e1, window: w1 }),
         CoreRate::Single(Rate { events: e2, window: w2 })) =>
            if w2 <= w1 {
                e1 <= e2
            } else {
                let bound = e2 / w2.div_ceil(*w1);
                *e1 <= bound
            },
        // TODO: We'll need to construct SMT encodings here and call out to a
        // solver like Z3. We return true as a placeholder for now.
        (_r1, _r2) => true
    }
}

fn ba_rate_sub(ba_rate1: &NormBARate, ba_rate2: &NormBARate) -> bool {
    match (ba_rate1, ba_rate2) {
        (NormBARate::Core(r1), NormBARate::Core(r2)) => {
            rate_sub(r1, r2)
        },
        (r, NormBARate::Or(bar1, bar2)) => {
            ba_rate_sub(r, bar1) || ba_rate_sub(r, bar2)
        },
        (NormBARate::Or(bar1, bar2), r) => {
            ba_rate_sub(bar1, r) || ba_rate_sub(bar2, r)
        },
        (r, NormBARate::And(bar1, bar2)) => {
            ba_rate_sub(r, bar1) && ba_rate_sub(r, bar2)
        }
        (NormBARate::And(bar1, bar2), r) => {
            ba_rate_sub(bar1, r) && ba_rate_sub(bar2, r)
        }
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

// BARate::Raw(Rate{events: 0, window: 1})
// NOTE: The second return value is a bool indicating whether the reduction step
// actually changed the BARate. This is used in fixpoint computation, i.e. we
// stop when the BARate rewrites stop changing.
fn reduce_ba(bar: BARate) -> (BARate, bool) {
     match bar {
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
    let norm_ba_lhs = normalize_ba(convert_to_ba(sr1, &SubRel::LHS));
    let norm_ba_rhs = normalize_ba(convert_to_ba(sr2, &SubRel::RHS));
    ba_rate_sub(&norm_ba_lhs, &norm_ba_rhs)
}

fn main() {
    println!("Hello, world!");
}
