#[derive(Clone, Debug, PartialEq)]
struct Rate {
    // NOTE: We may be able to allow real-valued windows here without any issue,
    // but first get something working with integer-valued windows.
    events: usize,
    window: usize,
}

#[derive(Clone, Debug)]
enum BARate {
    ParSum(Vec<Box<Rate>>),
    // NOTE: We should always immediately collapse Concats on the LHS of a
    // potential subtyping relation when both elements are Raw. This case is
    // really only for the scenario where one (or both!) sides of the Concat
    // are ParSum (since our current set of rules can't immediately reduce this
    // form of rate type until abstraction/SMT solving time).
    LConcat(Vec<Box<BARate>>),
    Or(Box<BARate>, Box<BARate>),
    And(Box<BARate>, Box<BARate>)
}

#[derive(Clone, Debug)]
enum StreamRate {
    Base(BARate),
    Sum(Box<StreamRate>, Box<StreamRate>),
    Par(Box<StreamRate>, Box<StreamRate>),
    Concat(Box<StreamRate>, Box<StreamRate>),
    Star(Box<StreamRate>),
}

#[derive(Clone, Debug)]
enum SubRel {
    LHS,
    RHS,
}

fn rate_sub(rate1: &Rate, rate2: &Rate) -> bool {
    match (rate1, rate2) {
         (Rate::Raw { events: e1, window: w1 }, Rate::Raw { events: e2, window: w2 }) =>
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

fn ba_rate_sub(ba_rate1: &BARate, ba_rate2: &BARate) -> bool {
    match (ba_rate1, ba_rate2) {
        (BARate::Core(r1), BARate::Core(r2)) => {
            rate_sub(r1, r2)
        },
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
        }
    }
}

// BARate::Core(Rate::Raw{events: 0, window: 1})
fn lower_to_ba(sr: &StreamRate, rel: &SubRel) -> BARate {
    match sr {
        StreamRate::Base(r) => r.clone(),
        StreamRate::Sum(box_sr1, box_sr2) => {
            match rel {
                SubRel::LHS => {
                    BARate::Or(Box::new(lower_to_ba(box_sr1, rel)),
                               Box::new(lower_to_ba(box_sr2, rel)))
                },
                SubRel::RHS => {
                    BARate::And(Box::new(lower_to_ba(box_sr1, rel)),
                                Box::new(lower_to_ba(box_sr2, rel)))
                }
            }
        },
        StreamRate::Par(box_sr1, box_sr2) => {
            // TODO: This looks terrible...?
            match (**box_sr1, **box_sr2) {
                (StreamRate::Base(bar1), StreamRate::Base(bar2)) => {
                    // TODO: Do algebraic rewriting here to simplify
                },
                (StreamRate::Base(bar), sr2) => {
                    lower_to_ba(sr2, rel)
                },
                (sr1, sr2)
            }
            BARate::Core(Rate::Raw{events: 0, window: 1})
        },
        StreamRate::Concat(box_r1, box_r2) => BARate::Core(Rate::Raw{events: 0, window: 1}),
        StreamRate::Star(box_r) => BARate::Core(Rate::Raw{events: 0, window: 1}),

        // TODO: Might be a bad clone...
        // StreamRate::Base(r) => r.clone(),
        // StreamRate::Sum(r1, r2) => {
        //     match (lower_lb(r1), lower_lb(r2)) {
        //         (Rate::Raw { events: e1, window: w1 }, Rate::Raw { events: e2, window: w2 }) =>
        //             Rate::Or(vec![Box::new(Rate::Raw { events: e1, window: w1 }),
        //                           Box::new(Rate::Raw { events: e2, window: w2 })]),
        //         (Rate::Or(v1), Rate::Or(v2)) => {
        //             // TODO: Here's a bad clone...
        //             let mut newv1 = v1.clone();
        //             let mut newv2 = v2.clone();
        //             newv1.append(&mut newv2);
        //             Rate::Or(newv1)
        //         }
        //         (Rate::Or(v), r)  | (r, Rate::Or(v))=> {
        //             // TODO: Here's a bad clone...
        //             let mut newv = v.clone();
        //             newv.push(Box::new(r));
        //             Rate::Or(newv)
        //         },
        //         (r1, r2) => {
        //             Rate::Or(vec![Box::new(r1), Box::new(r1)])
        //         },
        //     }
        // }
        // StreamRate::Par(r1, r2) => {
        //     match (lower_lb(r1), lower_lb(r2)) {
        //         (Rate::Or(v), r) =>

        //     }
        // }

    }
}

fn stream_sub(sr1: &StreamRate, sr2: &StreamRate) -> bool {
    let lowered_sr_lhs = lower_to_ba(sr1, &SubRel::LHS);
    let lowered_sr_rhs = lower_to_ba(sr2, &SubRel::RHS);
    ba_rate_sub(&lowered_sr_lhs, &lowered_sr_rhs)
}

fn main() {
    println!("Hello, world!");
}
