#[derive(Clone, Debug, PartialEq)]
enum Rate {
    // NOTE: We may be able to allow real-valued windows here without any issue,
    // but first get something working with integer-valued windows.
    Raw { events: usize, window: usize},
    // TODO: Perhaps it's better to keep things consistent and use a binary
    // relation for both of these instead of a vector, i.e. Or(Box<Rate>, Box<Rate>).
    Or(Vec<Box<Rate>>),
    And(Vec<Box<Rate>>),
    // TODO: We probably will need to introduce a ParSum base rate type, since
    // we might not want to reduce such rate types to And/Or and may instead
    // want to have some custom decision procedure. But do rough heuristics
    // first.
}

#[derive(Clone, Debug)]
enum StreamRate {
    Base(Rate),
    Sum(Box<StreamRate>, Box<StreamRate>),
    Par(Box<StreamRate>, Box<StreamRate>),
    Concat(Box<StreamRate>, Box<StreamRate>),
    Star(Box<StreamRate>),
}

fn rate_sub(rate1: &Rate, rate2: &Rate) -> bool {
    match (rate1, rate2) {
        (Rate::Raw { events: e1, window: w1 }, Rate::Raw { events: e2, window: w2 }) =>
            if w2 <= w1 {
                e1 <= e2
            } else {
                let bound = e2 / w2.div_ceil(*w1);
                *e1 <= bound
            }
        (r, Rate::Or(v)) => {
            for i in v.iter() {
                if rate_sub(r, i) {
                    return true
                }
            };
            return false
        }
        (Rate::Or(v), r) => {
            for i in v.iter() {
                if rate_sub(i, r) {
                    return true
                }
            };
            return false
        }
        (r, Rate::And(v)) => {
            for i in v.iter() {
                if !rate_sub(r, i) {
                    return false
                }
            };
            return true
        }
        (Rate::And(v), r) => {
            for i in v.iter() {
                if rate_sub(i, r) {
                    return true
                }
            };
            return false
        }
    }
}


// =============================================================================
// TODO: Temporary rough heuristics for parallel sum of rates.
fn par_raw_ub(r1: &Rate, r2: &Rate) -> Rate {
    match (r1, r2) {
        (Rate::Raw { events: e1, window: w1 }, Rate::Raw { events: e2, window: w2 }) =>
            if w1 <= w2 {
                Rate::Raw { events: e1 + e2, window: *w1 }
            } else {
                Rate::Raw { events: e1 + e2, window: *w2 }
            }
        (_, _) => panic!("Precondition r1, r2 are Rate::Raw not satisfied")
    }
}

fn par_raw_lb(r1: &Rate, r2: &Rate) -> Rate {
     match (r1, r2) {
        (Rate::Raw { events: _, window: _ }, Rate::Raw { events: _, window: _ }) =>
             // TODO: Bad clone...
             Rate::Or(vec![Box::new(r1.clone()), Box::new(r2.clone())]),
        (_, _) => panic!("Precondition r1, r2 are Rate::Raw not satisfied")
    }
}
// =============================================================================

fn lower_lb(sr: &StreamRate) -> Rate {
    match sr {
        // TODO: This might be a bad clone...
        StreamRate::Base(r) => r.clone(),
        StreamRate::Sum(r1, r2) => {
            match (lower_lb(r1), lower_lb(r2)) {
                (Rate::Raw { events: e1, window: w1 }, Rate::Raw { events: e2, window: w2 }) =>
                    Rate::Or(vec![Box::new(Rate::Raw { events: e1, window: w1 }),
                                  Box::new(Rate::Raw { events: e2, window: w2 })]),
                (Rate::Or(v1), Rate::Or(v2)) => {
                    // TODO: Here's a bad clone...
                    let mut newv1 = v1.clone();
                    let mut newv2 = v2.clone();
                    newv1.append(&mut newv2);
                    Rate::Or(newv1)
                }
                (Rate::Or(v), r)  | (r, Rate::Or(v))=> {
                    // TODO: Here's a bad clone...
                    let mut newv = v.clone();
                    newv.push(Box::new(r));
                    Rate::Or(newv)
                },
                (r1, r2) => {
                    Rate::Or(vec![Box::new(r1), Box::new(r1)])
                },
            }
        }
        StreamRate::Par(r1, r2) => {
            match (lower_lb(r1), lower_lb(r2)) {
                (Rate::Or(v), r) =>

            }
        }

    }
}

fn stream_sub(sr1: &StreamRate, sr2: &StreamRate) -> bool {
    false
}

fn main() {
    println!("Hello, world!");
}
