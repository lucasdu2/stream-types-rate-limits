#[derive(Copy, Clone, Debug)]
struct Rate {
    events: usize,
    window: usize,
}

type RateRefine = Vec<Rate>;

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
        return rate1.events <= rate2.events;
    } else {
        let bound = rate2.events / (rate2.window).div_ceil(rate1.window);
        return rate1.events <= bound;
    }
}

fn uniform_refine_sub(refine1: &RateRefine, refine2: &RateRefine) -> bool {
    let check_rate_sub = |rate1: &Rate| -> bool {
        for rate2 in refine2 {if uniform_rate_sub(rate1, rate2) {return true}};
        return false;
    };
    for rate1 in refine1 {if !check_rate_sub(rate1) {return false}};
    return true;
}

fn merge_refine(mut inner_refine: &RateRefine, outer_refine: &RateRefine) -> RateRefine {
    // TODO: Why do I need two borrows here?
    let can_erase = |out_r: &&Rate| -> bool {
        for in_r in inner_refine {if uniform_rate_sub(in_r, out_r) {return true}};
        return false;
    };
    // TODO: Figure out functional weirdness here --- might just want to do
    // this imperatively for now...
    let mut to_add: RateRefine = outer_refine.into_iter().filter(can_erase).collect();
    inner_refine.append(&to_add)
}

fn check_subtype (s1: &StreamTy, s2: &StreamTy) -> bool {
    match (s1, s2) {
        (StreamTy::Int(refine1), StreamTy::Int(refine2)) => {
            uniform_rr_sub(&refine1, &refine2)
        },
        (StreamTy::Sum(s1, s2, refine1), StreamTy::Sum(t1, t2, refine2)) => {
            // TODO: Either need to figure out how to nicely pattern match on
            // empty vectors or re-do the implementation a bit to run the push
            // in (or "normalize") operation as part of check_subtype.
            uniform_rr_sub(&refine1, &refine2) && check_subtype(s1, t1) && check_subtype(s2, t2)
        },
        _ => false,
    };
   return false;
}

fn main() {
    println!("Hello, world!");
}
