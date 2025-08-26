struct Rate {
    events: usize,
    window: usize,
}
type RateRefine = Vec<Rate>;
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

fn uniform_rr_sub(refine1: &RateRefine, refine2: &RateRefine) -> bool {
    let check_rate_sub = |rate1: &Rate| -> bool {
        for rate2 in refine2 {if uniform_rate_sub(rate1, rate2) {return true}};
        return false;
    };
    for rate1 in refine1 {if !check_rate_sub(rate1) {return false}};
    return true;
}

fn check_subtype (s1: &StreamTy, s2: &StreamTy) -> bool {
    // TODO: Fix this borrow checker problem.
    match (s1, s2) {
        (&StreamTy::Int(refine1), &StreamTy::Int(refine2)) => uniform_rr_sub(&refine1, &refine2),
        _ => false,
    };
   return false;
}

fn main() {
    println!("Hello, world!");
}
