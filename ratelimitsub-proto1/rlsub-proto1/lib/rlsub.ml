type rate =
  | NoLimit (* i.e. ∞ *)
  | Rate of {events: int; window: int}
type rl =
  | Uniform of rate
  | Segment of rate (* TODO: We only handle Uniform for now. *)

type typ =
  | TypInt of rl (* NOTE: Placeholder base type. Adding more adds complexity. *)
  | TypConcat of typ * typ * rl
  | TypSum of typ * typ * rl
  | TypPar of typ * typ * rl
  | TypStar of typ * rl

(* =========================   SUBTYPING   ================================== *)
(* Two pass approach: push outer refinements inwards, then inner refinements
   outwards when you come back up from the recursive calls. *)

(* TODO: How do we define a normalized type? *)
let rec normalize_super (s: typ) =
  match s with
  | TypInt(r) -> TypInt(r)
  | TypConcat(s1, s2, r) ->
     (if r = Uniform(NoLimit) then
        TypConcat(normalize_super(s1), normalize_super(s2), r)
      else
        )



let uniform_rate_sub (r1: rate) (r2: rate) =
  match (r1, r2) with
  | (_, NoLimit) -> true
  | (NoLimit, _) -> false
  | (Rate(r1), Rate(r2)) ->
     (let (n1, t1) = (r1.events, r1.window) in
      let (n2, t2) = (r2.events, r2.window) in
      if t2 <= t1 then
        if n1 <= n2 then true else false
      else
        (let bound = (n2 / ((t2 / t1) + 1)) in
         if n1 <= bound then true else false))
