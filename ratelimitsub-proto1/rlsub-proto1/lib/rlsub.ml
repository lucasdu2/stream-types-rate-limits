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
let typ_rl (t: typ) =
  match t with
  | TypInt(r) -> r
  | TypConcat(_, _, r) -> r
  | TypSum(_, _, r) -> r
  | TypPar(_, _, r) -> r
  | TypStar(_, r) -> r

(* =========================   SUBTYPING   ================================== *)
(* Two pass approach: push outer refinements inwards, then inner refinements
   outwards when you come back up from the recursive calls. *)
let rec subtype typS typT =
  match (typS, typT) with
  | (TypInt(rl1), TypInt(rl2)) ->
     (match (rl1, rl2) with
      | (Uniform(r1), Uniform(r2)) -> uniform_rate_sub r1 r2
      | (_, _) -> false)
  | (TypConcat(s1, t1, rl1), TypConcat(s2, t2, rl2)) ->
     (match (rl1, rl2) with
      |
     )
  | (_, _) -> false
and normalize typS typT =
  |
and uniform_rate_sub (r1: rate) (r2: rate) =
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
and uniform_concat_expand s1 t1 rl1 s2 t2 =


(*   (\* TODO: Add proper bodies to each case statement here. *\) *)
(*   | (Uniform(_t1), Uniform(_t2)) -> false *)
(*   | (Segment(_t1), Segment(_t2)) -> false *)
(*   | (Uniform(_t1), Segment(_t2)) -> false *)
(*   | (Segment(_t1), Uniform(_t2)) -> false *)
(* and uniform_rr_sub rr1 rr2 = *)
(*   match (rr1, rr2) with *)
(*   | (_, Top) -> true *)
(*   | (Rate(rate1), Rate(rate2)) -> *)
(*      if rate2.window <= rate1.window then *)
(*        if rate1.events <= rate2.events then true else false *)
(*      else (\* rate2.window > rate1.window *\) *)
(*        (\* NOTE: Model everything with integers --- indeed, natural numbers --- *)
(*           here. This is expressive enough, since each increment can correspond to *)
(*           a tick in whatever discrete time-keeping system we are talking about. *)
(*           This is probably also how we'll formalize the semantics of our *)
(*           subtyping rules. *\) *)
(*        (let bound = (rate2.events / ((rate2.window / rate1.window) + 1)) in *)
(*         if (rate1.events <= bound) then true else false) *)
(*   | (Top, _) -> false *)
(* and uniform_sub typS typT = *)
(*   (=) typS typT || *)
(*     match (typS, typT) with *)
(*     (\* Basic subtyping rules on rate refinements only *\) *)
(*     | ({base = b1; refine = rr1}, {base = b2; refine = rr2}) -> *)
(*        (uniform_rr_sub rr1 rr2) && (subtype b1 b2) *)
(*     | (TypConcat(rr1, typS1, typT1), TypConcat(rr2, typS2, typT2)) -> *)
(*        (uniform_rr_sub rr1 rr2) && (subtype typS1 typS2) && (subtype typT1 typT2) *)
(*     | (TypSum(rr1, typS1, typT1), TypSum(rr2, typS2, typT2)) -> *)
(*        (uniform_rr_sub rr1 rr2) && (subtype typS1 typS2) && (subtype typT1 typT2) *)
(*     | (TypPar(rr1, typS1, typT1), TypPar(rr2, typS2, typT2)) -> *)
(*        (uniform_rr_sub rr1 rr2) && (subtype typS1 typS2) && (subtype typT1 typT2) *)
(*     | (TypStar(rr1, typS1), TypStar(rr2, typS2)) -> *)
(*        (uniform_rr_sub rr1 rr2) && (subtype typS1 typS2) *)
(*     (\* Subtyping rules for "expand" and "factor" *\) *)
(*     (\* NOTE/TODO: Seems like we need to figure out how to handle nested rate *)
(*        refinements fairly urgently. *\) *)
(*     | (TypConcat(l_rr, typS1, typT1), TypConcat(Top, typS2rr, typT2rr)) -> *)
(*        let r_rr1 = rltyp_rr typS2rr in *)
(*        let r_rr2 = rltyp_rr typT2rr in *)
(*        (uniform_rr_sub l_rr r_rr1) && (uniform_rr_sub l_rr r_rr2) && *)
(*          (subtype typS1 ) *)
(*     | (_, _) -> false *)

(* and segment_sub typS typT *)

(* and convert_sub *)
