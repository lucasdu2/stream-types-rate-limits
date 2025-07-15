type rate = {events: int; window: int}
type rr =
  | Top (* i.e. ∞ *)
  | Rate of rate

type typ =
  | TypInt of rr (* NOTE: Placeholder base type. *)
  | TypConcat of rr * rltyp * rltyp
  | TypSum of rr * rltyp * rltyp
  | TypPar of rr * rltyp * rltyp
  | TypStar of rr * rltyp
and rltyp =
  | Uniform of typ
  | Segment of typ
let typ_rr (t: typ) =
  match t with
  | TypInt(rr) -> rr
  | TypConcat(rr, _, _) -> rr
  | TypSum(rr, _, _) -> rr
  | TypPar(rr, _, _) -> rr
  | TypStar(rr, _) -> rr


(* =========================   SUBTYPING   ================================== *)
let rec subtype rltypS rltypT =
  match (rltypS, rltypT) with
  (* TODO: Add proper bodies to each case statement here. *)
  | (Uniform(_t1), Uniform(_t2)) -> false
  | (Segment(_t1), Segment(_t2)) -> false
  | (Uniform(_t1), Segment(_t2)) -> false
  | (Segment(_t1), Uniform(_t2)) -> false
and uniform_rr_sub rr1 rr2 =
  match (rr1, rr2) with
  | (_, Top) -> true
  | (Rate(rate1), Rate(rate2)) ->
     if rate2.window <= rate2.window then
       if rate1.events <= rate2.events then true else false
     else (* rate2.window > rate1.window *)
       (* NOTE: Model everything with integers --- indeed, natural numbers ---
          here. This is expressive enough, since each increment can correspond to
          a tick in whatever discrete time-keeping system we are talking about.
          This is probably also how we'll formalize the semantics of our
          subtyping rules. *)
       (let bound = (rate2.events / ((rate2.window / rate1.window) + 1)) in
        if (rate1.events <= bound) then true else false)
  | (Top, _) -> false
and uniform_sub typS typT =
  (=) typS typT ||
    match (typS, typT) with
    (* Basic subtyping rules on rate refinements only *)
    | (TypInt(rr1), TypInt(rr2)) -> (uniform_rr_sub rr1 rr2)
    | (TypConcat(rr1, typS1, typT1), TypConcat(rr2, typS2, typT2)) ->
       (uniform_rr_sub rr1 rr2) && (subtype typS1 typS2) && (subtype typT1 typT2)
    | (TypSum(rr1, typS1, typT1), TypSum(rr2, typS2, typT2)) ->
       (uniform_rr_sub rr1 rr2) && (subtype typS1 typS2) && (subtype typT1 typT2)
    | (TypPar(rr1, typS1, typT1), TypPar(rr2, typS2, typT2)) ->
       (uniform_rr_sub rr1 rr2) && (subtype typS1 typS2) && (subtype typT1 typT2)
    | (TypStar(rr1, typS1), TypStar(rr2, typS2)) ->
       (uniform_rr_sub rr1 rr2) && (subtype typS1 typS2)
    (* Subtyping rules for "expand" and "factor" *)
    (* NOTE/TODO: Seems like we need to figure out how to handle nested rate
       refinements fairly urgently. *)
    | (TypConcat(l_rr, typS1, typT1), TypConcat(Top, typS2rr, typT2rr)) ->
       let r_rr1 = typ_rr typS2rr in
       let r_rr2 = typ_rr typT2rr in
       (uniform_rr_sub l_rr r_rr1) && (uniform_rr_sub l_rr r_rr2) && (subtype)
    | (_, _) -> false

(* and segment_sub typS typT *)

(* and convert_sub *)
