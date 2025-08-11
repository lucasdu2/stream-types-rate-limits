type rate = {events: int; window: int}
(* NOTE: Yeah, we only handle Uniform rates for now :D *)
(* NOTE: We represent the possibility of multiple refinements as a list. An
   empty list means there are no rate limits. *)
type rr = rate list

type typ =
  | TypInt of rr (* NOTE: Placeholder base type. Adding more adds complexity. *)
  | TypSum of typ * typ * rr
  | TypPar of typ * typ * rr
  | TypConcat of typ * typ * rr
  | TypStar of typ * rr

(* =========================   SUBTYPING   ================================== *)
(* NOTE: For now (out of naivete), we simply define a normalized type as one in
 which the only refinements are directly attached to the base type Int. *)

(* NOTE: Determine if r1 is a subtype of r2, in a unified way (i.e. both event
   counts and window size can be different). *)
let uniform_rate_sub (r1: rate) (r2: rate) : bool =
  let (n1, t1) = (r1.events, r1.window) in
  let (n2, t2) = (r2.events, r2.window) in
  if t2 <= t1 then
    if n1 <= n2 then true else false
  else
    (let bound = (n2 / ((t2 / t1) + 1)) in
     if n1 <= bound then true else false)

let uniform_rr_sub (rr1: rr) (rr2: rr) : bool =
  (* NOTE: This is basically just implication checking using our individual
     rate subtyping decision procedure above, where we use the interpretation:
     subtype implies supertype. *)
  let rec rr_impl_rate (rest: rr)(r: rate) : bool =
    (match rest with
     | [] -> false
     | hd :: tl ->
        (if (uniform_rate_sub hd r) then true else rr_impl_rate tl r)) in
  let rec uniform_rr_sub_aux (remain_rr2: rr) : bool =
    (match remain_rr2 with
     | [] -> true
     | hd :: tl ->
        (if (rr_impl_rate rr1 hd) then uniform_rr_sub_aux tl else false)) in
  uniform_rr_sub_aux rr2

(* NOTE: We sometimes need to "add" rates in order to push them outwards (i.e.
   our "factoring" subtyping rules). We provide two ways to do this on
   arbitrary rates (even rates where window sizes don't match), one of which
   gives us a subtype of the "real" result of the addition, the other of which
   gives us a supertype. There is no formal proof that this is the greatest
   subtype (glb) or the least supertype (lub), but I suspect it shouldn't be
   hard to prove this, given our particular subtyping rules/semantics, of course.*)
let uniform_rate_add_sup (rr1: rr) (_rr2: rr) : rr = rr1 (*TODO*)

let uniform_rate_add_sub (rr1: rr) (_rr2: rr) : rr = rr1 (*TODO*)
(* TODO: Is there a way to do this over entire rate refinements? When we have
   two conjunctive clauses, the addition here seems non-deterministic, i.e.
   which rates do we choose to add together? *)

(* TODO: Should we have functions here to produce the meet (lub) and join (glb)
   of two rate refinements, for use in subtyping? *)
let uniform_rr_meet (rr1: rr) (_rr2: rr) : rr = rr1
let uniform_rr_join (rr1: rr) (_rr2: rr) : rr = rr1

(* NOTE: We need to merge rate refinements somehow when doing normalization. *)
let merge_rr (s: typ) (outer_r: rr) =
  let rec can_erase (remain_r1: rr) (one_r2: rate) : bool =
    (match remain_r1 with
     | [] -> false
     | hd :: tl ->
        if (uniform_rate_sub hd one_r2) then true else (can_erase tl one_r2)) in
  let merge_rr_aux (full_r1: rr) (full_r2: rr) : rr =
    (let to_add = List.filter (can_erase full_r1) full_r2 in
     List.append full_r1 to_add) in
  match s with
  | TypInt(inner_r) -> TypInt(merge_rr_aux inner_r outer_r)
  | TypSum(s1, s2, inner_r) -> TypSum(s1, s2, merge_rr_aux inner_r outer_r)
  | TypPar(s1, s2, inner_r) -> TypPar(s1, s2, merge_rr_aux inner_r outer_r)
  | TypConcat(s1, s2, inner_r) -> TypConcat(s1, s2, merge_rr_aux inner_r outer_r)
  | TypStar(s, inner_r) -> TypStar(s, merge_rr_aux inner_r outer_r)

(* NOTE: normalize_sub will find the normalized glb/maximum subtype.NOTE: If we
   don't include concat and sup as reducible terms, then I guess
   normalize_sub and normalize_sup are equivalent. *)

(* NOTE: normalize_sup will find the normalized lub/minimum supertype. *)
let rec normalize_sup (s: typ) =
  match s with
  | TypInt(r) -> TypInt(r)
  | TypSum(s1, s2, r) ->
     (if r = [] then TypSum(normalize_sup(s1), normalize_sup(s2), r)
      else reduce_sum_sup s1 s2 r)
  | TypPar(s1, s2, r) ->
     (if r = [] then TypPar(normalize_sup(s1), normalize_sup(s2), r)
      else reduce_par_sup s1 s2 r)
  | TypConcat(s1, s2, r) ->
     (if r = [] then TypConcat(normalize_sup(s1), normalize_sup(s2), r)
      else reduce_concat_sup s1 s2 r)
  | TypStar(s, r) ->
     (if r = [] then TypStar(normalize_sup(s), r)
      else reduce_star_sup s r)
and reduce_par_sup (s1: typ) (s2: typ) (outer_r: rr) =
  let red_s1 = merge_rr s1 outer_r in
  let red_s2 = merge_rr s2 outer_r in
  TypPar(normalize_sup red_s1, normalize_sup red_s2, [])
and reduce_sum_sup (s1: typ) (s2: typ) (outer_r: rr) =
  let red_s1 = merge_rr s1 outer_r in
  let red_s2 = merge_rr s2 outer_r in
  TypSum(normalize_sup red_s1, normalize_sup red_s2, [])
and reduce_concat_sup (s1: typ) (s2: typ) (outer_r: rr) =
  (* NOTE: It's still unclear to me right now how to handle this, since the
     same approach as above, i.e. just merging the rates, is not actually valid.
     We just leave it as irreducible for now. This might actually be fine. *)
  TypConcat(normalize_sup s1, normalize_sup s2, outer_r)
and reduce_star_sup (s: typ) (outer_r: rr) =
  (* NOTE: We do the same thing as concat for now, for the same reasons. *)
  TypStar(normalize_sup s, outer_r)

let rec check_subtype (s1: typ) (s2: typ) : bool =
  (* NOTE: We assume that both s1 and s2 are normalized here. If not, we will
     have to throw an error. *)
  (* NOTE: I guess we'll just individually handle each possible combination for
     now lmfao. There might be a more clever way to do this. *)
  match (s1, s2) with
  | TypInt(rr1), TypInt(rr2) -> uniform_rr_sub rr1 rr2
  | TypSum(s1, s2, []), TypSum(s3, s4, []) ->
     ((check_subtype s1 s3) && (check_subtype s2 s4))
  (* NOTE: In this case, this seems to be a pretty bad rule, since it's possible
     that the two types on the LHS, when "summed," could still be a subtype of
     the "summed" RHS. Should think about when and when not this sort of
     "summing" thing could make sense. See the uniform_rr_add rule above. *)
  | TypPar(s1, s2, []), TypPar(s3, s4, []) ->
     ((check_subtype s1 s3) && (check_subtype s2 s4))
  | TypConcat(s1, s2, rr1), TypConcat(s3, s4, rr2) ->
     ((uniform_rr_sub rr1 rr2) && (check_subtype s1 s3) && (check_subtype s2 s4))
  | TypStar(s1, rr1), TypStar(s2, rr2) ->
     ((uniform_rr_sub rr1 rr2) && (check_subtype s1 s2))
  | s0, TypSum(s1, s2, []) ->
     ((check_subtype s0 s1) && (check_subtype s0 s2))
  | s0, TypPar(s1, s2, []) ->
     ((check_subtype s0 s1) || (check_subtype s0 s2))
  | TypStar(s1, rr1), TypConcat(s2, s3, rr2) -> false (* TODO *)
  | s0, TypConcat(s1, s2, rr1) -> false (* TODO *)
  | TypConcat(s1, s2, rr1), TypStar(s3, rr2) -> false
  | s0, TypStar(s1, rr1) -> false
  | TypSum(s1, s2, []), s3 -> false
  | TypPar(s1, s2, []), s3 -> false
  | TypConcat(s1, s2, rr1), TypStar(s3, rr2) -> false
  | TypConcat(s1, s2, rr1), s3 -> false
  | TypStar(s1, rr1), TypConcat(s2, s3, rr2) -> false
  | TypStar(s1, rr1), s3 -> false


     (* TODO: It seems like the push inwards, then outwards strategy may be the
        right one. Specifically, we first "normalize" by pushing inward as much
        as we can. Then, if our subtyping gets stuck at any point due to mismatched
        constructors, for example, we then try to push the refinements outwards
        again to get to some other types that *are comparable*. *)
