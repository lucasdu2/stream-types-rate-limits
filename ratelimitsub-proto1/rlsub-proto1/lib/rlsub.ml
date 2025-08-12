type rate = {events: int; window: int}
(* TODO: We might want to add a Bot and Top type to this for the future. It
   would help a bit with the fold_left stuff, for example, later on (to have a
   Bot type in that case). *)
(* NOTE: Yeah, we only handle Uniform rates for now :D *)
(* NOTE: We represent the possibility of multiple refinements as a list. An
   empty list means there are no rate limits. *)
type rr = rate list
(* NOTE: Not sure when I'll use this, but could be handy to have, since OCaml
   doesn't have a nat type. *)
let validate_rate (r: rate) = assert (r.events >= 0 && r.window >= 0)

type typ =
  | TypInt of rr (* NOTE: Placeholder base type. Adding more adds complexity. *)
  | TypSum of typ * typ * rr
  | TypPar of typ * typ * rr
  | TypConcat of typ * typ * rr
  | TypStar of typ * rr

(* =========================   SUBTYPING   ================================== *)

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
let uniform_rate_add_sup (r1: rate) (r2: rate) : rate =
  let {events = n1; window = t1} = r1 in
  let {events = n2; window = t2} = r2 in
  (* NOTE: Basically, we just need to convert one of the rates have a window
     size matching that of the other rate. Then we can just add up events. *)
  if t1 = t2 then {events = (n1 + n2); window = t1}
  else if t1 < t2 then
    (* NOTE: There might be some proof that one of these is always better (more
       minimal) than the other. I think option2 might always be better,
       actually, but without a formal proof, let's just keep both for now. *)
    (let option1 =
       {events = (n1 + n2); window = t1} in
     let option2 =
       (let ratio_ceil = (t2 / t1 + 1) in
        {events = (n1 * ratio_ceil + n2); window = t2}) in
     if uniform_rate_sub option1 option2 then option1 else option2)
  else (* t1 > t2 *)
    (let option1 =
       {events = (n1 + n2); window = t2} in
     let option2 =
       (let ratio_ceil = (t1 / t2 + 1) in
        {events = (n2 * ratio_ceil + n1); window = t1}) in
     if uniform_rate_sub option1 option2 then option1 else option2)

let uniform_rate_add_sub (r1: rate) (r2: rate) : rate =
  let {events = n1; window = t1} = r1 in
  let {events = n2; window = t2} = r2 in
  if t1 = t2 then {events = (n1 + n2); window = t1}
  else if t1 < t2 then
    (let option1 =
       {events = (n1 + n2); window = t2} in
     let option2 =
       (let ratio_ceil = (t2 / t1 + 1) in
        {events = (n2 / ratio_ceil); window = t1}) in
     if uniform_rate_sub option1 option2 then option1 else option2)
  else (* t1 > t2 *)
    (let option1 =
       {events = (n1 + n2); window = t1} in
     let option2 =
       (let ratio_ceil = (t1 / t2 + 1) in
        {events = (n1 / ratio_ceil); window = t2}) in
     if uniform_rate_sub option1 option2 then option1 else option2)

(* TODO: Is there a way to do this over entire rate refinements? When we have
   two conjunctive clauses, the addition here seems non-deterministic, i.e.
   which rates do we choose to add together? Yes, just take the meet or join of
   each refinement and then use the corresponding add function (either add_sup
   or add_sub) on those. This does mean that our final result will just be a
   singleton rate refinement...perhaps there is a way retain as many rates as
   possible in the refinement, in hopes that this gives us a better/more precise
   result? I guess that would be TODO. *)
let uniform_rate_lub (r1: rate) (r2: rate) : rate =
  if uniform_rate_sub r1 r2 then r2
  else if uniform_rate_sub r2 r1 then r1
  else
    (* TODO: It seems like there is some way to generalize the stuff we're
       doing in here to compute rates with common window sizes. Perhaps you can
       factor it out into separate function? *)
    (let {events = n1; window = t1} = r1 in
     let {events = n2; window = t2} = r2 in
     if t1 <= t2 then
       (let ratio_ceil = (t2 / t1 + 1) in
        let convert_n1 = n1 * ratio_ceil in
        if convert_n1 > n2 then {events = convert_n1; window = t2}
        else {events = n2; window = t2})
     else (* t1 >= t2 *)
       (let ratio_ceil = (t1 / t2 + 1) in
        let convert_n2 = n2 * ratio_ceil in
        if convert_n2 > n1 then {events = convert_n2; window = t1}
        else {events = n1; window = t1}))
let uniform_rate_glb (r1: rate) (r2: rate) : rate =
  if uniform_rate_sub r1 r2 then r1
  else if uniform_rate_sub r2 r1 then r2
  else
     (let {events = n1; window = t1} = r1 in
     let {events = n2; window = t2} = r2 in
     if t1 <= t2 then
       (let ratio_ceil = (t2 / t1 + 1) in
        let convert_n2 = n2 / ratio_ceil in
        if convert_n2 < n1 then {events = convert_n2; window = t1}
        else {events = n1; window = t1})
     else (* t1 >= t2 *)
       (let ratio_ceil = (t1 / t2 + 1) in
        let convert_n1 = n1 / ratio_ceil in
        if convert_n1 < n1 then {events = convert_n1; window = t2}
        else {events = n2; window = t2}))

let singleton_uniform_rr_lub (rrefine: rr) : rr =
  assert (List.length rrefine >= 1);
  List.fold_left uniform_rate_lub rrefine[0] rrefine

let uniform_rr_add_sup (rr1: rr) (rr2: rr) : rr =
let uniform_rr_add_sub (rr1: rr) (rr2: rr) :

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


(* NOTE: For now (out of naivete), we simply define a normalized type as one in
 which the only refinements are directly attached to the base type Int. *)

(* NOTE: normalize_sub will find the normalized glb/maximum subtype. NOTE: If we
   don't include concat and sup as reducible terms, then I guess
   normalize_sub and normalize_sup are equivalent, since the normalization we
   do here for sum and par are the same "in both directions," i.e. for subtyping
   and supertyping, as the merging defined here is really an equivalence
   relation on these type constructors. *)

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

(* TODO: These both depend on our "summing" and "max"/"min" functions defined
   above. "max" and "min" are the lub/join and glb/meet things. I'm still
   confused about the definitions of join and meet...but this is the Wikipedia
   version. *)
let rec pushout_sup (s: typ) = s
let rec pushout_sub (s: typ) = s

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
  (* TODO: Also: TypInt subtypes all other constructors, which could also help
     with subtyping. *)
  | _, _ -> raise (Invalid_argument "input types are (probably) not normalized")


     (* TODO: It seems like the push inwards, then outwards strategy may be the
        right one. Specifically, we first "normalize" by pushing inward as much
        as we can. Then, if our subtyping gets stuck at any point due to mismatched
        constructors, for example, we then try to push the refinements outwards
        again to get to some other types that *are comparable*. *)
