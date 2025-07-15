(* Define a datatype for StreamRate -- or something to that effect -- that is
   essentially a monotonic sequence of reals -- can do naturals too, but there
   might be some additional semantic translation involved... -- where an event is
   represented just by its location in time, i.e. a real number. *)
(* TODO: Need to encode monotonicity using some sort of dependent typing. *)

Inductive StreamRate: Type :=
| Nil
| Cons (event : nat) (rest: StreamRate).

Definition events_in_window(sr: stream_rate, w_start: nat, w_end: nat): nat := ()

Definition stream_rate_of(sr: stream_rate, n: nat, t: nat) : Prop := ()

Theorem s_relative_rate: forall (r: StreamRate) forall (n1 n2: nat) forall (t: nat), (n1 < n2) -> (stream_rate_of(r, n1, t) -> stream_rate_of(r, n2, t))

(* Define a function that gets the number of events in some window (defined by
   a start and end time, again represented by a real). *)

(* Define a relation called StreamRateOf -- or something to that effect -- that
   tells us if a StreamRate type has <= n events in windows of size t. This will
   need to be different for Uniform and Segmented rate types. *)
