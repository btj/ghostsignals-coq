(* Finite multisets *)
Parameter bag: forall (T: Type), Type.

Parameter level: Type.
Parameter degree: Type.

Inductive phasecomp := Forker | Forkee.
Definition thread_phase := list phasecomp.

Definition cmd_size := nat.
Definition signal := nat.
Definition thread := nat.

Record thread_state := ThreadState {
  size: cmd_size;
  phase: thread_phase;
  obs: bag signal
}.

Record state := State {
  threads: list thread_state;
  callPerms: bag (thread_phase * degree);
  waitPerms: bag (thread_phase * signal * degree);
  signals: list (level * bool)
}.

Inductive step_label :=
| Burn(consumes: bag degree)(produces: bag degree)
| Fork(forkee_obs: bag signal)
| CreateSignal(t: thread)(lev: level)
| SetSignal(t: thread)(s: signal)
| CreateWaitPerm(t: thread)(s: signal)(ph: thread_phase)(dcons: degree)(dprod: degree)
| Wait(t: thread)(ph: thread_phase)(s: signal)(d: degree)
.

Inductive step: state -> thread -> step_label -> state -> Prop :=
| SBurn Ts1 size ph obs Ts2 CPs WPs Ss t C P size':
  length Ts1 = t ->
  (forall ph' d, Bmem (ph', d) C -> is_ancestor_of ph' ph) ->
  (forall ph' d, Bmem (ph', d) P -> exists ph'' d', Bmem (ph'', d') C /\ degree_lt d' d /\ is_ancestor_of ph'' ph') ->
  Bis_subbag_of C CPs ->
  (* size' can be anything! *)
  step
    (State (Ts1 ++ [ThreadState size ph obs] ++ Ts2) CPs WPs Ss)
    t (Burn C P)
    (State (Ts1 ++ [ThreadState size' ph obs] ++ Ts2) (Bplus (Bminus CPs C) P) WPs Ss)
| SFork Ts1 size ph obs Ts2 CPs WPs Ss t size':
  step
    (State (Ts1 ++ [ThreadState size ph 