Require Import List.
Import ListNotations.

(* Finite multisets *)
Parameter bag: forall (T: Type), Type.
Parameter Bempty: forall {T}, bag T.
Parameter Bmem: forall {T}, T -> bag T -> Prop.
Parameter Bplus: forall {T}, bag T -> bag T -> bag T.
Parameter Binsert: forall {T}, T -> bag T -> bag T.
Parameter Bremove1: forall {T}, T -> bag T -> bag T.

Parameter level: Type.
Parameter level_lt: level -> level -> Prop.
Parameter degree: Type.
Parameter degree_lt: degree -> degree -> Prop.
Parameter cmd_size: Type.
Parameter size_zero: cmd_size.
Parameter size_lt: cmd_size -> cmd_size -> Prop.

Inductive phasecomp := Forker | Forkee.
Definition thread_phase := list phasecomp. (* To be read backwards: [Forker; Forkee] denotes a thread that was forked by the main thread and then forked a child thread. *)
Fixpoint is_ancestor_of (ph1 ph2: thread_phase) :=
  ph1 = ph2 \/
  match ph2 with
    [] => False
  | phc::ph => is_ancestor_of ph1 ph
  end.

Definition signal := nat.
Definition thread := nat.

Record thread_state := ThreadState {
  size: cmd_size;
  phase: thread_phase;
  obs: bag signal
}.

Record state := State {
  callPerms: bag (thread_phase * degree);
  waitPerms: bag (thread_phase * signal * degree);
  signals: list (level * bool)
}.

Record config := Config {
  cfg_state: state;
  threads: list thread_state
}.

Inductive step_label :=
| Burn(consumes: (thread_phase * degree))(produces: bag (thread_phase * degree))
| Fork(forkee_obs: bag signal)
| CreateSignal(lev: level)
| SetSignal(s: signal)
| CreateWaitPerm(s: signal)(consumes: (thread_phase * degree))(produces: degree)
| Wait(ph: thread_phase)(s: signal)(d: degree)
.

Inductive thread_step: state -> thread_state -> step_label -> state -> thread_state -> list thread_state -> Prop :=
| SBurn size ph obs ph_cp d CPs WPs Ss P size':
  size <> size_zero -> (* Threads of size zero are finished *)
  (forall ph' d', Bmem (ph', d') P -> is_ancestor_of ph_cp ph' /\ degree_lt d' d) ->
  (* size' can be anything! *)
  thread_step
    (State (Binsert (ph_cp, d) CPs) WPs Ss)
    (ThreadState size ph obs)
    (Burn (ph_cp, d) P)
    (State (Bplus CPs P) WPs Ss)
    (ThreadState size' ph obs)
    []
| SFork CPs WPs Ss size ph obs forkee_obs size' size'':
  size_lt size' size ->
  size_lt size'' size ->
  thread_step
    (State CPs WPs Ss)
    (ThreadState size ph (Bplus obs forkee_obs))
    (Fork forkee_obs)
    (State CPs WPs Ss)
    (ThreadState size' (Forker::ph) obs)
    [ThreadState size'' (Forkee::ph) forkee_obs]
| SCreateSignal CPs WPs Ss size ph obs lev size':
  size_lt size' size ->
  thread_step
    (State CPs WPs Ss)
    (ThreadState size ph obs)
    (CreateSignal lev)
    (State CPs WPs (Ss ++ [(lev, false)]))
    (ThreadState size' ph (Binsert (length Ss) obs))
    []
| SSetSignal CPs WPs Ss1 lev Ss2 size ph obs size':
  size_lt size' size ->
  thread_step
    (State CPs WPs (Ss1 ++ [(lev, false)] ++ Ss2))
    (ThreadState size ph obs)
    (SetSignal (length Ss1))
    (State CPs WPs (Ss1 ++ [(lev, true)] ++ Ss2))
    (ThreadState size' ph (Bremove1 (length Ss1) obs))
    []
| SCreateWaitPerm ph_cp dc CPs WPs Ss size ph obs s dp size':
  size_lt size' size ->
  s < length Ss ->
  degree_lt dp dc ->
  thread_step
    (State (Binsert (ph_cp, dc) CPs) WPs Ss)
    (ThreadState size ph obs)
    (CreateWaitPerm s (ph_cp, dc) dp)
    (State CPs (Binsert (ph_cp, s, dp) WPs) Ss)
    (ThreadState size' ph obs)
    []
| SWait lev CPs WPs Ss size ph obs ph_wp s d size':
  size_lt size' size ->
  Bmem (ph_wp, s, d) WPs ->
  nth_error Ss s = Some (lev, false) ->
  (forall s_obs lev_s_obs,
   Bmem s_obs obs ->
   nth_error Ss s_obs = Some (lev_s_obs, false) ->
   level_lt lev lev_s_obs) ->
  thread_step
    (State CPs WPs Ss)
    (ThreadState size ph obs)
    (Wait ph_wp s d)
    (State (Binsert (ph, d) CPs) WPs Ss)
    (ThreadState size' ph obs)
    []
.

Inductive step: config -> thread -> step_label -> config -> Prop :=
| Step st tcfg t lab st' tcfg' tcfgs Ts1 Ts2:
  t = length Ts1 ->
  thread_step st tcfg lab st' tcfg' tcfgs ->
  step (Config st (Ts1 ++ [tcfg] ++ Ts2)) t lab (Config st' (Ts1 ++ [tcfg'] ++ Ts2 ++ tcfgs))
.

Definition cfg_index := nat.
Definition step_index := nat.

(* We assume an infinite fair execution and we prove False. *)

Parameter configs: cfg_index -> config.
Parameter step_threads: step_index -> thread.
Parameter labels: step_index -> step_label.
Axiom steps_ok: forall i, step (configs i) (step_threads i) (labels i) (configs (S i)).
(* Finished threads have no obligations *)
Axiom finished_no_obs:
  forall i st Ts1 ph obs Ts2,
  configs i = Config st (Ts1 ++ [ThreadState size_zero ph obs] ++ Ts2) ->
  obs = Bempty.
(* Fairness: If at a config i, some thread has not finished, then it takes a step at some index j >= i. *)
Axiom fair:
  forall i st Ts1 size ph obs Ts2,
  configs i = Config st (Ts1 ++ [ThreadState size ph obs] ++ Ts2) ->
  size <> size_zero ->
  exists j,
  i <= j /\
  step_threads j = length Ts1.

Parameter CPs0: bag (thread_phase * degree).
Parameter main_size0: cmd_size.
Axiom configs0: configs 0 = Config (State CPs0 Bempty []) [ThreadState main_size0 [] Bempty].

