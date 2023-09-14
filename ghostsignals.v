Require Import Init.Wf Relations.Relations Wellfounded.Lexicographic_Product List Classical ClassicalDescription ClassicalEpsilon.
Import ListNotations.
Require Import Lia.
Require Import Nat.

Lemma slexprod_trans {A B} (R1: A -> A -> Prop) (R2: B -> B -> Prop):
  transitive _ R1 ->
  transitive _ R2 ->
  transitive _ (slexprod _ _ R1 R2).
Proof.
  intros.
  intros [x1 x2] [y1 y2] [z1 z2] Hxy Hyz.
  inversion Hxy; subst; inversion Hyz; subst.
  + left.
    apply (H _ _ _ H2 H3).
  + left.
    assumption.
  + left.
    assumption.
  + right.
    apply (H0 _ _ _ H2 H3).
Qed.

Lemma clos_refl_trans_r {A} R (x y z: A):
  transitive _ R ->
  R x y -> clos_refl _ R y z -> R x z.
Proof.
  intros.
  inversion H1; subst.
  - apply (H _ _ _ H0 H2).
  - assumption.
Qed.

Lemma clos_refl_transitive {A} R:
  transitive A R ->
  transitive A (clos_refl _ R).
Proof.
  intros.
  intros x y z Hxy Hyz.
  inversion Hxy; subst; inversion Hyz; subst; try assumption.
  left.
  apply (H _ _ _ H0 H1).
Qed.

Definition If{T}(P: Prop)(t1 t2: T) := if excluded_middle_informative P then t1 else t2.

(* Finite multisets *)
Parameter bag: forall (T: Type), Type.
Parameter Bempty: forall {T}, bag T.
Parameter Bsing: forall {T}, T -> bag T.
Parameter Bmem: forall {T}, T -> bag T -> Prop.
Parameter Bplus: forall {T}, bag T -> bag T -> bag T.
Parameter Binsert: forall {T}, T -> bag T -> bag T.
Parameter Bremove1: forall {T}, T -> bag T -> bag T.
Parameter Bflatmap: forall {A B}, (A -> bag B) -> bag A -> bag B.
Parameter Blt: forall {T}, (T -> T -> Prop) -> bag T -> bag T -> Prop.
Axiom Blt_trans: forall {T} (Tlt: T -> T -> Prop), transitive _ Tlt -> transitive _ (Blt Tlt).
Axiom Blt_wf: forall {T} (Tlt: T -> T -> Prop), well_founded Tlt -> well_founded (Blt Tlt).

Fixpoint Btimes{T}(n: nat)(e: T): bag T :=
  match n with
    O => Bempty
  | S n0 => Binsert e (Btimes n0 e)
  end.

Parameter level: Type.
Parameter level_lt: level -> level -> Prop.
Axiom level_lt_wf: well_founded level_lt.

Parameter degree: Type.
Parameter degree_lt: degree -> degree -> Prop.
Axiom degree_lt_trans: transitive _ degree_lt.
Axiom degree_lt_wf: well_founded degree_lt.

Parameter cmd_size: Type.
Parameter size_zero: cmd_size.
Parameter size_lt: cmd_size -> cmd_size -> Prop.
Axiom size_lt_trans: transitive _ size_lt.
Axiom size_lt_wf: well_founded size_lt.

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
Inductive thread_alive i: nat -> Prop :=
  thread_alive_intro st Ts1 size ph obs Ts2:
  configs i = Config st (Ts1 ++ [ThreadState size ph obs] ++ Ts2) ->
  size <> size_zero ->
  thread_alive i (length Ts1).
Axiom fair:
  forall i t,
  thread_alive i t ->
  exists j,
  i <= j /\
  step_threads j = t.

Parameter CPs0: bag (thread_phase * degree).
Parameter main_size0: cmd_size.
Axiom configs0: configs 0 = Config (State CPs0 Bempty []) [ThreadState main_size0 [] Bempty].

(* Signals waited for infinitely often *)

Section Signal.

  Variable s: signal.

  Definition Sinf := forall i, exists j ph d, i <= j /\ labels j = Wait ph s d.

  (* Assume s is not waited for infinitely often. *)

  Hypothesis not_Sinf: ~ Sinf.

  Definition is_not_waited_for_as_of i := forall j ph d, i <= j -> labels j <> Wait ph s d.

  Definition not_waited_for_as_of: {i | is_not_waited_for_as_of i}.
  Proof.
    apply constructive_indefinite_description.
    apply NNPP.
    intro H.
    apply not_Sinf.
    intro i.
    apply NNPP.
    intro.
    apply H.
    exists i.
    intros j ph d Hj.
    intro.
    apply H0.
    exists j; exists  ph; exists d.
    tauto.
  Qed.

End Signal.

(* Paths *)

Definition forks_at(i: step_index)(forker: thread)(forkee: thread) :=
  exists st Ts forkee_obs,
  configs i = Config st Ts /\
  step_threads i = forker /\
  labels i = Fork forkee_obs /\
  length Ts = forkee.

Lemma forks_at_step_threads i t t':
  forks_at i t t' -> step_threads i = t.
Proof.
  intros.
  destruct H as [? [? [? ?]]].
  tauto.
Qed.

Section Path.

  Variable p: cfg_index -> thread.

  Definition is_path :=
    p 0 = 0 /\
    forall i, p (S i) = p i \/ forks_at i (p i) (p (S i)).

  Hypothesis His_path: is_path.
  
  Lemma path_fork_step i j:
    i <= j -> p j <> p i ->
    exists k, i <= k /\ p k = p i /\ step_threads k = p k.
  Proof.
    induction j; intros.
    - assert (i = 0). { lia. }
      subst.
      elim H0.
      reflexivity.
    - assert (i <= j). {
        destruct (classic (i = S j)).
        - subst. lia.
        - lia.
      }
      destruct (classic (p j = p i)).
      + destruct His_path.
        destruct (H4 j).
        * congruence.
        * apply forks_at_step_threads in H5.
          exists j. tauto.
      + apply IHj; tauto.
  Qed.
  
  Definition path_is_alive j := thread_alive j (p j).
  
  Lemma path_next_step i: path_is_alive i -> exists j, i <= j /\ step_threads j = p j.
  Proof.
    intro Halive.
    apply fair in Halive.
    destruct Halive as [j [Hij Hjpi]].
    destruct (classic (p j = p i)).
    - rewrite <- H in Hjpi.
      exists j. tauto.
    - apply path_fork_step in H.
      + destruct H as [k [Hk1 [Hk2 Hk3]]].
        exists k. tauto.
      + assumption.
  Qed.
  
  Definition path_is_infinite :=
    forall j, path_is_alive j.
  
  Hypothesis Hinf: path_is_infinite.
  
  Definition path_waits_for_signal_as_of(s: signal)(i: step_index) :=
    exists j ph d,
    i <= j /\
    step_threads j = p j /\
    labels j = Wait ph s d.
  
  Variable i0: step_index.
  (* As of i0, p only waits for signals not waited for infinitely often *)
  Hypothesis Hwaits_not_Sinf: forall s, path_waits_for_signal_as_of s i0 -> ~ Sinf s.
  
  Definition path_phase_at(i: cfg_index) :=
    let (st, Ts) := configs i in
    let (size, ph, obs) := nth (p i) Ts (ThreadState size_zero [] Bempty) in
    ph.
  
  Definition path_fuel_at(i: cfg_index) :=
    let (st, Ts) := configs i in
    let (CPs, WPs, Ss) := st in
    let filtered_CPs :=
      Bflatmap (fun (cp: thread_phase * degree) =>
          let (ph, d) := cp in
          If (is_ancestor_of ph (path_phase_at i)) (Bsing d) Bempty
        )
        CPs
    in
    let filtered_WPs :=
      Bflatmap (fun (wp: thread_phase * signal * degree) =>
          match wp with
            (ph, s, d) =>
            If (is_ancestor_of ph (path_phase_at i)) (
              match excluded_middle_informative (Sinf s) with
                left _ => Bempty
              | right HSinf => Btimes (proj1_sig (not_waited_for_as_of s HSinf) - i) d
              end
            ) Bempty
          end
        )
        WPs
    in
    let (size, ph, obs) := nth (p i) Ts (ThreadState size_zero [] Bempty) in
    (Bplus filtered_CPs filtered_WPs, size).
  
  Definition fuel_lt := slexprod _ _ (Blt degree_lt) size_lt.
  Definition fuel_le := clos_refl _ fuel_lt.
  
  Lemma path_fuel_decreases_at_path_step(i: step_index):
    i0 <= i ->
    step_threads i = p i ->
    fuel_lt (path_fuel_at (S i)) (path_fuel_at i).
  Admitted.
  
  Lemma path_fuel_does_not_increase_at_non_path_step(i: step_index):
    i0 <= i ->
    step_threads i <> p i ->
    fuel_le (path_fuel_at (S i)) (path_fuel_at i).
  Admitted.
  
  Lemma fuel_lt_transitive: transitive _ fuel_lt.
  Proof.
    apply slexprod_trans.
    * apply Blt_trans. apply degree_lt_trans.
    * apply size_lt_trans.
  Qed.
  
  Lemma fuel_le_transitive: transitive _ fuel_le.
  Proof.
    apply (clos_refl_transitive _ fuel_lt_transitive).
  Qed.
  
  Lemma fuel_lt_le x y z: fuel_lt x y -> fuel_le y z -> fuel_lt x z.
  Proof.
    apply clos_refl_trans_r.
    apply fuel_lt_transitive.
  Qed.
  
  Lemma path_fuel_mono i j:
    i0 <= i ->
    i <= j ->
    fuel_le (path_fuel_at j) (path_fuel_at i).
  Proof.
    intro.
    revert j.
    intro j.
    induction j; intros.
    - assert (i = 0). { lia. }
      subst.
      right.
    - destruct (classic (i = S j)).
      + subst.
        right.
      + apply (fuel_le_transitive _ (path_fuel_at j) _).
        * destruct (classic (step_threads j = p j)).
          -- left.
             apply path_fuel_decreases_at_path_step; [lia | assumption].
          -- apply path_fuel_does_not_increase_at_non_path_step; [lia | assumption].
        * apply IHj; lia.
  Qed.
  
  Lemma path_fuel_wf: well_founded (slexprod _ _ (Blt degree_lt) size_lt).
  Proof.
    apply wf_slexprod.
    - apply Blt_wf.
      apply degree_lt_wf.
    - apply size_lt_wf.
  Qed.
  
  Lemma path_not_infinite: False.
  Proof.
    assert (forall d, forall i, i0 <= i -> d = path_fuel_at i -> False). {
      intro d.
      apply (well_founded_ind path_fuel_wf) with (a:=d).
      intros.
      clear d.
      subst.
      destruct (path_next_step i (Hinf i)) as [j [Hj1 Hj2]].
      apply (H (path_fuel_at (S j))) with (i:=S j).
      - apply fuel_lt_le with (y:=path_fuel_at j).
        + apply (path_fuel_decreases_at_path_step j).
          * lia.
          * assumption.
        + apply path_fuel_mono; lia.
      - lia.
      - reflexivity.
    }
    apply (H (path_fuel_at i0) i0); [ lia | reflexivity ].
  Qed.
