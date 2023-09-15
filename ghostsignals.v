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
Axiom level_inhabited: inhabited level.

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
| CreateSignal(s: signal)(lev: level)
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
| SCreateSignal CPs WPs Ss size ph obs s lev size':
  size_lt size' size ->
  s = length Ss ->
  thread_step
    (State CPs WPs Ss)
    (ThreadState size ph obs)
    (CreateSignal s lev)
    (State CPs WPs (Ss ++ [(lev, false)]))
    (ThreadState size' ph (Binsert s obs))
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

Definition step_waits_for i s := exists ph d, labels i = Wait ph s d.

(* Signals waited for infinitely often *)

Section Signal.

  Variable s: signal.
  
  Definition Sinf := forall i, exists j, i <= j /\ step_waits_for j s.

  (* Assume s is not waited for infinitely often. *)

  Hypothesis not_Sinf: ~ Sinf.

  Definition is_not_waited_for_as_of i := forall j, i <= j -> ~ step_waits_for j s.

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
    intros j Hj.
    intro.
    apply H0.
    exists j.
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

Lemma step_threads_alive i t:
  step_threads i = t -> thread_alive i t.
Proof.
Admitted.

Lemma step_threads_alive' i:
  thread_alive i (step_threads i).
Proof.
Admitted.

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
    exists j,
    i <= j /\
    step_threads j = p j /\
    step_waits_for j s.
  
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

End Path.

Lemma point_pred i t:
  thread_alive (S i) t ->
  thread_alive i t \/
  exists t', forks_at i t' t.
Proof.
Admitted.

Lemma decide {P Q}: P \/ Q -> {P} + {Q}.
Proof.
  intros.
  destruct (excluded_middle_informative P); tauto.
Qed.

Fixpoint point_path i t: forall (Halive: thread_alive i t) (j: cfg_index), thread :=
  match i as I return forall (Halive: thread_alive I t) (j: cfg_index), thread with
    O => fun _ _ => 0
  | S i => fun Halive j =>
    match excluded_middle_informative (S i <= j) with
      left Hle => t
    | right Hnotle =>
      match decide (point_pred i t Halive) with
        left Halive' => point_path i t Halive' j
      | right Hforks =>
        let (t', Ht') := constructive_indefinite_description _ Hforks in
        point_path i t' (step_threads_alive _ _ (forks_at_step_threads _ _ _ Ht')) j
      end
    end
  end.
  
Lemma thread_alive_0 t: thread_alive 0 t -> t = 0.
Proof.
Admitted.

Lemma point_path_alive i t (Halive: thread_alive i t) j:
  j <= i ->
  thread_alive j (point_path i t Halive j).
Proof.
  revert i t Halive.
  induction i; intros.
  - assert (j = 0). { lia. } subst.
    simpl.
    pose proof (thread_alive_0 _ Halive).
    subst.
    assumption.
  - simpl.
    destruct (excluded_middle_informative (S i <= j)).
    + assert (j = S i). { lia. } subst.
      assumption.
    + destruct (decide (point_pred i t Halive)).
      * apply IHi.
        lia.
      * destruct (constructive_indefinite_description (fun t' => forks_at i t' t) e).
        apply IHi.
        lia.
Qed.

Lemma point_path_is_path i t (Halive: thread_alive i t): is_path (point_path i t Halive).
Proof.
  revert t Halive.
  induction i; intros.
  - simpl.
    split.
    + reflexivity.
    + intros.
      left.
      reflexivity.
  - simpl.
    split.
    + destruct (excluded_middle_informative (S i <= 0)).
      * lia.
      * destruct (decide (point_pred i t Halive)).
        -- destruct (IHi t t0).
           assumption.
        -- destruct (constructive_indefinite_description (fun t' => forks_at i t' t) e).
           destruct (IHi x (step_threads_alive i x (forks_at_step_threads i x t f))).
           assumption.
    + intros j.
      destruct (excluded_middle_informative (S i <= j)).
      * left.
        destruct (excluded_middle_informative (S i <= S j)); try lia.
      * destruct (excluded_middle_informative (S i <= S j)).
        -- assert (j = i). { lia. }
           subst.
           destruct (decide (point_pred i t Halive)).
           ++ left.
              destruct i.
              ** simpl. apply thread_alive_0. assumption.
              ** simpl.
                 destruct (excluded_middle_informative (S i <= S i)); try lia.
           ++ destruct (constructive_indefinite_description (fun t' => forks_at i t' t) e).
              right.
              destruct i.
              ** simpl.
                 pose proof f.
                 apply forks_at_step_threads in H.
                 apply step_threads_alive in H.
                 apply thread_alive_0 in H.
                 subst.
                 assumption.
              ** simpl.
                 destruct (excluded_middle_informative (S i <= S i)); try lia.
                 assumption.
        -- destruct (decide (point_pred i t Halive)).
           ++ destruct (IHi t t0).
              apply H0.
           ++ destruct (constructive_indefinite_description (fun t' => forks_at i t' t) e).
              destruct (IHi x (step_threads_alive i x (forks_at_step_threads i x t f))).
              apply H0.
Qed.

Definition subtree_alive_at i t j :=
  exists t' (Halive: thread_alive j t'), point_path j t' Halive i = t.

Definition has_infinite_subtree i t :=
  forall j, i <= j -> subtree_alive_at i t j.

Lemma subtree_alive_at_mono i t j k:
  i <= j -> j <= k ->
  subtree_alive_at i t k -> subtree_alive_at i t j.
Proof.
  intros Hj.
  induction k; intros.
  - assert (j = 0). { lia. }
    subst.
    assumption.
  - destruct (classic (j = S k)).
    + subst.
      assumption.
    + assert (j <= k). { lia. }
      pose proof (IHk H2).
      clear IHk H H1.
      destruct H0 as [t' [Halive Ht']].
      apply H3.
      clear H3.
      simpl in Ht'.
      destruct (excluded_middle_informative (S k <= i)); try lia.
      destruct (decide (point_pred k t' Halive)).
      * exists t'.
        exists t0.
        assumption.
      * destruct (constructive_indefinite_description (fun t'' => forks_at k t'' t') e).
        exists x.
        exists (step_threads_alive k x (forks_at_step_threads k x t' f)).
        apply Ht'.
Qed.

Lemma not_forall_exists_not{A}(P: A -> Prop):
  ~ (forall x, P x) -> exists x, ~ P x.
Proof.
  intros.
  destruct (classic (exists x, ~ P x)). { assumption. }
  elim H.
  intros.
  destruct (classic (P x)). { assumption. }
  elim H0.
  exists x.
  assumption.
Qed.

Lemma point_path_at_point i t (Halive: thread_alive i t):
  point_path i t Halive i = t.
Proof.
  destruct i.
  - pose proof (thread_alive_0 _ Halive).
    subst.
    reflexivity.
  - simpl.
    destruct (excluded_middle_informative (S i <= S i)); try lia.
Qed.

Lemma forks_at_unique i t t' t'':
  forks_at i t t' ->
  forks_at i t t'' ->
  t' = t''.
Proof.
Admitted.

Lemma subtree_cases i t j t' (Halive: thread_alive j t'):
  S i <= j ->
  point_path j t' Halive i = t ->
  point_path j t' Halive (S i) = t \/
  exists t'', forks_at i t t'' /\ point_path j t' Halive (S i) = t''.
Proof.
  revert t' Halive.
  induction j; intros. { lia. }
  simpl in *.
  destruct (excluded_middle_informative (S j <= i)); try lia.
  destruct (excluded_middle_informative (S j <= S i)).
  - assert (i = j). { lia. } subst j.
    destruct (decide (point_pred i t' Halive)).
    + subst.
      left.
      rewrite point_path_at_point.
      reflexivity.
    + destruct (constructive_indefinite_description (fun t'' => forks_at i t'' t') e).
      right.
      rewrite point_path_at_point in H0.
      subst.
      exists t'.
      tauto.
  - destruct (decide (point_pred j t' Halive)).
    + apply IHj.
      * lia.
      * assumption.
    + destruct (constructive_indefinite_description (fun t'' => forks_at j t'' t') e).
      apply IHj.
      * lia.
      * assumption.
Qed.

Fixpoint infinite_path i :=
  match i with
    O => 0
  | S i =>
    let t := infinite_path i in
    match excluded_middle_informative (has_infinite_subtree (S i) t) with
      left _ => t
    | right _ =>
      match excluded_middle_informative (exists t', forks_at i t t') with
        left H =>
        let (t', Ht') := constructive_indefinite_description _ H in
        t'
      | right _ =>
        t (* Can't happen *)
      end
    end
  end.

Lemma infinite_path_lemma i: has_infinite_subtree i (infinite_path i).
Proof.
  induction i.
  - intros j Hj.
    exists (step_threads j).
    assert (thread_alive j (step_threads j)). {apply step_threads_alive. reflexivity. }
    exists H.
    destruct (point_path_is_path j (step_threads j) H).
    assumption.
  - simpl.
    set (t:=infinite_path i).
    destruct (excluded_middle_informative (has_infinite_subtree (S i) t)).
    + assumption.
    + apply not_forall_exists_not in n.
      destruct n as [j Hj].
      assert (S i <= j). {
        destruct (classic (S i <= j)). { assumption. }
        elim Hj.
        intros.
        elim (H H0).
      }
      assert (~ subtree_alive_at (S i) t j). {
        intro.
        apply Hj.
        tauto.
      }
      clear Hj.
      destruct (excluded_middle_informative (exists t', forks_at i t t')).
      * destruct e as [t' Ht'].
        intros k Hk.
        destruct (classic (j <= k)).
        -- pose proof (IHi k).
           destruct H2 as [t'' [Halive Ht'']]. { lia. }
           apply subtree_cases in Ht''. 2:{ lia. }
           destruct Ht''.
           ++ assert (subtree_alive_at (S i) t k). {
                exists t''. exists Halive.
                assumption.
              }
              apply subtree_alive_at_mono with (j:=j) in H3. 2:{ lia. } 2:{ assumption. }
              elim (H0 H3).
           ++ destruct H2 as [t'_ [Ht'_ ?]].
              apply forks_at_unique with (1:=Ht') in Ht'_.
              subst t'_.
              destruct (constructive_indefinite_description (forks_at i t) (ex_intro (fun t' => forks_at i t t') t' Ht')).
              apply forks_at_unique with (1:=Ht') in f.
              subst x.
              exists t''. exists Halive.
              assumption.
        -- destruct (constructive_indefinite_description (forks_at i t) (ex_intro (fun t' => forks_at i t t') t' Ht')).
           apply forks_at_unique with (1:=Ht') in f.
           subst x.
           apply subtree_alive_at_mono with (k:=j); try lia.
           destruct (IHi j); try lia.
           destruct H2 as [Halive ?].
           apply subtree_cases in H2. 2:{ lia. }
           destruct H2.
           ++ elim H0.
              exists x.
              exists Halive.
              assumption.
           ++ destruct H2 as [t'' [? ?]].
              apply forks_at_unique with (1:=Ht') in H2.
              subst t''.
              exists x.
              exists Halive.
              assumption.
      * elim H0.
        destruct (IHi j); try lia.
        destruct H1.
        apply subtree_cases in H1; try lia.
        destruct H1.
        -- exists x.
           exists x0.
           assumption.
        -- destruct H1 as [? [? ?]].
           elim n.
           exists x1.
           assumption.
Qed.

Lemma infinite_path_is_path: is_path infinite_path.
Proof.
  split.
  - reflexivity.
  - intro i.
    simpl.
    destruct (excluded_middle_informative (has_infinite_subtree (S i) (infinite_path i))). { tauto. }
    destruct (excluded_middle_informative (exists t', forks_at i (infinite_path i) t')).
    * destruct (constructive_indefinite_description (forks_at i (infinite_path i)) e).
      tauto.
    * tauto.
Qed.

Lemma infinite_path_is_infinite: path_is_infinite infinite_path.
Proof.
  intro i.
  pose proof (infinite_path_lemma i i).
  destruct H; try lia.
  destruct H.
  rewrite point_path_at_point in H.
  subst.
  assumption.
Qed.

Section Not_Sinf.

  Hypothesis Hnot_Sinf: forall s, ~ Sinf s.
  
  Lemma not_not_Sinf: False.
  Proof.
    apply (path_not_infinite infinite_path infinite_path_is_path infinite_path_is_infinite 0).
    intros.
    apply Hnot_Sinf.
  Qed.

End Not_Sinf.

(* Some signal that is waited for infinitely often. *)
Definition s_inf: {s | Sinf s}.
Proof.
  destruct (excluded_middle_informative (exists s, Sinf s)).
  - apply constructive_indefinite_description.
    assumption.
  - elim not_not_Sinf.
    intro s.
    destruct (classic (Sinf s)).
    + elim n.
      exists s.
      assumption.
    + assumption.
Qed.

Inductive exists_dec{A}(P: A -> Prop): Type :=
  exists_dec_ex x: P x -> exists_dec P
| exists_dec_nex: ~ (exists x, P x) -> exists_dec P.

Definition decide_exists{A}(P: A -> Prop): exists_dec P.
Proof.
  destruct (excluded_middle_informative (exists x, P x)).
  - apply constructive_indefinite_description in e.
    destruct e.
    apply (exists_dec_ex _ x).
    assumption.
  - apply exists_dec_nex; assumption.
Qed.

Definition dummy_level: level.
Proof.
  assert (exists l: level, True). {
    destruct level_inhabited.
    exists X.
    exact I.
  }
  apply constructive_indefinite_description in H.
  destruct H.
  apply x.
Qed.

Definition sig_lev s :=
  match decide_exists (fun l =>
      exists i b,
      let (state, _) := configs i in
      let (CPs, WPs, Ss) := state in
      nth_error Ss s = Some (l, b)
    ) with
    exists_dec_ex _ l _ => l
  | exists_dec_nex _ _ => dummy_level
  end.

Definition sig_lt s1 s2 := level_lt (sig_lev s1) (sig_lev s2).
Lemma sig_lt_wf: well_founded sig_lt.
Proof.
  assert (forall l, Acc level_lt l -> forall s, l = sig_lev s -> Acc sig_lt s). {
    induction 1.
    intros.
    constructor.
    intros.
    apply H0 with (y:=sig_lev y).
    - subst.
      apply H2.
    - reflexivity.
  }
  intro.
  apply (H (sig_lev a)).
  - apply level_lt_wf.
  - reflexivity.
Qed.

Definition s_inf0_: {s | Sinf s /\ ~ exists s', Sinf s' /\ sig_lt s' s}.
Proof.
  assert (forall s, Acc sig_lt s -> Sinf s -> exists s', Sinf s' /\ ~ exists s'', Sinf s'' /\ sig_lt s'' s'). {
    induction 1.
    rename x into s.
    destruct (classic (exists s', Sinf s' /\ sig_lt s' s)).
    - destruct H1 as [s' [? ?]].
      intros.
      apply H0 with (1:=H2).
      assumption.
    - intros.
      exists s.
      tauto.
  }
  apply constructive_indefinite_description.
  destruct s_inf.
  apply H with (s:=x).
  - apply sig_lt_wf.
  - assumption.
Qed.

Definition s_inf0 := proj1_sig s_inf0_.

Lemma Sinf_s_inf0: Sinf s_inf0.
Proof.
  destruct (proj2_sig s_inf0_).
  apply H.
Qed.

Lemma s_inf0_minimal s: Sinf s -> ~ sig_lt s s_inf0.
Proof.
  destruct (proj2_sig s_inf0_).
  intros; intro.
  elim H0.
  exists s.
  tauto.
Qed.

Definition step_creates_signal i s := exists l, labels i = CreateSignal s l.

Definition signal_creation_step s :=
  match decide_exists (fun i => step_creates_signal i s) with
    exists_dec_ex _ i _ => i
  | exists_dec_nex _ _ => 0
  end.

Lemma wait_after_creates i s:
  step_waits_for i s ->
  signal_creation_step s <= i /\ step_creates_signal (signal_creation_step s) s.
Proof.
Admitted.

Lemma step_creates_signal_s_inf0:
  step_creates_signal (signal_creation_step s_inf0) s_inf0.
Proof.
  pose proof (Sinf_s_inf0 0).
  destruct H as [j [? ?]].
  apply wait_after_creates in H0.
  destruct H0.
  assumption.
Qed.

Inductive thread_holds_obligation_at i t s: Prop :=
  thread_holds_obligation_at_intro st Ts1 sz ph obs Ts2:
  length Ts1 = t ->
  configs i = Config st (Ts1 ++ [ThreadState sz ph (Binsert s obs)] ++ Ts2) ->
  thread_holds_obligation_at i t s.

Lemma thread_holds_obligation_after_signal_creation_step i s:
  step_creates_signal i s ->
  thread_holds_obligation_at (S i) (step_threads i) s.
Proof.
Admitted.

Definition ob_thread s i :=
  match decide_exists (fun t => thread_holds_obligation_at i t s) with
    exists_dec_ex _ t _ => t
  | exists_dec_nex _ _ => 0
  end.

Lemma wait_holds_ob i s:
  step_waits_for i s ->
  forall j,
  signal_creation_step s < j -> j <= S i ->
  thread_holds_obligation_at j (ob_thread s j) s.
Proof.
Admitted.

Lemma thread_holds_obligation_at_alive i t s:
  thread_holds_obligation_at i t s -> thread_alive i t.
Proof.
Admitted.

Lemma thread_holds_obligation_at_unique i t s:
  thread_holds_obligation_at i t s -> t = ob_thread s i.
Proof.
Admitted.

Lemma thread_holds_obligation_at_pred i t s:
  thread_holds_obligation_at (S i) t s ->
  i = signal_creation_step s \/
  thread_holds_obligation_at i t s \/
  exists t', forks_at i t' t /\ thread_holds_obligation_at i t' s.
Proof.
Admitted.

Lemma wait_ob_lt i s s':
  step_waits_for i s ->
  thread_holds_obligation_at i (step_threads i) s' ->
  sig_lt s s'.
Proof.
Admitted.

Definition s_inf0_ob_path i :=
  match excluded_middle_informative (signal_creation_step s_inf0 < i) with
    left _ => ob_thread s_inf0 i
  | right _ => point_path (signal_creation_step s_inf0) (step_threads (signal_creation_step s_inf0)) (step_threads_alive' (signal_creation_step s_inf0)) i
  end.

Lemma s_inf0_ob_path_holds_obligation i:
  signal_creation_step s_inf0 < i ->
  thread_holds_obligation_at i (s_inf0_ob_path i) s_inf0.
Proof.
  intros.
  destruct (Sinf_s_inf0 i) as [j [? ?]].
  apply wait_holds_ob with (j:=i) in H1; try lia.
  unfold s_inf0_ob_path.
  destruct (excluded_middle_informative (signal_creation_step s_inf0 < i)); try lia.
  assumption.
Qed.

Lemma s_inf0_ob_path_is_path: is_path s_inf0_ob_path.
Proof.
  split.
  - unfold s_inf0_ob_path.
    destruct (excluded_middle_informative (signal_creation_step s_inf0 < 0)); try lia.
    apply point_path_is_path.
  - intros.
    pose proof (s_inf0_ob_path_holds_obligation (S i)).
    unfold s_inf0_ob_path in *.
    destruct (excluded_middle_informative (signal_creation_step s_inf0 < i)).
    + destruct (excluded_middle_informative (signal_creation_step s_inf0 < S i)); try lia.
      apply thread_holds_obligation_at_pred in H; try lia.
      destruct H; try lia.
      destruct H.
      * apply thread_holds_obligation_at_unique in H.
        tauto.
      * destruct H as [t' [? ?]].
        right.
        apply thread_holds_obligation_at_unique in H0.
        subst.
        assumption.
    + destruct (excluded_middle_informative (signal_creation_step s_inf0 < S i)).
      * assert (signal_creation_step s_inf0 = i). { lia. }
        subst.
        left.
        rewrite point_path_at_point.
        pose proof (thread_holds_obligation_after_signal_creation_step (signal_creation_step s_inf0) s_inf0).
        apply thread_holds_obligation_at_unique in H0. 2:{
          apply step_creates_signal_s_inf0.
        }
        congruence.
      * apply point_path_is_path.
Qed.

Lemma s_inf0_ob_path_is_infinite: path_is_infinite s_inf0_ob_path.
Proof.
  intros j.
  pose proof (s_inf0_ob_path_holds_obligation j).
  unfold path_is_alive.
  unfold s_inf0_ob_path in *.
  destruct (excluded_middle_informative (signal_creation_step s_inf0 < j)).
  - apply thread_holds_obligation_at_alive with (s:=s_inf0).
    apply H.
    assumption.
  - apply point_path_alive.
    lia.
Qed.

Theorem no_infinite_fair_executions: False.
Proof.
  apply (path_not_infinite s_inf0_ob_path) with (i0:=S (signal_creation_step s_inf0)).
  - apply s_inf0_ob_path_is_path.
  - apply s_inf0_ob_path_is_infinite.
  - intros.
    destruct H as [i [? [? ?]]].
    lapply (s_inf0_ob_path_holds_obligation i). 2:{ lia. }
    intros.
    rewrite <- H0 in H2.
    apply wait_ob_lt with (2:=H2) in H1.
    intro.
    apply s_inf0_minimal with (1:=H3).
    assumption.
Qed.
