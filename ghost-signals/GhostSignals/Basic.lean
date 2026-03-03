import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.DershowitzManna

set_option warn.sorry false

noncomputable section

noncomputable section

open Multiset

-- Basic Types and Multisets
abbrev bag := Multiset
abbrev Bempty {T : Type} : bag T := 0
abbrev Bsing {T : Type} (e : T) : bag T := {e}
abbrev Bmem {T : Type} (e : T) (b : bag T) : Prop := e ∈ b
def Bplus {T : Type} (b1 b2 : bag T) : bag T := (b1 : Multiset T) + (b2 : Multiset T)
def Binsert {T : Type} (e : T) (b : bag T) : bag T := e ::ₘ (b : Multiset T)
def Bremove1 {T : Type} [DecidableEq T] (e : T) (b : bag T) : bag T := (b : Multiset T).erase e
def Bflatmap {A B : Type} (f : A → bag B) (b : bag A) : bag B := (b : Multiset A).bind f
def Blt {T : Type} [Preorder T] (b1 b2 : bag T) : Prop := @Multiset.IsDershowitzMannaLT T _ b1 b2

theorem Blt_trans {T : Type} [Preorder T] : Transitive (@Blt T _) :=
  fun _ _ _ h1 h2 => Multiset.IsDershowitzMannaLT.trans h1 h2
theorem Blt_wf {T : Type} [Preorder T] (Hwf : WellFounded (fun (x y : T) => x < y)) : WellFounded (@Blt T _) :=
  have : WellFoundedLT T := ⟨Hwf⟩
  Multiset.wellFounded_isDershowitzMannaLT
theorem binsert_not_empty {A : Type} (e : A) (b : bag A) : Binsert e b ≠ Bempty := sorry

def Btimes {T : Type} : Nat → T → bag T
| 0, _ => Bempty
| n + 1, e => Binsert e (Btimes n e)

axiom degree : Type
axiom degree_lt : degree → degree → Prop
axiom degree_le : degree → degree → Prop
instance : Preorder degree where
  le := degree_le
  lt := degree_lt
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_ge := sorry
axiom degree_lt_trans : Transitive degree_lt
axiom degree_lt_wf : WellFounded (fun (x y : degree) => x < y)

axiom cmd_size : Type
axiom size_zero : cmd_size
axiom size_lt : cmd_size → cmd_size → Prop
axiom size_lt_trans : Transitive size_lt
axiom size_lt_wf : WellFounded size_lt
axiom size_zero_minimal : ∀ sz, size_lt sz size_zero → False
axiom cmd_size_eq_dec : ∀ sz sz' : cmd_size, sz = sz' ∨ sz ≠ sz'

def slexprod {A B : Type} (R1 : A → A → Prop) (R2 : B → B → Prop) (x y : A × B) : Prop :=
  R1 x.1 y.1 ∨ (x.1 = y.1 ∧ R2 x.2 y.2)

theorem slexprod_trans {A B : Type} (R1 : A → A → Prop) (R2 : B → B → Prop) :
  Transitive R1 → Transitive R2 → Transitive (slexprod R1 R2) := sorry

def clos_refl {A : Type} (R : A → A → Prop) (x y : A) : Prop :=
  R x y ∨ x = y

theorem clos_refl_trans_r {A : Type} (R : A → A → Prop) (x y z : A) :
  Transitive R → R x y → clos_refl R y z → R x z := sorry

theorem clos_refl_transitive {A : Type} (R : A → A → Prop) :
  Transitive R → Transitive (clos_refl R) := sorry

def If {T : Type} (P : Prop) [Decidable P] (t1 t2 : T) : T :=
  if P then t1 else t2

inductive phasecomp where
| Forker
| Forkee
deriving Inhabited, DecidableEq

def thread_phase := List phasecomp

def is_ancestor_of (ph1 ph2 : thread_phase) : Prop :=
  ph1 = ph2 ∨
  match ph2 with
  | [] => False
  | _ :: ph => is_ancestor_of ph1 ph

abbrev signal := Nat
abbrev thread := Nat

structure thread_state where
  size : cmd_size
  phase : thread_phase
  obs : bag signal

structure state ℒ where
  callPerms : bag (thread_phase × degree)
  waitPerms : bag (thread_phase × signal × degree)
  signals : List (ℒ × Bool)

structure config ℒ where
  cfg_state : state ℒ
  threads : List thread_state

inductive step_label ℒ where
| Burn (consumes : thread_phase × degree) (produces : bag (thread_phase × degree))
| Fork (forkee_obs : bag signal)
| CreateSignal (s : signal) (lev : ℒ)
| SetSignal (s : signal)
| CreateWaitPerm (s : signal) (consumes : thread_phase × degree) (produces : degree)
| Wait (ph : thread_phase) (s : signal) (d : degree)

axiom nth_error {A : Type} : List A → Nat → Option A

inductive thread_step {ℒ} [LT ℒ] : state ℒ → thread_state → step_label ℒ → state ℒ → thread_state → List thread_state → Prop
| SBurn (size : cmd_size) (ph : thread_phase) (obs : bag signal) (ph_cp : thread_phase) (d : degree)
    (CPs : bag (thread_phase × degree)) (WPs : bag (thread_phase × signal × degree))
    (Ss : List (ℒ × Bool)) (P : bag (thread_phase × degree)) (size' : cmd_size) :
  size ≠ size_zero →
  (∀ ph' d', Bmem (ph', d') P → is_ancestor_of ph_cp ph' ∧ degree_lt d' d) →
  thread_step
    ⟨Binsert (ph_cp, d) CPs, WPs, Ss⟩
    ⟨size, ph, obs⟩
    (step_label.Burn (ph_cp, d) P)
    ⟨Bplus CPs P, WPs, Ss⟩
    ⟨size', ph, obs⟩
    []
| SFork (CPs WPs Ss size ph obs forkee_obs size' size'') :
  size_lt size' size →
  size_lt size'' size →
  thread_step
    ⟨CPs, WPs, Ss⟩
    ⟨size, ph, Bplus obs forkee_obs⟩
    (step_label.Fork forkee_obs)
    ⟨CPs, WPs, Ss⟩
    ⟨size', phasecomp.Forker :: ph, obs⟩
    [⟨size'', phasecomp.Forkee :: ph, forkee_obs⟩]
| SCreateSignal (CPs WPs Ss size ph obs s lev size') :
  size_lt size' size →
  s = Ss.length →
  thread_step
    ⟨CPs, WPs, Ss⟩
    ⟨size, ph, obs⟩
    (step_label.CreateSignal s lev)
    ⟨CPs, WPs, Ss ++ [(lev, false)]⟩
    ⟨size', ph, Binsert s obs⟩
    []
| SSetSignal (CPs WPs Ss1 lev Ss2 size ph obs size') :
  size_lt size' size →
  thread_step
    ⟨CPs, WPs, Ss1 ++ [(lev, false)] ++ Ss2⟩
    ⟨size, ph, obs⟩
    (step_label.SetSignal Ss1.length)
    ⟨CPs, WPs, Ss1 ++ [(lev, true)] ++ Ss2⟩
    ⟨size', ph, Bremove1 Ss1.length obs⟩
    []
| SCreateWaitPerm (ph_cp dc CPs WPs Ss size ph obs s dp size') :
  size_lt size' size →
  s < Ss.length →
  degree_lt dp dc →
  thread_step
    ⟨Binsert (ph_cp, dc) CPs, WPs, Ss⟩
    ⟨size, ph, obs⟩
    (step_label.CreateWaitPerm s (ph_cp, dc) dp)
    ⟨CPs, Binsert (ph_cp, s, dp) WPs, Ss⟩
    ⟨size', ph, obs⟩
    []
| SWait (lev CPs WPs Ss size ph obs ph_wp s d size') :
  size_lt size' size →
  Bmem (ph_wp, s, d) WPs →
  nth_error Ss s = some (lev, false) →
  (∀ s_obs lev_s_obs, Bmem s_obs obs → nth_error Ss s_obs = some (lev_s_obs, false) → lev < lev_s_obs) →
  thread_step
    ⟨CPs, WPs, Ss⟩
    ⟨size, ph, obs⟩
    (step_label.Wait ph_wp s d)
    ⟨Binsert (ph, d) CPs, WPs, Ss⟩
    ⟨size', ph, obs⟩
    []

inductive step {ℒ} [LT ℒ]: config ℒ → thread → step_label ℒ → config ℒ → Prop
| Step (st : state ℒ) (tcfg : thread_state) (t : thread) (lab : step_label ℒ) (st' : state ℒ) (tcfg' : thread_state) (tcfgs : List thread_state) (Ts1 Ts2 : List thread_state) :
  t = Ts1.length →
  thread_step st tcfg lab st' tcfg' tcfgs →
  step ⟨st, Ts1 ++ [tcfg] ++ Ts2⟩ t lab ⟨st', Ts1 ++ [tcfg'] ++ Ts2 ++ tcfgs⟩

abbrev cfg_index := Nat
abbrev step_index := Nat

axiom ℒ : Type
instance : Preorder ℒ := sorry
instance : WellFoundedLT ℒ := sorry
instance : Inhabited ℒ := sorry

axiom configs : cfg_index → config ℒ
axiom step_threads : step_index → thread
axiom labels : step_index → step_label ℒ
axiom steps_ok : ∀ i, step (configs i) (step_threads i) (labels i) (configs (i + 1))

axiom finished_no_obs :
  ∀ i st Ts1 ph obs Ts2,
  configs i = ⟨st, Ts1 ++ [⟨size_zero, ph, obs⟩] ++ Ts2⟩ →
  obs = Bempty

inductive thread_alive (i : Nat) : Nat → Prop
| intro (st : state ℒ) (Ts1 : List thread_state) (size : cmd_size) (ph : thread_phase) (obs : bag signal) (Ts2 : List thread_state) :
  configs i = ⟨st, Ts1 ++ [⟨size, ph, obs⟩] ++ Ts2⟩ →
  size ≠ size_zero →
  thread_alive i Ts1.length

axiom fair :
  ∀ i t,
  thread_alive i t →
  ∃ j, i ≤ j ∧ step_threads j = t

axiom CPs0 : bag (thread_phase × degree)
axiom main_size0 : cmd_size
axiom configs0 : configs 0 = ⟨⟨CPs0, Bempty, []⟩, [⟨main_size0, [], Bempty⟩]⟩

def step_waits_for (i : step_index) (s : signal) : Prop :=
  ∃ ph d, labels i = step_label.Wait ph s d

section Signal

variable (s : signal)

def Sinf : Prop := ∀ i, ∃ j, i ≤ j ∧ step_waits_for j s

variable (not_Sinf : ¬ Sinf s)

def is_not_waited_for_as_of (i : step_index) : Prop :=
  ∀ j, i ≤ j → ¬ step_waits_for j s

axiom not_waited_for_as_of (H : ¬ Sinf s) : { i : step_index // is_not_waited_for_as_of s i }

end Signal

def forks_at (i : step_index) (forker : thread) (forkee : thread) : Prop :=
  ∃ st Ts forkee_obs,
    configs i = ⟨st, Ts⟩ ∧
    step_threads i = forker ∧
    labels i = step_label.Fork forkee_obs ∧
    Ts.length = forkee

theorem forks_at_step_threads : ∀ i t t', forks_at i t t' → step_threads i = t := sorry
theorem thread_step_alive : ∀ st tcfg (l : step_label ℒ) st' tcfg' tcfgs, thread_step st tcfg l st' tcfg' tcfgs → tcfg.size ≠ size_zero := sorry
theorem step_threads_alive : ∀ i t, step_threads i = t → thread_alive i t := sorry
theorem step_threads_alive' : ∀ i, thread_alive i (step_threads i) := sorry

structure InfinitePath where
  p : cfg_index → thread
  is_path : p 0 = 0 ∧ ∀ i, p (i + 1) = p i ∨ forks_at i (p i) (p (i + 1))
  is_infinite : ∀ j, thread_alive j (p j)
  i0 : step_index
  waits_not_Sinf : ∀ s, (∃ j, i0 ≤ j ∧ step_threads j = p j ∧ step_waits_for j s) → ¬ Sinf s

namespace InfinitePath

variable (P : InfinitePath)

theorem path_fork_step : ∀ i j, i ≤ j → P.p j ≠ P.p i → ∃ k, i ≤ k ∧ P.p k = P.p i ∧ step_threads k = P.p k := sorry
theorem path_next_step : ∀ i, thread_alive i (P.p i) → ∃ j, i ≤ j ∧ step_threads j = P.p j := sorry

def path_waits_for_signal_as_of (s : signal) (i : step_index) : Prop :=
  ∃ j, i ≤ j ∧ step_threads j = P.p j ∧ step_waits_for j s

axiom default_thread_state : thread_state

def path_phase_at (i : cfg_index) : thread_phase :=
  let st_Ts := configs i
  let tcfg := st_Ts.threads.getD (P.p i) default_thread_state
  tcfg.phase

-- Provide Decidable for Sinf
axiom dec_Sinf (s : signal) : Decidable (Sinf s)
attribute [local instance] dec_Sinf

-- Provide Decidable for is_ancestor_of
axiom dec_is_ancestor_of (ph1 ph2 : thread_phase) : Decidable (is_ancestor_of ph1 ph2)
attribute [local instance] dec_is_ancestor_of

def path_fuel_at (i : cfg_index) : bag degree × cmd_size :=
  let st_Ts := configs i
  let CPs := st_Ts.cfg_state.callPerms
  let WPs := st_Ts.cfg_state.waitPerms
  let filtered_CPs := Bflatmap (fun cp : thread_phase × degree =>
    If (is_ancestor_of cp.1 (P.path_phase_at i)) (Bsing cp.2) Bempty) CPs
  let filtered_WPs := Bflatmap (fun wp : thread_phase × signal × degree =>
    If (is_ancestor_of wp.1 (P.path_phase_at i))
      (if h : Sinf wp.2.1 then Bempty else Btimes ((not_waited_for_as_of wp.2.1 h).val - i) wp.2.2)
      Bempty) WPs
  let tcfg := st_Ts.threads.getD (P.p i) default_thread_state
  (Bplus filtered_CPs filtered_WPs, tcfg.size)

def fuel_lt (x y : bag degree × cmd_size) : Prop :=
  slexprod Blt size_lt x y

def fuel_le (x y : bag degree × cmd_size) : Prop :=
  clos_refl fuel_lt x y

theorem path_fuel_decreases_at_path_step : ∀ i, P.i0 ≤ i → step_threads i = P.p i → fuel_lt (P.path_fuel_at (i + 1)) (P.path_fuel_at i) := sorry
theorem path_fuel_does_not_increase_at_non_path_step : ∀ i, P.i0 ≤ i → step_threads i ≠ P.p i → fuel_le (P.path_fuel_at (i + 1)) (P.path_fuel_at i) := sorry

theorem fuel_lt_transitive : Transitive fuel_lt := sorry
theorem fuel_le_transitive : Transitive fuel_le := sorry
theorem fuel_lt_le : ∀ x y z, fuel_lt x y → fuel_le y z → fuel_lt x z := sorry
theorem path_fuel_mono : ∀ i j, P.i0 ≤ i → i ≤ j → fuel_le (P.path_fuel_at j) (P.path_fuel_at i) := sorry
theorem path_fuel_wf : WellFounded fuel_lt := sorry

theorem path_not_infinite : False := sorry

end InfinitePath

-- Remainder of file translations
theorem cmd_greater_not_zero : ∀ sz sz', size_lt sz sz' → sz' ≠ size_zero := sorry
theorem preserve_suspended_threads : ∀ i idx, step (configs i) (step_threads i) (labels i) (configs (i + 1)) →
  idx < (configs i).threads.length → idx ≠ step_threads i →
  (configs i).threads.getD idx default_thread_state = (configs (i + 1)).threads.getD idx default_thread_state := sorry

theorem fork_extra_thread : ∀ i, step (configs i) (step_threads i) (labels i) (configs (i + 1)) →
  (configs i).threads.length < (configs (i + 1)).threads.length →
  ∃ obs', labels i = step_label.Fork obs' := sorry

theorem point_pred : ∀ i t, thread_alive (i + 1) t → thread_alive i t ∨ ∃ t', forks_at i t' t := sorry

axiom point_path : ∀ i t, thread_alive i t → cfg_index → thread
theorem thread_alive_0 : ∀ t, thread_alive 0 t → t = 0 := sorry
theorem point_path_alive : ∀ i t (H : thread_alive i t) j, j ≤ i → thread_alive j (point_path i t H j) := sorry
theorem point_path_is_path : ∀ i t (H : thread_alive i t),
  (point_path i t H 0 = 0 ∧ ∀ j, point_path i t H (j + 1) = point_path i t H j ∨ forks_at j (point_path i t H j) (point_path i t H (j + 1))) := sorry

axiom subtree_alive_at : cfg_index → thread → cfg_index → Prop
axiom has_infinite_subtree : cfg_index → thread → Prop
theorem subtree_alive_at_mono : ∀ i t j k, i ≤ j → j ≤ k → subtree_alive_at i t k → subtree_alive_at i t j := sorry
theorem not_forall_exists_not : ∀ {A : Type} (P : A → Prop), ¬ (∀ x, P x) → ∃ x, ¬ P x := sorry
theorem point_path_at_point : ∀ i t (H : thread_alive i t), point_path i t H i = t := sorry
theorem forks_at_unique : ∀ i t t' t'', forks_at i t t' → forks_at i t t'' → t' = t'' := sorry
theorem subtree_cases : ∀ i t j t' (H : thread_alive j t'), i + 1 ≤ j → point_path j t' H i = t →
  point_path j t' H (i + 1) = t ∨ ∃ t'', forks_at i t t'' ∧ point_path j t' H (i + 1) = t'' := sorry

axiom infinite_path : cfg_index → thread
theorem infinite_path_lemma : ∀ i, has_infinite_subtree i (infinite_path i) := sorry
theorem infinite_path_is_path :
  infinite_path 0 = 0 ∧ ∀ i, infinite_path (i + 1) = infinite_path i ∨ forks_at i (infinite_path i) (infinite_path (i + 1)) := sorry
theorem infinite_path_is_infinite : ∀ i, thread_alive i (infinite_path i) := sorry

theorem not_not_Sinf (Hnot_Sinf : ∀ s, ¬ Sinf s) : False := sorry

axiom s_inf : { s // Sinf s }

inductive exists_dec {A : Type} (P : A → Prop)
| ex (x : A) (h : P x)
| nex (h : ¬ ∃ x, P x)

axiom decide_exists {A : Type} (P : A → Prop) : exists_dec P
axiom dummy_level : ℒ
axiom sig_lev : signal → ℒ
axiom sig_lt : signal → signal → Prop
theorem sig_lt_wf : WellFounded sig_lt := sorry

axiom s_inf0_ : { s // Sinf s ∧ ¬ ∃ s', Sinf s' ∧ sig_lt s' s }
def s_inf0 := s_inf0_.val
theorem Sinf_s_inf0 : Sinf s_inf0 := sorry
theorem s_inf0_minimal : ∀ s, Sinf s → ¬ sig_lt s s_inf0 := sorry

axiom step_creates_signal : step_index → signal → Prop
axiom signal_creation_step : signal → step_index
theorem wait_after_creates : ∀ i s, step_waits_for i s → signal_creation_step s ≤ i ∧ step_creates_signal (signal_creation_step s) s := sorry
theorem step_creates_signal_s_inf0 : step_creates_signal (signal_creation_step s_inf0) s_inf0 := sorry

inductive thread_holds_obligation_at (i : step_index) (t : thread) (s : signal) : Prop
| intro (st : state ℒ) (Ts1 : List thread_state) (sz : cmd_size) (ph : thread_phase) (obs : bag signal) (Ts2 : List thread_state) :
  Ts1.length = t →
  configs i = ⟨st, Ts1 ++ [⟨sz, ph, Binsert s obs⟩] ++ Ts2⟩ →
  thread_holds_obligation_at i t s

theorem thread_holds_obligation_after_signal_creation_step : ∀ i s, step_creates_signal i s → thread_holds_obligation_at (i + 1) (step_threads i) s := sorry
axiom ob_thread : signal → step_index → thread
theorem wait_holds_ob : ∀ i s, step_waits_for i s → ∀ j, signal_creation_step s < j → j ≤ i + 1 → thread_holds_obligation_at j (ob_thread s j) s := sorry

theorem thread_holds_obligation_at_alive : ∀ i t s, thread_holds_obligation_at i t s → thread_alive i t := sorry
theorem thread_holds_obligation_at_unique : ∀ i t s, thread_holds_obligation_at i t s → t = ob_thread s i := sorry
theorem thread_holds_obligation_at_pred : ∀ i t s, thread_holds_obligation_at (i + 1) t s →
  i = signal_creation_step s ∨ thread_holds_obligation_at i t s ∨ ∃ t', forks_at i t' t ∧ thread_holds_obligation_at i t' s := sorry

theorem wait_ob_lt : ∀ i s s', step_waits_for i s → thread_holds_obligation_at i (step_threads i) s' → sig_lt s s' := sorry

axiom dec_lt_signal_creation_step (i : step_index) : Decidable (signal_creation_step s_inf0 < i)
attribute [local instance] dec_lt_signal_creation_step

def s_inf0_ob_path (i : cfg_index) : thread :=
  if signal_creation_step s_inf0 < i then ob_thread s_inf0 i
  else point_path (signal_creation_step s_inf0) (step_threads (signal_creation_step s_inf0)) (step_threads_alive' _) i

theorem s_inf0_ob_path_holds_obligation : ∀ i, signal_creation_step s_inf0 < i → thread_holds_obligation_at i (s_inf0_ob_path i) s_inf0 := sorry

theorem s_inf0_ob_path_is_path :
  s_inf0_ob_path 0 = 0 ∧ ∀ i, s_inf0_ob_path (i + 1) = s_inf0_ob_path i ∨ forks_at i (s_inf0_ob_path i) (s_inf0_ob_path (i + 1)) := sorry

theorem s_inf0_ob_path_is_infinite : ∀ j, thread_alive j (s_inf0_ob_path j) := sorry

theorem no_infinite_fair_executions : False := sorry
