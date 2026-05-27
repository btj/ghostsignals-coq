import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.DershowitzManna

set_option warn.sorry false

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

def If {T : Type} (P : Prop) (t1 t2 : T) : T :=
  open Classical in
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

structure thread_state 𝕊 where
  size : 𝕊
  phase : thread_phase
  obs : bag signal

structure state (ℒ 𝒟 : Type) where
  callPerms : bag (thread_phase × 𝒟)
  waitPerms : bag (thread_phase × signal × 𝒟)
  signals : List (ℒ × Bool)

structure config (ℒ 𝒟 𝕊 : Type) where
  cfg_state : state ℒ 𝒟
  threads : List (thread_state 𝕊)

inductive step_label (ℒ 𝒟 : Type) where
| Burn (consumes : thread_phase × 𝒟) (produces : bag (thread_phase × 𝒟))
| Fork (forkee_obs : bag signal)
| CreateSignal (s : signal) (lev : ℒ)
| SetSignal (s : signal)
| CreateWaitPerm (s : signal) (consumes : thread_phase × 𝒟) (produces : 𝒟)
| Wait (ph : thread_phase) (s : signal) (d : 𝒟)

def nth_error {A : Type} : List A → Nat → Option A := (·[·]?)

inductive thread_step {ℒ 𝒟 𝕊 : Type} [LT ℒ] [LT 𝒟] [LT 𝕊] : state ℒ 𝒟 → thread_state 𝕊 → step_label ℒ 𝒟 → state ℒ 𝒟 → thread_state 𝕊 → List (thread_state 𝕊) → Prop
| SBurn (size : 𝕊) (ph : thread_phase) (obs : bag signal) (ph_cp : thread_phase) (d : 𝒟)
    (CPs : bag (thread_phase × 𝒟)) (WPs : bag (thread_phase × signal × 𝒟))
    (Ss : List (ℒ × Bool)) (P : bag (thread_phase × 𝒟)) (size' : 𝕊) :
  size ≠ size_zero →
  (∀ ph' d', Bmem (ph', d') P → is_ancestor_of ph_cp ph' ∧ d' < d) →
  thread_step
    ⟨Binsert (ph_cp, d) CPs, WPs, Ss⟩
    ⟨size, ph, obs⟩
    (step_label.Burn (ph_cp, d) P)
    ⟨Bplus CPs P, WPs, Ss⟩
    ⟨size', ph, obs⟩
    []
| SFork (CPs WPs Ss size ph obs forkee_obs size' size'') :
  size' < size →
  size'' < size →
  thread_step
    ⟨CPs, WPs, Ss⟩
    ⟨size, ph, Bplus obs forkee_obs⟩
    (step_label.Fork forkee_obs)
    ⟨CPs, WPs, Ss⟩
    ⟨size', phasecomp.Forker :: ph, obs⟩
    [⟨size'', phasecomp.Forkee :: ph, forkee_obs⟩]
| SCreateSignal (CPs WPs Ss size ph obs s lev size') :
  size' < size →
  s = Ss.length →
  thread_step
    ⟨CPs, WPs, Ss⟩
    ⟨size, ph, obs⟩
    (step_label.CreateSignal s lev)
    ⟨CPs, WPs, Ss ++ [(lev, false)]⟩
    ⟨size', ph, Binsert s obs⟩
    []
| SSetSignal (CPs WPs Ss1 lev Ss2 size ph obs size') :
  size' < size →
  thread_step
    ⟨CPs, WPs, Ss1 ++ [(lev, false)] ++ Ss2⟩
    ⟨size, ph, obs⟩
    (step_label.SetSignal Ss1.length)
    ⟨CPs, WPs, Ss1 ++ [(lev, true)] ++ Ss2⟩
    ⟨size', ph, Bremove1 Ss1.length obs⟩
    []
| SCreateWaitPerm (ph_cp dc CPs WPs Ss size ph obs s dp size') :
  size' < size →
  s < Ss.length →
  dp < dc →
  thread_step
    ⟨Binsert (ph_cp, dc) CPs, WPs, Ss⟩
    ⟨size, ph, obs⟩
    (step_label.CreateWaitPerm s (ph_cp, dc) dp)
    ⟨CPs, Binsert (ph_cp, s, dp) WPs, Ss⟩
    ⟨size', ph, obs⟩
    []
| SWait (lev CPs WPs Ss size ph obs ph_wp s d size') :
  size' < size →
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

inductive step {ℒ 𝒟 𝕊 : Type} [LT ℒ] [LT 𝒟] [LT 𝕊] : config ℒ 𝒟 𝕊 → thread → step_label ℒ 𝒟 → config ℒ 𝒟 𝕊 → Prop
| Step (st : state ℒ 𝒟) (tcfg : thread_state 𝕊) (t : thread) (lab : step_label ℒ 𝒟) (st' : state ℒ 𝒟) (tcfg' : thread_state 𝕊) (tcfgs : List (thread_state 𝕊)) (Ts1 Ts2 : List (thread_state 𝕊)) :
  t = Ts1.length →
  thread_step st tcfg lab st' tcfg' tcfgs →
  step ⟨st, Ts1 ++ [tcfg] ++ Ts2⟩ t lab ⟨st', Ts1 ++ [tcfg'] ++ Ts2 ++ tcfgs⟩

abbrev cfg_index := Nat
abbrev step_index := Nat

structure Execution
    (ℒ : Type) [Preorder ℒ] [WellFoundedLT ℒ] [Inhabited ℒ]
    (𝒟 : Type) [Preorder 𝒟] [WellFoundedLT 𝒟] [Inhabited 𝒟]
    (𝕊 : Type) [Preorder 𝕊] [WellFoundedLT 𝕊] [Inhabited 𝕊] [OrderBot 𝕊]
  where
    configs : cfg_index → config ℒ 𝒟 𝕊
    step_threads : step_index → thread
    labels : step_index → step_label ℒ 𝒟
    steps_ok : ∀ i, step (configs i) (step_threads i) (labels i) (configs (i + 1))

    finished_no_obs :
      ∀ i st Ts1 ph obs Ts2,
      configs i = ⟨st, Ts1 ++ [⟨size_zero, ph, obs⟩] ++ Ts2⟩ →
      obs = Bempty

    CPs0 : bag (thread_phase × 𝒟)
    main_size0 : 𝕊
    configs0 : configs 0 = ⟨⟨CPs0, Bempty, []⟩, [⟨main_size0, [], Bempty⟩]⟩

variable {ℒ : Type} [Preorder ℒ] [WellFoundedLT ℒ] [Inhabited ℒ]
variable {𝒟 : Type} [Preorder 𝒟] [WellFoundedLT 𝒟] [Inhabited 𝒟]
variable {𝕊 : Type} [Preorder 𝕊] [WellFoundedLT 𝕊] [Inhabited 𝕊] [OrderBot 𝕊]

inductive thread_alive (E : Execution ℒ 𝒟 𝕊) (i : Nat) : Nat → Prop
| intro (st : state ℒ 𝒟) (Ts1 : List (thread_state 𝕊)) (size : 𝕊) (ph : thread_phase) (obs : bag signal) (Ts2 : List (thread_state 𝕊)) :
  E.configs i = ⟨st, Ts1 ++ [⟨size, ph, obs⟩] ++ Ts2⟩ →
  size ≠ ⊥ →
  thread_alive E i Ts1.length

variable (E : Execution ℒ 𝒟 𝕊)

def fair :=
  ∀ i t,
  thread_alive E i t →
  ∃ j, i ≤ j ∧ E.step_threads j = t

def step_waits_for (i : step_index) (s : signal) : Prop :=
  ∃ ph d, E.labels i = step_label.Wait ph s d

section Signal

variable (s : signal)

def Sinf : Prop := ∀ i, ∃ j, i ≤ j ∧ step_waits_for E j s

variable (not_Sinf : ¬ Sinf E s)

def is_not_waited_for_as_of (i : step_index) : Prop :=
  ∀ j, i ≤ j → ¬ step_waits_for E j s

def not_waited_for_as_of (H : ¬ Sinf E s) : { i : step_index // is_not_waited_for_as_of E s i } := sorry

end Signal

def forks_at (i : step_index) (forker : thread) (forkee : thread) : Prop :=
  ∃ st Ts forkee_obs,
    E.configs i = ⟨st, Ts⟩ ∧
    E.step_threads i = forker ∧
    E.labels i = step_label.Fork forkee_obs ∧
    Ts.length = forkee

theorem forks_at_step_threads : ∀ i t t', forks_at E i t t' → E.step_threads i = t := sorry
theorem thread_step_alive : ∀ st tcfg (l : step_label ℒ 𝒟) st' tcfg' tcfgs, thread_step (𝕊:=𝕊) st tcfg l st' tcfg' tcfgs → tcfg.size ≠ ⊥ := sorry
theorem step_threads_alive : ∀ i t, E.step_threads i = t → thread_alive E i t := sorry
theorem step_threads_alive' : ∀ i, thread_alive E i (E.step_threads i) := sorry

def is_path (p : cfg_index → thread) : Prop :=
  p 0 = 0 ∧ ∀ i, p (i + 1) = p i ∨ forks_at E i (p i) (p (i + 1))

structure InfinitePath where
  p : cfg_index → thread
  is_path : is_path E p
  is_infinite : ∀ j, thread_alive E j (p j)
  i0 : step_index
  waits_not_Sinf : ∀ s, (∃ j, i0 ≤ j ∧ E.step_threads j = p j ∧ step_waits_for E j s) → ¬ Sinf E s

namespace InfinitePath

variable (P : InfinitePath E)

theorem path_fork_step : ∀ i j, i ≤ j → P.p j ≠ P.p i → ∃ k, i ≤ k ∧ P.p k = P.p i ∧ E.step_threads k = P.p k := sorry
def path_is_alive j := thread_alive E j (P.p j)
theorem path_next_step : ∀ i, path_is_alive E P i → ∃ j, i ≤ j ∧ E.step_threads j = P.p j := sorry

def path_is_infinite := ∀ j, path_is_alive E P j

def path_waits_for_signal_as_of (s : signal) (i : step_index) : Prop :=
  ∃ j, i ≤ j ∧ E.step_threads j = P.p j ∧ step_waits_for E j s

def default_thread_state : thread_state 𝕊 := ⟨default, [], Bempty⟩

instance : Inhabited (thread_state 𝕊) := ⟨default_thread_state⟩

def path_phase_at {E : Execution ℒ 𝒟 𝕊} (P : InfinitePath E) (i : cfg_index) : thread_phase :=
  let st_Ts := E.configs i
  let tcfg := st_Ts.threads[P.p i]!
  tcfg.phase

def path_fuel_at {E : Execution ℒ 𝒟 𝕊} (P : InfinitePath E) (i : cfg_index) : bag 𝒟 × 𝕊 :=
  let ⟨ st, Ts ⟩ := E.configs i
  let ⟨ CPs, WPs, _Ss ⟩ := st
  let filtered_CPs := Bflatmap (fun cp : thread_phase × 𝒟 =>
    let ⟨ ph, d ⟩ := cp
    If (is_ancestor_of ph (P.path_phase_at i)) (Bsing d) Bempty
  ) CPs
  let filtered_WPs := Bflatmap (fun wp : thread_phase × signal × 𝒟 =>
    let ⟨ ph, s, d ⟩ := wp
    If (is_ancestor_of ph (P.path_phase_at i)) (
      match Classical.propDecidable (Sinf E s) with
      | isTrue _ => Bempty
      | isFalse Hnot_Sinf => Btimes (not_waited_for_as_of E s Hnot_Sinf).1 d
    ) Bempty
  ) WPs
  let ⟨ size, _ph, _obs ⟩ := Ts[P.p i]!
  (Bplus filtered_CPs filtered_WPs, size)

def fuel_lt (x y : bag 𝒟 × 𝕊) : Prop :=
  slexprod Blt (· < ·) x y

def fuel_le (x y : bag 𝒟 × 𝕊) : Prop :=
  clos_refl fuel_lt x y

theorem path_fuel_decreases_at_path_step : ∀ i, P.i0 ≤ i → E.step_threads i = P.p i → fuel_lt (P.path_fuel_at (i + 1)) (P.path_fuel_at i) := sorry
theorem path_fuel_does_not_increase_at_non_path_step : ∀ i, P.i0 ≤ i → E.step_threads i ≠ P.p i → fuel_le (P.path_fuel_at (i + 1)) (P.path_fuel_at i) := sorry

theorem fuel_lt_transitive : Transitive (fuel_lt (𝒟:=𝒟) (𝕊:=𝕊)) := sorry
theorem fuel_le_transitive : Transitive (fuel_le (𝒟:=𝒟) (𝕊:=𝕊)) := sorry
theorem fuel_lt_le : ∀ x y z, fuel_lt (𝒟:=𝒟) (𝕊:=𝕊) x y → fuel_le y z → fuel_lt x z := sorry
theorem path_fuel_mono : ∀ i j, P.i0 ≤ i → i ≤ j → fuel_le (P.path_fuel_at j) (P.path_fuel_at i) := sorry
theorem path_fuel_wf : WellFounded (fuel_lt (𝒟:=𝒟) (𝕊:=𝕊)) := sorry

theorem path_not_infinite (P : InfinitePath E) : False := sorry

end InfinitePath

-- Remainder of file translations
theorem cmd_greater_not_zero : ∀ (sz sz' : 𝕊), sz < sz' → sz' ≠ ⊥ := sorry
theorem preserve_suspended_threads : ∀ i idx, step (E.configs i) (E.step_threads i) (E.labels i) (E.configs (i + 1)) →
  idx < (E.configs i).threads.length → idx ≠ E.step_threads i →
  (E.configs i).threads[idx]! = (E.configs (i + 1)).threads[idx]! := sorry

theorem fork_extra_thread : ∀ i, step (E.configs i) (E.step_threads i) (E.labels i) (E.configs (i + 1)) →
  (E.configs i).threads.length < (E.configs (i + 1)).threads.length →
  ∃ obs', E.labels i = step_label.Fork obs' := sorry

theorem point_pred : ∀ i t, thread_alive E (i + 1) t → thread_alive E i t ∨ ∃ t', forks_at E i t' t := sorry

inductive SumBool (P Q : Prop) : Type where
| inl (h : P) : SumBool P Q
| inr (h : Q) : SumBool P Q

def decide : P ∨ Q → SumBool P Q := by
  intro h
  cases Classical.propDecidable P
  case isTrue HP =>
    exact SumBool.inl HP
  case isFalse HnP =>
    exact SumBool.inr (Or.resolve_left h HnP)

def point_path (E : Execution ℒ 𝒟 𝕊) i t : ∀ (Halive : thread_alive E i t) (j : cfg_index), thread := by
  cases i
  case zero =>
    intro Halive j
    exact 0
  case succ i =>
    intro Halive j
    cases Classical.propDecidable (i.succ ≤ j)
    case isTrue Hle =>
      exact t
    case isFalse Hnle =>
      cases decide (point_pred E i t Halive)
      case inl Halive' =>
        exact point_path E i t Halive' j
      case inr Hforks =>
        let t' := Classical.choose Hforks
        let Ht' := Classical.choose_spec Hforks
        exact point_path E i t' (step_threads_alive _ _ _ (forks_at_step_threads E i t' t Ht')) j

theorem thread_alive_0 : ∀ t, thread_alive E 0 t → t = 0 := sorry
theorem point_path_alive : ∀ i t (H : thread_alive E i t) j, j ≤ i → thread_alive E j (point_path E i t H j) := sorry
theorem point_path_is_path : ∀ i t (H : thread_alive E i t),
  is_path (point_path i t H) := sorry

def subtree_alive_at : cfg_index → thread → cfg_index → Prop := sorry
def has_infinite_subtree : cfg_index → thread → Prop := sorry
theorem subtree_alive_at_mono : ∀ i t j k, i ≤ j → j ≤ k → subtree_alive_at i t k → subtree_alive_at i t j := sorry
theorem not_forall_exists_not : ∀ {A : Type} (P : A → Prop), ¬ (∀ x, P x) → ∃ x, ¬ P x := sorry
theorem point_path_at_point : ∀ i t (H : thread_alive E i t), point_path E i t H i = t := sorry
theorem forks_at_unique : ∀ i t t' t'', forks_at E i t t' → forks_at E i t t'' → t' = t'' := sorry
theorem subtree_cases : ∀ i t j t' (H : thread_alive E j t'), i + 1 ≤ j → point_path E j t' H i = t →
  point_path E j t' H (i + 1) = t ∨ ∃ t'', forks_at E i t t'' ∧ point_path E j t' H (i + 1) = t'' := sorry

variable (infinite_path : cfg_index → thread)
theorem infinite_path_lemma : ∀ i, has_infinite_subtree i (infinite_path i) := sorry
theorem infinite_path_is_path :
  infinite_path 0 = 0 ∧ ∀ i, infinite_path (i + 1) = infinite_path i ∨ forks_at E i (infinite_path i) (infinite_path (i + 1)) := sorry
theorem infinite_path_is_infinite : ∀ i, thread_alive E i (infinite_path i) := sorry

theorem not_not_Sinf (Hnot_Sinf : ∀ s, ¬ Sinf E s) : False := sorry

axiom s_inf : { s // Sinf E s }

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
| intro (st : state ℒ 𝒟) (Ts1 : List (thread_state 𝕊)) (sz : 𝕊) (ph : thread_phase) (obs : bag signal) (Ts2 : List (thread_state 𝕊)) :
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
