/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD` (Space Needle / BMO6)

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout
`1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD`
(see <https://wiki.bbchallenge.org/wiki/Space_Needle>)
(**Space Needle** / **BMO6**, `cryptid_10`, holdout #486, `suspect_94`).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$C(d, k, a, b) := 0^\infty\,1^k\,0\,1^{d+1}\,\mathrm{C}{>}\,1^a\,0\,1^b\,0^\infty$$
at $C(1, 0, 0, 0)$ in 7 steps, and every $C(d, k, a, b)$ advances in `ReachesPlus` either to
another $C(d', k', a', b')$ or to a halting configuration (when $d = 0$, $k = 0$, and $a = 0$).

## Collatz-like Acceleration Rules

```text
Consider:
C(d, k, a, b) = 0^inf 1^k 0 1^{d+1} C> 1^a 0 1^b 0^inf

C(0, 0, 0, b)         -> Halt
C(0, k+1, 0, b)       -> C(k, 0, 0, b+2)
C(1, 0, 0, b)         -> C(1, 0, b+1, 0)
C(1, k+1, 0, b)       -> C(k, 0, 2, b+1)
C(d+2, k, 0, b)       -> C(d, k+1, 0, b+1)
C(0, 0, a+1, b)       -> C(a+2, 0, b, 0)
C(0, k+1, a+1, b)     -> C(k, 0, a+3, b)
C(d+1, k, a+1, b)     -> C(d, k+1, a+1, b)

Start: C(1, 0, 0, 0), reached after 7 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Bounce Lemmas -/

/-- Leftward shift across `1^k` in state `A`. -/
private theorem shift_A_1 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
        (ListBlank.append [1] r))
      (Cfg.headRight A l
        (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight A
            (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l))
            (ListBlank.append [1] r))
          (Cfg.headRight A
            (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1] (ListBlank.append [1] r))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] r) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Rightward shift across `1^k` in state `E`. -/
private theorem shift_E_1 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E l (ListBlank.append (([1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight E (ListBlank.append (([1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight E l (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight E (ListBlank.append [1] l)
            (ListBlank.append (([1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1] : List (Fin 2)) ^ k) (ListBlank.append [1] l) =
          ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Leftward shift in state `A` across `1^d`, bounce off `0`, and rightward shift in state `E`. -/
private theorem bounce_A_E (d : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.append [0] l))
        (ListBlank.append [1] r))
      (Cfg.headRight E
        (ListBlank.append (([1] : List (Fin 2)) ^ d)
          (ListBlank.append [0] (ListBlank.append [1] l)))
        r) := by
  have h1 := shift_A_1 d (ListBlank.append [0] l) r
  have h2 :
      ReachesPlus target
        (Cfg.headRight A (ListBlank.append [0] l)
          (ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) r)))
        (Cfg.headRight E (ListBlank.append [0] (ListBlank.append [1] l))
          (ListBlank.append (([1] : List (Fin 2)) ^ d) r)) := by
    bb_steps
  have h3 := shift_E_1 d (ListBlank.append [0] (ListBlank.append [1] l)) r
  exact (h1.trans_plus h2).trans_star h3

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$C(d, k, a, b) := 0^\infty\,1^k\,0\,1^{d+1}\,\mathrm{C}{>}\,1^a\,0\,1^b\,0^\infty$. -/
def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1] 0 (.sym 0 (.rep [1] 1 .default)))
    head := some C
    right := .rep [1] 2 (.sym 0 (.rep [1] 3 .default)) }

/-- Closed pattern set for `1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C, .true)]

/-- Configuration $C(d, k, a, b)$. -/
private def cfg_C (d k a b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C
    (ListBlank.append [1]
      (ListBlank.append (([1] : List (Fin 2)) ^ d)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ k) default))))
    (ListBlank.append (([1] : List (Fin 2)) ^ a)
      (ListBlank.append [0]
        (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))

private theorem eval_pat_C (vars : ℕ → ℕ) :
    evalTapePattern pat_C vars = cfg_C (vars 0) (vars 1) (vars 2) (vars 3) :=
  rfl

private theorem in_ps_C (d k a b : ℕ) : IsInPatternSet ps (cfg_C d k a b) :=
  ⟨(pat_C, .true), List.Mem.head _,
    fun i => match i with | 0 => d | 1 => k | 2 => a | 3 => b | _ => 0, rfl, trivial⟩

/-! ## Accelerated Transition Rules -/

private theorem step_C_d0_k0_a0 (b : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C 0 0 0 b) cfg' ∧ (step target cfg').isNone := by
  have h1 :
      ReachesPlus target (cfg_C 0 0 0 b)
        (Cfg.headRight F default
          (ListBlank.append [0, 1, 1, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ b) default))) := by
    unfold cfg_C
    rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  refine ⟨_, h1, ?_⟩
  bb_halt

private theorem step_C_d0_ksucc_a0 (k b : ℕ) :
    ReachesPlus target (cfg_C 0 (k + 1) 0 b) (cfg_C k 0 0 (b + 2)) := by
  unfold cfg_C
  rw [list_pow_zero, ListBlank.append_nil,
    ListBlank.append_pow_succ ([1] : List (Fin 2)) k,
    ListBlank.append_pow_succ ([1] : List (Fin 2)) (b + 1),
    ListBlank.append_pow_succ ([1] : List (Fin 2)) b]
  bb_steps

private theorem step_C_d1_k0_a0 (b : ℕ) :
    ReachesPlus target (cfg_C 1 0 0 b) (cfg_C 1 0 (b + 1) 0) := by
  unfold cfg_C
  rw [list_pow_zero, list_pow_one, ListBlank.append_nil,
    ListBlank.append_pow_succ ([1] : List (Fin 2)) b]
  bb_steps

private theorem step_C_d1_ksucc_a0 (k b : ℕ) :
    ReachesPlus target (cfg_C 1 (k + 1) 0 b) (cfg_C k 0 2 (b + 1)) := by
  unfold cfg_C
  have h2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
  rw [list_pow_zero, list_pow_one, h2, ListBlank.append_nil,
    ListBlank.append_pow_succ ([1] : List (Fin 2)) k,
    ListBlank.append_pow_succ ([1] : List (Fin 2)) b]
  bb_steps

private theorem step_C_dadd2_a0 (d k b : ℕ) :
    ReachesPlus target (cfg_C (d + 2) k 0 b) (cfg_C d (k + 1) 0 (b + 1)) := by
  have h1 :
      ReachesPlus target (cfg_C (d + 2) k 0 b)
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ d)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ k) default)))
          (ListBlank.append [1]
            (ListBlank.append [0, 0, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))) := by
    unfold cfg_C
    rw [list_pow_zero, ListBlank.append_nil,
      ListBlank.append_pow_succ ([1] : List (Fin 2)) (d + 1),
      ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
    bb_steps
  have h2 := bounce_A_E d
    (ListBlank.append (([1] : List (Fin 2)) ^ k) default)
    (ListBlank.append [0, 0, 1] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
  have h3 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append (([1] : List (Fin 2)) ^ d)
            (ListBlank.append [0]
              (ListBlank.append [1]
                (ListBlank.append (([1] : List (Fin 2)) ^ k) default))))
          (ListBlank.append [0, 0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))
        (cfg_C d (k + 1) 0 (b + 1)) := by
    unfold cfg_C
    rw [list_pow_zero, ListBlank.append_nil,
      ListBlank.append_pow_succ ([1] : List (Fin 2)) k,
      ListBlank.append_pow_succ ([1] : List (Fin 2)) b]
    bb_steps
  exact (h1.trans h2).trans h3

private theorem step_C_d0_k0_asucc (a b : ℕ) :
    ReachesPlus target (cfg_C 0 0 (a + 1) b) (cfg_C (a + 2) 0 b 0) := by
  have h1 :
      ReachesPlus target (cfg_C 0 0 (a + 1) b)
        (Cfg.headRight E (ListBlank.append [1, 1] default)
          (ListBlank.append (([1] : List (Fin 2)) ^ a)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))) := by
    unfold cfg_C
    rw [list_pow_zero, ListBlank.append_nil,
      ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
    bb_steps
  have h2 := shift_E_1 a (ListBlank.append [1, 1] default)
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ b) default))
  have h_eq :
      ListBlank.append (([1] : List (Fin 2)) ^ a)
        (ListBlank.append [1, 1] (default : ListBlank (Fin 2))) =
        ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default := by
    have h_2 : ([1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 2 := rfl
    rw [h_2, ← ListBlank.append_pow_add]
  rw [h_eq] at h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight E (ListBlank.append (([1] : List (Fin 2)) ^ (a + 2)) default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))
        (cfg_C (a + 2) 0 b 0) := by
    unfold cfg_C
    rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact (h1.trans_star h2).trans h3

private theorem step_C_d0_ksucc_asucc (k a b : ℕ) :
    ReachesPlus target (cfg_C 0 (k + 1) (a + 1) b) (cfg_C k 0 (a + 3) b) := by
  unfold cfg_C
  rw [list_pow_zero, ListBlank.append_nil,
    ListBlank.append_pow_succ ([1] : List (Fin 2)) k,
    ListBlank.append_pow_succ ([1] : List (Fin 2)) (a + 2),
    ListBlank.append_pow_succ ([1] : List (Fin 2)) (a + 1),
    ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
  bb_steps

private theorem step_C_dsucc_asucc (d k a b : ℕ) :
    ReachesPlus target (cfg_C (d + 1) k (a + 1) b) (cfg_C d (k + 1) (a + 1) b) := by
  have h1 :
      ReachesPlus target (cfg_C (d + 1) k (a + 1) b)
        (Cfg.headRight A
          (ListBlank.append (([1] : List (Fin 2)) ^ d)
            (ListBlank.append [0]
              (ListBlank.append (([1] : List (Fin 2)) ^ k) default)))
          (ListBlank.append [1]
            (ListBlank.append [0, 1]
              (ListBlank.append (([1] : List (Fin 2)) ^ a)
                (ListBlank.append [0]
                  (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))))) := by
    unfold cfg_C
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) d,
      ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
    bb_steps
  have h2 := bounce_A_E d
    (ListBlank.append (([1] : List (Fin 2)) ^ k) default)
    (ListBlank.append [0, 1]
      (ListBlank.append (([1] : List (Fin 2)) ^ a)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ b) default))))
  have h3 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append (([1] : List (Fin 2)) ^ d)
            (ListBlank.append [0]
              (ListBlank.append [1]
                (ListBlank.append (([1] : List (Fin 2)) ^ k) default))))
          (ListBlank.append [0, 1]
            (ListBlank.append (([1] : List (Fin 2)) ^ a)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))))
        (cfg_C d (k + 1) (a + 1) b) := by
    unfold cfg_C
    rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) k,
      ListBlank.append_pow_succ ([1] : List (Fin 2)) a]
    bb_steps
  exact (h1.trans h2).trans h3

private theorem step_C (d k a b : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C d k a b) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases a with _ | a'
  · rcases d with _ | _ | d'
    · rcases k with _ | k'
      · obtain ⟨cfg', h1, h2⟩ := step_C_d0_k0_a0 b
        exact ⟨cfg', h1, Or.inr h2⟩
      · exact ⟨cfg_C k' 0 0 (b + 2), step_C_d0_ksucc_a0 k' b,
          Or.inl (in_ps_C k' 0 0 (b + 2))⟩
    · rcases k with _ | k'
      · exact ⟨cfg_C 1 0 (b + 1) 0, step_C_d1_k0_a0 b, Or.inl (in_ps_C 1 0 (b + 1) 0)⟩
      · exact ⟨cfg_C k' 0 2 (b + 1), step_C_d1_ksucc_a0 k' b,
          Or.inl (in_ps_C k' 0 2 (b + 1))⟩
    · exact ⟨cfg_C d' (k + 1) 0 (b + 1), step_C_dadd2_a0 d' k b,
        Or.inl (in_ps_C d' (k + 1) 0 (b + 1))⟩
  · rcases d with _ | d'
    · rcases k with _ | k'
      · exact ⟨cfg_C (a' + 2) 0 b 0, step_C_d0_k0_asucc a' b,
          Or.inl (in_ps_C (a' + 2) 0 b 0)⟩
      · exact ⟨cfg_C k' 0 (a' + 3) b, step_C_d0_ksucc_asucc k' a' b,
          Or.inl (in_ps_C k' 0 (a' + 3) b)⟩
    · exact ⟨cfg_C d' (k + 1) (a' + 1) b, step_C_dsucc_asucc d' k a' b,
        Or.inl (in_ps_C d' (k + 1) (a' + 1) b)⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_C 1 0 0 0) := by
  have h_init : ReachesPlus target (init []) (cfg_C 1 0 0 0) := by
    unfold cfg_C
    rw [list_pow_zero, list_pow_one]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_C 1 0 0 0, init_reaches_start, in_ps_C 1 0 0 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_C]
  exact step_C (vars 0) (vars 1) (vars 2) (vars 3)

/-- `1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD`. -/
inductive State where
  /-- $C(d, k, a, b) := 0^\infty\,1^k\,0\,1^{d+1}\,\mathrm{C}{>}\,1^a\,0\,1^b\,0^\infty$. -/
  | C (d k a b : ℕ)

/-- Initial symbolic state $C(1, 0, 0, 0)$, reached after 7 raw TM steps. -/
def start : State := .C 1 0 0 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C d k a b =>
    Cfg.headRight SixState.C
      (ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ d)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ k) default))))
      (ListBlank.append (([1] : List (Fin 2)) ^ a)
        (ListBlank.append [0]
          (ListBlank.append (([1] : List (Fin 2)) ^ b) default)))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .C 0 0 0 _ => none
  | .C 0 (k + 1) 0 b => some (.C k 0 0 (b + 2))
  | .C 1 0 0 b => some (.C 1 0 (b + 1) 0)
  | .C 1 (k + 1) 0 b => some (.C k 0 2 (b + 1))
  | .C (d + 2) k 0 b => some (.C d (k + 1) 0 (b + 1))
  | .C 0 0 (a + 1) b => some (.C (a + 2) 0 b 0)
  | .C 0 (k + 1) (a + 1) b => some (.C k 0 (a + 3) b)
  | .C (d + 1) k (a + 1) b => some (.C d (k + 1) (a + 1) b)

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨d, k, a, b⟩ s' hnext
    rcases a with _ | a'
    · rcases d with _ | _ | d'
      · rcases k with _ | k'
        · simp [next] at hnext
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_C_d0_ksucc_a0 k' b
      · rcases k with _ | k'
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_C_d1_k0_a0 b
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_C_d1_ksucc_a0 k' b
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_C_dadd2_a0 d' k b
    · rcases d with _ | d'
      · rcases k with _ | k'
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_C_d0_k0_asucc a' b
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact step_C_d0_ksucc_asucc k' a' b
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_C_dsucc_asucc d' k a' b
  step_none := by
    rintro ⟨d, k, a, b⟩ hnext
    rcases a with _ | a'
    · rcases d with _ | _ | d'
      · rcases k with _ | k'
        · obtain ⟨cfg', hp, hh⟩ := step_C_d0_k0_a0 b
          exact ⟨cfg', hp.to_star, hh⟩
        · simp [next] at hnext
      · rcases k with _ | k' <;> simp [next] at hnext
      · simp [next] at hnext
    · rcases d with _ | d'
      · rcases k with _ | k' <;> simp [next] at hnext
      · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
