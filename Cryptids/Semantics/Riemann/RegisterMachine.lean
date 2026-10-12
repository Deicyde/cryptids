/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Propositions
public import Cryptids.Semantics.Riemann.Dispatcher
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

/-!
# Layer 3: NQL Register Machine Verification for `riemann_744`

This file formalizes the 16-register machine compiled from `riemann.nql` (`riemann.subs`) and proves
that starting from `regInit = ⟨0, []⟩`, it halts if and only if there exists `x : ℕ` satisfying
`MatiyasevichRiemannCounterexample x`.
-/

@[expose] public section

namespace ConjectureMachines.Semantics.Riemann

open Turing StateTransition

@[simp]
theorem harmNum_zero : harmNum 0 = 0 := rfl

@[simp]
theorem harmNum_succ (n : ℕ) :
    harmNum (n + 1) = harmNum n * (n + 1) + n.factorial := rfl

/-- Least common multiple of `{1, ..., x}`. -/
def lcmUpTo (x : ℕ) : ℕ :=
  (Finset.Icc 1 x).lcm id

/-!
## 1. Abstract Register Machine Definitions
-/

@[simp]
theorem regNSteps_zero (c : RegCfg) : regNSteps 0 c = some c := rfl

@[simp]
theorem regNSteps_succ (n : ℕ) (c : RegCfg) :
    regNSteps (n + 1) c = (regStep c).bind (regNSteps n) := rfl

theorem regNSteps_one {c₁ c₂ : RegCfg} (h : regStep c₁ = some c₂) :
    regNSteps 1 c₁ = some c₂ := by
  simp [h]

theorem regNSteps_add (m n : ℕ) (c : RegCfg) :
    regNSteps (m + n) c = (regNSteps m c).bind (regNSteps n) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, regNSteps_succ, regNSteps_succ]
    cases regStep c with
    | none => rfl
    | some c' => exact ih c'

theorem regNSteps_bind_eq {m n : ℕ} {c₁ c₂ c₃ : RegCfg}
    (h₁ : regNSteps m c₁ = some c₂) (h₂ : regNSteps n c₂ = some c₃) :
    regNSteps (m + n) c₁ = some c₃ := by
  rw [regNSteps_add, h₁, Option.bind_some, h₂]


/-- The register machine halts starting from configuration `c`. -/
def RegHaltsFrom (c : RegCfg) : Prop :=
  ∃ n : ℕ, regNSteps n c = none

theorem regHalts_iff_regHaltsFrom :
    RegHalts ↔ RegHaltsFrom regInit := by
  rw [regHalts_iff_exists_regNSteps]
  constructor
  · rintro ⟨n, c, hn, hnone⟩
    exact ⟨n + 1, by rw [regNSteps_add, hn, Option.bind_some, regNSteps_succ, hnone,
      Option.bind_none]⟩
  · rintro ⟨n, hn⟩
    have haux : ∀ m (c₀ : RegCfg), regNSteps m c₀ = none → ∃ k c, regNSteps k c₀ =
        some c ∧ regStep c = none := by
      intro m
      induction m with
      | zero => intro c₀ h; cases h
      | succ m ih =>
        intro c₀ h
        rw [regNSteps_succ] at h
        rcases hs : regStep c₀ with _ | c₁
        · exact ⟨0, c₀, rfl, hs⟩
        · rw [hs, Option.bind_some] at h
          obtain ⟨k, c, hk, hnone⟩ := ih c₁ h
          exact ⟨k + 1, c, by rw [regNSteps_succ, hs, Option.bind_some, hk], hnone⟩
    exact haux n regInit hn

theorem regNSteps_none_add (m n : ℕ) (c : RegCfg) (h : regNSteps m c = none) :
    regNSteps (m + n) c = none := by
  rw [regNSteps_add, h, Option.bind_none]

theorem regNSteps_none_of_le {m n : ℕ} {c : RegCfg} (hle : m ≤ n) (h : regNSteps m c = none) :
    regNSteps n c = none := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact regNSteps_none_add m k c h

theorem regHaltsFrom_of_regNSteps {k : ℕ} {c₁ c₂ : RegCfg}
    (h : regNSteps k c₁ = some c₂) :
    RegHaltsFrom c₁ ↔ RegHaltsFrom c₂ := by
  constructor
  · rintro ⟨n, hn⟩
    have hlt : k < n := by
      by_contra hle
      have hnone := regNSteps_none_of_le (Nat.le_of_not_lt hle) hn
      rw [h] at hnone
      cases hnone
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hlt)
    rw [regNSteps_add, h, Option.bind_some] at hn
    exact ⟨d, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨k + n, by rw [regNSteps_add, h, Option.bind_some, hn]⟩

theorem not_regHaltsFrom_of_unbounded {c : RegCfg}
    (h : ∀ n : ℕ, ∃ m c', n ≤ m ∧ regNSteps m c = some c') :
    ¬ RegHaltsFrom c := by
  rintro ⟨n, hn⟩
  obtain ⟨m, c', hle, hm⟩ := h n
  have hnone := regNSteps_none_of_le hle hn
  rw [hm] at hnone
  cases hnone


/-!
## 2. Register Bank (`List ℕ`) Extensionality and Primitive Step Lemmas
-/

theorem getElem!_of_lt (regs : List ℕ) (k : ℕ) (hk : k < regs.length) :
    regs[k]! = regs[k] := by
  simp [hk]

theorem getElem!_set_self (regs : List ℕ) (k v : ℕ) (hk : k < regs.length) :
    (regs.set k v)[k]! = v := by
  induction regs generalizing k with
  | nil => simp at hk
  | cons a as ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hk
      exact ih k hk

theorem getElem!_set_ne (regs : List ℕ) (k j v : ℕ) (hne : k ≠ j) :
    (regs.set k v)[j]! = regs[j]! := by
  induction regs generalizing k j with
  | nil => rfl
  | cons a as ih =>
    cases k with
    | zero =>
      cases j with
      | zero => contradiction
      | succ j => rfl
    | succ k =>
      cases j with
      | zero => rfl
      | succ j =>
        exact ih k j (by omega)

@[simp]
theorem getElem!_set (regs : List ℕ) (k i v : ℕ) (hk : k < regs.length) :
    (regs.set k v)[i]! = if k = i then v else regs[i]! := by
  split_ifs with hki
  · subst hki
    exact getElem!_set_self regs k v hk
  · exact getElem!_set_ne regs k i v hki

theorem regs_ext {regs₁ regs₂ : List ℕ} (h₁ : regs₁.length = 16) (h₂ : regs₂.length = 16)
    (h : ∀ i < 16, regs₁[i]! = regs₂[i]!) : regs₁ = regs₂ := by
  apply List.ext_getElem (by omega)
  intro i hi₁ hi₂
  have hi : i < 16 := by omega
  have eq1 := getElem!_of_lt regs₁ i hi₁
  have eq2 := getElem!_of_lt regs₂ i hi₂
  rw [← eq1, ← eq2]
  exact h i hi

theorem getD_zero_eq_getElem! (regs : List ℕ) (i : ℕ) : regs.getD i 0 = regs[i]! := by
  induction regs generalizing i with
  | nil => rfl
  | cons a as ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

@[simp] theorem fin16_val_0 : (0 : Fin 16).val = 0 := rfl
@[simp] theorem fin16_val_1 : (1 : Fin 16).val = 1 := rfl
@[simp] theorem fin16_val_2 : (2 : Fin 16).val = 2 := rfl
@[simp] theorem fin16_val_3 : (3 : Fin 16).val = 3 := rfl
@[simp] theorem fin16_val_4 : (4 : Fin 16).val = 4 := rfl
@[simp] theorem fin16_val_5 : (5 : Fin 16).val = 5 := rfl
@[simp] theorem fin16_val_6 : (6 : Fin 16).val = 6 := rfl
@[simp] theorem fin16_val_7 : (7 : Fin 16).val = 7 := rfl
@[simp] theorem fin16_val_8 : (8 : Fin 16).val = 8 := rfl
@[simp] theorem fin16_val_9 : (9 : Fin 16).val = 9 := rfl
@[simp] theorem fin16_val_10 : (10 : Fin 16).val = 10 := rfl
@[simp] theorem fin16_val_11 : (11 : Fin 16).val = 11 := rfl
@[simp] theorem fin16_val_12 : (12 : Fin 16).val = 12 := rfl
@[simp] theorem fin16_val_13 : (13 : Fin 16).val = 13 := rfl
@[simp] theorem fin16_val_14 : (14 : Fin 16).val = 14 := rfl
@[simp] theorem fin16_val_15 : (15 : Fin 16).val = 15 := rfl

@[simp] theorem lt16_0 : 0 < 16 := by decide
@[simp] theorem lt16_1 : 1 < 16 := by decide
@[simp] theorem lt16_2 : 2 < 16 := by decide
@[simp] theorem lt16_3 : 3 < 16 := by decide
@[simp] theorem lt16_4 : 4 < 16 := by decide
@[simp] theorem lt16_5 : 5 < 16 := by decide
@[simp] theorem lt16_6 : 6 < 16 := by decide
@[simp] theorem lt16_7 : 7 < 16 := by decide
@[simp] theorem lt16_8 : 8 < 16 := by decide
@[simp] theorem lt16_9 : 9 < 16 := by decide
@[simp] theorem lt16_10 : 10 < 16 := by decide
@[simp] theorem lt16_11 : 11 < 16 := by decide
@[simp] theorem lt16_12 : 12 < 16 := by decide
@[simp] theorem lt16_13 : 13 < 16 := by decide
@[simp] theorem lt16_14 : 14 < 16 := by decide
@[simp] theorem lt16_15 : 15 < 16 := by decide

macro "regs_eq " h:ident : tactic =>
  `(tactic| (
    apply regs_ext (by simp only [List.length_set, $h:term]) (by simp only [List.length_set,
      $h:term]);
    intro i hi;
    simp only [getElem!_set, List.length_set, $h:term, Fin.is_lt,
      lt16_0, lt16_1, lt16_2, lt16_3, lt16_4, lt16_5, lt16_6, lt16_7,
      lt16_8, lt16_9, lt16_10, lt16_11, lt16_12, lt16_13, lt16_14, lt16_15,
      fin16_val_0, fin16_val_1, fin16_val_2, fin16_val_3,
      fin16_val_4, fin16_val_5, fin16_val_6, fin16_val_7,
      fin16_val_8, fin16_val_9, fin16_val_10, fin16_val_11,
      fin16_val_12, fin16_val_13, fin16_val_14, fin16_val_15];
    (try split_ifs) <;>
      first | rfl | contradiction | ((try subst i); first | rfl | contradiction | omega | ring)))

macro "reg_val " h:ident : tactic =>
  `(tactic| (
    simp only [getElem!_set, List.length_set, $h:term, Fin.is_lt,
      lt16_0, lt16_1, lt16_2, lt16_3, lt16_4, lt16_5, lt16_6, lt16_7,
      lt16_8, lt16_9, lt16_10, lt16_11, lt16_12, lt16_13, lt16_14, lt16_15,
      fin16_val_0, fin16_val_1, fin16_val_2, fin16_val_3,
      fin16_val_4, fin16_val_5, fin16_val_6, fin16_val_7,
      fin16_val_8, fin16_val_9, fin16_val_10, fin16_val_11,
      fin16_val_12, fin16_val_13, fin16_val_14, fin16_val_15,
      Nat.reduceEqDiff, ↓reduceIte];
    try ((try split_ifs) <;> first | rfl | contradiction | omega | ring)))

theorem step_incr {pc : ℕ} {k : Fin 16} (h : program pc = .incr k) (regs : List ℕ) :
    regNSteps 1 ⟨pc, regs⟩ = some ⟨pc + 1, regs.set k.val (regs[k.val]! + 1)⟩ := by
  unfold regNSteps regStep
  rw [h]
  dsimp only
  rw [getD_zero_eq_getElem!]
  rfl

theorem step_jump {pc target : ℕ} (h : program pc = .jump target) (regs : List ℕ) :
    regNSteps 1 ⟨pc, regs⟩ = some ⟨target, regs⟩ := by
  unfold regNSteps regStep
  rw [h]
  rfl

theorem step_decr_zero {pc : ℕ} {k : Fin 16} (h : program pc = .decr k) (regs : List ℕ)
    (hz : regs[k.val]! = 0) :
    regNSteps 1 ⟨pc, regs⟩ = some ⟨pc + 1, regs⟩ := by
  unfold regNSteps regStep
  rw [h]
  dsimp only
  rw [getD_zero_eq_getElem!, hz]
  rfl

theorem step_decr_pos {pc : ℕ} {k : Fin 16} (h : program pc = .decr k) (regs : List ℕ)
    {v : ℕ} (hv : regs[k.val]! = v + 1) :
    regNSteps 1 ⟨pc, regs⟩ = some ⟨pc + 2, regs.set k.val v⟩ := by
  unfold regNSteps regStep
  rw [h]
  dsimp only
  rw [getD_zero_eq_getElem!, hv]
  rfl

theorem step_halt {pc : ℕ} (h : program pc = .halt) (regs : List ℕ) :
    regNSteps 1 ⟨pc, regs⟩ = none := by
  unfold regNSteps regStep
  rw [h]
  rfl

/-!
## 3. Parametric Subroutine Verification (`transfer`, `copy_add`, `mul`, `decr_pair`, `div`, `sub`)
-/

def isNoopTo (pc target : ℕ) : Bool :=
  (program pc == .jump target) ||
  match program pc with
  | .jump mid =>
    (program mid == .jump target) ||
    match program mid with
    | .jump mid2 => program mid2 == .jump target
    | _ => false
  | _ => false

theorem exec_noop_to {pc target : ℕ} (h : isNoopTo pc target = true) (regs : List ℕ) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨pc, regs⟩ = some ⟨target, regs⟩ := by
  unfold isNoopTo at h
  rw [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h1 | h2
  · exact ⟨1, by omega, step_jump h1 regs⟩
  · rcases hp : program pc with _ | _ | _ | mid | _ <;> rw [hp] at h2 <;> try cases h2
    rw [Bool.or_eq_true, beq_iff_eq] at h2
    rcases h2 with h2 | h3
    · exact ⟨2, by omega, regNSteps_bind_eq (step_jump hp regs) (step_jump h2 regs)⟩
    · rcases hm : program mid with _ | _ | _ | mid2 | _ <;> rw [hm] at h3 <;> try cases h3
      rw [beq_iff_eq] at h3
      exact ⟨3, by omega,
        regNSteps_bind_eq (regNSteps_bind_eq (step_jump hp regs) (step_jump hm regs)) (step_jump h3
          regs)⟩

def isReachOrEq (pc target : ℕ) : Bool :=
  (pc == target) || isNoopTo pc target

theorem exec_reach_or_eq {pc target : ℕ} (h : isReachOrEq pc target = true) (regs : List ℕ) :
    ∃ s, regNSteps s ⟨pc, regs⟩ = some ⟨target, regs⟩ := by
  unfold isReachOrEq at h
  rw [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h2
  · exact ⟨0, rfl⟩
  · obtain ⟨s, _, hs⟩ := exec_noop_to h2 regs
    exact ⟨s, hs⟩

def isTransfer1 (base : ℕ) (r : Fin 16) : Bool :=
  (program base == .decr r) &&
  (program (base + 1) == .jump (base + 3)) &&
  (program (base + 2) == .jump base) &&
  (program (base + 3) == .jump (base + 4))

theorem exec_transfer1_aux {base : ℕ} {r : Fin 16}
    (h0 : program base = .decr r)
    (h1 : program (base + 1) = .jump (base + 3))
    (h2 : program (base + 2) = .jump base)
    (h3 : program (base + 3) = .jump (base + 4)) :
    ∀ (v : ℕ) (regs : List ℕ), regs.length = 16 → regs[r.val]! = v →
      ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ = some ⟨base + 4, regs.set r.val 0⟩
  | 0, regs, hlen, hv => by
    have s1 := step_decr_zero h0 regs hv
    have s2 := step_jump h1 regs
    have s3 := step_jump h3 regs
    refine ⟨3, by omega, ?_⟩
    have hste := regNSteps_bind_eq (regNSteps_bind_eq s1 s2) s3
    have hset : regs.set r.val 0 = regs := by regs_eq hlen
    rw [hset]
    exact hste
  | v + 1, regs, hlen, hv => by
    have s1 := step_decr_pos h0 regs hv
    have s2 := step_jump h2 (regs.set r.val v)
    have hlen' : (regs.set r.val v).length = 16 := by simp [hlen]
    have hv' : (regs.set r.val v)[r.val]! = v := by simp [hlen]
    obtain ⟨s, hs, ih⟩ := exec_transfer1_aux h0 h1 h2 h3 v (regs.set r.val v) hlen' hv'
    have hset : (regs.set r.val v).set r.val 0 = regs.set r.val 0 := by regs_eq hlen
    rw [hset] at ih
    exact ⟨2 + s, by omega, regNSteps_bind_eq (regNSteps_bind_eq s1 s2) ih⟩

theorem exec_transfer1 {base : ℕ} {r : Fin 16} (h : isTransfer1 base r = true)
    (regs : List ℕ) (hlen : regs.length = 16) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ = some ⟨base + 4, regs.set r.val 0⟩ := by
  unfold isTransfer1 at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
  exact exec_transfer1_aux h0 h1 h2 h3 regs[r.val]! regs hlen rfl

def isTransfer2 (base : ℕ) (r dst : Fin 16) : Bool :=
  (r != dst) &&
  (program base == .decr r) &&
  (program (base + 1) == .jump (base + 4)) &&
  (program (base + 2) == .incr dst) &&
  (program (base + 3) == .jump base)

theorem exec_transfer2_aux {base : ℕ} {r dst : Fin 16} (hne : r.val ≠ dst.val)
    (h0 : program base = .decr r)
    (h1 : program (base + 1) = .jump (base + 4))
    (h2 : program (base + 2) = .incr dst)
    (h3 : program (base + 3) = .jump base) :
    ∀ (v : ℕ) (regs : List ℕ), regs.length = 16 → regs[r.val]! = v →
      ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
        some ⟨base + 4, (regs.set dst.val (regs[dst.val]! + v)).set r.val 0⟩
  | 0, regs, hlen, hv => by
    have s1 := step_decr_zero h0 regs hv
    have s2 := step_jump h1 regs
    refine ⟨2, by omega, ?_⟩
    have hset : (regs.set dst.val (regs[dst.val]! + 0)).set r.val 0 = regs := by regs_eq hlen
    rw [hset]
    exact regNSteps_bind_eq s1 s2
  | v + 1, regs, hlen, hv => by
    have s1 := step_decr_pos h0 regs hv
    let regs1 := regs.set r.val v
    have s2 := step_incr h2 regs1
    let regs2 := regs1.set dst.val (regs1[dst.val]! + 1)
    have s3 := step_jump h3 regs2
    have hlen2 : regs2.length = 16 := by simp [regs2, regs1, hlen]
    have hv2 : regs2[r.val]! = v := by
      simp only [regs2, regs1, getElem!_set, List.length_set, hlen, r.is_lt, dst.is_lt]
      split_ifs <;> omega
    obtain ⟨s, hs, ih⟩ := exec_transfer2_aux hne h0 h1 h2 h3 v regs2 hlen2 hv2
    have hdst2 : regs2[dst.val]! = regs[dst.val]! + 1 := by
      simp only [regs2, regs1, getElem!_set, List.length_set, hlen, r.is_lt, dst.is_lt]
      split_ifs <;> omega
    have heq : (regs2.set dst.val (regs2[dst.val]! + v)).set r.val 0 =
        (regs.set dst.val (regs[dst.val]! + (v + 1))).set r.val 0 := by
      rw [hdst2]
      dsimp only [regs2, regs1]
      regs_eq hlen
    rw [heq] at ih
    exact ⟨3 + s, by omega, regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq s1 s2) s3) ih⟩

theorem exec_transfer2 {base : ℕ} {r dst : Fin 16} (h : isTransfer2 base r dst = true)
    (regs : List ℕ) (hlen : regs.length = 16) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨base + 4, (regs.set dst.val (regs[dst.val]! + regs[r.val]!)).set r.val 0⟩ := by
  unfold isTransfer2 at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨hne', h0⟩, h1⟩, h2⟩, h3⟩
  have hne : r.val ≠ dst.val := fun heq => hne' (Fin.ext heq)
  exact exec_transfer2_aux hne h0 h1 h2 h3 regs[r.val]! regs hlen rfl

def isTransfer3 (base : ℕ) (r dst1 dst2 : Fin 16) : Bool :=
  (r != dst1) && (r != dst2) && (dst1 != dst2) &&
  (program base == .decr r) &&
  (program (base + 1) == .jump (base + 5)) &&
  (program (base + 2) == .incr dst1) &&
  (program (base + 3) == .incr dst2) &&
  (program (base + 4) == .jump base) &&
  (program (base + 5) == .jump (base + 6)) &&
  (program (base + 6) == .jump (base + 8))

theorem exec_transfer3_aux {base : ℕ} {r dst1 dst2 : Fin 16}
    (hne1 : r.val ≠ dst1.val) (hne2 : r.val ≠ dst2.val) (hne12 : dst1.val ≠ dst2.val)
    (h0 : program base = .decr r)
    (h1 : program (base + 1) = .jump (base + 5))
    (h2 : program (base + 2) = .incr dst1)
    (h3 : program (base + 3) = .incr dst2)
    (h4 : program (base + 4) = .jump base)
    (h5 : program (base + 5) = .jump (base + 6))
    (h6 : program (base + 6) = .jump (base + 8)) :
    ∀ (v : ℕ) (regs : List ℕ), regs.length = 16 → regs[r.val]! = v →
      ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
        some ⟨base + 8,
          ((regs.set dst1.val (regs[dst1.val]! + v)).set dst2.val (regs[dst2.val]! +
            v)).set r.val 0⟩
  | 0, regs, hlen, hv => by
    have s1 := step_decr_zero h0 regs hv
    have s2 := step_jump h1 regs
    have s3 := step_jump h5 regs
    have s4 := step_jump h6 regs
    refine ⟨4, by omega, ?_⟩
    have hset : ((regs.set dst1.val (regs[dst1.val]! + 0)).set dst2.val (regs[dst2.val]! +
        0)).set r.val 0 = regs := by regs_eq hlen
    rw [hset]
    exact regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq s1 s2) s3) s4
  | v + 1, regs, hlen, hv => by
    have s1 := step_decr_pos h0 regs hv
    let regs1 := regs.set r.val v
    have s2 := step_incr h2 regs1
    let regs2 := regs1.set dst1.val (regs1[dst1.val]! + 1)
    have s3 := step_incr h3 regs2
    let regs3 := regs2.set dst2.val (regs2[dst2.val]! + 1)
    have s4 := step_jump h4 regs3
    have hlen3 : regs3.length = 16 := by simp [regs3, regs2, regs1, hlen]
    have hv3 : regs3[r.val]! = v := by
      simp only [regs3, regs2, regs1, getElem!_set, List.length_set, hlen, r.is_lt, dst1.is_lt,
        dst2.is_lt]
      split_ifs <;> omega
    obtain ⟨s, hs, ih⟩ := exec_transfer3_aux hne1 hne2 hne12 h0 h1 h2 h3 h4 h5 h6 v regs3 hlen3 hv3
    have hdst1_3 : regs3[dst1.val]! = regs[dst1.val]! + 1 := by
      simp only [regs3, regs2, regs1, getElem!_set, List.length_set, hlen, r.is_lt, dst1.is_lt,
        dst2.is_lt]
      split_ifs <;> omega
    have hdst2_3 : regs3[dst2.val]! = regs[dst2.val]! + 1 := by
      simp only [regs3, regs2, regs1, getElem!_set, List.length_set, hlen, r.is_lt, dst1.is_lt,
        dst2.is_lt]
      split_ifs <;> omega
    have heq : ((regs3.set dst1.val (regs3[dst1.val]! + v)).set dst2.val (regs3[dst2.val]! +
        v)).set r.val 0 =
        ((regs.set dst1.val (regs[dst1.val]! + (v + 1))).set dst2.val (regs[dst2.val]! + (v +
          1))).set r.val 0 := by
      rw [hdst1_3, hdst2_3]
      dsimp only [regs3, regs2, regs1]
      regs_eq hlen
    rw [heq] at ih
    exact ⟨4 + s, by omega,
      regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq s1 s2) s3) s4) ih⟩

theorem exec_transfer3 {base : ℕ} {r dst1 dst2 : Fin 16} (h : isTransfer3 base r dst1 dst2 = true)
    (regs : List ℕ) (hlen : regs.length = 16) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨base + 8,
        ((regs.set dst1.val (regs[dst1.val]! + regs[r.val]!)).set dst2.val (regs[dst2.val]! +
          regs[r.val]!)).set r.val 0⟩ := by
  unfold isTransfer3 at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hne1', hne2'⟩, hne12'⟩, h0⟩, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
  have hne1 : r.val ≠ dst1.val := fun heq => hne1' (Fin.ext heq)
  have hne2 : r.val ≠ dst2.val := fun heq => hne2' (Fin.ext heq)
  have hne12 : dst1.val ≠ dst2.val := fun heq => hne12' (Fin.ext heq)
  exact exec_transfer3_aux hne1 hne2 hne12 h0 h1 h2 h3 h4 h5 h6 regs[r.val]! regs hlen rfl

def isCopyAdd (base : ℕ) (src dst tmp : Fin 16) : Bool :=
  isTransfer3 base src dst tmp && isTransfer2 (base + 8) tmp src

theorem exec_copy_add {base : ℕ} {src dst tmp : Fin 16} (h : isCopyAdd base src dst tmp = true)
    (regs : List ℕ) (hlen : regs.length = 16) (htmp : regs[tmp.val]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨base + 12, regs.set dst.val (regs[dst.val]! + regs[src.val]!)⟩ := by
  have h' := h
  unfold isCopyAdd at h'
  rw [Bool.and_eq_true] at h'
  obtain ⟨h3, h2⟩ := h'
  have h3_props := h3
  unfold isTransfer3 at h3_props
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h3_props
  rcases h3_props with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hne1', hne2'⟩, hne12'⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩
  have hne1 : src.val ≠ dst.val := fun heq => hne1' (Fin.ext heq)
  have hne2 : src.val ≠ tmp.val := fun heq => hne2' (Fin.ext heq)
  have hne12 : dst.val ≠ tmp.val := fun heq => hne12' (Fin.ext heq)
  obtain ⟨s1, hs1, step1⟩ := exec_transfer3 h3 regs hlen
  let regs1 := ((regs.set dst.val (regs[dst.val]! +
      regs[src.val]!)).set tmp.val (regs[tmp.val]! + regs[src.val]!)).set src.val 0
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  obtain ⟨s2, hs2, step2⟩ := exec_transfer2 h2 regs1 hlen1
  refine ⟨s1 + s2, by omega, ?_⟩
  have hcomb := regNSteps_bind_eq step1 step2
  have heq_pc : base + 8 + 4 = base + 12 := by omega
  have hsrc1 : regs1[src.val]! = 0 := by simp [regs1, hlen]
  have htmp1 : regs1[tmp.val]! = regs[src.val]! := by
    simp only [regs1, getElem!_set, List.length_set, hlen, dst.is_lt, tmp.is_lt, src.is_lt]
    split_ifs <;> omega
  have heq_regs : (regs1.set src.val (regs1[src.val]! + regs1[tmp.val]!)).set tmp.val 0 =
      regs.set dst.val (regs[dst.val]! + regs[src.val]!) := by
    rw [hsrc1, htmp1, Nat.zero_add]
    dsimp only [regs1]
    regs_eq hlen
  rw [heq_pc, heq_regs] at hcomb
  exact hcomb

def isMulLoop (base mid end_pc : ℕ) (cnt src dst tmp : Fin 16) : Bool :=
  (cnt != src) && (cnt != dst) && (cnt != tmp) &&
  (src != dst) && (src != tmp) && (dst != tmp) &&
  (program base == .decr cnt) &&
  (program (base + 1) == .jump end_pc) &&
  isNoopTo (base + 2) mid &&
  isCopyAdd mid src dst tmp &&
  (program (mid + 12) == .jump base)

theorem exec_mul_loop_aux {base mid end_pc : ℕ} {cnt src dst tmp : Fin 16}
    (hcnt_src : cnt.val ≠ src.val) (hcnt_dst : cnt.val ≠ dst.val) (hcnt_tmp : cnt.val ≠ tmp.val)
    (hsrc_dst : src.val ≠ dst.val) (hsrc_tmp : src.val ≠ tmp.val) (hdst_tmp : dst.val ≠ tmp.val)
    (h0 : program base = .decr cnt)
    (h1 : program (base + 1) = .jump end_pc)
    (hnoop : isNoopTo (base + 2) mid = true)
    (hcopy : isCopyAdd mid src dst tmp = true)
    (hback : program (mid + 12) = .jump base) :
    ∀ (v : ℕ) (regs : List ℕ), regs.length = 16 → regs[cnt.val]! = v → regs[tmp.val]! = 0 →
      ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
        some ⟨end_pc, (regs.set dst.val (regs[dst.val]! + v * regs[src.val]!)).set cnt.val 0⟩
  | 0, regs, hlen, hv, htmp => by
    have s1 := step_decr_zero h0 regs hv
    have s2 := step_jump h1 regs
    refine ⟨2, by omega, ?_⟩
    have hset : (regs.set dst.val (regs[dst.val]! + 0 * regs[src.val]!)).set cnt.val 0 = regs := by
      rw [Nat.zero_mul, Nat.add_zero]
      regs_eq hlen
    rw [hset]
    exact regNSteps_bind_eq s1 s2
  | v + 1, regs, hlen, hv, htmp => by
    have s1 := step_decr_pos h0 regs hv
    let regs1 := regs.set cnt.val v
    obtain ⟨sn, hsn, s2⟩ := exec_noop_to hnoop regs1
    have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
    have htmp1 : regs1[tmp.val]! = 0 := by
      simp only [regs1, getElem!_set, hlen, cnt.is_lt]
      split_ifs <;> omega
    obtain ⟨sc, hsc, s3⟩ := exec_copy_add hcopy regs1 hlen1 htmp1
    let regs2 := regs1.set dst.val (regs1[dst.val]! + regs1[src.val]!)
    have s4 := step_jump hback regs2
    have hlen2 : regs2.length = 16 := by simp [regs2, regs1, hlen]
    have hv2 : regs2[cnt.val]! = v := by
      simp only [regs2, regs1, getElem!_set, List.length_set, hlen, cnt.is_lt, dst.is_lt]
      split_ifs <;> omega
    have htmp2 : regs2[tmp.val]! = 0 := by
      simp only [regs2, regs1, getElem!_set, List.length_set, hlen, cnt.is_lt, dst.is_lt]
      split_ifs <;> omega
    obtain ⟨s, hs, ih⟩ := exec_mul_loop_aux
      hcnt_src hcnt_dst hcnt_tmp hsrc_dst hsrc_tmp hdst_tmp
      h0 h1 hnoop hcopy hback v regs2 hlen2 hv2 htmp2
    have hdst2 : regs2[dst.val]! = regs[dst.val]! + regs[src.val]! := by
      simp only [regs2, regs1, getElem!_set, List.length_set, hlen, cnt.is_lt, dst.is_lt]
      split_ifs <;> omega
    have hsrc2 : regs2[src.val]! = regs[src.val]! := by
      simp only [regs2, regs1, getElem!_set, List.length_set, hlen, cnt.is_lt, dst.is_lt]
      split_ifs <;> omega
    have heq : (regs2.set dst.val (regs2[dst.val]! + v * regs2[src.val]!)).set cnt.val 0 =
        (regs.set dst.val (regs[dst.val]! + (v + 1) * regs[src.val]!)).set cnt.val 0 := by
      rw [hdst2, hsrc2]
      dsimp only [regs2, regs1]
      regs_eq hlen
    rw [heq] at ih
    exact ⟨1 + sn + sc + 1 + s, by omega,
      regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq s1 s2) s3) s4) ih⟩

theorem exec_mul_loop {base mid end_pc : ℕ} {cnt src dst tmp : Fin 16}
    (h : isMulLoop base mid end_pc cnt src dst tmp = true)
    (regs : List ℕ) (hlen : regs.length = 16) (htmp : regs[tmp.val]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨end_pc,
        (regs.set dst.val (regs[dst.val]! + regs[cnt.val]! * regs[src.val]!)).set cnt.val 0⟩ := by
  unfold isMulLoop at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩
  exact exec_mul_loop_aux
    (fun e => h1 (Fin.ext e)) (fun e => h2 (Fin.ext e)) (fun e => h3 (Fin.ext e))
    (fun e => h4 (Fin.ext e)) (fun e => h5 (Fin.ext e)) (fun e => h6 (Fin.ext e))
    h7 h8 h9 h10 h11 regs[cnt.val]! regs hlen rfl htmp

def isDecrPair (base tA tB : ℕ) (rA rB : Fin 16) : Bool :=
  (rA != rB) &&
  (program base == .decr rA) &&
  (program (base + 1) == .jump tA) &&
  (program (base + 2) == .decr rB) &&
  (program (base + 3) == .jump tB) &&
  (program (base + 4) == .jump base)

theorem exec_decr_pair_le_aux {base tA : ℕ} {rA rB : Fin 16} (hne : rA.val ≠ rB.val)
    (h0 : program base = .decr rA)
    (h1 : program (base + 1) = .jump tA)
    (h2 : program (base + 2) = .decr rB)
    (h4 : program (base + 4) = .jump base) :
    ∀ (a b : ℕ) (regs : List ℕ), regs.length = 16 → regs[rA.val]! = a → regs[rB.val]! = b → a ≤ b →
      ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
        some ⟨tA, (regs.set rB.val (b - a)).set rA.val 0⟩
  | 0, b, regs, hlen, ha, hb, _ => by
    have s1 := step_decr_zero h0 regs ha
    have s2 := step_jump h1 regs
    refine ⟨2, by omega, ?_⟩
    have hset : (regs.set rB.val (b - 0)).set rA.val 0 = regs := by regs_eq hlen
    rw [hset]
    exact regNSteps_bind_eq s1 s2
  | a + 1, b, regs, hlen, ha, hb, hle => by
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have s1 := step_decr_pos h0 regs ha
    let regs1 := regs.set rA.val a
    have hb1 : regs1[rB.val]! = b' + 1 := by
      simp only [regs1, getElem!_set, hlen, rA.is_lt]
      split_ifs <;> omega
    have s2 := step_decr_pos h2 regs1 hb1
    let regs2 := regs1.set rB.val b'
    have s3 := step_jump h4 regs2
    have hlen2 : regs2.length = 16 := by simp [regs2, regs1, hlen]
    have ha2 : regs2[rA.val]! = a := by
      simp only [regs2, regs1, getElem!_set, List.length_set, hlen, rA.is_lt, rB.is_lt]
      split_ifs <;> omega
    have hb2 : regs2[rB.val]! = b' := by
      simp only [regs2, regs1, getElem!_set, List.length_set, hlen, rA.is_lt, rB.is_lt]
      split_ifs <;> omega
    obtain ⟨s, hs, ih⟩ := exec_decr_pair_le_aux hne h0 h1 h2 h4 a b' regs2 hlen2 ha2 hb2 (by omega)
    have heq : (regs2.set rB.val (b' - a)).set rA.val 0 =
        (regs.set rB.val (b' + 1 - (a + 1))).set rA.val 0 := by
      dsimp only [regs2, regs1]
      regs_eq hlen
    rw [heq] at ih
    exact ⟨3 + s, by omega, regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq s1 s2) s3) ih⟩

theorem exec_decr_pair_le {base tA tB : ℕ} {rA rB : Fin 16}
    (h : isDecrPair base tA tB rA rB = true)
    (regs : List ℕ) (hlen : regs.length = 16) (hle : regs[rA.val]! ≤ regs[rB.val]!) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨tA, (regs.set rB.val (regs[rB.val]! - regs[rA.val]!)).set rA.val 0⟩ := by
  unfold isDecrPair at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hne', h0⟩, h1⟩, h2⟩, _⟩, h4⟩
  exact exec_decr_pair_le_aux (fun e => hne' (Fin.ext e)) h0 h1 h2 h4
    regs[rA.val]! regs[rB.val]! regs hlen rfl rfl hle

theorem exec_decr_pair_gt_aux {base tB : ℕ} {rA rB : Fin 16} (hne : rA.val ≠ rB.val)
    (h0 : program base = .decr rA)
    (h2 : program (base + 2) = .decr rB)
    (h3 : program (base + 3) = .jump tB)
    (h4 : program (base + 4) = .jump base) :
    ∀ (b a : ℕ) (regs : List ℕ), regs.length = 16 → regs[rA.val]! = a → regs[rB.val]! = b → b < a →
      ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
        some ⟨tB, (regs.set rA.val (a - 1 - b)).set rB.val 0⟩
  | 0, a, regs, hlen, ha, hb, hgt => by
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have s1 := step_decr_pos h0 regs ha
    let regs1 := regs.set rA.val a'
    have hb1 : regs1[rB.val]! = 0 := by
      simp only [regs1, getElem!_set, hlen, rA.is_lt]
      split_ifs <;> omega
    have s2 := step_decr_zero h2 regs1 hb1
    have s3 := step_jump h3 regs1
    refine ⟨3, by omega, ?_⟩
    have hset : (regs.set rA.val (a' + 1 - 1 - 0)).set rB.val 0 = regs1 := by
      dsimp only [regs1]
      regs_eq hlen
    rw [hset]
    exact regNSteps_bind_eq (regNSteps_bind_eq s1 s2) s3
  | b + 1, a, regs, hlen, ha, hb, hgt => by
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have s1 := step_decr_pos h0 regs ha
    let regs1 := regs.set rA.val a'
    have hb1 : regs1[rB.val]! = b + 1 := by
      simp only [regs1, getElem!_set, hlen, rA.is_lt]
      split_ifs <;> omega
    have s2 := step_decr_pos h2 regs1 hb1
    let regs2 := regs1.set rB.val b
    have s3 := step_jump h4 regs2
    have hlen2 : regs2.length = 16 := by simp [regs2, regs1, hlen]
    have ha2 : regs2[rA.val]! = a' := by
      simp only [regs2, regs1, getElem!_set, List.length_set, hlen, rA.is_lt, rB.is_lt]
      split_ifs <;> omega
    have hb2 : regs2[rB.val]! = b := by
      simp only [regs2, regs1, getElem!_set, List.length_set, hlen, rA.is_lt, rB.is_lt]
      split_ifs <;> omega
    obtain ⟨s, hs, ih⟩ := exec_decr_pair_gt_aux hne h0 h2 h3 h4 b a' regs2 hlen2 ha2 hb2 (by omega)
    have heq : (regs2.set rA.val (a' - 1 - b)).set rB.val 0 =
        (regs.set rA.val (a' + 1 - 1 - (b + 1))).set rB.val 0 := by
      dsimp only [regs2, regs1]
      regs_eq hlen
    rw [heq] at ih
    exact ⟨3 + s, by omega, regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq s1 s2) s3) ih⟩

theorem exec_decr_pair_gt {base tA tB : ℕ} {rA rB : Fin 16}
    (h : isDecrPair base tA tB rA rB = true)
    (regs : List ℕ) (hlen : regs.length = 16) (hgt : regs[rB.val]! < regs[rA.val]!) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨tB, (regs.set rA.val (regs[rA.val]! - 1 - regs[rB.val]!)).set rB.val 0⟩ := by
  unfold isDecrPair at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hne', h0⟩, _⟩, h2⟩, h3⟩, h4⟩
  exact exec_decr_pair_gt_aux (fun e => hne' (Fin.ext e)) h0 h2 h3 h4
    regs[rB.val]! regs[rA.val]! regs hlen rfl rfl hgt

def isDivLoop (base : ℕ) (div_reg cnt_reg rem_reg quot_reg tmp_reg : Fin 16) : Bool :=
  (div_reg != cnt_reg) && (div_reg != rem_reg) && (div_reg != quot_reg) && (div_reg != tmp_reg) &&
  (cnt_reg != rem_reg) && (cnt_reg != quot_reg) && (cnt_reg != tmp_reg) &&
  (rem_reg != quot_reg) && (rem_reg != tmp_reg) && (quot_reg != tmp_reg) &&
  (program base == .jump (base + 4)) &&
  isCopyAdd (base + 4) div_reg cnt_reg tmp_reg &&
  isDecrPair (base + 16) (base + 21) (base + 23) cnt_reg rem_reg &&
  (program (base + 21) == .incr quot_reg) &&
  (program (base + 22) == .jump base) &&
  (program (base + 23) == .jump (base + 24)) &&
  isTransfer1 (base + 24) cnt_reg

set_option maxHeartbeats 800000 in -- large decide / symbolic evaluation
theorem exec_div_loop_aux {base : ℕ} {div_reg cnt_reg rem_reg quot_reg tmp_reg : Fin 16}
    (_h1 : div_reg.val ≠ cnt_reg.val) (h2 : div_reg.val ≠ rem_reg.val)
    (h3 : div_reg.val ≠ quot_reg.val) (h4 : div_reg.val ≠ tmp_reg.val)
    (h5 : cnt_reg.val ≠ rem_reg.val) (h6 : cnt_reg.val ≠ quot_reg.val)
    (h7 : cnt_reg.val ≠ tmp_reg.val) (h8 : rem_reg.val ≠ quot_reg.val)
    (h9 : rem_reg.val ≠ tmp_reg.val) (h10 : quot_reg.val ≠ tmp_reg.val)
    (hj0 : program base = .jump (base + 4))
    (hcopy : isCopyAdd (base + 4) div_reg cnt_reg tmp_reg = true)
    (hpair : isDecrPair (base + 16) (base + 21) (base + 23) cnt_reg rem_reg = true)
    (hincr : program (base + 21) = .incr quot_reg)
    (hback : program (base + 22) = .jump base)
    (hj23 : program (base + 23) = .jump (base + 24))
    (htr1 : isTransfer1 (base + 24) cnt_reg = true)
    (rem : ℕ) :
    ∀ (regs : List ℕ), regs.length = 16 →
      0 < regs[div_reg.val]! → regs[rem_reg.val]! = rem →
      regs[cnt_reg.val]! = 0 → regs[tmp_reg.val]! = 0 →
      ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
        some ⟨base + 28,
          (regs.set quot_reg.val (regs[quot_reg.val]! +
            rem / regs[div_reg.val]!)).set rem_reg.val 0⟩ := by
  induction rem using Nat.strongRecOn with
  | ind rem ih =>
    intro regs hlen hdiv_pos hrem hcnt htmp
    set d := regs[div_reg.val]!
    have s1 := step_jump hj0 regs
    obtain ⟨sc, hsc, s2⟩ := exec_copy_add hcopy regs hlen htmp
    let regs1 := regs.set cnt_reg.val (regs[cnt_reg.val]! + d)
    have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
    have hcnt1 : regs1[cnt_reg.val]! = d := by
      simp only [regs1, d, getElem!_set, hlen, cnt_reg.is_lt]
      split_ifs <;> omega
    have hrem1 : regs1[rem_reg.val]! = rem := by
      simp only [regs1, getElem!_set, hlen, cnt_reg.is_lt]
      split_ifs <;> omega
    by_cases hlt : rem < d
    · have hgt1 : regs1[rem_reg.val]! < regs1[cnt_reg.val]! := by omega
      obtain ⟨sp, hsp, s3⟩ := exec_decr_pair_gt hpair regs1 hlen1 hgt1
      let regs2 := (regs1.set cnt_reg.val (regs1[cnt_reg.val]! - 1 -
          regs1[rem_reg.val]!)).set rem_reg.val 0
      have s4 := step_jump hj23 regs2
      have hlen2 : regs2.length = 16 := by simp [regs2, regs1, hlen]
      obtain ⟨st, hst, s5⟩ := exec_transfer1 htr1 regs2 hlen2
      have hdiv_zero : rem / d = 0 := Nat.div_eq_of_lt hlt
      have heq_pc : base + 24 + 4 = base + 28 := by omega
      have heq_regs : regs2.set cnt_reg.val 0 =
          (regs.set quot_reg.val (regs[quot_reg.val]! + rem / d)).set rem_reg.val 0 := by
        rw [hdiv_zero, Nat.add_zero]
        dsimp only [regs2, regs1]
        regs_eq hlen
      rw [heq_pc, heq_regs] at s5
      exact ⟨1 + sc + sp + 1 + st, by omega,
        regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq s1 s2) s3) s4)
          s5⟩
    · have hle : d ≤ rem := Nat.le_of_not_lt hlt
      have hle1 : regs1[cnt_reg.val]! ≤ regs1[rem_reg.val]! := by omega
      obtain ⟨sp, hsp, s3⟩ := exec_decr_pair_le hpair regs1 hlen1 hle1
      let regs2 := regs.set rem_reg.val (rem - d)
      have hregs2 : (regs1.set rem_reg.val (regs1[rem_reg.val]! -
          regs1[cnt_reg.val]!)).set cnt_reg.val 0 = regs2 := by
        rw [hrem1, hcnt1]
        dsimp only [regs2, regs1]
        regs_eq hlen
      rw [hregs2] at s3
      have s4 := step_incr hincr regs2
      let regs3 := (regs.set rem_reg.val (rem - d)).set quot_reg.val (regs[quot_reg.val]! + 1)
      have hquot2 : regs2[quot_reg.val]! = regs[quot_reg.val]! := by
        simp only [regs2, getElem!_set, hlen, rem_reg.is_lt]
        split_ifs <;> omega
      have hregs3 : regs2.set quot_reg.val (regs2[quot_reg.val]! + 1) = regs3 := by
        rw [hquot2]
      rw [hregs3] at s4
      have s5 := step_jump hback regs3
      have hlen3 : regs3.length = 16 := by simp [regs3, hlen]
      have hdiv3 : regs3[div_reg.val]! = d := by
        simp only [regs3, d, getElem!_set, List.length_set, hlen, rem_reg.is_lt, quot_reg.is_lt]
        split_ifs <;> omega
      have hrem3 : regs3[rem_reg.val]! = rem - d := by
        simp only [regs3, getElem!_set, List.length_set, hlen, rem_reg.is_lt, quot_reg.is_lt]
        split_ifs <;> omega
      have hcnt3 : regs3[cnt_reg.val]! = 0 := by
        simp only [regs3, getElem!_set, List.length_set, hlen, rem_reg.is_lt, quot_reg.is_lt]
        split_ifs <;> omega
      have htmp3 : regs3[tmp_reg.val]! = 0 := by
        simp only [regs3, getElem!_set, List.length_set, hlen, rem_reg.is_lt, quot_reg.is_lt]
        split_ifs <;> omega
      have hquot3 : regs3[quot_reg.val]! = regs[quot_reg.val]! + 1 := by
        simp only [regs3, getElem!_set, List.length_set, hlen, rem_reg.is_lt, quot_reg.is_lt]
        split_ifs <;> omega
      have hdiv_pos3 : 0 < regs3[div_reg.val]! := by omega
      obtain ⟨s_ih, hs_ih, step_ih⟩ :=
          ih (rem - d) (by omega) regs3 hlen3 hdiv_pos3 hrem3 hcnt3 htmp3
      have hdiv_eq : rem / d = (rem - d) / d + 1 := Nat.div_eq_sub_div hdiv_pos hle
      have heq_regs : (regs3.set quot_reg.val (regs3[quot_reg.val]! +
          (rem - d) / regs3[div_reg.val]!)).set rem_reg.val 0 =
          (regs.set quot_reg.val (regs[quot_reg.val]! + rem / d)).set rem_reg.val 0 := by
        rw [hquot3, hdiv3, hdiv_eq]
        dsimp only [regs3]
        regs_eq hlen
      rw [heq_regs] at step_ih
      exact ⟨1 + sc + sp + 1 + 1 + s_ih, by omega,
        regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
          (regNSteps_bind_eq s1 s2) s3) s4) s5) step_ih⟩

theorem exec_div_loop {base : ℕ} {div_reg cnt_reg rem_reg quot_reg tmp_reg : Fin 16}
    (h : isDivLoop base div_reg cnt_reg rem_reg quot_reg tmp_reg = true)
    (regs : List ℕ) (hlen : regs.length = 16)
    (hdiv_pos : 0 < regs[div_reg.val]!)
    (hcnt : regs[cnt_reg.val]! = 0) (htmp : regs[tmp_reg.val]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨base + 28,
        (regs.set quot_reg.val (regs[quot_reg.val]! +
          regs[rem_reg.val]! / regs[div_reg.val]!)).set rem_reg.val 0⟩ := by
  unfold isDivLoop at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, hj0⟩, hcopy⟩,
      hpair⟩, hincr⟩, hback⟩, hj23⟩, htr1⟩
  exact exec_div_loop_aux
    (fun e => h1 (Fin.ext e)) (fun e => h2 (Fin.ext e)) (fun e => h3 (Fin.ext e))
    (fun e => h4 (Fin.ext e)) (fun e => h5 (Fin.ext e)) (fun e => h6 (Fin.ext e))
    (fun e => h7 (Fin.ext e)) (fun e => h8 (Fin.ext e)) (fun e => h9 (Fin.ext e))
    (fun e => h10 (Fin.ext e))
    hj0 hcopy hpair hincr hback hj23 htr1 regs[rem_reg.val]! regs hlen hdiv_pos rfl hcnt htmp

def isSubLoop (base : ℕ) (rA rB : Fin 16) : Bool :=
  (rA != rB) &&
  (program base == .decr rA) &&
  (program (base + 1) == .jump (base + 5)) &&
  (program (base + 2) == .decr rB) &&
  (program (base + 3) == .jump (base + 4)) &&
  (program (base + 4) == .jump base)

theorem exec_sub_loop_aux {base : ℕ} {rA rB : Fin 16} (hne : rA.val ≠ rB.val)
    (h0 : program base = .decr rA)
    (h1 : program (base + 1) = .jump (base + 5))
    (h2 : program (base + 2) = .decr rB)
    (h3 : program (base + 3) = .jump (base + 4))
    (h4 : program (base + 4) = .jump base) :
    ∀ (a : ℕ) (regs : List ℕ), regs.length = 16 → regs[rA.val]! = a →
      ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
        some ⟨base + 5, (regs.set rB.val (regs[rB.val]! - a)).set rA.val 0⟩
  | 0, regs, hlen, ha => by
    have s1 := step_decr_zero h0 regs ha
    have s2 := step_jump h1 regs
    refine ⟨2, by omega, ?_⟩
    have hset : (regs.set rB.val (regs[rB.val]! - 0)).set rA.val 0 = regs := by regs_eq hlen
    rw [hset]
    exact regNSteps_bind_eq s1 s2
  | a + 1, regs, hlen, ha => by
    have s1 := step_decr_pos h0 regs ha
    let regs1 := regs.set rA.val a
    have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
    rcases hb : regs[rB.val]! with _ | b
    · have hb1 : regs1[rB.val]! = 0 := by
        simp only [regs1, getElem!_set, hlen, rA.is_lt]
        split_ifs <;> omega
      have s2 := step_decr_zero h2 regs1 hb1
      have s3 := step_jump h3 regs1
      have s4 := step_jump h4 regs1
      have ha1 : regs1[rA.val]! = a := by simp [regs1, hlen]
      obtain ⟨s, hs, ih⟩ := exec_sub_loop_aux hne h0 h1 h2 h3 h4 a regs1 hlen1 ha1
      have heq : (regs1.set rB.val (regs1[rB.val]! - a)).set rA.val 0 =
          (regs.set rB.val (0 - (a + 1))).set rA.val 0 := by
        rw [hb1]
        dsimp only [regs1]
        regs_eq hlen
      rw [heq] at ih
      exact ⟨4 + s, by omega,
        regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq s1 s2) s3) s4)
          ih⟩
    · have hb1 : regs1[rB.val]! = b + 1 := by
        simp only [regs1, getElem!_set, hlen, rA.is_lt]
        split_ifs <;> omega
      have s2 := step_decr_pos h2 regs1 hb1
      let regs2 := regs1.set rB.val b
      have s3 := step_jump h4 regs2
      have hlen2 : regs2.length = 16 := by simp [regs2, regs1, hlen]
      have ha2 : regs2[rA.val]! = a := by
        simp only [regs2, regs1, getElem!_set, List.length_set, hlen, rA.is_lt, rB.is_lt]
        split_ifs <;> omega
      obtain ⟨s, hs, ih⟩ := exec_sub_loop_aux hne h0 h1 h2 h3 h4 a regs2 hlen2 ha2
      have hb2 : regs2[rB.val]! = b := by
        simp only [regs2, regs1, getElem!_set, List.length_set, hlen, rA.is_lt, rB.is_lt]
        split_ifs <;> omega
      have heq : (regs2.set rB.val (regs2[rB.val]! - a)).set rA.val 0 =
          (regs.set rB.val (b + 1 - (a + 1))).set rA.val 0 := by
        rw [hb2]
        dsimp only [regs2, regs1]
        regs_eq hlen
      rw [heq] at ih
      exact ⟨3 + s, by omega,
        regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq s1 s2) s3) ih⟩

theorem exec_sub_loop {base : ℕ} {rA rB : Fin 16} (h : isSubLoop base rA rB = true)
    (regs : List ℕ) (hlen : regs.length = 16) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨base + 5, (regs.set rB.val (regs[rB.val]! - regs[rA.val]!)).set rA.val 0⟩ := by
  unfold isSubLoop at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨hne', h0⟩, h1⟩, h2⟩, h3⟩, h4⟩
  exact exec_sub_loop_aux (fun e => hne' (Fin.ext e)) h0 h1 h2 h3 h4 regs[rA.val]! regs hlen rfl

/-!
## 4. Comparison Gadgets (`isCmpBranch`, `isLeBranch`), `isSquareAssign`, and Unrolled `x > 253`
-/

def isCmpBranch (base eq_pc lt_pc gt_pc : ℕ) (rA rB : Fin 16) : Bool :=
  isDecrPair base (base + 5) (base + 12) rA rB &&
  (program (base + 5) == .decr rB) &&
  (program (base + 6) == .jump eq_pc) &&
  isTransfer1 (base + 7) rB &&
  (program (base + 11) == .jump lt_pc) &&
  isNoopTo (base + 12) (base + 15) &&
  isTransfer1 (base + 15) rA &&
  isReachOrEq (base + 19) gt_pc

theorem exec_cmp_branch_eq {base eq_pc lt_pc gt_pc : ℕ} {rA rB : Fin 16}
    (h : isCmpBranch base eq_pc lt_pc gt_pc rA rB = true)
    (regs : List ℕ) (hlen : regs.length = 16) (heq : regs[rA.val]! = regs[rB.val]!) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨eq_pc, (regs.set rB.val 0).set rA.val 0⟩ := by
  unfold isCmpBranch at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hpair, h5⟩, h6⟩, _⟩, _⟩, _⟩, _⟩, _⟩
  obtain ⟨s1, hs1, step1⟩ := exec_decr_pair_le hpair regs hlen (by omega)
  let regs1 := (regs.set rB.val 0).set rA.val 0
  have hsub : regs[rB.val]! - regs[rA.val]! = 0 := by omega
  rw [hsub] at step1
  have hb1 : regs1[rB.val]! = 0 := by
    simp only [regs1, getElem!_set, List.length_set, hlen, rA.is_lt, rB.is_lt]
    split_ifs <;> omega
  have step2 := step_decr_zero h5 regs1 hb1
  have step3 := step_jump h6 regs1
  exact ⟨s1 + 1 + 1, by omega, regNSteps_bind_eq (regNSteps_bind_eq step1 step2) step3⟩

theorem exec_cmp_branch_lt {base eq_pc lt_pc gt_pc : ℕ} {rA rB : Fin 16}
    (h : isCmpBranch base eq_pc lt_pc gt_pc rA rB = true)
    (regs : List ℕ) (hlen : regs.length = 16) (hlt : regs[rA.val]! < regs[rB.val]!) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨lt_pc, (regs.set rB.val 0).set rA.val 0⟩ := by
  unfold isCmpBranch at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hpair, h5⟩, _⟩, htrB⟩, h11⟩, _⟩, _⟩, _⟩
  have hne : rA.val ≠ rB.val := by
    intro e
    rw [e] at hlt
    omega
  obtain ⟨s1, hs1, step1⟩ := exec_decr_pair_le hpair regs hlen (by omega)
  let regs1 := (regs.set rB.val (regs[rB.val]! - regs[rA.val]!)).set rA.val 0
  have hb1 : regs1[rB.val]! = (regs[rB.val]! - regs[rA.val]! - 1) + 1 := by
    simp only [regs1, getElem!_set, List.length_set, hlen, rA.is_lt, rB.is_lt]
    split_ifs <;> omega
  have step2 := step_decr_pos h5 regs1 hb1
  let regs2 := regs1.set rB.val (regs[rB.val]! - regs[rA.val]! - 1)
  have hlen2 : regs2.length = 16 := by simp [regs2, regs1, hlen]
  obtain ⟨s3, hs3, step3⟩ := exec_transfer1 htrB regs2 hlen2
  have heq_pc : base + 7 + 4 = base + 11 := by omega
  have heq_regs : regs2.set rB.val 0 = (regs.set rB.val 0).set rA.val 0 := by
    dsimp only [regs2, regs1]
    regs_eq hlen
  rw [heq_pc, heq_regs] at step3
  have step4 := step_jump h11 ((regs.set rB.val 0).set rA.val 0)
  exact ⟨s1 + 1 + s3 + 1, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq step1 step2) step3) step4⟩

theorem exec_cmp_branch_gt {base eq_pc lt_pc gt_pc : ℕ} {rA rB : Fin 16}
    (h : isCmpBranch base eq_pc lt_pc gt_pc rA rB = true)
    (regs : List ℕ) (hlen : regs.length = 16) (hgt : regs[rB.val]! < regs[rA.val]!) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨gt_pc, (regs.set rB.val 0).set rA.val 0⟩ := by
  unfold isCmpBranch at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hpair, _⟩, _⟩, _⟩, _⟩, hnoop⟩, htrA⟩, hreach⟩
  have hne : rA.val ≠ rB.val := by
    intro e
    rw [e] at hgt
    omega
  obtain ⟨s1, hs1, step1⟩ := exec_decr_pair_gt hpair regs hlen hgt
  let regs1 := (regs.set rA.val (regs[rA.val]! - 1 - regs[rB.val]!)).set rB.val 0
  obtain ⟨s2, hs2, step2⟩ := exec_noop_to hnoop regs1
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  obtain ⟨s3, hs3, step3⟩ := exec_transfer1 htrA regs1 hlen1
  have heq_pc : base + 15 + 4 = base + 19 := by omega
  have heq_regs : regs1.set rA.val 0 = (regs.set rB.val 0).set rA.val 0 := by
    dsimp only [regs1]
    regs_eq hlen
  rw [heq_pc, heq_regs] at step3
  obtain ⟨s4, step4⟩ := exec_reach_or_eq hreach ((regs.set rB.val 0).set rA.val 0)
  exact ⟨s1 + s2 + s3 + s4, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq step1 step2) step3) step4⟩

theorem exec_cmp_branch_ne {base eq_pc neq_pc : ℕ} {rA rB : Fin 16}
    (h : isCmpBranch base eq_pc neq_pc neq_pc rA rB = true)
    (regs : List ℕ) (hlen : regs.length = 16) (hne : regs[rA.val]! ≠ regs[rB.val]!) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨neq_pc, (regs.set rB.val 0).set rA.val 0⟩ := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact exec_cmp_branch_lt h regs hlen hlt
  · exact exec_cmp_branch_gt h regs hlen hgt

def isLeBranch (base gt_pc : ℕ) (rA rB : Fin 16) : Bool :=
  isDecrPair base (base + 5) (base + 13) rA rB &&
  (program (base + 5) == .decr rB) &&
  (program (base + 6) == .jump (base + 20)) &&
  (program (base + 7) == .jump (base + 8)) &&
  isTransfer1 (base + 8) rB &&
  (program (base + 12) == .jump gt_pc) &&
  isNoopTo (base + 13) (base + 16) &&
  isTransfer1 (base + 16) rA

theorem exec_le_branch_le {base gt_pc : ℕ} {rA rB : Fin 16}
    (h : isLeBranch base gt_pc rA rB = true)
    (regs : List ℕ) (hlen : regs.length = 16) (hle : regs[rB.val]! ≤ regs[rA.val]!) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨base + 20, (regs.set rB.val 0).set rA.val 0⟩ := by
  unfold isLeBranch at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hpair, h5⟩, h6⟩, _⟩, _⟩, _⟩, hnoop⟩, htrA⟩
  by_cases heq : regs[rB.val]! = regs[rA.val]!
  · obtain ⟨s1, hs1, step1⟩ := exec_decr_pair_le hpair regs hlen (by omega)
    let regs1 := (regs.set rB.val 0).set rA.val 0
    have hsub : regs[rB.val]! - regs[rA.val]! = 0 := by omega
    rw [hsub] at step1
    have hb1 : regs1[rB.val]! = 0 := by
      simp only [regs1, getElem!_set, List.length_set, hlen, rA.is_lt, rB.is_lt]
      split_ifs <;> omega
    have step2 := step_decr_zero h5 regs1 hb1
    have step3 := step_jump h6 regs1
    exact ⟨s1 + 1 + 1, by omega, regNSteps_bind_eq (regNSteps_bind_eq step1 step2) step3⟩
  · have hgt : regs[rB.val]! < regs[rA.val]! := by omega
    have hne : rA.val ≠ rB.val := by intro e; rw [e] at hgt; omega
    obtain ⟨s1, hs1, step1⟩ := exec_decr_pair_gt hpair regs hlen hgt
    let regs1 := (regs.set rA.val (regs[rA.val]! - 1 - regs[rB.val]!)).set rB.val 0
    obtain ⟨s2, hs2, step2⟩ := exec_noop_to hnoop regs1
    have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
    obtain ⟨s3, hs3, step3⟩ := exec_transfer1 htrA regs1 hlen1
    have heq_pc : base + 16 + 4 = base + 20 := by omega
    have heq_regs : regs1.set rA.val 0 = (regs.set rB.val 0).set rA.val 0 := by
      dsimp only [regs1]
      regs_eq hlen
    rw [heq_pc, heq_regs] at step3
    exact ⟨s1 + s2 + s3, by omega, regNSteps_bind_eq (regNSteps_bind_eq step1 step2) step3⟩

theorem exec_le_branch_gt {base gt_pc : ℕ} {rA rB : Fin 16}
    (h : isLeBranch base gt_pc rA rB = true)
    (regs : List ℕ) (hlen : regs.length = 16) (hgt : regs[rA.val]! < regs[rB.val]!) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨gt_pc, (regs.set rB.val 0).set rA.val 0⟩ := by
  unfold isLeBranch at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨hpair, h5⟩, _⟩, h7⟩, htrB⟩, h12⟩, _⟩, _⟩
  have hne : rA.val ≠ rB.val := by intro e; rw [e] at hgt; omega
  obtain ⟨s1, hs1, step1⟩ := exec_decr_pair_le hpair regs hlen (by omega)
  let regs1 := (regs.set rB.val (regs[rB.val]! - regs[rA.val]!)).set rA.val 0
  have hb1 : regs1[rB.val]! = (regs[rB.val]! - regs[rA.val]! - 1) + 1 := by
    simp only [regs1, getElem!_set, List.length_set, hlen, rA.is_lt, rB.is_lt]
    split_ifs <;> omega
  have step2 := step_decr_pos h5 regs1 hb1
  let regs2 := regs1.set rB.val (regs[rB.val]! - regs[rA.val]! - 1)
  have step3 := step_jump h7 regs2
  have hlen2 : regs2.length = 16 := by simp [regs2, regs1, hlen]
  obtain ⟨s4, hs4, step4⟩ := exec_transfer1 htrB regs2 hlen2
  have heq_pc : base + 8 + 4 = base + 12 := by omega
  have heq_regs : regs2.set rB.val 0 = (regs.set rB.val 0).set rA.val 0 := by
    dsimp only [regs2, regs1]
    regs_eq hlen
  rw [heq_pc, heq_regs] at step4
  have step5 := step_jump h12 ((regs.set rB.val 0).set rA.val 0)
  exact ⟨s1 + 1 + 1 + s4 + 1, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq step1 step2) step3)
      step4) step5⟩

def isSquareAssign (base : ℕ) (src dst sCnt sProd sTmp : Fin 16) : Bool :=
  (src != sCnt) && (src != sProd) && (src != sTmp) &&
  (dst != sCnt) && (dst != sProd) && (dst != sTmp) &&
  (sCnt != sProd) && (sCnt != sTmp) && (sProd != sTmp) &&
  isCopyAdd base src sCnt sTmp &&
  isMulLoop (base + 12) (base + 16) (base + 29) sCnt src sProd sTmp &&
  isNoopTo (base + 29) (base + 32) &&
  isTransfer1 (base + 32) dst &&
  isTransfer2 (base + 36) sProd dst

theorem exec_square_assign {base : ℕ} {src dst sCnt sProd sTmp : Fin 16}
    (h : isSquareAssign base src dst sCnt sProd sTmp = true)
    (regs : List ℕ) (hlen : regs.length = 16)
    (hCnt : regs[sCnt.val]! = 0) (hProd : regs[sProd.val]! = 0) (hTmp : regs[sTmp.val]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨base, regs⟩ =
      some ⟨base + 40, regs.set dst.val (regs[src.val]! * regs[src.val]!)⟩ := by
  unfold isSquareAssign at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1', h2'⟩, _h3'⟩, _h4'⟩, h5'⟩, _h6'⟩, h7'⟩, h8'⟩, _h9'⟩, hcopy⟩,
      hmul⟩, hnoop⟩, htr1⟩, htr2⟩
  have h1 : src.val ≠ sCnt.val := fun e => h1' (Fin.ext e)
  have h2 : src.val ≠ sProd.val := fun e => h2' (Fin.ext e)
  have h5 : dst.val ≠ sProd.val := fun e => h5' (Fin.ext e)
  have h7 : sCnt.val ≠ sProd.val := fun e => h7' (Fin.ext e)
  have h8 : sCnt.val ≠ sTmp.val := fun e => h8' (Fin.ext e)
  obtain ⟨s1, hs1, step1⟩ := exec_copy_add hcopy regs hlen hTmp
  let regs1 := regs.set sCnt.val (regs[sCnt.val]! + regs[src.val]!)
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have hTmp1 : regs1[sTmp.val]! = 0 := by
    simp only [regs1, getElem!_set, hlen, sCnt.is_lt]
    split_ifs <;> omega
  obtain ⟨s2, hs2, step2⟩ := exec_mul_loop hmul regs1 hlen1 hTmp1
  let regs2 := (regs1.set sProd.val (regs1[sProd.val]! +
      regs1[sCnt.val]! * regs1[src.val]!)).set sCnt.val 0
  obtain ⟨s3, hs3, step3⟩ := exec_noop_to hnoop regs2
  have hlen2 : regs2.length = 16 := by simp [regs2, regs1, hlen]
  obtain ⟨s4, hs4, step4⟩ := exec_transfer1 htr1 regs2 hlen2
  let regs3 := regs2.set dst.val 0
  have hlen3 : regs3.length = 16 := by simp [regs3, regs2, regs1, hlen]
  obtain ⟨s5, hs5, step5⟩ := exec_transfer2 htr2 regs3 hlen3
  have heq_pc : base + 36 + 4 = base + 40 := by omega
  have hCnt1 : regs1[sCnt.val]! = regs[src.val]! := by
    simp only [regs1, getElem!_set, hlen, sCnt.is_lt]
    split_ifs <;> omega
  have hProd1 : regs1[sProd.val]! = 0 := by
    simp only [regs1, getElem!_set, hlen, sCnt.is_lt]
    split_ifs <;> omega
  have hSrc1 : regs1[src.val]! = regs[src.val]! := by
    simp only [regs1, getElem!_set, hlen, sCnt.is_lt]
    split_ifs <;> omega
  have hDst3 : regs3[dst.val]! = 0 := by simp [regs3, hlen2]
  have hProd3 : regs3[sProd.val]! = regs[src.val]! * regs[src.val]! := by
    simp only [regs3, regs2, hProd1, hCnt1, hSrc1, Nat.zero_add, getElem!_set, List.length_set,
      hlen1,
      sProd.is_lt, sCnt.is_lt, dst.is_lt]
    split_ifs <;> omega
  have heq_regs : (regs3.set dst.val (regs3[dst.val]! + regs3[sProd.val]!)).set sProd.val 0 =
      regs.set dst.val (regs[src.val]! * regs[src.val]!) := by
    rw [hDst3, hProd3, Nat.zero_add]
    dsimp only [regs3, regs2, regs1]
    regs_eq hlen
  rw [heq_pc, heq_regs] at step5
  exact ⟨s1 + s2 + s3 + s4 + s5, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq step1 step2) step3)
      step4) step5⟩

def checkUnrolled254 : ℕ → Bool
  | 0 => true
  | k + 1 =>
    (program (268 + 2 * k) == .decr 2) &&
    (program (268 + 2 * k + 1) == .jump 21) &&
    checkUnrolled254 k

set_option maxRecDepth 20000 in
theorem checkUnrolled254_true : checkUnrolled254 254 = true := by decide

theorem checkUnrolled254_get :
    ∀ (n k : ℕ), k < n → checkUnrolled254 n = true →
      program (268 + 2 * k) = .decr 2 ∧ program (268 + 2 * k + 1) = .jump 21
  | 0, _, hk, _ => by omega
  | n + 1, k, hk, h => by
    unfold checkUnrolled254 at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨h1, h2⟩, h3⟩
    by_cases heq : k = n
    · subst heq; exact ⟨h1, h2⟩
    · exact checkUnrolled254_get n k (by omega) h3

theorem program_unrolled_254 {k : ℕ} (hk : k < 254) :
    program (268 + 2 * k) = .decr 2 ∧ program (268 + 2 * k + 1) = .jump 21 :=
  checkUnrolled254_get 254 k hk checkUnrolled254_true

theorem exec_unrolled_ge :
    ∀ (m : ℕ), m ≤ 254 → ∀ (v : ℕ) (regs : List ℕ), regs.length = 16 → m ≤ v →
      ∃ s, regNSteps s ⟨268 + 2 * (254 - m), regs.set 2 v⟩ =
        some ⟨776, regs.set 2 (v - m)⟩
  | 0, _, v, regs, _, _ => ⟨0, rfl⟩
  | m + 1, hm, v, regs, hlen, hmv => by
    obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
    have hk : 254 - (m + 1) < 254 := by omega
    have ⟨hdecr, _⟩ := program_unrolled_254 hk
    have hv : (regs.set 2 (v' + 1))[(2 : Fin 16).val]! = v' + 1 := by reg_val hlen
    have s1 := step_decr_pos hdecr (regs.set 2 (v' + 1)) hv
    have hpc : 268 + 2 * (254 - (m + 1)) + 2 = 268 + 2 * (254 - m) := by omega
    have hset : (regs.set 2 (v' + 1)).set (2 : Fin 16).val v' = regs.set 2 v' := by
      change (regs.set (2 : Fin 16).val (v' + 1)).set (2 : Fin 16).val v' =
        regs.set (2 : Fin 16).val v'
      regs_eq hlen
    rw [hpc, hset] at s1
    obtain ⟨s2, step2⟩ := exec_unrolled_ge m (by omega) v' regs hlen (by omega)
    have hsub : v' - m = v' + 1 - (m + 1) := by omega
    rw [hsub] at step2
    exact ⟨1 + s2, regNSteps_bind_eq s1 step2⟩

theorem exec_unrolled_lt :
    ∀ (m : ℕ), m ≤ 254 → ∀ (v : ℕ) (regs : List ℕ), regs.length = 16 → regs[2]! = 0 → v < m →
      ∃ s, 1 ≤ s ∧ regNSteps s ⟨268 + 2 * (254 - m), regs.set 2 v⟩ =
        some ⟨21, regs⟩
  | 0, _, _, _, _, _, hlt => by omega
  | m + 1, _, 0, regs, hlen, hz2, _ => by
    have hk : 254 - (m + 1) < 254 := by omega
    have ⟨hdecr, hjump⟩ := program_unrolled_254 hk
    have hset0 : regs.set 2 0 = regs := by
      change regs.set (2 : Fin 16).val 0 = regs
      regs_eq hlen
    rw [hset0]
    have s1 := step_decr_zero hdecr regs hz2
    have s2 := step_jump hjump regs
    exact ⟨2, by omega, regNSteps_bind_eq s1 s2⟩
  | m + 1, hm, v + 1, regs, hlen, hz2, hlt => by
    have hk : 254 - (m + 1) < 254 := by omega
    have ⟨hdecr, _⟩ := program_unrolled_254 hk
    have hv : (regs.set 2 (v + 1))[(2 : Fin 16).val]! = v + 1 := by reg_val hlen
    have s1 := step_decr_pos hdecr (regs.set 2 (v + 1)) hv
    have hpc : 268 + 2 * (254 - (m + 1)) + 2 = 268 + 2 * (254 - m) := by omega
    have hset : (regs.set 2 (v + 1)).set (2 : Fin 16).val v = regs.set 2 v := by
      change (regs.set (2 : Fin 16).val (v + 1)).set (2 : Fin 16).val v =
        regs.set (2 : Fin 16).val v
      regs_eq hlen
    rw [hpc, hset] at s1
    obtain ⟨s2, hs2, step2⟩ := exec_unrolled_lt m (by omega) v regs hlen hz2 (by omega)
    exact ⟨1 + s2, by omega, regNSteps_bind_eq s1 step2⟩

theorem exec_x_test_le (regs : List ℕ) (hlen : regs.length = 16)
    (hz2 : regs[2]! = 0) (hz3 : regs[3]! = 0) (hle : regs[1]! ≤ 253) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨256, regs⟩ = some ⟨21, regs⟩ := by
  have hcopy : isCopyAdd 256 1 2 3 = true := by decide
  obtain ⟨s1, hs1, step1⟩ := exec_copy_add hcopy regs hlen hz3
  have hpc : 256 + 12 = 268 + 2 * (254 - 254) := rfl
  have hset : regs.set (2 : Fin 16).val (regs[(2 : Fin 16).val]! + regs[(1 : Fin 16).val]!) =
      regs.set 2 regs[1]! := by
    simp only [fin16_val_2, fin16_val_1, hz2, Nat.zero_add]
  rw [hpc, hset] at step1
  obtain ⟨s2, hs2, step2⟩ := exec_unrolled_lt 254 (by omega) regs[1]! regs hlen hz2 (by omega)
  exact ⟨s1 + s2, by omega, regNSteps_bind_eq step1 step2⟩

theorem exec_x_test_gt (regs : List ℕ) (hlen : regs.length = 16)
    (hz2 : regs[2]! = 0) (hz3 : regs[3]! = 0) (hgt : 253 < regs[1]!) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨256, regs⟩ = some ⟨780, regs⟩ := by
  have hcopy : isCopyAdd 256 1 2 3 = true := by decide
  obtain ⟨s1, hs1, step1⟩ := exec_copy_add hcopy regs hlen hz3
  have hpc : 256 + 12 = 268 + 2 * (254 - 254) := rfl
  have hset : regs.set (2 : Fin 16).val (regs[(2 : Fin 16).val]! + regs[(1 : Fin 16).val]!) =
      regs.set 2 regs[1]! := by
    simp only [fin16_val_2, fin16_val_1, hz2, Nat.zero_add]
  rw [hpc, hset] at step1
  obtain ⟨s2, step2⟩ := exec_unrolled_ge 254 (by omega) regs[1]! regs hlen (by omega)
  have hlen2 : (regs.set 2 (regs[1]! - 254)).length = 16 := by simp [hlen]
  have htr : isTransfer1 776 2 = true := by decide
  obtain ⟨s3, hs3, step3⟩ := exec_transfer1 htr (regs.set 2 (regs[1]! - 254)) hlen2
  have hset3 : (regs.set 2 (regs[1]! - 254)).set (2 : Fin 16).val 0 = regs := by
    change (regs.set (2 : Fin 16).val (regs[1]! - 254)).set (2 : Fin 16).val 0 = regs
    regs_eq hlen
  rw [hset3] at step3
  exact ⟨s1 + s2 + s3, by omega, regNSteps_bind_eq (regNSteps_bind_eq step1 step2) step3⟩

/-!
## 5. LCM Loop Verification (`PC 21 .. 256`)
-/

theorem Icc_one_succ (n : ℕ) : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
  ext a
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

theorem lcmUpTo_zero : lcmUpTo 0 = 1 := by decide

theorem lcmUpTo_succ (n : ℕ) : lcmUpTo (n + 1) = Nat.lcm (lcmUpTo n) (n + 1) := by
  unfold lcmUpTo
  rw [Icc_one_succ, Finset.lcm_insert]
  exact Nat.lcm_comm (n + 1) _

theorem lcmUpTo_pos : ∀ n : ℕ, 0 < lcmUpTo n
  | 0 => by rw [lcmUpTo_zero]; omega
  | n + 1 => by rw [lcmUpTo_succ]; exact Nat.lcm_pos (lcmUpTo_pos n) (by omega)

theorem div_mul_eq_iff_dvd {m d : ℕ} : (m / d) * d = m ↔ d ∣ m := by
  constructor
  · intro h
    exact ⟨m / d, by rw [Nat.mul_comm, h]⟩
  · exact Nat.div_mul_cancel

theorem exec_loop_header (regs : List ℕ) (hlen : regs.length = 16)
    (hz2 : regs[2]! = 0) (hz3 : regs[3]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨21, regs⟩ =
      some ⟨44, (regs.set 1 (regs[1]! + 1)).set 4 regs[0]!⟩ := by
  have s1 := step_incr (by decide : program 21 = .incr 1) regs
  let regs1 := regs.set 1 (regs[1]! + 1)
  have s2 := step_jump (by decide : program 22 = .jump 24) regs1
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have hz3_1 : regs1[(3 : Fin 16).val]! = 0 := by dsimp only [regs1]; reg_val hlen
  obtain ⟨s3, hs3, step3⟩ := exec_copy_add (by decide : isCopyAdd 24 0 2 3 = true) regs1 hlen1 hz3_1
  let regs2 := regs1.set (2 : Fin 16).val (regs1[(2 : Fin 16).val]! + regs1[(0 : Fin 16).val]!)
  have hlen2 : regs2.length = 16 := by simp [regs2, regs1, hlen]
  obtain ⟨s4, hs4, step4⟩ := exec_transfer1 (by decide : isTransfer1 36 4 = true) regs2 hlen2
  let regs3 := regs2.set (4 : Fin 16).val 0
  have hlen3 : regs3.length = 16 := by simp [regs3, regs2, regs1, hlen]
  obtain ⟨s5, hs5, step5⟩ := exec_transfer2 (by decide : isTransfer2 40 2 4 = true) regs3 hlen3
  have h4_3 : regs3[(4 : Fin 16).val]! = 0 := by dsimp only [regs3]; reg_val hlen2
  have h2_3 : regs3[(2 : Fin 16).val]! = regs[0]! := by
    dsimp only [regs3, regs2, regs1]
    reg_val hlen
  have heq : (regs3.set (4 : Fin 16).val (regs3[(4 : Fin 16).val]! +
      regs3[(2 : Fin 16).val]!)).set (2 : Fin 16).val 0 =
      (regs.set (1 : Fin 16).val (regs[1]! + 1)).set (4 : Fin 16).val regs[0]! := by
    rw [h4_3, h2_3, Nat.zero_add]
    dsimp only [regs3, regs2, regs1]
    regs_eq hlen
  rw [heq] at step5
  exact ⟨1 + 1 + s3 + s4 + s5, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq s1 s2) step3) step4)
      step5⟩

theorem exec_div_check_48_prep (regs : List ℕ) (hlen : regs.length = 16)
    (hl_pos : 0 < regs[4]!)
    (hz2 : regs[2]! = 0) (hz3 : regs[3]! = 0) (hz5 : regs[5]! = 0)
    (hz6 : regs[6]! = 0) (hz7 : regs[7]! = 0) (hz8 : regs[8]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨48, regs⟩ =
      some ⟨125, (regs.set 2 regs[0]!).set 3 ((regs[0]! / regs[4]!) * regs[4]!)⟩ := by
  obtain ⟨s1, hs1, step1⟩ := exec_copy_add (by decide : isCopyAdd 48 0 2 3 = true) regs hlen hz3
  let regs1 := regs.set (2 : Fin 16).val (regs[(2 : Fin 16).val]! + regs[(0 : Fin 16).val]!)
  have s2 := step_jump (by decide : program 60 = .jump 64) regs1
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have hz8_1 : regs1[(8 : Fin 16).val]! = 0 := by dsimp only [regs1]; reg_val hlen
  obtain ⟨s3, hs3, step3⟩ := exec_copy_add (by decide : isCopyAdd 64 0 6 8 = true) regs1 hlen1 hz8_1
  let regs2 := regs1.set (6 : Fin 16).val (regs1[(6 : Fin 16).val]! + regs1[(0 : Fin 16).val]!)
  have hlen2 : regs2.length = 16 := by simp [regs2, regs1, hlen]
  have hl_2 : 0 < regs2[(4 : Fin 16).val]! := by dsimp only [regs2, regs1]; reg_val hlen
  have hz7_2 : regs2[(7 : Fin 16).val]! = 0 := by dsimp only [regs2, regs1]; reg_val hlen
  have hz8_2 : regs2[(8 : Fin 16).val]! = 0 := by dsimp only [regs2, regs1]; reg_val hlen
  obtain ⟨s4, hs4, step4⟩ :=
      exec_div_loop (by decide : isDivLoop 76 4 7 6 5 8 = true) regs2 hlen2 hl_2 hz7_2 hz8_2
  let regs3 := (regs2.set (5 : Fin 16).val (regs2[(5 : Fin 16).val]! +
      regs2[(6 : Fin 16).val]! / regs2[(4 : Fin 16).val]!)).set (6 : Fin 16).val 0
  have hlen3 : regs3.length = 16 := by simp [regs3, regs2, regs1, hlen]
  have hz7_3 : regs3[(7 : Fin 16).val]! = 0 := by dsimp only [regs3, regs2, regs1]; reg_val hlen
  obtain ⟨s5, hs5, step5⟩ :=
      exec_mul_loop (by decide : isMulLoop 104 112 125 5 4 3 7 = true) regs3 hlen3 hz7_3
  have h3_3 : regs3[(3 : Fin 16).val]! = 0 := by dsimp only [regs3, regs2, regs1]; reg_val hlen
  have h4_3 : regs3[(4 : Fin 16).val]! = regs[4]! := by
    dsimp only [regs3, regs2, regs1]; reg_val hlen
  have h6_2 : regs2[(6 : Fin 16).val]! = regs[0]! := by dsimp only [regs2, regs1]; reg_val hlen
  have h4_2 : regs2[(4 : Fin 16).val]! = regs[4]! := by dsimp only [regs2, regs1]; reg_val hlen
  have h5_2 : regs2[(5 : Fin 16).val]! = 0 := by dsimp only [regs2, regs1]; reg_val hlen
  have h5_3 : regs3[(5 : Fin 16).val]! = regs[0]! / regs[4]! := by
    dsimp only [regs3]
    rw [h5_2, h6_2, h4_2, Nat.zero_add]
    reg_val hlen2
  have heq : (regs3.set (3 : Fin 16).val (regs3[(3 : Fin 16).val]! +
      regs3[(5 : Fin 16).val]! * regs3[(4 : Fin 16).val]!)).set (5 : Fin 16).val 0 =
      (regs.set (2 : Fin 16).val regs[0]!).set (3 : Fin 16).val ((regs[0]! / regs[4]!) * regs[4]!)
        := by
    rw [h3_3, h5_3, h4_3, Nat.zero_add]
    dsimp only [regs3, regs2, regs1]
    regs_eq hlen
  rw [heq] at step5
  exact ⟨s1 + 1 + s3 + s4 + s5, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq step1 s2) step3)
      step4) step5⟩

theorem exec_div_check_152_prep (regs : List ℕ) (hlen : regs.length = 16)
    (hx_pos : 0 < regs[1]!)
    (hz2 : regs[2]! = 0) (hz3 : regs[3]! = 0) (hz5 : regs[5]! = 0)
    (hz6 : regs[6]! = 0) (hz7 : regs[7]! = 0) (hz8 : regs[8]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨152, regs⟩ =
      some ⟨229, (regs.set 3 regs[0]!).set 2 ((regs[0]! / regs[1]!) * regs[1]!)⟩ := by
  obtain ⟨s1, hs1, step1⟩ := exec_copy_add (by decide : isCopyAdd 152 0 3 2 = true) regs hlen hz2
  let regs1 := regs.set (3 : Fin 16).val (regs[(3 : Fin 16).val]! + regs[(0 : Fin 16).val]!)
  have s2 := step_jump (by decide : program 164 = .jump 168) regs1
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have hz8_1 : regs1[(8 : Fin 16).val]! = 0 := by dsimp only [regs1]; reg_val hlen
  obtain ⟨s3, hs3, step3⟩ :=
      exec_copy_add (by decide : isCopyAdd 168 0 7 8 = true) regs1 hlen1 hz8_1
  let regs2 := regs1.set (7 : Fin 16).val (regs1[(7 : Fin 16).val]! + regs1[(0 : Fin 16).val]!)
  have hlen2 : regs2.length = 16 := by simp [regs2, regs1, hlen]
  have hx_2 : 0 < regs2[(1 : Fin 16).val]! := by dsimp only [regs2, regs1]; reg_val hlen
  have hz6_2 : regs2[(6 : Fin 16).val]! = 0 := by dsimp only [regs2, regs1]; reg_val hlen
  have hz8_2 : regs2[(8 : Fin 16).val]! = 0 := by dsimp only [regs2, regs1]; reg_val hlen
  obtain ⟨s4, hs4, step4⟩ :=
      exec_div_loop (by decide : isDivLoop 180 1 6 7 5 8 = true) regs2 hlen2 hx_2 hz6_2 hz8_2
  let regs3 := (regs2.set (5 : Fin 16).val (regs2[(5 : Fin 16).val]! +
      regs2[(7 : Fin 16).val]! / regs2[(1 : Fin 16).val]!)).set (7 : Fin 16).val 0
  have hlen3 : regs3.length = 16 := by simp [regs3, regs2, regs1, hlen]
  have hz6_3 : regs3[(6 : Fin 16).val]! = 0 := by dsimp only [regs3, regs2, regs1]; reg_val hlen
  obtain ⟨s5, hs5, step5⟩ :=
      exec_mul_loop (by decide : isMulLoop 208 216 229 5 1 2 6 = true) regs3 hlen3 hz6_3
  have h2_3 : regs3[(2 : Fin 16).val]! = 0 := by dsimp only [regs3, regs2, regs1]; reg_val hlen
  have h1_3 : regs3[(1 : Fin 16).val]! = regs[1]! := by
    dsimp only [regs3, regs2, regs1]; reg_val hlen
  have h7_2 : regs2[(7 : Fin 16).val]! = regs[0]! := by dsimp only [regs2, regs1]; reg_val hlen
  have h1_2 : regs2[(1 : Fin 16).val]! = regs[1]! := by dsimp only [regs2, regs1]; reg_val hlen
  have h5_2 : regs2[(5 : Fin 16).val]! = 0 := by dsimp only [regs2, regs1]; reg_val hlen
  have h5_3 : regs3[(5 : Fin 16).val]! = regs[0]! / regs[1]! := by
    dsimp only [regs3]
    rw [h5_2, h7_2, h1_2, Nat.zero_add]
    reg_val hlen2
  have heq : (regs3.set (2 : Fin 16).val (regs3[(2 : Fin 16).val]! +
      regs3[(5 : Fin 16).val]! * regs3[(1 : Fin 16).val]!)).set (5 : Fin 16).val 0 =
      (regs.set (3 : Fin 16).val regs[0]!).set (2 : Fin 16).val ((regs[0]! / regs[1]!) * regs[1]!)
        := by
    rw [h2_3, h5_3, h1_3, Nat.zero_add]
    dsimp only [regs3, regs2, regs1]
    regs_eq hlen
  rw [heq] at step5
  exact ⟨s1 + 1 + s3 + s4 + s5, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq step1 s2) step3)
      step4) step5⟩

theorem exec_lcm_iter_both_dvd (regs : List ℕ) (hlen : regs.length = 16)
    (hl_pos : 0 < regs[4]!) (hx_pos : 0 < regs[1]!)
    (hz2 : regs[2]! = 0) (hz3 : regs[3]! = 0) (hz5 : regs[5]! = 0)
    (hz6 : regs[6]! = 0) (hz7 : regs[7]! = 0) (hz8 : regs[8]! = 0)
    (hdvd_l : regs[4]! ∣ regs[0]!) (hdvd_x : regs[1]! ∣ regs[0]!) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨44, regs⟩ = some ⟨256, regs⟩ := by
  have s0 := step_jump (by decide : program 44 = .jump 48) regs
  obtain ⟨s1, hs1, step1⟩ := exec_div_check_48_prep regs hlen hl_pos hz2 hz3 hz5 hz6 hz7 hz8
  let regs1 := (regs.set (2 : Fin 16).val regs[0]!).set (3 : Fin 16).val ((regs[0]! / regs[4]!) *
      regs[4]!)
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have heq1 : regs1[(3 : Fin 16).val]! = regs1[(2 : Fin 16).val]! := by
    dsimp only [regs1]
    rw [div_mul_eq_iff_dvd.mpr hdvd_l]
    reg_val hlen
  obtain ⟨s2, hs2, step2⟩ :=
      exec_cmp_branch_eq (by decide : isCmpBranch 125 145 248 248 3 2 = true) regs1 hlen1 heq1
  have hclean1 : (regs1.set (2 : Fin 16).val 0).set (3 : Fin 16).val 0 = regs := by
    dsimp only [regs1]; regs_eq hlen
  rw [hclean1] at step2
  obtain ⟨s3, hs3, step3⟩ := exec_noop_to (by decide : isNoopTo 145 152 = true) regs
  obtain ⟨s4, hs4, step4⟩ := exec_div_check_152_prep regs hlen hx_pos hz2 hz3 hz5 hz6 hz7 hz8
  let regs2 := (regs.set (3 : Fin 16).val regs[0]!).set (2 : Fin 16).val ((regs[0]! / regs[1]!) *
      regs[1]!)
  have hlen2 : regs2.length = 16 := by simp [regs2, hlen]
  have heq2 : regs2[(2 : Fin 16).val]! = regs2[(3 : Fin 16).val]! := by
    dsimp only [regs2]
    rw [div_mul_eq_iff_dvd.mpr hdvd_x]
    reg_val hlen
  obtain ⟨s5, hs5, step5⟩ :=
      exec_cmp_branch_eq (by decide : isCmpBranch 229 250 248 248 2 3 = true) regs2 hlen2 heq2
  have hclean2 : (regs2.set (3 : Fin 16).val 0).set (2 : Fin 16).val 0 = regs := by
    dsimp only [regs2]; regs_eq hlen
  rw [hclean2] at step5
  obtain ⟨s6, hs6, step6⟩ := exec_noop_to (by decide : isNoopTo 250 256 = true) regs
  exact ⟨1 + s1 + s2 + s3 + s4 + s5 + s6, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
      (regNSteps_bind_eq s0 step1) step2) step3) step4) step5) step6⟩

theorem exec_lcm_iter_not_both (regs : List ℕ) (hlen : regs.length = 16)
    (hl_pos : 0 < regs[4]!) (hx_pos : 0 < regs[1]!)
    (hz2 : regs[2]! = 0) (hz3 : regs[3]! = 0) (hz5 : regs[5]! = 0)
    (hz6 : regs[6]! = 0) (hz7 : regs[7]! = 0) (hz8 : regs[8]! = 0)
    (hnot : ¬ (regs[4]! ∣ regs[0]! ∧ regs[1]! ∣ regs[0]!)) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨44, regs⟩ = some ⟨44, regs.set 0 (regs[0]! + 1)⟩ := by
  have s0 := step_jump (by decide : program 44 = .jump 48) regs
  obtain ⟨s1, hs1, step1⟩ := exec_div_check_48_prep regs hlen hl_pos hz2 hz3 hz5 hz6 hz7 hz8
  let regs1 := (regs.set (2 : Fin 16).val regs[0]!).set (3 : Fin 16).val ((regs[0]! / regs[4]!) *
      regs[4]!)
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have s_inc := step_incr (by decide : program 248 = .incr 0) regs
  have s_jmp := step_jump (by decide : program 249 = .jump 44) (regs.set 0 (regs[0]! + 1))
  have s248 : regNSteps 2 ⟨248, regs⟩ = some ⟨44, regs.set 0 (regs[0]! + 1)⟩ :=
    regNSteps_bind_eq s_inc s_jmp
  by_cases hdvd_l : regs[4]! ∣ regs[0]!
  · have hdvd_x : ¬ (regs[1]! ∣ regs[0]!) := fun hx => hnot ⟨hdvd_l, hx⟩
    have heq1 : regs1[(3 : Fin 16).val]! = regs1[(2 : Fin 16).val]! := by
      dsimp only [regs1]
      rw [div_mul_eq_iff_dvd.mpr hdvd_l]
      reg_val hlen
    obtain ⟨s2, hs2, step2⟩ :=
        exec_cmp_branch_eq (by decide : isCmpBranch 125 145 248 248 3 2 = true) regs1 hlen1 heq1
    have hclean1 : (regs1.set (2 : Fin 16).val 0).set (3 : Fin 16).val 0 = regs := by
      dsimp only [regs1]; regs_eq hlen
    rw [hclean1] at step2
    obtain ⟨s3, hs3, step3⟩ := exec_noop_to (by decide : isNoopTo 145 152 = true) regs
    obtain ⟨s4, hs4, step4⟩ := exec_div_check_152_prep regs hlen hx_pos hz2 hz3 hz5 hz6 hz7 hz8
    let regs2 := (regs.set (3 : Fin 16).val regs[0]!).set (2 : Fin 16).val ((regs[0]! / regs[1]!) *
        regs[1]!)
    have hlen2 : regs2.length = 16 := by simp [regs2, hlen]
    have hne2 : regs2[(2 : Fin 16).val]! ≠ regs2[(3 : Fin 16).val]! := by
      have h2 : regs2[(2 : Fin 16).val]! = (regs[0]! / regs[1]!) * regs[1]! := by
        dsimp only [regs2]; reg_val hlen
      have h3 : regs2[(3 : Fin 16).val]! = regs[0]! := by dsimp only [regs2]; reg_val hlen
      rw [h2, h3]
      exact fun h => hdvd_x (div_mul_eq_iff_dvd.mp h)
    obtain ⟨s5, hs5, step5⟩ :=
        exec_cmp_branch_ne (by decide : isCmpBranch 229 250 248 248 2 3 = true) regs2 hlen2 hne2
    have hclean2 : (regs2.set (3 : Fin 16).val 0).set (2 : Fin 16).val 0 = regs := by
      dsimp only [regs2]; regs_eq hlen
    rw [hclean2] at step5
    exact ⟨1 + s1 + s2 + s3 + s4 + s5 + 2, by omega,
      regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
        (regNSteps_bind_eq s0 step1) step2) step3) step4) step5) s248⟩
  · have hne1 : regs1[(3 : Fin 16).val]! ≠ regs1[(2 : Fin 16).val]! := by
      have h3 : regs1[(3 : Fin 16).val]! = (regs[0]! / regs[4]!) * regs[4]! := by
        dsimp only [regs1]; reg_val hlen
      have h2 : regs1[(2 : Fin 16).val]! = regs[0]! := by dsimp only [regs1]; reg_val hlen
      rw [h3, h2]
      exact fun h => hdvd_l (div_mul_eq_iff_dvd.mp h)
    obtain ⟨s2, hs2, step2⟩ :=
        exec_cmp_branch_ne (by decide : isCmpBranch 125 145 248 248 3 2 = true) regs1 hlen1 hne1
    have hclean1 : (regs1.set (2 : Fin 16).val 0).set (3 : Fin 16).val 0 = regs := by
      dsimp only [regs1]; regs_eq hlen
    rw [hclean1] at step2
    exact ⟨1 + s1 + s2 + 2, by omega,
      regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq s0 step1) step2) s248⟩

theorem exec_lcm_loop_aux :
    ∀ (k : ℕ) (regs : List ℕ), regs.length = 16 →
      0 < regs[4]! → 0 < regs[1]! → 0 < regs[0]! →
      regs[2]! = 0 → regs[3]! = 0 → regs[5]! = 0 →
      regs[6]! = 0 → regs[7]! = 0 → regs[8]! = 0 →
      regs[0]! + k = Nat.lcm regs[4]! regs[1]! →
      ∃ s, 1 ≤ s ∧ regNSteps s ⟨44, regs⟩ =
        some ⟨256, regs.set 0 (Nat.lcm regs[4]! regs[1]!)⟩
  | 0, regs, hlen, hl_pos, hx_pos, _, hz2, hz3, hz5, hz6, hz7, hz8, hk => by
    have hm : regs[0]! = Nat.lcm regs[4]! regs[1]! := by omega
    have hdvd_l : regs[4]! ∣ regs[0]! := by rw [hm]; exact Nat.dvd_lcm_left _ _
    have hdvd_x : regs[1]! ∣ regs[0]! := by rw [hm]; exact Nat.dvd_lcm_right _ _
    obtain ⟨s, hs, step⟩ :=
        exec_lcm_iter_both_dvd regs hlen hl_pos hx_pos hz2 hz3 hz5 hz6 hz7 hz8 hdvd_l hdvd_x
    have hset : regs.set 0 (Nat.lcm regs[4]! regs[1]!) = regs := by
      rw [← hm]
      change regs.set (0 : Fin 16).val regs[0]! = regs
      regs_eq hlen
    rw [hset]
    exact ⟨s, hs, step⟩
  | k + 1, regs, hlen, hl_pos, hx_pos, hm_pos, hz2, hz3, hz5, hz6, hz7, hz8, hk => by
    have hnot : ¬ (regs[4]! ∣ regs[0]! ∧ regs[1]! ∣ regs[0]!) := by
      rintro ⟨hl, hx⟩
      have hdvd : Nat.lcm regs[4]! regs[1]! ∣ regs[0]! := Nat.lcm_dvd hl hx
      have hle : Nat.lcm regs[4]! regs[1]! ≤ regs[0]! := Nat.le_of_dvd hm_pos hdvd
      omega
    obtain ⟨s1, hs1, step1⟩ :=
        exec_lcm_iter_not_both regs hlen hl_pos hx_pos hz2 hz3 hz5 hz6 hz7 hz8 hnot
    let regs1 := regs.set 0 (regs[0]! + 1)
    have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
    have h4_1 : regs1[4]! = regs[4]! := by dsimp only [regs1]; reg_val hlen
    have h1_1 : regs1[1]! = regs[1]! := by dsimp only [regs1]; reg_val hlen
    have h0_1 : regs1[0]! = regs[0]! + 1 := by dsimp only [regs1]; reg_val hlen
    have hz2_1 : regs1[2]! = 0 := by dsimp only [regs1]; reg_val hlen
    have hz3_1 : regs1[3]! = 0 := by dsimp only [regs1]; reg_val hlen
    have hz5_1 : regs1[5]! = 0 := by dsimp only [regs1]; reg_val hlen
    have hz6_1 : regs1[6]! = 0 := by dsimp only [regs1]; reg_val hlen
    have hz7_1 : regs1[7]! = 0 := by dsimp only [regs1]; reg_val hlen
    have hz8_1 : regs1[8]! = 0 := by dsimp only [regs1]; reg_val hlen
    obtain ⟨s2, hs2, step2⟩ := exec_lcm_loop_aux k regs1 hlen1
      (by omega) (by omega) (by omega) hz2_1 hz3_1 hz5_1 hz6_1 hz7_1 hz8_1
      (by rw [h4_1, h1_1, h0_1]; omega)
    have heq : regs1.set 0 (Nat.lcm regs1[4]! regs1[1]!) =
        regs.set 0 (Nat.lcm regs[4]! regs[1]!) := by
      rw [h4_1, h1_1]
      dsimp only [regs1]
      change (regs.set (0 : Fin 16).val (regs[0]! +
        1)).set (0 : Fin 16).val (Nat.lcm regs[4]! regs[1]!) =
        regs.set (0 : Fin 16).val (Nat.lcm regs[4]! regs[1]!)
      regs_eq hlen
    rw [heq] at step2
    exact ⟨s1 + s2, by omega, regNSteps_bind_eq step1 step2⟩

theorem exec_lcm_from_21 (regs : List ℕ) (hlen : regs.length = 16)
    (h0_pos : 0 < regs[0]!)
    (hz2 : regs[2]! = 0) (hz3 : regs[3]! = 0) (hz5 : regs[5]! = 0)
    (hz6 : regs[6]! = 0) (hz7 : regs[7]! = 0) (hz8 : regs[8]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨21, regs⟩ =
      some ⟨256, ((regs.set 1 (regs[1]! + 1)).set 4 regs[0]!).set 0 (Nat.lcm regs[0]! (regs[1]! +
        1))⟩ := by
  obtain ⟨s1, hs1, step1⟩ := exec_loop_header regs hlen hz2 hz3
  let regs1 := (regs.set 1 (regs[1]! + 1)).set 4 regs[0]!
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have h4_1 : regs1[4]! = regs[0]! := by dsimp only [regs1]; reg_val hlen
  have h1_1 : regs1[1]! = regs[1]! + 1 := by dsimp only [regs1]; reg_val hlen
  have h0_1 : regs1[0]! = regs[0]! := by dsimp only [regs1]; reg_val hlen
  have hz2_1 : regs1[2]! = 0 := by dsimp only [regs1]; reg_val hlen
  have hz3_1 : regs1[3]! = 0 := by dsimp only [regs1]; reg_val hlen
  have hz5_1 : regs1[5]! = 0 := by dsimp only [regs1]; reg_val hlen
  have hz6_1 : regs1[6]! = 0 := by dsimp only [regs1]; reg_val hlen
  have hz7_1 : regs1[7]! = 0 := by dsimp only [regs1]; reg_val hlen
  have hz8_1 : regs1[8]! = 0 := by dsimp only [regs1]; reg_val hlen
  have hlcm_pos : 0 < Nat.lcm regs[0]! (regs[1]! + 1) := Nat.lcm_pos h0_pos (by omega)
  have hlcm_le : regs[0]! ≤ Nat.lcm regs[0]! (regs[1]! + 1) :=
    Nat.le_of_dvd hlcm_pos (Nat.dvd_lcm_left _ _)
  obtain ⟨s2, hs2, step2⟩ :=
      exec_lcm_loop_aux (Nat.lcm regs[0]! (regs[1]! + 1) - regs[0]!) regs1 hlen1
      (by omega) (by omega) (by omega) hz2_1 hz3_1 hz5_1 hz6_1 hz7_1 hz8_1
      (by rw [h4_1, h1_1, h0_1]; omega)
  rw [h4_1, h1_1] at step2
  exact ⟨s1 + s2, by omega, regNSteps_bind_eq step1 step2⟩

/-!
## 6. Harmonic/Factorial Loops, Post-Harmonic Arithmetic, and Main Halting Equivalence
-/

theorem exec_harm_iter_780 (m : ℕ) (regs : List ℕ) (hlen : regs.length = 16)
    (hNum : regs[9]! = harmNum m) (hDenom : regs[10]! = m.factorial)
    (hI : regs[11]! = m + 1)
    (hsA : regs[2]! = 0) (hsB : regs[3]! = 0) (hsC : regs[5]! = 0)
    (hm : m < regs[0]!) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨797, regs⟩ =
      some ⟨797, ((regs.set 9 (harmNum (m + 1))).set 10 (m + 1).factorial).set 11 (m + 1 + 1)⟩ := by
  obtain ⟨s0, hs0, step0⟩ := exec_noop_to (by decide : isNoopTo 797 800 = true) regs
  obtain ⟨s1, hs1, step1⟩ := exec_copy_add (by decide : isCopyAdd 800 11 2 3 = true) regs hlen hsB
  have hset1 : regs.set (2 : Fin 16).val (regs[(2 : Fin 16).val]! + regs[(11 : Fin 16).val]!) =
      regs.set 2 (m + 1) := by regs_eq hlen
  rw [hset1] at step1
  let regs1 := regs.set 2 (m + 1)
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have step2 := step_jump (by decide : program 812 = .jump 816) regs1
  have hsC1 : regs1[(5 : Fin 16).val]! = 0 := by dsimp only [regs1]; reg_val hlen
  obtain ⟨s3, hs3, step3⟩ := exec_copy_add (by decide : isCopyAdd 816 0 3 5 = true) regs1 hlen1 hsC1
  have hset3 : regs1.set (3 : Fin 16).val (regs1[(3 : Fin 16).val]! + regs1[(0 : Fin 16).val]!) =
      (regs.set 2 (m + 1)).set 3 regs[0]! := by dsimp only [regs1]; regs_eq hlen
  rw [hset3] at step3
  let regs2 := (regs.set 2 (m + 1)).set 3 regs[0]!
  have hlen2 : regs2.length = 16 := by simp [regs2, hlen]
  have hle2 : regs2[(2 : Fin 16).val]! ≤ regs2[(3 : Fin 16).val]! := by
    dsimp only [regs2]; reg_val hlen
  obtain ⟨s4, hs4, step4⟩ :=
      exec_le_branch_le (by decide : isLeBranch 828 946 3 2 = true) regs2 hlen2 hle2
  have hset4 : (regs2.set (2 : Fin 16).val 0).set (3 : Fin 16).val 0 = regs := by
    dsimp only [regs2]; regs_eq hlen
  rw [hset4] at step4
  obtain ⟨s5, hs5, step5⟩ := exec_copy_add (by decide : isCopyAdd 848 9 2 5 = true) regs hlen hsC
  have hset5 : regs.set (2 : Fin 16).val (regs[(2 : Fin 16).val]! + regs[(9 : Fin 16).val]!) =
      regs.set 2 (harmNum m) := by regs_eq hlen
  rw [hset5] at step5
  let regs3 := regs.set 2 (harmNum m)
  have hlen3 : regs3.length = 16 := by simp [regs3, hlen]
  have hsC3 : regs3[(5 : Fin 16).val]! = 0 := by dsimp only [regs3]; reg_val hlen
  obtain ⟨s6, hs6, step6⟩ :=
      exec_mul_loop (by decide : isMulLoop 860 864 877 2 11 3 5 = true) regs3 hlen3 hsC3
  have hset6 : (regs3.set (3 : Fin 16).val (regs3[(3 : Fin 16).val]! +
      regs3[(2 : Fin 16).val]! * regs3[(11 : Fin 16).val]!)).set (2 : Fin 16).val 0 =
      regs.set 3 (harmNum m * (m + 1)) := by
    have hA3 : regs3[(2 : Fin 16).val]! = harmNum m := by dsimp only [regs3]; reg_val hlen
    have hI3 : regs3[(11 : Fin 16).val]! = m + 1 := by dsimp only [regs3]; reg_val hlen
    have hB3 : regs3[(3 : Fin 16).val]! = 0 := by dsimp only [regs3]; reg_val hlen
    rw [hA3, hI3, hB3, Nat.zero_add]; dsimp only [regs3]; regs_eq hlen
  rw [hset6] at step6
  let regs4 := regs.set 3 (harmNum m * (m + 1))
  have hlen4 : regs4.length = 16 := by simp [regs4, hlen]
  obtain ⟨s7, hs7, step7⟩ := exec_noop_to (by decide : isNoopTo 877 880 = true) regs4
  have hsA4 : regs4[(2 : Fin 16).val]! = 0 := by dsimp only [regs4]; reg_val hlen
  obtain ⟨s8, hs8, step8⟩ :=
      exec_copy_add (by decide : isCopyAdd 880 10 3 2 = true) regs4 hlen4 hsA4
  have hset8 : regs4.set (3 : Fin 16).val (regs4[(3 : Fin 16).val]! + regs4[(10 : Fin 16).val]!) =
      regs.set 3 (harmNum (m + 1)) := by
    rw [harmNum_succ]; dsimp only [regs4]; regs_eq hlen
  rw [hset8] at step8
  let regs5 := regs.set 3 (harmNum (m + 1))
  have hlen5 : regs5.length = 16 := by simp [regs5, hlen]
  obtain ⟨s9, hs9, step9⟩ := exec_transfer1 (by decide : isTransfer1 892 9 = true) regs5 hlen5
  let regs6 := regs5.set (9 : Fin 16).val 0
  have hlen6 : regs6.length = 16 := by simp [regs6, regs5, hlen]
  obtain ⟨s10, hs10, step10⟩ := exec_transfer2 (by decide : isTransfer2 896 3 9 = true) regs6 hlen6
  have hset10 : (regs6.set (9 : Fin 16).val (regs6[(9 : Fin 16).val]! +
      regs6[(3 : Fin 16).val]!)).set (3 : Fin 16).val 0 =
      regs.set 9 (harmNum (m + 1)) := by
    dsimp only [regs6, regs5]; regs_eq hlen
  rw [hset10] at step10
  let regs7 := regs.set 9 (harmNum (m + 1))
  have hlen7 : regs7.length = 16 := by simp [regs7, hlen]
  have step11 := step_jump (by decide : program 900 = .jump 904) regs7
  have hsC7 : regs7[(5 : Fin 16).val]! = 0 := by dsimp only [regs7]; reg_val hlen
  obtain ⟨s12, hs12, step12⟩ :=
      exec_copy_add (by decide : isCopyAdd 904 10 2 5 = true) regs7 hlen7 hsC7
  have hset12 : regs7.set (2 : Fin 16).val (regs7[(2 : Fin 16).val]! + regs7[(10 : Fin 16).val]!) =
      regs7.set 2 m.factorial := by dsimp only [regs7]; regs_eq hlen
  rw [hset12] at step12
  let regs8 := regs7.set 2 m.factorial
  have hlen8 : regs8.length = 16 := by simp [regs8, regs7, hlen]
  have hsC8 : regs8[(5 : Fin 16).val]! = 0 := by dsimp only [regs8, regs7]; reg_val hlen
  obtain ⟨s13, hs13, step13⟩ :=
      exec_mul_loop (by decide : isMulLoop 916 920 933 2 11 3 5 = true) regs8 hlen8 hsC8
  have hset13 : (regs8.set (3 : Fin 16).val (regs8[(3 : Fin 16).val]! +
      regs8[(2 : Fin 16).val]! * regs8[(11 : Fin 16).val]!)).set (2 : Fin 16).val 0 =
      regs7.set 3 (m + 1).factorial := by
    have hA8 : regs8[(2 : Fin 16).val]! = m.factorial := by dsimp only [regs8, regs7]; reg_val hlen
    have hI8 : regs8[(11 : Fin 16).val]! = m + 1 := by dsimp only [regs8, regs7]; reg_val hlen
    have hB8 : regs8[(3 : Fin 16).val]! = 0 := by dsimp only [regs8, regs7]; reg_val hlen
    have hfac : m.factorial * (m + 1) = (m + 1).factorial := by
      rw [Nat.factorial_succ, Nat.mul_comm]
    rw [hA8, hI8, hB8, Nat.zero_add, hfac]; dsimp only [regs8, regs7]; regs_eq hlen
  rw [hset13] at step13
  let regs9 := regs7.set 3 (m + 1).factorial
  have hlen9 : regs9.length = 16 := by simp [regs9, regs7, hlen]
  obtain ⟨s14, hs14, step14⟩ := exec_noop_to (by decide : isNoopTo 933 936 = true) regs9
  obtain ⟨s15, hs15, step15⟩ := exec_transfer1 (by decide : isTransfer1 936 10 = true) regs9 hlen9
  let regs10 := regs9.set (10 : Fin 16).val 0
  have hlen10 : regs10.length = 16 := by simp [regs10, regs9, regs7, hlen]
  obtain ⟨s16, hs16, step16⟩ :=
      exec_transfer2 (by decide : isTransfer2 940 3 10 = true) regs10 hlen10
  have hset16 : (regs10.set (10 : Fin 16).val (regs10[(10 : Fin 16).val]! +
      regs10[(3 : Fin 16).val]!)).set (3 : Fin 16).val 0 =
      (regs.set 9 (harmNum (m + 1))).set 10 (m + 1).factorial := by
    dsimp only [regs10, regs9, regs7]; regs_eq hlen
  rw [hset16] at step16
  let regs11 := (regs.set 9 (harmNum (m + 1))).set 10 (m + 1).factorial
  have step17 := step_incr (by decide : program 944 = .incr 11) regs11
  have hset17 : regs11.set (11 : Fin 16).val (regs11[(11 : Fin 16).val]! + 1) =
      ((regs.set 9 (harmNum (m + 1))).set 10 (m + 1).factorial).set 11 (m + 1 + 1) := by
    dsimp only [regs11]; regs_eq hlen
  rw [hset17] at step17
  let regs12 := ((regs.set 9 (harmNum (m + 1))).set 10 (m + 1).factorial).set 11 (m + 1 + 1)
  have step18 := step_jump (by decide : program 945 = .jump 797) regs12
  exact ⟨s0 + s1 + 1 + s3 + s4 + s5 + s6 + s7 + s8 + s9 + s10 + 1 + s12 + s13 + s14 + s15 + s16 +
    1 + 1, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
      (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
        (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
          (regNSteps_bind_eq
          (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq step0 step1) step2) step3) step4)
          step5) step6) step7) step8) step9) step10) step11) step12) step13) step14) step15)
            step16) step17) step18⟩

theorem exec_harm_exit_780 (regs : List ℕ) (hlen : regs.length = 16)
    (hI : regs[11]! = regs[0]! + 1)
    (hsA : regs[2]! = 0) (hsB : regs[3]! = 0) (hsC : regs[5]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨797, regs⟩ = some ⟨946, regs⟩ := by
  obtain ⟨s0, hs0, step0⟩ := exec_noop_to (by decide : isNoopTo 797 800 = true) regs
  obtain ⟨s1, hs1, step1⟩ := exec_copy_add (by decide : isCopyAdd 800 11 2 3 = true) regs hlen hsB
  have hset1 : regs.set (2 : Fin 16).val (regs[(2 : Fin 16).val]! + regs[(11 : Fin 16).val]!) =
      regs.set 2 (regs[0]! + 1) := by regs_eq hlen
  rw [hset1] at step1
  let regs1 := regs.set 2 (regs[0]! + 1)
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have step2 := step_jump (by decide : program 812 = .jump 816) regs1
  have hsC1 : regs1[(5 : Fin 16).val]! = 0 := by dsimp only [regs1]; reg_val hlen
  obtain ⟨s3, hs3, step3⟩ := exec_copy_add (by decide : isCopyAdd 816 0 3 5 = true) regs1 hlen1 hsC1
  have hset3 : regs1.set (3 : Fin 16).val (regs1[(3 : Fin 16).val]! + regs1[(0 : Fin 16).val]!) =
      (regs.set 2 (regs[0]! + 1)).set 3 regs[0]! := by dsimp only [regs1]; regs_eq hlen
  rw [hset3] at step3
  let regs2 := (regs.set 2 (regs[0]! + 1)).set 3 regs[0]!
  have hlen2 : regs2.length = 16 := by simp [regs2, hlen]
  have hgt2 : regs2[(3 : Fin 16).val]! < regs2[(2 : Fin 16).val]! := by
    dsimp only [regs2]; reg_val hlen
  obtain ⟨s4, hs4, step4⟩ :=
      exec_le_branch_gt (by decide : isLeBranch 828 946 3 2 = true) regs2 hlen2 hgt2
  have hset4 : (regs2.set (2 : Fin 16).val 0).set (3 : Fin 16).val 0 = regs := by
    dsimp only [regs2]; regs_eq hlen
  rw [hset4] at step4
  exact ⟨s0 + s1 + 1 + s3 + s4, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq step0 step1) step2)
      step3) step4⟩

theorem exec_harm_loop_aux_780 :
    ∀ (k m : ℕ) (regs : List ℕ), regs.length = 16 →
      regs[9]! = harmNum m → regs[10]! = m.factorial → regs[11]! = m + 1 →
      regs[2]! = 0 → regs[3]! = 0 → regs[5]! = 0 →
      m + k = regs[0]! →
      ∃ s, 1 ≤ s ∧ regNSteps s ⟨797, regs⟩ =
        some ⟨946, ((regs.set 9 (harmNum regs[0]!)).set 10 (regs[0]!).factorial).set 11 (regs[0]! +
          1)⟩
  | 0, m, regs, hlen, hNum, hDenom, hI, hsA, hsB, hsC, hk => by
    have hm : m = regs[0]! := by omega
    subst hm
    obtain ⟨s, hs, step⟩ := exec_harm_exit_780 regs hlen hI hsA hsB hsC
    have hset : ((regs.set 9 (harmNum regs[0]!)).set 10 (regs[0]!).factorial).set 11 (regs[0]! +
        1) = regs := by
      rw [← hNum, ← hDenom, ← hI]; regs_eq hlen
    rw [hset]
    exact ⟨s, hs, step⟩
  | k + 1, m, regs, hlen, hNum, hDenom, hI, hsA, hsB, hsC, hk => by
    have hm : m < regs[0]! := by omega
    obtain ⟨s1, hs1, step1⟩ := exec_harm_iter_780 m regs hlen hNum hDenom hI hsA hsB hsC hm
    let regs1 := ((regs.set 9 (harmNum (m + 1))).set 10 (m + 1).factorial).set 11 (m + 1 + 1)
    have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
    have hNum1 : regs1[9]! = harmNum (m + 1) := by dsimp only [regs1]; reg_val hlen
    have hDenom1 : regs1[10]! = (m + 1).factorial := by dsimp only [regs1]; reg_val hlen
    have hI1 : regs1[11]! = (m + 1) + 1 := by dsimp only [regs1]; reg_val hlen
    have hsA1 : regs1[2]! = 0 := by dsimp only [regs1]; reg_val hlen
    have hsB1 : regs1[3]! = 0 := by dsimp only [regs1]; reg_val hlen
    have hsC1 : regs1[5]! = 0 := by dsimp only [regs1]; reg_val hlen
    have hN1 : regs1[0]! = regs[0]! := by dsimp only [regs1]; reg_val hlen
    obtain ⟨s2, hs2, step2⟩ := exec_harm_loop_aux_780 k (m + 1) regs1 hlen1
      hNum1 hDenom1 hI1 hsA1 hsB1 hsC1 (by rw [hN1]; omega)
    have heq : ((regs1.set 9 (harmNum regs1[0]!)).set 10 (regs1[0]!).factorial).set 11 (regs1[0]! +
        1) =
        ((regs.set 9 (harmNum regs[0]!)).set 10 (regs[0]!).factorial).set 11 (regs[0]! + 1) := by
      rw [hN1]; dsimp only [regs1]; regs_eq hlen
    rw [heq] at step2
    exact ⟨s1 + s2, by omega, regNSteps_bind_eq step1 step2⟩

theorem exec_harm_780 (regs : List ℕ) (hlen : regs.length = 16)
    (hsA : regs[2]! = 0) (hsB : regs[3]! = 0) (hsC : regs[5]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨780, regs⟩ =
      some ⟨946, ((regs.set 9 (harmNum regs[0]!)).set 10 (regs[0]!).factorial).set 11 (regs[0]! +
        1)⟩ := by
  obtain ⟨s1, hs1, step1⟩ := exec_transfer1 (by decide : isTransfer1 780 9 = true) regs hlen
  let regs1 := regs.set (9 : Fin 16).val 0
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  obtain ⟨s2, hs2, step2⟩ := exec_transfer1 (by decide : isTransfer1 784 10 = true) regs1 hlen1
  let regs2 := regs1.set (10 : Fin 16).val 0
  have step3 := step_incr (by decide : program 788 = .incr 10) regs2
  let regs3 := regs2.set (10 : Fin 16).val (regs2[(10 : Fin 16).val]! + 1)
  obtain ⟨s4, hs4, step4⟩ := exec_noop_to (by decide : isNoopTo 789 792 = true) regs3
  have hlen3 : regs3.length = 16 := by simp [regs3, regs2, regs1, hlen]
  obtain ⟨s5, hs5, step5⟩ := exec_transfer1 (by decide : isTransfer1 792 11 = true) regs3 hlen3
  let regs4 := regs3.set (11 : Fin 16).val 0
  have step6 := step_incr (by decide : program 796 = .incr 11) regs4
  have hset6 : regs4.set (11 : Fin 16).val (regs4[(11 : Fin 16).val]! + 1) =
      ((regs.set 9 (harmNum 0)).set 10 (0 : ℕ).factorial).set 11 (0 + 1) := by
    dsimp only [regs4, regs3, regs2, regs1, harmNum, Nat.factorial]; regs_eq hlen
  rw [hset6] at step6
  let regs5 := ((regs.set 9 (harmNum 0)).set 10 (0 : ℕ).factorial).set 11 (0 + 1)
  have hlen5 : regs5.length = 16 := by simp [regs5, hlen]
  have hNum5 : regs5[9]! = harmNum 0 := by dsimp only [regs5]; reg_val hlen
  have hDenom5 : regs5[10]! = (0 : ℕ).factorial := by dsimp only [regs5]; reg_val hlen
  have hI5 : regs5[11]! = 0 + 1 := by dsimp only [regs5]; reg_val hlen
  have hsA5 : regs5[2]! = 0 := by dsimp only [regs5]; reg_val hlen
  have hsB5 : regs5[3]! = 0 := by dsimp only [regs5]; reg_val hlen
  have hsC5 : regs5[5]! = 0 := by dsimp only [regs5]; reg_val hlen
  have hN5 : regs5[0]! = regs[0]! := by dsimp only [regs5]; reg_val hlen
  obtain ⟨s7, hs7, step7⟩ := exec_harm_loop_aux_780 regs[0]! 0 regs5 hlen5
    hNum5 hDenom5 hI5 hsA5 hsB5 hsC5 (by rw [hN5]; omega)
  have heq : ((regs5.set 9 (harmNum regs5[0]!)).set 10 (regs5[0]!).factorial).set 11 (regs5[0]! +
      1) =
      ((regs.set 9 (harmNum regs[0]!)).set 10 (regs[0]!).factorial).set 11 (regs[0]! + 1) := by
    rw [hN5]; dsimp only [regs5]; regs_eq hlen
  rw [heq] at step7
  exact ⟨s1 + s2 + 1 + s4 + s5 + 1 + s7, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
      (regNSteps_bind_eq (regNSteps_bind_eq step1 step2) step3) step4) step5) step6) step7⟩

theorem exec_harm_iter_1104 (m : ℕ) (regs : List ℕ) (hlen : regs.length = 16)
    (hNum : regs[14]! = harmNum m) (hDenom : regs[15]! = m.factorial)
    (hI : regs[11]! = m + 1)
    (hsA : regs[3]! = 0) (hsB : regs[5]! = 0) (hsC : regs[2]! = 0)
    (hm : m < regs[1]!) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨1121, regs⟩ =
      some ⟨1121,
        ((regs.set 14 (harmNum (m + 1))).set 15 (m + 1).factorial).set 11 (m + 1 + 1)⟩ := by
  obtain ⟨s0, hs0, step0⟩ := exec_noop_to (by decide : isNoopTo 1121 1128 = true) regs
  obtain ⟨s1, hs1, step1⟩ := exec_copy_add (by decide : isCopyAdd 1128 11 3 5 = true) regs hlen hsB
  have hset1 : regs.set (3 : Fin 16).val (regs[(3 : Fin 16).val]! + regs[(11 : Fin 16).val]!) =
      regs.set 3 (m + 1) := by regs_eq hlen
  rw [hset1] at step1
  let regs1 := regs.set 3 (m + 1)
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have step2 := step_jump (by decide : program 1140 = .jump 1144) regs1
  have hsC1 : regs1[(2 : Fin 16).val]! = 0 := by dsimp only [regs1]; reg_val hlen
  obtain ⟨s3, hs3, step3⟩ :=
      exec_copy_add (by decide : isCopyAdd 1144 1 5 2 = true) regs1 hlen1 hsC1
  have hset3 : regs1.set (5 : Fin 16).val (regs1[(5 : Fin 16).val]! + regs1[(1 : Fin 16).val]!) =
      (regs.set 3 (m + 1)).set 5 regs[1]! := by dsimp only [regs1]; regs_eq hlen
  rw [hset3] at step3
  let regs2 := (regs.set 3 (m + 1)).set 5 regs[1]!
  have hlen2 : regs2.length = 16 := by simp [regs2, hlen]
  have hle2 : regs2[(3 : Fin 16).val]! ≤ regs2[(5 : Fin 16).val]! := by
    dsimp only [regs2]; reg_val hlen
  obtain ⟨s4, hs4, step4⟩ :=
      exec_le_branch_le (by decide : isLeBranch 1156 1274 5 3 = true) regs2 hlen2 hle2
  have hset4 : (regs2.set (3 : Fin 16).val 0).set (5 : Fin 16).val 0 = regs := by
    dsimp only [regs2]; regs_eq hlen
  rw [hset4] at step4
  obtain ⟨s5, hs5, step5⟩ := exec_copy_add (by decide : isCopyAdd 1176 14 3 2 = true) regs hlen hsC
  have hset5 : regs.set (3 : Fin 16).val (regs[(3 : Fin 16).val]! + regs[(14 : Fin 16).val]!) =
      regs.set 3 (harmNum m) := by regs_eq hlen
  rw [hset5] at step5
  let regs3 := regs.set 3 (harmNum m)
  have hlen3 : regs3.length = 16 := by simp [regs3, hlen]
  have hsC3 : regs3[(2 : Fin 16).val]! = 0 := by dsimp only [regs3]; reg_val hlen
  obtain ⟨s6, hs6, step6⟩ :=
      exec_mul_loop (by decide : isMulLoop 1188 1192 1205 3 11 5 2 = true) regs3 hlen3 hsC3
  have hset6 : (regs3.set (5 : Fin 16).val (regs3[(5 : Fin 16).val]! +
      regs3[(3 : Fin 16).val]! * regs3[(11 : Fin 16).val]!)).set (3 : Fin 16).val 0 =
      regs.set 5 (harmNum m * (m + 1)) := by
    have hA3 : regs3[(3 : Fin 16).val]! = harmNum m := by dsimp only [regs3]; reg_val hlen
    have hI3 : regs3[(11 : Fin 16).val]! = m + 1 := by dsimp only [regs3]; reg_val hlen
    have hB3 : regs3[(5 : Fin 16).val]! = 0 := by dsimp only [regs3]; reg_val hlen
    rw [hA3, hI3, hB3, Nat.zero_add]; dsimp only [regs3]; regs_eq hlen
  rw [hset6] at step6
  let regs4 := regs.set 5 (harmNum m * (m + 1))
  have hlen4 : regs4.length = 16 := by simp [regs4, hlen]
  obtain ⟨s7, hs7, step7⟩ := exec_noop_to (by decide : isNoopTo 1205 1208 = true) regs4
  have hsA4 : regs4[(3 : Fin 16).val]! = 0 := by dsimp only [regs4]; reg_val hlen
  obtain ⟨s8, hs8, step8⟩ :=
      exec_copy_add (by decide : isCopyAdd 1208 15 5 3 = true) regs4 hlen4 hsA4
  have hset8 : regs4.set (5 : Fin 16).val (regs4[(5 : Fin 16).val]! + regs4[(15 : Fin 16).val]!) =
      regs.set 5 (harmNum (m + 1)) := by
    rw [harmNum_succ]; dsimp only [regs4]; regs_eq hlen
  rw [hset8] at step8
  let regs5 := regs.set 5 (harmNum (m + 1))
  have hlen5 : regs5.length = 16 := by simp [regs5, hlen]
  obtain ⟨s9, hs9, step9⟩ := exec_transfer1 (by decide : isTransfer1 1220 14 = true) regs5 hlen5
  let regs6 := regs5.set (14 : Fin 16).val 0
  have hlen6 : regs6.length = 16 := by simp [regs6, regs5, hlen]
  obtain ⟨s10, hs10, step10⟩ :=
      exec_transfer2 (by decide : isTransfer2 1224 5 14 = true) regs6 hlen6
  have hset10 : (regs6.set (14 : Fin 16).val (regs6[(14 : Fin 16).val]! +
      regs6[(5 : Fin 16).val]!)).set (5 : Fin 16).val 0 =
      regs.set 14 (harmNum (m + 1)) := by
    dsimp only [regs6, regs5]; regs_eq hlen
  rw [hset10] at step10
  let regs7 := regs.set 14 (harmNum (m + 1))
  have hlen7 : regs7.length = 16 := by simp [regs7, hlen]
  have step11 := step_jump (by decide : program 1228 = .jump 1232) regs7
  have hsC7 : regs7[(2 : Fin 16).val]! = 0 := by dsimp only [regs7]; reg_val hlen
  obtain ⟨s12, hs12, step12⟩ :=
      exec_copy_add (by decide : isCopyAdd 1232 15 3 2 = true) regs7 hlen7 hsC7
  have hset12 : regs7.set (3 : Fin 16).val (regs7[(3 : Fin 16).val]! + regs7[(15 : Fin 16).val]!) =
      regs7.set 3 m.factorial := by dsimp only [regs7]; regs_eq hlen
  rw [hset12] at step12
  let regs8 := regs7.set 3 m.factorial
  have hlen8 : regs8.length = 16 := by simp [regs8, regs7, hlen]
  have hsC8 : regs8[(2 : Fin 16).val]! = 0 := by dsimp only [regs8, regs7]; reg_val hlen
  obtain ⟨s13, hs13, step13⟩ :=
      exec_mul_loop (by decide : isMulLoop 1244 1248 1261 3 11 5 2 = true) regs8 hlen8 hsC8
  have hset13 : (regs8.set (5 : Fin 16).val (regs8[(5 : Fin 16).val]! +
      regs8[(3 : Fin 16).val]! * regs8[(11 : Fin 16).val]!)).set (3 : Fin 16).val 0 =
      regs7.set 5 (m + 1).factorial := by
    have hA8 : regs8[(3 : Fin 16).val]! = m.factorial := by dsimp only [regs8, regs7]; reg_val hlen
    have hI8 : regs8[(11 : Fin 16).val]! = m + 1 := by dsimp only [regs8, regs7]; reg_val hlen
    have hB8 : regs8[(5 : Fin 16).val]! = 0 := by dsimp only [regs8, regs7]; reg_val hlen
    have hfac : m.factorial * (m + 1) = (m + 1).factorial := by
      rw [Nat.factorial_succ, Nat.mul_comm]
    rw [hA8, hI8, hB8, Nat.zero_add, hfac]; dsimp only [regs8, regs7]; regs_eq hlen
  rw [hset13] at step13
  let regs9 := regs7.set 5 (m + 1).factorial
  have hlen9 : regs9.length = 16 := by simp [regs9, regs7, hlen]
  obtain ⟨s14, hs14, step14⟩ := exec_noop_to (by decide : isNoopTo 1261 1264 = true) regs9
  obtain ⟨s15, hs15, step15⟩ := exec_transfer1 (by decide : isTransfer1 1264 15 = true) regs9 hlen9
  let regs10 := regs9.set (15 : Fin 16).val 0
  have hlen10 : regs10.length = 16 := by simp [regs10, regs9, regs7, hlen]
  obtain ⟨s16, hs16, step16⟩ :=
      exec_transfer2 (by decide : isTransfer2 1268 5 15 = true) regs10 hlen10
  have hset16 : (regs10.set (15 : Fin 16).val (regs10[(15 : Fin 16).val]! +
      regs10[(5 : Fin 16).val]!)).set (5 : Fin 16).val 0 =
      (regs.set 14 (harmNum (m + 1))).set 15 (m + 1).factorial := by
    dsimp only [regs10, regs9, regs7]; regs_eq hlen
  rw [hset16] at step16
  let regs11 := (regs.set 14 (harmNum (m + 1))).set 15 (m + 1).factorial
  have step17 := step_incr (by decide : program 1272 = .incr 11) regs11
  have hset17 : regs11.set (11 : Fin 16).val (regs11[(11 : Fin 16).val]! + 1) =
      ((regs.set 14 (harmNum (m + 1))).set 15 (m + 1).factorial).set 11 (m + 1 + 1) := by
    dsimp only [regs11]; regs_eq hlen
  rw [hset17] at step17
  let regs12 := ((regs.set 14 (harmNum (m + 1))).set 15 (m + 1).factorial).set 11 (m + 1 + 1)
  have step18 := step_jump (by decide : program 1273 = .jump 1121) regs12
  exact ⟨s0 + s1 + 1 + s3 + s4 + s5 + s6 + s7 + s8 + s9 + s10 + 1 + s12 + s13 + s14 + s15 + s16 +
    1 + 1, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
      (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
        (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
          (regNSteps_bind_eq
          (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq step0 step1) step2) step3) step4)
          step5) step6) step7) step8) step9) step10) step11) step12) step13) step14) step15)
            step16) step17) step18⟩

theorem exec_harm_exit_1104 (regs : List ℕ) (hlen : regs.length = 16)
    (hI : regs[11]! = regs[1]! + 1)
    (hsA : regs[3]! = 0) (hsB : regs[5]! = 0) (hsC : regs[2]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨1121, regs⟩ = some ⟨1274, regs⟩ := by
  obtain ⟨s0, hs0, step0⟩ := exec_noop_to (by decide : isNoopTo 1121 1128 = true) regs
  obtain ⟨s1, hs1, step1⟩ := exec_copy_add (by decide : isCopyAdd 1128 11 3 5 = true) regs hlen hsB
  have hset1 : regs.set (3 : Fin 16).val (regs[(3 : Fin 16).val]! + regs[(11 : Fin 16).val]!) =
      regs.set 3 (regs[1]! + 1) := by regs_eq hlen
  rw [hset1] at step1
  let regs1 := regs.set 3 (regs[1]! + 1)
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have step2 := step_jump (by decide : program 1140 = .jump 1144) regs1
  have hsC1 : regs1[(2 : Fin 16).val]! = 0 := by dsimp only [regs1]; reg_val hlen
  obtain ⟨s3, hs3, step3⟩ :=
      exec_copy_add (by decide : isCopyAdd 1144 1 5 2 = true) regs1 hlen1 hsC1
  have hset3 : regs1.set (5 : Fin 16).val (regs1[(5 : Fin 16).val]! + regs1[(1 : Fin 16).val]!) =
      (regs.set 3 (regs[1]! + 1)).set 5 regs[1]! := by dsimp only [regs1]; regs_eq hlen
  rw [hset3] at step3
  let regs2 := (regs.set 3 (regs[1]! + 1)).set 5 regs[1]!
  have hlen2 : regs2.length = 16 := by simp [regs2, hlen]
  have hgt2 : regs2[(5 : Fin 16).val]! < regs2[(3 : Fin 16).val]! := by
    dsimp only [regs2]; reg_val hlen
  obtain ⟨s4, hs4, step4⟩ :=
      exec_le_branch_gt (by decide : isLeBranch 1156 1274 5 3 = true) regs2 hlen2 hgt2
  have hset4 : (regs2.set (3 : Fin 16).val 0).set (5 : Fin 16).val 0 = regs := by
    dsimp only [regs2]; regs_eq hlen
  rw [hset4] at step4
  exact ⟨s0 + s1 + 1 + s3 + s4, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq step0 step1) step2)
      step3) step4⟩

theorem exec_harm_loop_aux_1104 :
    ∀ (k m : ℕ) (regs : List ℕ), regs.length = 16 →
      regs[14]! = harmNum m → regs[15]! = m.factorial → regs[11]! = m + 1 →
      regs[3]! = 0 → regs[5]! = 0 → regs[2]! = 0 →
      m + k = regs[1]! →
      ∃ s, 1 ≤ s ∧ regNSteps s ⟨1121, regs⟩ =
        some ⟨1274,
          ((regs.set 14 (harmNum regs[1]!)).set 15 (regs[1]!).factorial).set 11 (regs[1]! + 1)⟩
  | 0, m, regs, hlen, hNum, hDenom, hI, hsA, hsB, hsC, hk => by
    have hm : m = regs[1]! := by omega
    subst hm
    obtain ⟨s, hs, step⟩ := exec_harm_exit_1104 regs hlen hI hsA hsB hsC
    have hset : ((regs.set 14 (harmNum regs[1]!)).set 15 (regs[1]!).factorial).set 11 (regs[1]! +
        1) = regs := by
      rw [← hNum, ← hDenom, ← hI]; regs_eq hlen
    rw [hset]
    exact ⟨s, hs, step⟩
  | k + 1, m, regs, hlen, hNum, hDenom, hI, hsA, hsB, hsC, hk => by
    have hm : m < regs[1]! := by omega
    obtain ⟨s1, hs1, step1⟩ := exec_harm_iter_1104 m regs hlen hNum hDenom hI hsA hsB hsC hm
    let regs1 := ((regs.set 14 (harmNum (m + 1))).set 15 (m + 1).factorial).set 11 (m + 1 + 1)
    have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
    have hNum1 : regs1[14]! = harmNum (m + 1) := by dsimp only [regs1]; reg_val hlen
    have hDenom1 : regs1[15]! = (m + 1).factorial := by dsimp only [regs1]; reg_val hlen
    have hI1 : regs1[11]! = (m + 1) + 1 := by dsimp only [regs1]; reg_val hlen
    have hsA1 : regs1[3]! = 0 := by dsimp only [regs1]; reg_val hlen
    have hsB1 : regs1[5]! = 0 := by dsimp only [regs1]; reg_val hlen
    have hsC1 : regs1[2]! = 0 := by dsimp only [regs1]; reg_val hlen
    have hN1 : regs1[1]! = regs[1]! := by dsimp only [regs1]; reg_val hlen
    obtain ⟨s2, hs2, step2⟩ := exec_harm_loop_aux_1104 k (m + 1) regs1 hlen1
      hNum1 hDenom1 hI1 hsA1 hsB1 hsC1 (by rw [hN1]; omega)
    have heq : ((regs1.set 14 (harmNum regs1[1]!)).set 15 (regs1[1]!).factorial).set 11 (regs1[1]!
        + 1) =
        ((regs.set 14 (harmNum regs[1]!)).set 15 (regs[1]!).factorial).set 11 (regs[1]! + 1) := by
      rw [hN1]; dsimp only [regs1]; regs_eq hlen
    rw [heq] at step2
    exact ⟨s1 + s2, by omega, regNSteps_bind_eq step1 step2⟩

theorem exec_harm_1104 (regs : List ℕ) (hlen : regs.length = 16)
    (hsA : regs[3]! = 0) (hsB : regs[5]! = 0) (hsC : regs[2]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨1104, regs⟩ =
      some ⟨1274,
        ((regs.set 14 (harmNum regs[1]!)).set 15 (regs[1]!).factorial).set 11 (regs[1]! + 1)⟩ := by
  obtain ⟨s1, hs1, step1⟩ := exec_transfer1 (by decide : isTransfer1 1104 14 = true) regs hlen
  let regs1 := regs.set (14 : Fin 16).val 0
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  obtain ⟨s2, hs2, step2⟩ := exec_transfer1 (by decide : isTransfer1 1108 15 = true) regs1 hlen1
  let regs2 := regs1.set (15 : Fin 16).val 0
  have step3 := step_incr (by decide : program 1112 = .incr 15) regs2
  let regs3 := regs2.set (15 : Fin 16).val (regs2[(15 : Fin 16).val]! + 1)
  obtain ⟨s4, hs4, step4⟩ := exec_noop_to (by decide : isNoopTo 1113 1116 = true) regs3
  have hlen3 : regs3.length = 16 := by simp [regs3, regs2, regs1, hlen]
  obtain ⟨s5, hs5, step5⟩ := exec_transfer1 (by decide : isTransfer1 1116 11 = true) regs3 hlen3
  let regs4 := regs3.set (11 : Fin 16).val 0
  have step6 := step_incr (by decide : program 1120 = .incr 11) regs4
  have hset6 : regs4.set (11 : Fin 16).val (regs4[(11 : Fin 16).val]! + 1) =
      ((regs.set 14 (harmNum 0)).set 15 (0 : ℕ).factorial).set 11 (0 + 1) := by
    dsimp only [regs4, regs3, regs2, regs1, harmNum, Nat.factorial]; regs_eq hlen
  rw [hset6] at step6
  let regs5 := ((regs.set 14 (harmNum 0)).set 15 (0 : ℕ).factorial).set 11 (0 + 1)
  have hlen5 : regs5.length = 16 := by simp [regs5, hlen]
  have hNum5 : regs5[14]! = harmNum 0 := by dsimp only [regs5]; reg_val hlen
  have hDenom5 : regs5[15]! = (0 : ℕ).factorial := by dsimp only [regs5]; reg_val hlen
  have hI5 : regs5[11]! = 0 + 1 := by dsimp only [regs5]; reg_val hlen
  have hsA5 : regs5[3]! = 0 := by dsimp only [regs5]; reg_val hlen
  have hsB5 : regs5[5]! = 0 := by dsimp only [regs5]; reg_val hlen
  have hsC5 : regs5[2]! = 0 := by dsimp only [regs5]; reg_val hlen
  have hN5 : regs5[1]! = regs[1]! := by dsimp only [regs5]; reg_val hlen
  obtain ⟨s7, hs7, step7⟩ := exec_harm_loop_aux_1104 regs[1]! 0 regs5 hlen5
    hNum5 hDenom5 hI5 hsA5 hsB5 hsC5 (by rw [hN5]; omega)
  have heq : ((regs5.set 14 (harmNum regs5[1]!)).set 15 (regs5[1]!).factorial).set 11 (regs5[1]! +
      1) =
      ((regs.set 14 (harmNum regs[1]!)).set 15 (regs[1]!).factorial).set 11 (regs[1]! + 1) := by
    rw [hN5]; dsimp only [regs5]; regs_eq hlen
  rw [heq] at step7
  exact ⟨s1 + s2 + 1 + s4 + s5 + 1 + s7, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
      (regNSteps_bind_eq (regNSteps_bind_eq step1 step2) step3) step4) step5) step6) step7⟩

theorem exec_post_harm_946 (regs : List ℕ) (hlen : regs.length = 16)
    (hz2 : regs[2]! = 0) (hz3 : regs[3]! = 0) (hz5 : regs[5]! = 0)
    (hz6 : regs[6]! = 0) (hz7 : regs[7]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨946, regs⟩ =
      some ⟨1104,
        (regs.set 12 ((regs[9]! - regs[10]! * regs[1]!) ^ 2)).set 13 (regs[10]! ^ 2)⟩ := by
  obtain ⟨s0, hs0, step0⟩ := exec_noop_to (by decide : isNoopTo 946 952 = true) regs
  obtain ⟨s1, hs1, step1⟩ := exec_copy_add (by decide : isCopyAdd 952 9 2 5 = true) regs hlen hz5
  have hset1 : regs.set (2 : Fin 16).val (regs[(2 : Fin 16).val]! + regs[(9 : Fin 16).val]!) =
      regs.set 2 regs[9]! := by regs_eq hlen
  rw [hset1] at step1
  let regs1 := regs.set 2 regs[9]!
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have step2 := step_jump (by decide : program 964 = .jump 968) regs1
  have hz7_1 : regs1[(7 : Fin 16).val]! = 0 := by dsimp only [regs1]; reg_val hlen
  obtain ⟨s3, hs3, step3⟩ :=
      exec_copy_add (by decide : isCopyAdd 968 10 6 7 = true) regs1 hlen1 hz7_1
  have hset3 : regs1.set (6 : Fin 16).val (regs1[(6 : Fin 16).val]! + regs1[(10 : Fin 16).val]!) =
      (regs.set 2 regs[9]!).set 6 regs[10]! := by dsimp only [regs1]; regs_eq hlen
  rw [hset3] at step3
  let regs2 := (regs.set 2 regs[9]!).set 6 regs[10]!
  have hlen2 : regs2.length = 16 := by simp [regs2, hlen]
  have hz7_2 : regs2[(7 : Fin 16).val]! = 0 := by dsimp only [regs2]; reg_val hlen
  obtain ⟨s4, hs4, step4⟩ :=
      exec_mul_loop (by decide : isMulLoop 980 984 997 6 1 5 7 = true) regs2 hlen2 hz7_2
  have hset4 : (regs2.set (5 : Fin 16).val (regs2[(5 : Fin 16).val]! +
      regs2[(6 : Fin 16).val]! * regs2[(1 : Fin 16).val]!)).set (6 : Fin 16).val 0 =
      (regs.set 2 regs[9]!).set 5 (regs[10]! * regs[1]!) := by
    have h6_2 : regs2[(6 : Fin 16).val]! = regs[10]! := by dsimp only [regs2]; reg_val hlen
    have h1_2 : regs2[(1 : Fin 16).val]! = regs[1]! := by dsimp only [regs2]; reg_val hlen
    have h5_2 : regs2[(5 : Fin 16).val]! = 0 := by dsimp only [regs2]; reg_val hlen
    rw [h6_2, h1_2, h5_2, Nat.zero_add]; dsimp only [regs2]; regs_eq hlen
  rw [hset4] at step4
  let regs3 := (regs.set 2 regs[9]!).set 5 (regs[10]! * regs[1]!)
  have hlen3 : regs3.length = 16 := by simp [regs3, hlen]
  obtain ⟨s5, hs5, step5⟩ := exec_noop_to (by decide : isNoopTo 997 1000 = true) regs3
  obtain ⟨s6, hs6, step6⟩ := exec_transfer2 (by decide : isTransfer2 1000 2 3 = true) regs3 hlen3
  have hset6 : (regs3.set (3 : Fin 16).val (regs3[(3 : Fin 16).val]! +
      regs3[(2 : Fin 16).val]!)).set (2 : Fin 16).val 0 =
      (regs.set 3 regs[9]!).set 5 (regs[10]! * regs[1]!) := by
    dsimp only [regs3]; regs_eq hlen
  rw [hset6] at step6
  let regs4 := (regs.set 3 regs[9]!).set 5 (regs[10]! * regs[1]!)
  have hlen4 : regs4.length = 16 := by simp [regs4, hlen]
  obtain ⟨s7, hs7, step7⟩ := exec_sub_loop (by decide : isSubLoop 1004 5 3 = true) regs4 hlen4
  have hset7 : (regs4.set (3 : Fin 16).val (regs4[(3 : Fin 16).val]! -
      regs4[(5 : Fin 16).val]!)).set (5 : Fin 16).val 0 =
      regs.set 3 (regs[9]! - regs[10]! * regs[1]!) := by
    dsimp only [regs4]; regs_eq hlen
  rw [hset7] at step7
  let regs5 := regs.set 3 (regs[9]! - regs[10]! * regs[1]!)
  have hlen5 : regs5.length = 16 := by simp [regs5, hlen]
  obtain ⟨s8, hs8, step8⟩ := exec_noop_to (by decide : isNoopTo 1009 1012 = true) regs5
  obtain ⟨s9, hs9, step9⟩ := exec_transfer1 (by decide : isTransfer1 1012 12 = true) regs5 hlen5
  let regs6 := regs5.set (12 : Fin 16).val 0
  have hlen6 : regs6.length = 16 := by simp [regs6, regs5, hlen]
  obtain ⟨s10, hs10, step10⟩ :=
      exec_transfer2 (by decide : isTransfer2 1016 3 12 = true) regs6 hlen6
  have hset10 : (regs6.set (12 : Fin 16).val (regs6[(12 : Fin 16).val]! +
      regs6[(3 : Fin 16).val]!)).set (3 : Fin 16).val 0 =
      regs.set 12 (regs[9]! - regs[10]! * regs[1]!) := by
    dsimp only [regs6, regs5]; regs_eq hlen
  rw [hset10] at step10
  let regs7 := regs.set 12 (regs[9]! - regs[10]! * regs[1]!)
  have hlen7 : regs7.length = 16 := by simp [regs7, hlen]
  have step11 := step_jump (by decide : program 1020 = .jump 1024) regs7
  have hz5_7 : regs7[(5 : Fin 16).val]! = 0 := by dsimp only [regs7]; reg_val hlen
  have hz3_7 : regs7[(3 : Fin 16).val]! = 0 := by dsimp only [regs7]; reg_val hlen
  have hz2_7 : regs7[(2 : Fin 16).val]! = 0 := by dsimp only [regs7]; reg_val hlen
  obtain ⟨s12, hs12, step12⟩ :=
      exec_square_assign (by decide : isSquareAssign 1024 12 12 5 3 2 =
        true) regs7 hlen7 hz5_7 hz3_7 hz2_7
  have hset12 : regs7.set (12 : Fin 16).val (regs7[(12 : Fin 16).val]! * regs7[(12 : Fin 16).val]!)
      =
      regs.set 12 ((regs[9]! - regs[10]! * regs[1]!) ^ 2) := by
    have h12_7 : regs7[(12 : Fin 16).val]! = regs[9]! - regs[10]! * regs[1]! := by
      dsimp only [regs7]; reg_val hlen
    rw [h12_7]; dsimp only [regs7]; regs_eq hlen
  rw [hset12] at step12
  let regs8 := regs.set 12 ((regs[9]! - regs[10]! * regs[1]!) ^ 2)
  have hlen8 : regs8.length = 16 := by simp [regs8, hlen]
  have hz5_8 : regs8[(5 : Fin 16).val]! = 0 := by dsimp only [regs8]; reg_val hlen
  have hz3_8 : regs8[(3 : Fin 16).val]! = 0 := by dsimp only [regs8]; reg_val hlen
  have hz2_8 : regs8[(2 : Fin 16).val]! = 0 := by dsimp only [regs8]; reg_val hlen
  obtain ⟨s13, hs13, step13⟩ :=
      exec_square_assign (by decide : isSquareAssign 1064 10 13 5 3 2 =
        true) regs8 hlen8 hz5_8 hz3_8 hz2_8
  have hset13 : regs8.set (13 : Fin 16).val (regs8[(10 : Fin 16).val]! * regs8[(10 : Fin 16).val]!)
      =
      (regs.set 12 ((regs[9]! - regs[10]! * regs[1]!) ^ 2)).set 13 (regs[10]! ^ 2) := by
    have h10_8 : regs8[(10 : Fin 16).val]! = regs[10]! := by dsimp only [regs8]; reg_val hlen
    rw [h10_8]; dsimp only [regs8]; regs_eq hlen
  rw [hset13] at step13
  exact ⟨s0 + s1 + 1 + s3 + s4 + s5 + s6 + s7 + s8 + s9 + s10 + 1 + s12 + s13, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
      (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
        (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq step0 step1) step2) step3) step4)
        step5) step6) step7) step8) step9) step10) step11) step12) step13⟩

theorem exec_post_harm_1274 (regs : List ℕ) (hlen : regs.length = 16)
    (hz2 : regs[2]! = 0) (hz3 : regs[3]! = 0) (hz5 : regs[5]! = 0) (hz6 : regs[6]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨1274, regs⟩ =
      some ⟨1456, (regs.set 14 (regs[14]! ^ 4 * regs[1]!)).set 15 (regs[15]! ^ 4)⟩ := by
  obtain ⟨s0, hs0, step0⟩ := exec_noop_to (by decide : isNoopTo 1274 1280 = true) regs
  obtain ⟨s1, hs1, step1⟩ :=
      exec_square_assign (by decide : isSquareAssign 1280 14 14 3 5 2 = true) regs hlen hz3 hz5 hz2
  have hset1 : regs.set (14 : Fin 16).val (regs[(14 : Fin 16).val]! * regs[(14 : Fin 16).val]!) =
      regs.set 14 (regs[14]! ^ 2) := by regs_eq hlen
  rw [hset1] at step1
  let regs1 := regs.set 14 (regs[14]! ^ 2)
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have hz6_1 : regs1[(6 : Fin 16).val]! = 0 := by dsimp only [regs1]; reg_val hlen
  obtain ⟨s2, hs2, step2⟩ :=
      exec_copy_add (by decide : isCopyAdd 1320 14 2 6 = true) regs1 hlen1 hz6_1
  have hset2 : regs1.set (2 : Fin 16).val (regs1[(2 : Fin 16).val]! + regs1[(14 : Fin 16).val]!) =
      (regs.set 14 (regs[14]! ^ 2)).set 2 (regs[14]! ^ 2) := by dsimp only [regs1]; regs_eq hlen
  rw [hset2] at step2
  let regs2 := (regs.set 14 (regs[14]! ^ 2)).set 2 (regs[14]! ^ 2)
  have hlen2 : regs2.length = 16 := by simp [regs2, hlen]
  have hz6_2 : regs2[(6 : Fin 16).val]! = 0 := by dsimp only [regs2]; reg_val hlen
  obtain ⟨s3, hs3, step3⟩ :=
      exec_mul_loop (by decide : isMulLoop 1332 1336 1349 2 14 3 6 = true) regs2 hlen2 hz6_2
  have hset3 : (regs2.set (3 : Fin 16).val (regs2[(3 : Fin 16).val]! +
      regs2[(2 : Fin 16).val]! * regs2[(14 : Fin 16).val]!)).set (2 : Fin 16).val 0 =
      (regs.set 14 (regs[14]! ^ 2)).set 3 (regs[14]! ^ 4) := by
    have h2_2 : regs2[(2 : Fin 16).val]! = regs[14]! ^ 2 := by dsimp only [regs2]; reg_val hlen
    have h14_2 : regs2[(14 : Fin 16).val]! = regs[14]! ^ 2 := by dsimp only [regs2]; reg_val hlen
    have h3_2 : regs2[(3 : Fin 16).val]! = 0 := by dsimp only [regs2]; reg_val hlen
    have hpow : regs[14]! ^ 2 * regs[14]! ^ 2 = regs[14]! ^ 4 := by ring
    rw [h2_2, h14_2, h3_2, Nat.zero_add, hpow]; dsimp only [regs2]; regs_eq hlen
  rw [hset3] at step3
  let regs3 := (regs.set 14 (regs[14]! ^ 2)).set 3 (regs[14]! ^ 4)
  have hlen3 : regs3.length = 16 := by simp [regs3, hlen]
  have hz2_3 : regs3[(2 : Fin 16).val]! = 0 := by dsimp only [regs3]; reg_val hlen
  obtain ⟨s4, hs4, step4⟩ :=
      exec_mul_loop (by decide : isMulLoop 1349 1352 1365 3 1 5 2 = true) regs3 hlen3 hz2_3
  have hset4 : (regs3.set (5 : Fin 16).val (regs3[(5 : Fin 16).val]! +
      regs3[(3 : Fin 16).val]! * regs3[(1 : Fin 16).val]!)).set (3 : Fin 16).val 0 =
      (regs.set 14 (regs[14]! ^ 2)).set 5 (regs[14]! ^ 4 * regs[1]!) := by
    have h3_3 : regs3[(3 : Fin 16).val]! = regs[14]! ^ 4 := by dsimp only [regs3]; reg_val hlen
    have h1_3 : regs3[(1 : Fin 16).val]! = regs[1]! := by dsimp only [regs3]; reg_val hlen
    have h5_3 : regs3[(5 : Fin 16).val]! = 0 := by dsimp only [regs3]; reg_val hlen
    rw [h3_3, h1_3, h5_3, Nat.zero_add]; dsimp only [regs3]; regs_eq hlen
  rw [hset4] at step4
  let regs4 := (regs.set 14 (regs[14]! ^ 2)).set 5 (regs[14]! ^ 4 * regs[1]!)
  have hlen4 : regs4.length = 16 := by simp [regs4, hlen]
  obtain ⟨s5, hs5, step5⟩ := exec_noop_to (by decide : isNoopTo 1365 1368 = true) regs4
  obtain ⟨s6, hs6, step6⟩ := exec_transfer1 (by decide : isTransfer1 1368 14 = true) regs4 hlen4
  let regs5 := regs4.set (14 : Fin 16).val 0
  have hlen5 : regs5.length = 16 := by simp [regs5, regs4, hlen]
  obtain ⟨s7, hs7, step7⟩ := exec_transfer2 (by decide : isTransfer2 1372 5 14 = true) regs5 hlen5
  have hset7 : (regs5.set (14 : Fin 16).val (regs5[(14 : Fin 16).val]! +
      regs5[(5 : Fin 16).val]!)).set (5 : Fin 16).val 0 =
      regs.set 14 (regs[14]! ^ 4 * regs[1]!) := by
    dsimp only [regs5, regs4]; regs_eq hlen
  rw [hset7] at step7
  let regs6 := regs.set 14 (regs[14]! ^ 4 * regs[1]!)
  have hlen6 : regs6.length = 16 := by simp [regs6, hlen]
  have hz3_6 : regs6[(3 : Fin 16).val]! = 0 := by dsimp only [regs6]; reg_val hlen
  have hz5_6 : regs6[(5 : Fin 16).val]! = 0 := by dsimp only [regs6]; reg_val hlen
  have hz2_6 : regs6[(2 : Fin 16).val]! = 0 := by dsimp only [regs6]; reg_val hlen
  obtain ⟨s8, hs8, step8⟩ :=
      exec_square_assign (by decide : isSquareAssign 1376 15 15 3 5 2 =
        true) regs6 hlen6 hz3_6 hz5_6 hz2_6
  have hset8 : regs6.set (15 : Fin 16).val (regs6[(15 : Fin 16).val]! * regs6[(15 : Fin 16).val]!) =
      (regs.set 14 (regs[14]! ^ 4 * regs[1]!)).set 15 (regs[15]! ^ 2) := by
    dsimp only [regs6]; regs_eq hlen
  rw [hset8] at step8
  let regs7 := (regs.set 14 (regs[14]! ^ 4 * regs[1]!)).set 15 (regs[15]! ^ 2)
  have hlen7 : regs7.length = 16 := by simp [regs7, hlen]
  have hz3_7 : regs7[(3 : Fin 16).val]! = 0 := by dsimp only [regs7]; reg_val hlen
  have hz5_7 : regs7[(5 : Fin 16).val]! = 0 := by dsimp only [regs7]; reg_val hlen
  have hz2_7 : regs7[(2 : Fin 16).val]! = 0 := by dsimp only [regs7]; reg_val hlen
  obtain ⟨s9, hs9, step9⟩ :=
      exec_square_assign (by decide : isSquareAssign 1416 15 15 3 5 2 =
        true) regs7 hlen7 hz3_7 hz5_7 hz2_7
  have hset9 : regs7.set (15 : Fin 16).val (regs7[(15 : Fin 16).val]! * regs7[(15 : Fin 16).val]!) =
      (regs.set 14 (regs[14]! ^ 4 * regs[1]!)).set 15 (regs[15]! ^ 4) := by
    dsimp only [regs7]; regs_eq hlen
  rw [hset9] at step9
  exact ⟨s0 + s1 + s2 + s3 + s4 + s5 + s6 + s7 + s8 + s9, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
      (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq
        (regNSteps_bind_eq step0 step1) step2) step3) step4) step5) step6) step7) step8) step9⟩

theorem exec_final_1456_prep (regs : List ℕ) (hlen : regs.length = 16)
    (hz2 : regs[2]! = 0) (hz3 : regs[3]! = 0) (hz5 : regs[5]! = 0) (hz6 : regs[6]! = 0) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨1456, regs⟩ =
      some ⟨1517, (regs.set 5 (regs[12]! * regs[15]!)).set 3 (regs[13]! * regs[14]!)⟩ := by
  obtain ⟨s1, hs1, step1⟩ := exec_copy_add (by decide : isCopyAdd 1456 12 3 2 = true) regs hlen hz2
  have hset1 : regs.set (3 : Fin 16).val (regs[(3 : Fin 16).val]! + regs[(12 : Fin 16).val]!) =
      regs.set 3 regs[12]! := by regs_eq hlen
  rw [hset1] at step1
  let regs1 := regs.set 3 regs[12]!
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have hz2_1 : regs1[(2 : Fin 16).val]! = 0 := by dsimp only [regs1]; reg_val hlen
  obtain ⟨s2, hs2, step2⟩ :=
      exec_mul_loop (by decide : isMulLoop 1468 1472 1485 3 15 5 2 = true) regs1 hlen1 hz2_1
  have hset2 : (regs1.set (5 : Fin 16).val (regs1[(5 : Fin 16).val]! +
      regs1[(3 : Fin 16).val]! * regs1[(15 : Fin 16).val]!)).set (3 : Fin 16).val 0 =
      regs.set 5 (regs[12]! * regs[15]!) := by
    have h3_1 : regs1[(3 : Fin 16).val]! = regs[12]! := by dsimp only [regs1]; reg_val hlen
    have h15_1 : regs1[(15 : Fin 16).val]! = regs[15]! := by dsimp only [regs1]; reg_val hlen
    have h5_1 : regs1[(5 : Fin 16).val]! = 0 := by dsimp only [regs1]; reg_val hlen
    rw [h3_1, h15_1, h5_1, Nat.zero_add]; dsimp only [regs1]; regs_eq hlen
  rw [hset2] at step2
  let regs2 := regs.set 5 (regs[12]! * regs[15]!)
  have hlen2 : regs2.length = 16 := by simp [regs2, hlen]
  obtain ⟨s3, hs3, step3⟩ := exec_noop_to (by decide : isNoopTo 1485 1488 = true) regs2
  have hz6_2 : regs2[(6 : Fin 16).val]! = 0 := by dsimp only [regs2]; reg_val hlen
  obtain ⟨s4, hs4, step4⟩ :=
      exec_copy_add (by decide : isCopyAdd 1488 13 2 6 = true) regs2 hlen2 hz6_2
  have hset4 : regs2.set (2 : Fin 16).val (regs2[(2 : Fin 16).val]! + regs2[(13 : Fin 16).val]!) =
      (regs.set 5 (regs[12]! * regs[15]!)).set 2 regs[13]! := by dsimp only [regs2]; regs_eq hlen
  rw [hset4] at step4
  let regs3 := (regs.set 5 (regs[12]! * regs[15]!)).set 2 regs[13]!
  have hlen3 : regs3.length = 16 := by simp [regs3, hlen]
  have hz6_3 : regs3[(6 : Fin 16).val]! = 0 := by dsimp only [regs3]; reg_val hlen
  obtain ⟨s5, hs5, step5⟩ :=
      exec_mul_loop (by decide : isMulLoop 1500 1504 1517 2 14 3 6 = true) regs3 hlen3 hz6_3
  have hset5 : (regs3.set (3 : Fin 16).val (regs3[(3 : Fin 16).val]! +
      regs3[(2 : Fin 16).val]! * regs3[(14 : Fin 16).val]!)).set (2 : Fin 16).val 0 =
      (regs.set 5 (regs[12]! * regs[15]!)).set 3 (regs[13]! * regs[14]!) := by
    have h2_3 : regs3[(2 : Fin 16).val]! = regs[13]! := by dsimp only [regs3]; reg_val hlen
    have h14_3 : regs3[(14 : Fin 16).val]! = regs[14]! := by dsimp only [regs3]; reg_val hlen
    have h3_3 : regs3[(3 : Fin 16).val]! = 0 := by dsimp only [regs3]; reg_val hlen
    rw [h2_3, h14_3, h3_3, Nat.zero_add]; dsimp only [regs3]; regs_eq hlen
  rw [hset5] at step5
  exact ⟨s1 + s2 + s3 + s4 + s5, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq step1 step2) step3)
      step4) step5⟩

theorem regNSteps_bind_none {m n : ℕ} {c₁ c₂ : RegCfg}
    (h₁ : regNSteps m c₁ = some c₂) (h₂ : regNSteps n c₂ = none) :
    regNSteps (m + n) c₁ = none := by
  rw [regNSteps_add, h₁, Option.bind_some, h₂]

theorem exec_final_1456_halt (regs : List ℕ) (hlen : regs.length = 16)
    (hz2 : regs[2]! = 0) (hz3 : regs[3]! = 0) (hz5 : regs[5]! = 0) (hz6 : regs[6]! = 0)
    (hlt : regs[13]! * regs[14]! < regs[12]! * regs[15]!) :
    ∃ s, regNSteps s ⟨1456, regs⟩ = none := by
  obtain ⟨s1, hs1, step1⟩ := exec_final_1456_prep regs hlen hz2 hz3 hz5 hz6
  let regs1 := (regs.set 5 (regs[12]! * regs[15]!)).set 3 (regs[13]! * regs[14]!)
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have hlt1 : regs1[(3 : Fin 16).val]! < regs1[(5 : Fin 16).val]! := by
    dsimp only [regs1]; reg_val hlen
  obtain ⟨s2, hs2, step2⟩ :=
      exec_cmp_branch_lt (by decide : isCmpBranch 1517 21 1539 21 3 5 = true) regs1 hlen1 hlt1
  have hclean : (regs1.set (5 : Fin 16).val 0).set (3 : Fin 16).val 0 = regs := by
    dsimp only [regs1]; regs_eq hlen
  rw [hclean] at step2
  have step3 := step_halt (by decide : program 1539 = .halt) regs
  exact ⟨s1 + s2 + 1, regNSteps_bind_none (regNSteps_bind_eq step1 step2) step3⟩

theorem exec_final_1456_continue (regs : List ℕ) (hlen : regs.length = 16)
    (hz2 : regs[2]! = 0) (hz3 : regs[3]! = 0) (hz5 : regs[5]! = 0) (hz6 : regs[6]! = 0)
    (hge : ¬ (regs[13]! * regs[14]! < regs[12]! * regs[15]!)) :
    ∃ s, 1 ≤ s ∧ regNSteps s ⟨1456, regs⟩ = some ⟨21, regs⟩ := by
  obtain ⟨s1, hs1, step1⟩ := exec_final_1456_prep regs hlen hz2 hz3 hz5 hz6
  let regs1 := (regs.set 5 (regs[12]! * regs[15]!)).set 3 (regs[13]! * regs[14]!)
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have hclean : (regs1.set (5 : Fin 16).val 0).set (3 : Fin 16).val 0 = regs := by
    dsimp only [regs1]; regs_eq hlen
  by_cases heq : regs[13]! * regs[14]! = regs[12]! * regs[15]!
  · have heq1 : regs1[(3 : Fin 16).val]! = regs1[(5 : Fin 16).val]! := by
      dsimp only [regs1]; reg_val hlen
    obtain ⟨s2, hs2, step2⟩ :=
        exec_cmp_branch_eq (by decide : isCmpBranch 1517 21 1539 21 3 5 = true) regs1 hlen1 heq1
    rw [hclean] at step2
    exact ⟨s1 + s2, by omega, regNSteps_bind_eq step1 step2⟩
  · have hgt : regs[12]! * regs[15]! < regs[13]! * regs[14]! := by omega
    have hgt1 : regs1[(5 : Fin 16).val]! < regs1[(3 : Fin 16).val]! := by
      dsimp only [regs1]; reg_val hlen
    obtain ⟨s2, hs2, step2⟩ :=
        exec_cmp_branch_gt (by decide : isCmpBranch 1517 21 1539 21 3 5 = true) regs1 hlen1 hgt1
    rw [hclean] at step2
    exact ⟨s1 + s2, by omega, regNSteps_bind_eq step1 step2⟩

def ValidLoopCfg (x : ℕ) (regs : List ℕ) : Prop :=
  regs.length = 16 ∧
  regs[0]! = lcmUpTo x ∧
  regs[1]! = x ∧
  regs[2]! = 0 ∧
  regs[3]! = 0 ∧
  regs[5]! = 0 ∧
  regs[6]! = 0 ∧
  regs[7]! = 0 ∧
  regs[8]! = 0

theorem exec_init :
    regNSteps 20 regInit = some ⟨21, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]⟩ := by
  decide

theorem validLoopCfg_init :
    ValidLoopCfg 0 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [lcmUpTo_zero]
  rfl

theorem exec_full_calc_from_780 (x : ℕ) (regs : List ℕ) (hcfg : ValidLoopCfg x regs) :
    ∃ s regs', 1 ≤ s ∧ regNSteps s ⟨780, regs⟩ = some ⟨1456, regs'⟩ ∧
      ValidLoopCfg x regs' ∧
      regs'[12]! = (harmNum (lcmUpTo x) - (lcmUpTo x).factorial * x) ^ 2 ∧
      regs'[13]! = (lcmUpTo x).factorial ^ 2 ∧
      regs'[14]! = harmNum x ^ 4 * x ∧
      regs'[15]! = x.factorial ^ 4 := by
  rcases hcfg with ⟨hlen, h0, h1, hz2, hz3, hz5, hz6, hz7, hz8⟩
  obtain ⟨s1, hs1, step1⟩ := exec_harm_780 regs hlen hz2 hz3 hz5
  let regs1 := ((regs.set 9 (harmNum regs[0]!)).set 10 (regs[0]!).factorial).set 11 (regs[0]! + 1)
  have hlen1 : regs1.length = 16 := by simp [regs1, hlen]
  have hz2_1 : regs1[2]! = 0 := by dsimp only [regs1]; reg_val hlen
  have hz3_1 : regs1[3]! = 0 := by dsimp only [regs1]; reg_val hlen
  have hz5_1 : regs1[5]! = 0 := by dsimp only [regs1]; reg_val hlen
  have hz6_1 : regs1[6]! = 0 := by dsimp only [regs1]; reg_val hlen
  have hz7_1 : regs1[7]! = 0 := by dsimp only [regs1]; reg_val hlen
  obtain ⟨s2, hs2, step2⟩ := exec_post_harm_946 regs1 hlen1 hz2_1 hz3_1 hz5_1 hz6_1 hz7_1
  let regs2 := (regs1.set 12 ((regs1[9]! - regs1[10]! * regs1[1]!) ^ 2)).set 13 (regs1[10]! ^ 2)
  have hlen2 : regs2.length = 16 := by simp [regs2, regs1, hlen]
  have hz3_2 : regs2[3]! = 0 := by dsimp only [regs2, regs1]; reg_val hlen
  have hz5_2 : regs2[5]! = 0 := by dsimp only [regs2, regs1]; reg_val hlen
  have hz2_2 : regs2[2]! = 0 := by dsimp only [regs2, regs1]; reg_val hlen
  obtain ⟨s3, hs3, step3⟩ := exec_harm_1104 regs2 hlen2 hz3_2 hz5_2 hz2_2
  let regs3 := ((regs2.set 14 (harmNum regs2[1]!)).set 15 (regs2[1]!).factorial).set 11 (regs2[1]!
      + 1)
  have hlen3 : regs3.length = 16 := by simp [regs3, regs2, regs1, hlen]
  have hz2_3 : regs3[2]! = 0 := by dsimp only [regs3, regs2, regs1]; reg_val hlen
  have hz3_3 : regs3[3]! = 0 := by dsimp only [regs3, regs2, regs1]; reg_val hlen
  have hz5_3 : regs3[5]! = 0 := by dsimp only [regs3, regs2, regs1]; reg_val hlen
  have hz6_3 : regs3[6]! = 0 := by dsimp only [regs3, regs2, regs1]; reg_val hlen
  obtain ⟨s4, hs4, step4⟩ := exec_post_harm_1274 regs3 hlen3 hz2_3 hz3_3 hz5_3 hz6_3
  let regs4 := (regs3.set 14 (regs3[14]! ^ 4 * regs3[1]!)).set 15 (regs3[15]! ^ 4)
  refine ⟨s1 + s2 + s3 + s4, regs4, by omega,
    regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq step1 step2) step3) step4,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by simp [regs4, regs3, regs2, regs1, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [regs4, regs3, regs2, regs1]; reg_val hlen
    · dsimp only [regs4, regs3, regs2, regs1]; reg_val hlen
    · dsimp only [regs4, regs3, regs2, regs1]; reg_val hlen
    · dsimp only [regs4, regs3, regs2, regs1]; reg_val hlen
    · dsimp only [regs4, regs3, regs2, regs1]; reg_val hlen
    · dsimp only [regs4, regs3, regs2, regs1]; reg_val hlen
    · dsimp only [regs4, regs3, regs2, regs1]; reg_val hlen
    · dsimp only [regs4, regs3, regs2, regs1]; reg_val hlen
  · have h9_1 : regs1[9]! = harmNum (lcmUpTo x) := by rw [← h0]; dsimp only [regs1]; reg_val hlen
    have h10_1 : regs1[10]! = (lcmUpTo x).factorial := by
      rw [← h0]; dsimp only [regs1]; reg_val hlen
    have h1_1 : regs1[1]! = x := by rw [← h1]; dsimp only [regs1]; reg_val hlen
    have h12_4 : regs4[12]! = (regs1[9]! - regs1[10]! * regs1[1]!) ^ 2 := by
      dsimp only [regs4, regs3, regs2]; reg_val hlen1
    rw [h12_4, h9_1, h10_1, h1_1]
  · have h10_1 : regs1[10]! = (lcmUpTo x).factorial := by
      rw [← h0]; dsimp only [regs1]; reg_val hlen
    have h13_4 : regs4[13]! = regs1[10]! ^ 2 := by
      dsimp only [regs4, regs3, regs2]; reg_val hlen1
    rw [h13_4, h10_1]
  · have h1_2 : regs2[1]! = x := by rw [← h1]; dsimp only [regs2, regs1]; reg_val hlen
    have h14_3 : regs3[14]! = harmNum x := by rw [← h1_2]; dsimp only [regs3]; reg_val hlen2
    have h1_3 : regs3[1]! = x := by rw [← h1_2]; dsimp only [regs3]; reg_val hlen2
    have h14_4 : regs4[14]! = regs3[14]! ^ 4 * regs3[1]! := by
      dsimp only [regs4]; reg_val hlen3
    rw [h14_4, h14_3, h1_3]
  · have h1_2 : regs2[1]! = x := by rw [← h1]; dsimp only [regs2, regs1]; reg_val hlen
    have h15_3 : regs3[15]! = x.factorial := by rw [← h1_2]; dsimp only [regs3]; reg_val hlen2
    have h15_4 : regs4[15]! = regs3[15]! ^ 4 := by
      dsimp only [regs4]; reg_val hlen3
    rw [h15_4, h15_3]

theorem main_iter_halts (x : ℕ) (regs : List ℕ) (hcfg : ValidLoopCfg x regs)
    (hce : MatiyasevichRiemannCounterexample (x + 1)) :
    RegHaltsFrom ⟨21, regs⟩ := by
  rcases hcfg with ⟨hlen, h0, h1, hz2, hz3, hz5, hz6, hz7, hz8⟩
  have h0_pos : 0 < regs[0]! := by rw [h0]; exact lcmUpTo_pos x
  obtain ⟨s1, hs1, step1⟩ := exec_lcm_from_21 regs hlen h0_pos hz2 hz3 hz5 hz6 hz7 hz8
  let regs1 := ((regs.set 1 (regs[1]! + 1)).set 4 regs[0]!).set 0 (Nat.lcm regs[0]! (regs[1]! + 1))
  have hcfg1 : ValidLoopCfg (x + 1) regs1 := by
    refine ⟨by simp [regs1, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h0_1 : regs1[0]! = Nat.lcm regs[0]! (regs[1]! + 1) := by dsimp only [regs1]; reg_val hlen
      rw [h0_1, h0, h1, ← lcmUpTo_succ]
    · dsimp only [regs1]; reg_val hlen
    · dsimp only [regs1]; reg_val hlen
    · dsimp only [regs1]; reg_val hlen
    · dsimp only [regs1]; reg_val hlen
    · dsimp only [regs1]; reg_val hlen
    · dsimp only [regs1]; reg_val hlen
    · dsimp only [regs1]; reg_val hlen
  rcases hce with ⟨hgt, hlt⟩
  have hgt1 : 253 < regs1[1]! := by rw [hcfg1.2.2.1]; exact hgt
  obtain ⟨s2, hs2, step2⟩ := exec_x_test_gt regs1 hcfg1.1 hcfg1.2.2.2.1 hcfg1.2.2.2.2.1 hgt1
  obtain ⟨s3, regs2, hs3, step3, hcfg2, h12, h13, h14, h15⟩ :=
      exec_full_calc_from_780 (x + 1) regs1 hcfg1
  have hlt2 : regs2[13]! * regs2[14]! < regs2[12]! * regs2[15]! := by
    rw [h12, h13, h14, h15]
    exact hlt
  obtain ⟨s4, step4⟩ := exec_final_1456_halt regs2 hcfg2.1
    hcfg2.2.2.2.1 hcfg2.2.2.2.2.1 hcfg2.2.2.2.2.2.1 hcfg2.2.2.2.2.2.2.1 hlt2
  exact ⟨s1 + s2 + s3 + s4,
    regNSteps_bind_none (regNSteps_bind_eq (regNSteps_bind_eq step1 step2) step3) step4⟩

theorem main_iter_continue (x : ℕ) (regs : List ℕ) (hcfg : ValidLoopCfg x regs)
    (hnot : ¬ MatiyasevichRiemannCounterexample (x + 1)) :
    ∃ s regs', 1 ≤ s ∧ regNSteps s ⟨21, regs⟩ = some ⟨21, regs'⟩ ∧ ValidLoopCfg (x + 1) regs' := by
  rcases hcfg with ⟨hlen, h0, h1, hz2, hz3, hz5, hz6, hz7, hz8⟩
  have h0_pos : 0 < regs[0]! := by rw [h0]; exact lcmUpTo_pos x
  obtain ⟨s1, hs1, step1⟩ := exec_lcm_from_21 regs hlen h0_pos hz2 hz3 hz5 hz6 hz7 hz8
  let regs1 := ((regs.set 1 (regs[1]! + 1)).set 4 regs[0]!).set 0 (Nat.lcm regs[0]! (regs[1]! + 1))
  have hcfg1 : ValidLoopCfg (x + 1) regs1 := by
    refine ⟨by simp [regs1, hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h0_1 : regs1[0]! = Nat.lcm regs[0]! (regs[1]! + 1) := by dsimp only [regs1]; reg_val hlen
      rw [h0_1, h0, h1, ← lcmUpTo_succ]
    · dsimp only [regs1]; reg_val hlen
    · dsimp only [regs1]; reg_val hlen
    · dsimp only [regs1]; reg_val hlen
    · dsimp only [regs1]; reg_val hlen
    · dsimp only [regs1]; reg_val hlen
    · dsimp only [regs1]; reg_val hlen
    · dsimp only [regs1]; reg_val hlen
  by_cases hle : x + 1 ≤ 253
  · have hle1 : regs1[1]! ≤ 253 := by rw [hcfg1.2.2.1]; exact hle
    obtain ⟨s2, hs2, step2⟩ := exec_x_test_le regs1 hcfg1.1 hcfg1.2.2.2.1 hcfg1.2.2.2.2.1 hle1
    exact ⟨s1 + s2, regs1, by omega, regNSteps_bind_eq step1 step2, hcfg1⟩
  · have hgt : 253 < x + 1 := by omega
    have hgt1 : 253 < regs1[1]! := by rw [hcfg1.2.2.1]; exact hgt
    obtain ⟨s2, hs2, step2⟩ := exec_x_test_gt regs1 hcfg1.1 hcfg1.2.2.2.1 hcfg1.2.2.2.2.1 hgt1
    obtain ⟨s3, regs2, hs3, step3, hcfg2, h12, h13, h14, h15⟩ :=
        exec_full_calc_from_780 (x + 1) regs1 hcfg1
    have hge2 : ¬ (regs2[13]! * regs2[14]! < regs2[12]! * regs2[15]!) := by
      rw [h12, h13, h14, h15]
      intro hlt
      exact hnot ⟨hgt, hlt⟩
    obtain ⟨s4, hs4, step4⟩ := exec_final_1456_continue regs2 hcfg2.1
      hcfg2.2.2.2.1 hcfg2.2.2.2.2.1 hcfg2.2.2.2.2.2.1 hcfg2.2.2.2.2.2.2.1 hge2
    exact ⟨s1 + s2 + s3 + s4, regs2, by omega,
      regNSteps_bind_eq (regNSteps_bind_eq (regNSteps_bind_eq step1 step2) step3) step4, hcfg2⟩

theorem reach_stage_of_no_counterexample :
    ∀ (x : ℕ), (∀ y, 1 ≤ y → y ≤ x → ¬ MatiyasevichRiemannCounterexample y) →
      ∃ s regs, x ≤ s ∧ regNSteps (20 + s) regInit = some ⟨21, regs⟩ ∧ ValidLoopCfg x regs
  | 0, _ =>
    ⟨0, [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], Nat.le_refl 0, exec_init,
      validLoopCfg_init⟩
  | x + 1, hno => by
    obtain ⟨s1, regs1, hs1, step1, hcfg1⟩ :=
      reach_stage_of_no_counterexample x (fun y hy1 hyx => hno y hy1 (by omega))
    have hnot : ¬ MatiyasevichRiemannCounterexample (x + 1) := hno (x + 1) (by omega) (by omega)
    obtain ⟨s2, regs2, hs2, step2, hcfg2⟩ := main_iter_continue x regs1 hcfg1 hnot
    refine ⟨s1 + s2, regs2, by omega, ?_, hcfg2⟩
    have hadd : 20 + (s1 + s2) = (20 + s1) + s2 := by omega
    rw [hadd]
    exact regNSteps_bind_eq step1 step2

/-- Main Layer 3 halting equivalence theorem:
The register machine starting from `regInit` halts if and only if there exists a positive integer
`x` satisfying `MatiyasevichRiemannCounterexample x`. -/
theorem regHalts_iff_exists_counterexample :
    RegHalts ↔ ∃ x : ℕ, MatiyasevichRiemannCounterexample x := by
  rw [regHalts_iff_regHaltsFrom]
  constructor
  · intro hhalts
    by_contra hno
    apply not_regHaltsFrom_of_unbounded _ hhalts
    intro n
    obtain ⟨s, regs, hs, step, _⟩ :=
      reach_stage_of_no_counterexample n (fun y _ _ hy => hno ⟨y, hy⟩)
    exact ⟨20 + s, ⟨21, regs⟩, by omega, step⟩
  · intro hex
    classical
    let x := Nat.find hex
    have hx : MatiyasevichRiemannCounterexample x := Nat.find_spec hex
    have hx_gt : 253 < x := hx.1
    have hx_eq : (x - 1) + 1 = x := by omega
    obtain ⟨s, regs, _, step, hcfg⟩ :=
      reach_stage_of_no_counterexample (x - 1) (fun y _ hy => Nat.find_min hex (by omega))
    rw [← hx_eq] at hx
    have hhalts21 : RegHaltsFrom ⟨21, regs⟩ := main_iter_halts (x - 1) regs hcfg hx
    exact (regHaltsFrom_of_regNSteps step).mpr hhalts21

end ConjectureMachines.Semantics.Riemann
