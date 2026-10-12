/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Zf.Dispatcher
public import Cryptids.Semantics.Zf.RegisterMachine

/-!
# Call-Stack Subroutine Verification for `zf_432_wade.tm`

This module bridges the abstract call-stack + register machine (`Layer2.ZfRegHalts` in
`Cryptids.Semantics.Zf.Dispatcher`) and the functional main-loop model (`MainLoopHalts` in
`Cryptids.Semantics.Zf.RegisterMachine`).
-/

@[expose] public section

namespace ConjectureMachines.Semantics.Zf

open Turing StateTransition ConjectureMachines.Semantics.Zf ConjectureMachines.Semantics.Zf.Layer2

/-! ## Section 1: Fixed-Width 11-Register Machine (`zfReg11Step`) -/

/-- Fixed-width 11-register step: identical to `zfRegStep` except that `decnz` success does not
append a trailing `0` register, keeping `regs.length = 11` invariant. -/
def zfReg11Step (c : ZfRegCfg) : Option ZfRegCfg :=
  match evalStack c.stack with
  | .halt => none
  | .jump stack' => some ⟨stack', c.regs⟩
  | .inc r stack_succ =>
    some ⟨stack_succ, c.regs.set r (c.regs.getD r 0 + 1)⟩
  | .decnz r stack_succ stack_fail =>
    if c.regs.getD r 0 == 0 then
      some ⟨stack_fail, c.regs⟩
    else
      some ⟨stack_succ, c.regs.set r (c.regs.getD r 0 - 1)⟩

/-- `n`-step execution of `zfReg11Step`. -/
def zfReg11NSteps : ℕ → ZfRegCfg → Option ZfRegCfg
  | 0, c => some c
  | n + 1, c => (zfReg11Step c).bind (zfReg11NSteps n)

@[simp]
theorem zfReg11NSteps_zero (c : ZfRegCfg) : zfReg11NSteps 0 c = some c := rfl

@[simp]
theorem zfReg11NSteps_succ (n : ℕ) (c : ZfRegCfg) :
    zfReg11NSteps (n + 1) c = (zfReg11Step c).bind (zfReg11NSteps n) := rfl

theorem zfReg11Step_one {c c' : ZfRegCfg} (h : zfReg11Step c = some c') :
    zfReg11NSteps 1 c = some c' := by
  simp [zfReg11NSteps, h]

theorem step_zfReg11NSteps {n : ℕ} {c₁ c₂ c₃ : ZfRegCfg}
    (h1 : zfReg11Step c₁ = some c₂) (h2 : zfReg11NSteps n c₂ = some c₃) :
    zfReg11NSteps (n + 1) c₁ = some c₃ := by
  simp [zfReg11NSteps, h1, h2]

theorem zfReg11NSteps_add (m n : ℕ) (c : ZfRegCfg) :
    zfReg11NSteps (m + n) c = (zfReg11NSteps m c).bind (zfReg11NSteps n) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    simp only [Nat.succ_add, zfReg11NSteps_succ]
    cases zfReg11Step c <;> simp [ih]

theorem zfReg11NSteps_bind_eq {m n : ℕ} {c₁ c₂ c₃ : ZfRegCfg}
    (h1 : zfReg11NSteps m c₁ = some c₂) (h2 : zfReg11NSteps n c₂ = some c₃) :
    zfReg11NSteps (m + n) c₁ = some c₃ := by
  rw [zfReg11NSteps_add, h1, Option.bind_some, h2]

theorem zfReg11Step_sim {c₁ c₂ : ZfRegCfg} (hsim : ZfRegSim c₁ c₂) :
    match zfRegStep c₁, zfReg11Step c₂ with
    | none, none => True
    | some c₁', some c₂' => ZfRegSim c₁' c₂'
    | _, _ => False := by
  rcases hsim with ⟨hstack, hlen₁, hlen₂, htake⟩
  have hr_lt := evalStack_reg_lt_11 c₁.stack
  unfold zfRegStep zfReg11Step
  rw [← hstack]
  rcases hev : evalStack c₁.stack with _ | stack' | ⟨r, stack_succ⟩ | ⟨r, stack_succ, stack_fail⟩
  · trivial
  · exact ⟨rfl, hlen₁, hlen₂, htake⟩
  · rw [hev] at hr_lt
    have hget := getD_eq_of_take_11 hr_lt htake
    refine ⟨rfl, by simp [hlen₁], by simp [hlen₂], ?_⟩
    rw [List.take_set, List.take_set, hget, htake]
  · rw [hev] at hr_lt
    have hget := getD_eq_of_take_11 hr_lt htake
    dsimp only
    rw [hget]
    by_cases hz : (c₂.regs.getD r 0 == 0) = true
    · simp only [hz, ↓reduceIte]
      exact ⟨rfl, hlen₁, hlen₂, htake⟩
    · simp only [hz, Bool.false_eq_true, ↓reduceIte]
      refine ⟨rfl, by simp; omega, by simp [hlen₂], ?_⟩
      dsimp only
      have hle₁ : 11 ≤ (c₁.regs.set r (c₂.regs.getD r 0 - 1)).length := by simp [hlen₁]
      rw [List.take_append_of_le_length hle₁, List.take_set, List.take_set, htake]

theorem zfRegHalts_iff_exists_zfReg11NSteps :
    ZfRegHalts ↔ ∃ n c, zfReg11NSteps n zfRegInit = some c ∧ zfReg11Step c = none := by
  rw [zfRegHalts_iff_exists_zfRegNSteps]
  have hsim₀ : ZfRegSim zfRegInit zfRegInit := ⟨rfl, by decide, by decide, rfl⟩
  constructor
  · rintro ⟨n, ch₁, hn, hnone⟩
    have hstep_n : ∀ m {a₁ a₂ : ZfRegCfg}, ZfRegSim a₁ a₂ →
        zfRegNSteps m a₁ = some ch₁ →
        ∃ ch₂, zfReg11NSteps m a₂ = some ch₂ ∧ ZfRegSim ch₁ ch₂ := by
      intro m
      induction m with
      | zero =>
        intro a₁ a₂ hsim_a hm
        injection hm with hm'; subst hm'
        exact ⟨a₂, rfl, hsim_a⟩
      | succ m ih =>
        intro a₁ a₂ hsim_a hm
        unfold zfRegNSteps at hm
        unfold zfReg11NSteps
        have hstep := zfReg11Step_sim hsim_a
        rcases hs₁ : zfRegStep a₁ with _ | a₁' <;> rcases hs₂ : zfReg11Step a₂ with _ | a₂'
        · rw [hs₁] at hm; cases hm
        · rw [hs₁, hs₂] at hstep; cases hstep
        · rw [hs₁, hs₂] at hstep; cases hstep
        · rw [hs₁, hs₂] at hstep
          rw [hs₁, Option.bind_some] at hm
          exact ih hstep hm
    obtain ⟨ch₂, hn₂, hsim_ch⟩ := hstep_n n hsim₀ hn
    have hstep_ch := zfReg11Step_sim hsim_ch
    rw [hnone] at hstep_ch
    rcases hs₂ : zfReg11Step ch₂ with _ | ch₂'
    · exact ⟨n, ch₂, hn₂, hs₂⟩
    · rw [hs₂] at hstep_ch; cases hstep_ch
  · rintro ⟨n, ch₂, hn, hnone⟩
    have hstep_n : ∀ m {a₁ a₂ : ZfRegCfg}, ZfRegSim a₁ a₂ →
        zfReg11NSteps m a₂ = some ch₂ →
        ∃ ch₁, zfRegNSteps m a₁ = some ch₁ ∧ ZfRegSim ch₁ ch₂ := by
      intro m
      induction m with
      | zero =>
        intro a₁ a₂ hsim_a hm
        injection hm with hm'; subst hm'
        exact ⟨a₁, rfl, hsim_a⟩
      | succ m ih =>
        intro a₁ a₂ hsim_a hm
        unfold zfReg11NSteps at hm
        unfold zfRegNSteps
        have hstep := zfReg11Step_sim hsim_a
        rcases hs₁ : zfRegStep a₁ with _ | a₁' <;> rcases hs₂ : zfReg11Step a₂ with _ | a₂'
        · rw [hs₂] at hm; cases hm
        · rw [hs₁, hs₂] at hstep; cases hstep
        · rw [hs₁, hs₂] at hstep; cases hstep
        · rw [hs₁, hs₂] at hstep
          rw [hs₂, Option.bind_some] at hm
          exact ih hstep hm
    obtain ⟨ch₁, hn₁, hsim_ch⟩ := hstep_n n hsim₀ hn
    have hstep_ch := zfReg11Step_sim hsim_ch
    rw [hnone] at hstep_ch
    rcases hs₁ : zfRegStep ch₁ with _ | ch₁'
    · exact ⟨n, ch₁, hn₁, hs₁⟩
    · rw [hs₁] at hstep_ch; cases hstep_ch

/-! ## Section 2: Return-Stack & Prefix-Invariance Lemmas -/

/-- Return stack when breaking out of a subroutine at call-stack prefix `P`. -/
def retStack (P : List (Fin 2)) : List (Fin 2) :=
  (popBreakRev 0 P.reverse).reverse

@[simp]
theorem retStack_append_zero (P : List (Fin 2)) :
    retStack (P ++ [0]) = P ++ [1] := by
  simp [retStack]

@[simp]
theorem retStack_append_one (P : List (Fin 2)) :
    retStack (P ++ [1]) = retStack P := by
  simp [retStack]

@[simp]
theorem retStack_replicate_one (k : ℕ) :
    retStack (List.replicate k 1) = [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', retStack_append_one, ih]

@[simp]
theorem trimZeros_append_zero (P : List (Fin 2)) :
    trimZeros (P ++ [0]) = trimZeros P := by
  simp [trimZeros]

@[simp]
theorem trimZeros_append_one (P : List (Fin 2)) :
    trimZeros (P ++ [1]) = P ++ [1] := by
  simp [trimZeros]

@[simp]
theorem trimZeros_replicate_zero (k : ℕ) :
    trimZeros (List.replicate k 0) = [] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ', trimZeros_append_zero, ih]

@[simp]
theorem trimZeros_replicate_one (k : ℕ) :
    trimZeros (List.replicate k 1) = List.replicate k 1 := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [List.replicate_succ', trimZeros_append_one]

theorem popContinueRev_zero_eq_dropLeadingZeros (rev : List (Fin 2)) :
    popContinueRev 0 rev = dropLeadingZeros rev := by
  induction rev with
  | nil => rfl
  | cons b rest ih =>
    rcases b with ⟨_ | _ | n, hn⟩
    · simp [ih]
    · rfl
    · omega

theorem applyContinue_zero_eq_trimZeros (bits : List (Fin 2)) (pos : ℕ) :
    applyContinue bits pos 0 = trimZeros (padTo bits pos) := by
  simp [applyContinue, trimZeros, popContinueRev_zero_eq_dropLeadingZeros]

theorem walkInternal_snoc {q q_mid q_end : Fin 432} {P : List (Fin 2)} {b : Fin 2}
    (hP : walkInternal q P = some q_mid)
    (htr : refTrans q_mid b = some (b, .right, q_end))
    (hq_end : 96 ≤ q_end.val) :
    walkInternal q (P ++ [b]) = some q_end := by
  have hge := (walkInternal_ge_96 hP).2
  rw [walkInternal_append, hP, Option.bind_some]
  simp [walkInternal, hge, htr, hq_end]

theorem count_zero_replicate_zero (m : ℕ) :
    (List.replicate m (0 : Fin 2)).count 0 = m := by
  simp

/-- Key prefix-invariance theorem: for any `P` that walks in `96..431` from `126` to `q`,
`evalStack (trimZeros P)` and `evalStack P` produce the exact same instruction, and it is
the leaf instruction at `zeroLeaf q` after `zeroDepth q` zero-steps from `P`. -/
theorem evalStack_of_walkInternal {P : List (Fin 2)} {q : Fin 432}
    (h : walkInternal 126 P = some q) :
    evalStack (trimZeros P) = evalStack P ∧
    evalStack P =
      if isLeafInc (zeroLeaf q) then
        .inc (leafReg (zeroLeaf q)) (applyBreak P (P.length + zeroDepth q) 0)
      else
        .decnz (leafReg (zeroLeaf q)) (applyBreak P (P.length + zeroDepth q) 0)
          (applyBreak P (P.length + zeroDepth q) 1) := by
  have hq : 96 ≤ q.val := (walkInternal_ge_96 h).2
  have hz := zeroStepBool_all q
  simp only [zeroStepBool, hq, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
    Bool.and_assoc] at hz
  rcases hz with ⟨hd1, _, hd_max0, _, _, _⟩
  have hb := walkInternal_root_bounds h
  have hd_eq : zeroDepth q = (zeroDepth q - 1) + 1 := by omega
  have hrep := walkTape_replicate_zero (zeroDepth q - 1) hq hd_eq P (pad := 12) (by omega)
  rcases hrep with ⟨hw_pad, _, _⟩
  rw [← hd_eq] at hw_pad
  have hwalk_P : walkTape 126 [] (P ++ List.replicate 12 0) =
      .regLeaf (zeroLeaf q) (P ++ List.replicate (zeroDepth q) 0)
        (List.replicate (12 - zeroDepth q) 0) := by
    rw [walkTape_of_walkInternal h [] (List.replicate 12 0), List.nil_append, hw_pad]
  have hev_P : evalStack P =
      if isLeafInc (zeroLeaf q) then
        .inc (leafReg (zeroLeaf q)) (applyBreak P (P.length + zeroDepth q) 0)
      else
        .decnz (leafReg (zeroLeaf q)) (applyBreak P (P.length + zeroDepth q) 0)
          (applyBreak P (P.length + zeroDepth q) 1) :=
    evalStack_of_regLeaf hwalk_P
  let m := P.length - (trimZeros P).length
  have hm_def : m = P.length - (trimZeros P).length := rfl
  have hP_split : P = trimZeros P ++ List.replicate m 0 := eq_trimZeros_append_replicate P
  have hm_cnt : m ≤ P.count 0 := by
    have hcnt := congrArg (List.count 0) hP_split
    rw [List.count_append, count_zero_replicate_zero] at hcnt
    omega
  have hm_12 : m + zeroDepth q ≤ 12 := by omega
  have h12_split : List.replicate 12 (0 : Fin 2) =
      List.replicate m 0 ++ List.replicate (12 - m) 0 := by
    rw [← List.replicate_add, Nat.add_sub_of_le (by omega)]
  have hrep_trim :=
    walkTape_replicate_zero (zeroDepth q - 1) hq hd_eq P (pad := 12 - m) (by omega)
  rcases hrep_trim with ⟨hw_pad_trim, _, _⟩
  rw [← hd_eq] at hw_pad_trim
  have hwalk_trim : walkTape 126 [] (trimZeros P ++ List.replicate 12 0) =
      .regLeaf (zeroLeaf q) (P ++ List.replicate (zeroDepth q) 0)
        (List.replicate (12 - m - zeroDepth q) 0) := by
    rw [h12_split, ← List.append_assoc, ← hP_split,
      walkTape_of_walkInternal h [] (List.replicate (12 - m) 0), List.nil_append, hw_pad_trim]
  have hpad_eq : padTo (trimZeros P) (P.length + zeroDepth q) =
      padTo P (P.length + zeroDepth q) := by
    have hle1 : (trimZeros P).length ≤ P.length := trimZeros_length_le P
    rw [padTo_of_le (by omega), padTo_of_le (by omega)]
    have hsub : P.length + zeroDepth q - (trimZeros P).length = m + zeroDepth q := by omega
    rw [hsub, List.replicate_add, ← List.append_assoc, ← hP_split, Nat.add_sub_cancel_left]
  have hbrk_eq : ∀ k, applyBreak (trimZeros P) (P.length + zeroDepth q) k =
      applyBreak P (P.length + zeroDepth q) k := by
    intro k
    simp [applyBreak, hpad_eq]
  have hev_trim : evalStack (trimZeros P) = evalStack P := by
    unfold evalStack
    rw [hwalk_trim, hwalk_P]
    unfold outcomeToInstr
    simp [hbrk_eq]
  exact ⟨hev_trim, hev_P⟩

theorem evalStack_trimZeros_of_walkInternal {P : List (Fin 2)} {q : Fin 432}
    (h : walkInternal 126 P = some q) :
    evalStack (trimZeros P) = evalStack P :=
  (evalStack_of_walkInternal h).1

/-- When `q` has a direct `0`-transition to a leaf `q' ∈ {49..70}`, `evalStack P` (and hence
`evalStack (trimZeros P)`) executes `q'` with success stack `P ++ [1]` and fail stack
`retStack P`. -/
theorem evalStack_leaf0_of_walkInternal {P : List (Fin 2)} {q q' : Fin 432}
    (h : walkInternal 126 P = some q)
    (htr : refTrans q 0 = some (0, .right, q'))
    (h49 : 49 ≤ q'.val) (h70 : q'.val ≤ 70) :
    evalStack P =
      if isLeafInc q' then
        .inc (leafReg q') (P ++ [1])
      else
        .decnz (leafReg q') (P ++ [1]) (retStack P) := by
  have hleaf : (49 ≤ q'.val && q'.val ≤ 70) = true := by
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]; exact ⟨h49, h70⟩
  have hwalk : walkTape 126 [] (P ++ List.replicate 12 0) =
      .regLeaf q' (P ++ [0]) (List.replicate 11 0) := by
    rw [walkTape_of_walkInternal h [] (List.replicate 12 0), List.nil_append]
    change walkTape q P (0 :: List.replicate 11 0) = _
    simp [walkTape, htr, hleaf]
  have hev := evalStack_of_regLeaf (m := 1) hwalk
  have hpad : padTo P (P.length + 1) = P ++ [0] := by
    rw [padTo_of_le (by omega)]
    simp
  have hbrk0 : applyBreak P (P.length + 1) 0 = P ++ [1] := by
    simp [applyBreak, hpad]
  have hbrk1 : applyBreak P (P.length + 1) 1 = retStack P := by
    simp [applyBreak, hpad, retStack]
  rw [hev, hbrk0, hbrk1]

/-- When `q` has a direct `1`-transition to an increment leaf `q' ∈ {49..70}`,
`evalStack (P ++ [1])` increments `leafReg q'` and transitions to `retStack P`. -/
theorem evalStack_leaf1_inc_of_walkInternal {P : List (Fin 2)} {q q' : Fin 432}
    (h : walkInternal 126 P = some q)
    (htr : refTrans q 1 = some (1, .right, q'))
    (h49 : 49 ≤ q'.val) (h70 : q'.val ≤ 70) (hinc : isLeafInc q' = true) :
    evalStack (P ++ [1]) = .inc (leafReg q') (retStack P) := by
  have hleaf : (49 ≤ q'.val && q'.val ≤ 70) = true := by
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]; exact ⟨h49, h70⟩
  have hwalk : walkTape 126 [] ((P ++ [1]) ++ List.replicate 12 0) =
      .regLeaf q' (P ++ [1]) (List.replicate 12 0) := by
    rw [List.append_assoc, walkTape_of_walkInternal h [] ([1] ++ List.replicate 12 0),
      List.nil_append]
    change walkTape q P (1 :: List.replicate 12 0) = _
    simp [walkTape, htr, hleaf]
  have hev := evalStack_of_regLeaf (bits := P ++ [1]) (m := 0) (by simpa using hwalk)
  have hpad : padTo (P ++ [1]) (P.length + 1) = P ++ [1] := by
    rw [padTo_of_le (by simp)]
    simp
  have hbrk0 : applyBreak (P ++ [1]) ((P ++ [1]).length + 0) 0 = retStack P := by
    simp [applyBreak, hpad, retStack]
  rw [hev, hbrk0]
  simp [hinc]

/-- When `q` has a `1`-transition `(0, .left, 89 + k)` (`6.break.k`, `k ≤ 2`),
`evalStack (P ++ [1])` jumps to `(popBreakRev k P.reverse).reverse`. -/
theorem evalStack_break1_of_walkInternal {P : List (Fin 2)} {q : Fin 432} {k : ℕ}
    (hk2 : k ≤ 2) (h : walkInternal 126 P = some q)
    (htr : refTrans q 1 = some (0, .left, ⟨89 + k, by omega⟩)) :
    evalStack (P ++ [1]) = .jump (popBreakRev k P.reverse).reverse := by
  have hwalk : walkTape 126 [] ((P ++ [1]) ++ List.replicate 12 0) =
      .jumpLeft ⟨89 + k, by omega⟩ P (List.replicate 12 0) := by
    rw [List.append_assoc, walkTape_of_walkInternal h [] ([1] ++ List.replicate 12 0),
      List.nil_append]
    change walkTape q P (1 :: List.replicate 12 0) = _
    simp [walkTape, htr]
  rw [evalStack_of_jumpBreak hk2 hwalk]
  have hpad : padTo (P ++ [1]) P.length = P := by
    rw [padTo_of_ge (by simp)]
    simp
  simp [applyBreak, hpad]

/-- When `q` has a `1`-transition `(0, .left, 92 + k)` (`6.continue.k`, `k ≤ 3`),
`evalStack (P ++ [1])` jumps to `(popContinueRev k P.reverse).reverse`. -/
theorem evalStack_continue1_of_walkInternal {P : List (Fin 2)} {q : Fin 432} {k : ℕ}
    (hk3 : k ≤ 3) (h : walkInternal 126 P = some q)
    (htr : refTrans q 1 = some (0, .left, ⟨92 + k, by omega⟩)) :
    evalStack (P ++ [1]) = .jump (popContinueRev k P.reverse).reverse := by
  have hwalk : walkTape 126 [] ((P ++ [1]) ++ List.replicate 12 0) =
      .jumpLeft ⟨92 + k, by omega⟩ P (List.replicate 12 0) := by
    rw [List.append_assoc, walkTape_of_walkInternal h [] ([1] ++ List.replicate 12 0),
      List.nil_append]
    change walkTape q P (1 :: List.replicate 12 0) = _
    simp [walkTape, htr]
  rw [evalStack_of_jumpContinue hk3 hwalk]
  have hpad : padTo (P ++ [1]) P.length = P := by
    rw [padTo_of_ge (by simp)]
    simp
  simp [applyContinue, hpad]

/-! ## Section 3: Universal Subroutine Specification (`SubEval`) & Combinators -/

/-- Universal specification of a decision-tree subroutine node `q ∈ {96..431}`:
for any call-stack prefix `P` reaching `q` from `126` (`walkInternal 126 P = some q`) and any
11-register bank `regs`, starting from `⟨trimZeros P, regs⟩` reaches `⟨retStack P, f regs⟩`
in `s ≥ 1` steps of `zfReg11Step`. -/
def SubEval (q : Fin 432) (f : List ℕ → List ℕ) : Prop :=
  ∀ (P : List (Fin 2)),
    walkInternal 126 P = some q →
    ∀ (regs : List ℕ), regs.length = 11 →
      ∃ s ≥ 1, zfReg11NSteps s ⟨trimZeros P, regs⟩ = some ⟨retStack P, f regs⟩ ∧
        (f regs).length = 11

theorem SubEval.congr {q : Fin 432} {f g : List ℕ → List ℕ}
    (h : SubEval q f) (heq : ∀ regs, regs.length = 11 → f regs = g regs) :
    SubEval q g := by
  intro P hP regs hlen
  obtain ⟨s, hs, hsteps, hflen⟩ := h P hP regs hlen
  rw [heq regs hlen] at hsteps hflen
  exact ⟨s, hs, hsteps, hflen⟩

/-- Sequential composition combinator: if `q` transitions on `0` to `q₀` (`96 ≤ q₀.val`) and on
`1` to `q₁` (`96 ≤ q₁.val`), then `SubEval q₀ f₀` and `SubEval q₁ f₁` compose to
`SubEval q (fun regs => f₁ (f₀ regs))`. -/
theorem subEval_seq {q q₀ q₁ : Fin 432} {f₀ f₁ : List ℕ → List ℕ}
    (htr0 : refTrans q 0 = some (0, .right, q₀)) (hq₀ : 96 ≤ q₀.val)
    (htr1 : refTrans q 1 = some (1, .right, q₁)) (hq₁ : 96 ≤ q₁.val)
    (h0 : SubEval q₀ f₀) (h1 : SubEval q₁ f₁) :
    SubEval q (fun regs => f₁ (f₀ regs)) := by
  intro P hP regs hlen
  have hP0 : walkInternal 126 (P ++ [0]) = some q₀ := walkInternal_snoc hP htr0 hq₀
  have hP1 : walkInternal 126 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  obtain ⟨s₀, hs₀, hsteps₀, hlen₀⟩ := h0 (P ++ [0]) hP0 regs hlen
  rw [trimZeros_append_zero, retStack_append_zero] at hsteps₀
  obtain ⟨s₁, hs₁, hsteps₁, hlen₁⟩ := h1 (P ++ [1]) hP1 (f₀ regs) hlen₀
  rw [trimZeros_append_one, retStack_append_one] at hsteps₁
  exact ⟨s₀ + s₁, by omega, zfReg11NSteps_bind_eq hsteps₀ hsteps₁, hlen₁⟩

theorem zfReg11Step_of_jump {s s' : List (Fin 2)} {regs : List ℕ}
    (h : evalStack s = .jump s') :
    zfReg11Step ⟨s, regs⟩ = some ⟨s', regs⟩ := by
  unfold zfReg11Step; dsimp only; rw [h]

theorem zfReg11Step_of_inc {s s' : List (Fin 2)} {r : ℕ} {regs : List ℕ}
    (h : evalStack s = .inc r s') :
    zfReg11Step ⟨s, regs⟩ = some ⟨s', regs.set r (regs.getD r 0 + 1)⟩ := by
  unfold zfReg11Step; dsimp only; rw [h]

theorem zfReg11Step_of_decnz_zero {s s_succ s_fail : List (Fin 2)} {r : ℕ} {regs : List ℕ}
    (h : evalStack s = .decnz r s_succ s_fail) (hz : regs.getD r 0 = 0) :
    zfReg11Step ⟨s, regs⟩ = some ⟨s_fail, regs⟩ := by
  unfold zfReg11Step; dsimp only; rw [h]; dsimp only; rw [hz]; rfl

theorem zfReg11Step_of_decnz_succ {s s_succ s_fail : List (Fin 2)} {r v : ℕ} {regs : List ℕ}
    (h : evalStack s = .decnz r s_succ s_fail) (hv : regs.getD r 0 = v + 1) :
    zfReg11Step ⟨s, regs⟩ = some ⟨s_succ, regs.set r v⟩ := by
  unfold zfReg11Step; dsimp only; rw [h]; dsimp only; rw [hv]; rfl

/-- Sequential + increment leaf combinator: if `q` transitions on `0` to `q₀` (`96 ≤ q₀.val`) and
on `1` to an increment leaf `q₁ ∈ {49..70}`, then `SubEval q₀ f₀` composes with the increment of
`leafReg q₁`. -/
theorem subEval_seq_inc {q q₀ q₁ : Fin 432} {f₀ : List ℕ → List ℕ}
    (htr0 : refTrans q 0 = some (0, .right, q₀)) (hq₀ : 96 ≤ q₀.val)
    (htr1 : refTrans q 1 = some (1, .right, q₁))
    (h49 : 49 ≤ q₁.val) (h70 : q₁.val ≤ 70) (hinc : isLeafInc q₁ = true)
    (h0 : SubEval q₀ f₀) :
    SubEval q (fun regs =>
      let r := f₀ regs
      r.set (leafReg q₁) (r.getD (leafReg q₁) 0 + 1)) := by
  intro P hP regs hlen
  have hP0 : walkInternal 126 (P ++ [0]) = some q₀ := walkInternal_snoc hP htr0 hq₀
  obtain ⟨s₀, hs₀, hsteps₀, hlen₀⟩ := h0 (P ++ [0]) hP0 regs hlen
  rw [trimZeros_append_zero, retStack_append_zero] at hsteps₀
  have hev1 := evalStack_leaf1_inc_of_walkInternal hP htr1 h49 h70 hinc
  have hstep1 := zfReg11Step_of_inc (regs := f₀ regs) hev1
  refine ⟨s₀ + 1, by omega, zfReg11NSteps_bind_eq hsteps₀ (zfReg11Step_one hstep1), ?_⟩
  simp [hlen₀]

/-- Two-increment leaf node combinator: if `q` transitions on `0` to increment leaf `q₀` and on
`1` to increment leaf `q₁`, then `q` increments `leafReg q₀` followed by `leafReg q₁`. -/
theorem subEval_inc_inc {q q₀ q₁ : Fin 432}
    (htr0 : refTrans q 0 = some (0, .right, q₀))
    (h0_49 : 49 ≤ q₀.val) (h0_70 : q₀.val ≤ 70) (hinc0 : isLeafInc q₀ = true)
    (htr1 : refTrans q 1 = some (1, .right, q₁))
    (h1_49 : 49 ≤ q₁.val) (h1_70 : q₁.val ≤ 70) (hinc1 : isLeafInc q₁ = true) :
    SubEval q (fun regs =>
      let r₁ := regs.set (leafReg q₀) (regs.getD (leafReg q₀) 0 + 1)
      r₁.set (leafReg q₁) (r₁.getD (leafReg q₁) 0 + 1)) := by
  intro P hP regs hlen
  have hev0 : evalStack (trimZeros P) = .inc (leafReg q₀) (P ++ [1]) := by
    rw [evalStack_trimZeros_of_walkInternal hP, evalStack_leaf0_of_walkInternal hP htr0 h0_49 h0_70]
    simp [hinc0]
  have hstep0 := zfReg11Step_of_inc (regs := regs) hev0
  have hev1 := evalStack_leaf1_inc_of_walkInternal hP htr1 h1_49 h1_70 hinc1
  let r₁ := regs.set (leafReg q₀) (regs.getD (leafReg q₀) 0 + 1)
  have hstep1 := zfReg11Step_of_inc (regs := r₁) hev1
  refine ⟨2, by omega, step_zfReg11NSteps hstep0 (zfReg11Step_one hstep1), ?_⟩
  simp [hlen]

/-- Increment leaf + sequential combinator: if `q` transitions on `0` to an increment leaf
`q₀ ∈ {49..70}` and on `1` to `q₁` (`96 ≤ q₁.val`), then `q` increments `leafReg q₀` followed by
`f₁`. -/
theorem subEval_inc_seq {q q₀ q₁ : Fin 432} {f₁ : List ℕ → List ℕ}
    (htr0 : refTrans q 0 = some (0, .right, q₀))
    (h49 : 49 ≤ q₀.val) (h70 : q₀.val ≤ 70) (hinc : isLeafInc q₀ = true)
    (htr1 : refTrans q 1 = some (1, .right, q₁)) (hq₁ : 96 ≤ q₁.val)
    (h1 : SubEval q₁ f₁) :
    SubEval q (fun regs =>
      f₁ (regs.set (leafReg q₀) (regs.getD (leafReg q₀) 0 + 1))) := by
  intro P hP regs hlen
  have hev0 : evalStack (trimZeros P) = .inc (leafReg q₀) (P ++ [1]) := by
    rw [evalStack_trimZeros_of_walkInternal hP, evalStack_leaf0_of_walkInternal hP htr0 h49 h70]
    simp [hinc]
  let r₀ := regs.set (leafReg q₀) (regs.getD (leafReg q₀) 0 + 1)
  have hstep0 : zfReg11Step ⟨trimZeros P, regs⟩ = some ⟨P ++ [1], r₀⟩ :=
    zfReg11Step_of_inc hev0
  have hP1 : walkInternal 126 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  obtain ⟨s₁, hs₁, hsteps₁, hlen₁⟩ := h1 (P ++ [1]) hP1 r₀ (by simp [r₀, hlen])
  rw [trimZeros_append_one, retStack_append_one] at hsteps₁
  exact ⟨s₁ + 1, by omega, step_zfReg11NSteps hstep0 hsteps₁, hlen₁⟩

/-! ## Section 4: Register Bank Arithmetic Helpers & Parametric Loop Lemmas -/

theorem getD_set_self (regs : List ℕ) (r v : ℕ) (hr : r < regs.length) :
    (regs.set r v).getD r 0 = v := by
  simp [List.getD_eq_getElem?_getD, hr]

theorem getD_set_ne (regs : List ℕ) {r₁ r₂ : ℕ} (v : ℕ) (hne : r₁ ≠ r₂) :
    (regs.set r₁ v).getD r₂ 0 = regs.getD r₂ 0 := by
  simp [List.getD_eq_getElem?_getD, hne]

theorem set_getD_self (regs : List ℕ) (r : ℕ) :
    regs.set r (regs.getD r 0) = regs := by
  apply List.ext_getElem
  · simp
  · intro i hi1 hi2
    rw [List.getElem_set]
    split_ifs with heq
    · subst heq
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
    · rfl

theorem set_eq_self_of_getD_eq {regs : List ℕ} {r v : ℕ} (h : regs.getD r 0 = v) :
    regs.set r v = regs := by
  rw [← h, set_getD_self]

theorem set_comm_of_ne (regs : List ℕ) {r₁ r₂ : ℕ} (v₁ v₂ : ℕ) (hne : r₁ ≠ r₂) :
    (regs.set r₁ v₁).set r₂ v₂ = (regs.set r₂ v₂).set r₁ v₁ :=
  List.set_comm v₁ v₂ hne

/-- Parametric `while_decnz(r, ())` loop: clears register `r` to `0`.
Covers states `381, 385, 391, 395, 398, 415, 420, 421`. -/
theorem subEval_while_clear {q q_dec : Fin 432} (r : ℕ) (hr : r < 11)
    (htr0 : refTrans q 0 = some (0, .right, q_dec))
    (h49 : 49 ≤ q_dec.val) (h70 : q_dec.val ≤ 70) (hdec : isLeafInc q_dec = false)
    (hlr : leafReg q_dec = r)
    (htr1 : refTrans q 1 = some (0, .left, 92)) :
    SubEval q (fun regs => regs.set r 0) := by
  intro P hP
  have hev0 : evalStack (trimZeros P) = .decnz r (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP, evalStack_leaf0_of_walkInternal hP htr0 h49 h70]
    simp [hdec, hlr]
  have hev1 : evalStack (P ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (k := 0) (by omega) hP htr1
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (v : ℕ) (regs : List ℕ), regs.length = 11 → regs.getD r 0 = v →
      ∃ s ≥ 1, zfReg11NSteps s ⟨trimZeros P, regs⟩ = some ⟨retStack P, regs.set r 0⟩ ∧
        (regs.set r 0).length = 11 := by
    intro v
    induction v with
    | zero =>
      intro regs hlen hv
      have hstep := zfReg11Step_of_decnz_zero hev0 hv
      rw [set_eq_self_of_getD_eq hv]
      exact ⟨1, le_refl 1, zfReg11Step_one hstep, hlen⟩
    | succ v ih =>
      intro regs hlen hv
      have hstep1 := zfReg11Step_of_decnz_succ hev0 hv
      have hstep2 := zfReg11Step_of_jump (regs := regs.set r v) hev1
      have hlen' : (regs.set r v).length = 11 := by simp [hlen]
      have hv' : (regs.set r v).getD r 0 = v := getD_set_self regs r v (by omega)
      obtain ⟨s, hs, hsteps, _⟩ := ih (regs.set r v) hlen' hv'
      rw [List.set_set] at hsteps
      exact ⟨s + 2, by omega,
        step_zfReg11NSteps hstep1 (step_zfReg11NSteps hstep2 hsteps), by simp [hlen]⟩
  intro regs hlen
  exact hloop (regs.getD r 0) regs hlen rfl

/-- Parametric `while_decnz(r₁, 3.<r₂>.inc)` loop: adds `r₁` into `r₂` and zeroes `r₁`.
Covers states `399, 401, 403, 405, 407, 409, 410, 411, 416, 418, 419, 425, 427, 428`. -/
theorem subEval_while_move1 {q q_dec q₁ q_inc : Fin 432} (r₁ r₂ : ℕ)
    (hr₁ : r₁ < 11) (_hr₂ : r₂ < 11) (hne : r₁ ≠ r₂)
    (htr0 : refTrans q 0 = some (0, .right, q_dec))
    (hdec49 : 49 ≤ q_dec.val) (hdec70 : q_dec.val ≤ 70) (hdec : isLeafInc q_dec = false)
    (hlr1 : leafReg q_dec = r₁)
    (htr1 : refTrans q 1 = some (1, .right, q₁)) (hq₁ : 96 ≤ q₁.val)
    (htr10 : refTrans q₁ 0 = some (0, .right, q_inc))
    (hinc49 : 49 ≤ q_inc.val) (hinc70 : q_inc.val ≤ 70) (hinc : isLeafInc q_inc = true)
    (hlr2 : leafReg q_inc = r₂)
    (htr11 : refTrans q₁ 1 = some (0, .left, 93)) :
    SubEval q (fun regs => (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + regs.getD r₁ 0)) := by
  intro P hP
  have hP1 : walkInternal 126 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  have hev0 : evalStack (trimZeros P) = .decnz r₁ (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP htr0 hdec49 hdec70]
    simp [hdec, hlr1]
  have hev10 : evalStack (P ++ [1]) = .inc r₂ (P ++ [1] ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hP1 htr10 hinc49 hinc70
    simpa [hinc, hlr2] using h
  have hev11 : evalStack (P ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (P := P ++ [1]) (k := 1) (by omega) hP1 htr11
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (v : ℕ) (regs : List ℕ), regs.length = 11 → regs.getD r₁ 0 = v →
      ∃ s ≥ 1, zfReg11NSteps s ⟨trimZeros P, regs⟩ =
        some ⟨retStack P, (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + v)⟩ ∧
        ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + v)).length = 11 := by
    intro v
    induction v with
    | zero =>
      intro regs hlen hv
      have hstep := zfReg11Step_of_decnz_zero hev0 hv
      have hset : (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + 0) = regs := by
        rw [Nat.add_zero, set_eq_self_of_getD_eq hv, set_getD_self]
      rw [hset]
      exact ⟨1, le_refl 1, zfReg11Step_one hstep, hlen⟩
    | succ v ih =>
      intro regs hlen hv
      let regs₁ := (regs.set r₁ v).set r₂ (regs.getD r₂ 0 + 1)
      have hstep1 := zfReg11Step_of_decnz_succ hev0 hv
      have hstep2 : zfReg11Step ⟨P ++ [1], regs.set r₁ v⟩ = some ⟨P ++ [1] ++ [1], regs₁⟩ := by
        rw [zfReg11Step_of_inc hev10, getD_set_ne _ _ hne]
      have hstep3 := zfReg11Step_of_jump (regs := regs₁) hev11
      have hlen₁ : regs₁.length = 11 := by simp [regs₁, hlen]
      have hv₁ : regs₁.getD r₁ 0 = v := by
        dsimp [regs₁]
        rw [getD_set_ne _ _ hne.symm, getD_set_self regs r₁ v (by omega)]
      obtain ⟨s, hs, hsteps, _⟩ := ih regs₁ hlen₁ hv₁
      have hregs_eq : (regs₁.set r₁ 0).set r₂ (regs₁.getD r₂ 0 + v) =
          (regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + (v + 1)) := by
        have hr₂_get : regs₁.getD r₂ 0 = regs.getD r₂ 0 + 1 :=
          getD_set_self (regs.set r₁ v) r₂ (regs.getD r₂ 0 + 1) (by simp; omega)
        rw [hr₂_get]
        dsimp only [regs₁]
        rw [set_comm_of_ne (regs.set r₁ v) (regs.getD r₂ 0 + 1) 0 hne.symm,
          List.set_set, List.set_set]
        congr 1
        omega
      rw [hregs_eq] at hsteps
      exact ⟨s + 3, by omega,
        step_zfReg11NSteps hstep1 (step_zfReg11NSteps hstep2 (step_zfReg11NSteps hstep3 hsteps)),
        by simp [hlen]⟩
  intro regs hlen
  exact hloop (regs.getD r₁ 0) regs hlen rfl

/-- Parametric `while_decnz(r₁, { inc r₂; inc r₃ })` loop: adds `r₁` into both `r₂` and `r₃`
and zeroes `r₁`. Covers states `382, 386, 387, 388, 392, 393, 394, 396, 397, 412, 422`. -/
theorem subEval_while_move2 {q q_dec q₁ q₂ q_inc1 q_inc2 : Fin 432} (r₁ r₂ r₃ : ℕ)
    (hr₁ : r₁ < 11) (hr₂ : r₂ < 11) (hr₃ : r₃ < 11)
    (hne12 : r₁ ≠ r₂) (hne13 : r₁ ≠ r₃) (hne23 : r₂ ≠ r₃)
    (htr0 : refTrans q 0 = some (0, .right, q_dec))
    (hdec49 : 49 ≤ q_dec.val) (hdec70 : q_dec.val ≤ 70) (hdec : isLeafInc q_dec = false)
    (hlr1 : leafReg q_dec = r₁)
    (htr1 : refTrans q 1 = some (1, .right, q₁)) (hq₁ : 96 ≤ q₁.val)
    (htr10 : refTrans q₁ 0 = some (0, .right, q₂)) (hq₂ : 96 ≤ q₂.val)
    (htr11 : refTrans q₁ 1 = some (0, .left, 93))
    (htr20 : refTrans q₂ 0 = some (0, .right, q_inc1))
    (hinc1_49 : 49 ≤ q_inc1.val) (hinc1_70 : q_inc1.val ≤ 70) (hinc1 : isLeafInc q_inc1 = true)
    (hlr2 : leafReg q_inc1 = r₂)
    (htr21 : refTrans q₂ 1 = some (1, .right, q_inc2))
    (hinc2_49 : 49 ≤ q_inc2.val) (hinc2_70 : q_inc2.val ≤ 70) (hinc2 : isLeafInc q_inc2 = true)
    (hlr3 : leafReg q_inc2 = r₃) :
    SubEval q (fun regs =>
      ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + regs.getD r₁ 0)).set
        r₃ (regs.getD r₃ 0 + regs.getD r₁ 0)) := by
  intro P hP
  have hP1 : walkInternal 126 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  have hP10 : walkInternal 126 (P ++ [1] ++ [0]) = some q₂ := walkInternal_snoc hP1 htr10 hq₂
  have hbody := subEval_inc_inc htr20 hinc1_49 hinc1_70 hinc1 htr21 hinc2_49 hinc2_70 hinc2
  have hev0 : evalStack (trimZeros P) = .decnz r₁ (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP htr0 hdec49 hdec70]
    simp [hdec, hlr1]
  have hev11 : evalStack (P ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal (P := P ++ [1]) (k := 1) (by omega) hP1 htr11
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (v : ℕ) (regs : List ℕ), regs.length = 11 → regs.getD r₁ 0 = v →
      ∃ s ≥ 1, zfReg11NSteps s ⟨trimZeros P, regs⟩ =
        some ⟨retStack P,
          ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + v)).set r₃ (regs.getD r₃ 0 + v)⟩ ∧
        (((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + v)).set
          r₃ (regs.getD r₃ 0 + v)).length = 11 := by
    intro v
    induction v with
    | zero =>
      intro regs hlen hv
      have hstep := zfReg11Step_of_decnz_zero hev0 hv
      have hset :
          ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + 0)).set r₃ (regs.getD r₃ 0 + 0) = regs := by
        rw [Nat.add_zero, Nat.add_zero, set_eq_self_of_getD_eq hv, set_getD_self, set_getD_self]
      rw [hset]
      exact ⟨1, le_refl 1, zfReg11Step_one hstep, hlen⟩
    | succ v ih =>
      intro regs hlen hv
      have hstep1 := zfReg11Step_of_decnz_succ hev0 hv
      obtain ⟨sb, hsb, hsteps_b, hlen_b⟩ :=
        hbody (P ++ [1] ++ [0]) hP10 (regs.set r₁ v) (by simp [hlen])
      rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero, hlr2, hlr3] at hsteps_b
      let regs₁ := ((regs.set r₁ v).set r₂ (regs.getD r₂ 0 + 1)).set r₃ (regs.getD r₃ 0 + 1)
      have hb_eq : ((regs.set r₁ v).set r₂ ((regs.set r₁ v).getD r₂ 0 + 1)).set
          r₃ (((regs.set r₁ v).set r₂ ((regs.set r₁ v).getD r₂ 0 + 1)).getD r₃ 0 + 1) = regs₁ := by
        dsimp only [regs₁]
        rw [getD_set_ne _ _ hne12, getD_set_ne _ _ hne23, getD_set_ne _ _ hne13]
      dsimp only at hsteps_b
      rw [hb_eq] at hsteps_b
      have hstep3 := zfReg11Step_of_jump (regs := regs₁) hev11
      have hlen₁ : regs₁.length = 11 := by simp [regs₁, hlen]
      have hv₁ : regs₁.getD r₁ 0 = v := by
        dsimp [regs₁]
        rw [getD_set_ne _ _ hne13.symm, getD_set_ne _ _ hne12.symm,
          getD_set_self regs r₁ v (by omega)]
      obtain ⟨s, hs, hsteps, _⟩ := ih regs₁ hlen₁ hv₁
      have hregs_eq :
          ((regs₁.set r₁ 0).set r₂ (regs₁.getD r₂ 0 + v)).set r₃ (regs₁.getD r₃ 0 + v) =
          ((regs.set r₁ 0).set r₂ (regs.getD r₂ 0 + (v + 1))).set
            r₃ (regs.getD r₃ 0 + (v + 1)) := by
        have hr₂_get : regs₁.getD r₂ 0 = regs.getD r₂ 0 + 1 := by
          dsimp [regs₁]
          rw [getD_set_ne _ _ hne23.symm,
            getD_set_self (regs.set r₁ v) r₂ (regs.getD r₂ 0 + 1) (by simp; omega)]
        have hr₃_get : regs₁.getD r₃ 0 = regs.getD r₃ 0 + 1 := by
          dsimp [regs₁]
          exact getD_set_self _ r₃ (regs.getD r₃ 0 + 1) (by simp; omega)
        rw [hr₂_get, hr₃_get]
        dsimp only [regs₁]
        rw [set_comm_of_ne _ (regs.getD r₃ 0 + 1) 0 hne13.symm,
          set_comm_of_ne (regs.set r₁ v) (regs.getD r₂ 0 + 1) 0 hne12.symm,
          List.set_set,
          set_comm_of_ne _ (regs.getD r₃ 0 + 1) (regs.getD r₂ 0 + 1 + v) hne23.symm,
          List.set_set, List.set_set]
        have hadd1 : regs.getD r₂ 0 + 1 + v = regs.getD r₂ 0 + (v + 1) := by omega
        have hadd2 : regs.getD r₃ 0 + 1 + v = regs.getD r₃ 0 + (v + 1) := by omega
        rw [hadd1, hadd2]
      rw [hregs_eq] at hsteps
      have hchain1 := step_zfReg11NSteps hstep1 hsteps_b
      have hchain2 := zfReg11NSteps_bind_eq hchain1 (step_zfReg11NSteps hstep3 hsteps)
      exact ⟨(sb + 1) + (s + 1), by omega, hchain2, by simp [hlen]⟩
  intro regs hlen
  exact hloop (regs.getD r₁ 0) regs hlen rfl

/-! ## Section 5: Concrete `while_decnz` Subroutine Instantiations -/

/-- `while_decnz(axiomcode,()).0` (State `381`): clears register `4`. -/
theorem subEval_381 : SubEval 381 (fun regs => regs.set 4 0) :=
  subEval_while_clear 4 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(param1,()).0` (State `385`): clears register `5`. -/
theorem subEval_385 : SubEval 385 (fun regs => regs.set 5 0) :=
  subEval_while_clear 5 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(param2,()).0` (State `391`): clears register `6`. -/
theorem subEval_391 : SubEval 391 (fun regs => regs.set 6 0) :=
  subEval_while_clear 6 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(param3,()).0` (State `395`): clears register `7`. -/
theorem subEval_395 : SubEval 395 (fun regs => regs.set 7 0) :=
  subEval_while_clear 7 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,()).0` (State `398`): clears register `8`. -/
theorem subEval_398 : SubEval 398 (fun regs => regs.set 8 0) :=
  subEval_while_clear 8 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch2,()).0` (State `415`): clears register `9`. -/
theorem subEval_415 : SubEval 415 (fun regs => regs.set 9 0) :=
  subEval_while_clear 9 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch3,()).0` (State `420`): clears register `10`. -/
theorem subEval_420 : SubEval 420 (fun regs => regs.set 10 0) :=
  subEval_while_clear 10 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(topwff,()).0` (State `421`): clears register `2`. -/
theorem subEval_421 : SubEval 421 (fun regs => regs.set 2 0) :=
  subEval_while_clear 2 (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.axiomcode.inc).0` (State `399`):
adds register `8` into `4` and zeroes `8`. -/
theorem subEval_399 :
    SubEval 399 (fun regs => (regs.set 8 0).set 4 (regs.getD 4 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 4 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.nextproof.inc).0` (State `401`):
adds register `8` into `1` and zeroes `8`. -/
theorem subEval_401 :
    SubEval 401 (fun regs => (regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 1 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.param1.inc).0` (State `403`):
adds register `8` into `5` and zeroes `8`. -/
theorem subEval_403 :
    SubEval 403 (fun regs => (regs.set 8 0).set 5 (regs.getD 5 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 5 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.param2.inc).0` (State `405`):
adds register `8` into `6` and zeroes `8`. -/
theorem subEval_405 :
    SubEval 405 (fun regs => (regs.set 8 0).set 6 (regs.getD 6 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 6 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.param3.inc).0` (State `407`):
adds register `8` into `7` and zeroes `8`. -/
theorem subEval_407 :
    SubEval 407 (fun regs => (regs.set 8 0).set 7 (regs.getD 7 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 7 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.scratch2.inc).0` (State `409`):
adds register `8` into `9` and zeroes `8`. -/
theorem subEval_409 :
    SubEval 409 (fun regs => (regs.set 8 0).set 9 (regs.getD 9 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 9 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.topwff.inc).0` (State `410`):
adds register `8` into `2` and zeroes `8`. -/
theorem subEval_410 :
    SubEval 410 (fun regs => (regs.set 8 0).set 2 (regs.getD 2 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 2 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch1,3.wffstack.inc).0` (State `411`):
adds register `8` into `3` and zeroes `8`. -/
theorem subEval_411 :
    SubEval 411 (fun regs => (regs.set 8 0).set 3 (regs.getD 3 0 + regs.getD 8 0)) :=
  subEval_while_move1 8 3 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch2,3.prooflist.inc).0` (State `416`):
adds register `9` into `0` and zeroes `9`. -/
theorem subEval_416 :
    SubEval 416 (fun regs => (regs.set 9 0).set 0 (regs.getD 0 0 + regs.getD 9 0)) :=
  subEval_while_move1 9 0 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch2,3.topwff.inc).0` (State `418`):
adds register `9` into `2` and zeroes `9`. -/
theorem subEval_418 :
    SubEval 418 (fun regs => (regs.set 9 0).set 2 (regs.getD 2 0 + regs.getD 9 0)) :=
  subEval_while_move1 9 2 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(scratch2,3.wffstack.inc).0` (State `419`):
adds register `9` into `3` and zeroes `9`. -/
theorem subEval_419 :
    SubEval 419 (fun regs => (regs.set 9 0).set 3 (regs.getD 3 0 + regs.getD 9 0)) :=
  subEval_while_move1 9 3 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(topwff,3.scratch1.inc).0` (State `425`):
adds register `2` into `8` and zeroes `2`. -/
theorem subEval_425 :
    SubEval 425 (fun regs => (regs.set 2 0).set 8 (regs.getD 8 0 + regs.getD 2 0)) :=
  subEval_while_move1 2 8 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(topwff,3.scratch2.inc).0` (State `427`):
adds register `2` into `9` and zeroes `2`. -/
theorem subEval_427 :
    SubEval 427 (fun regs => (regs.set 2 0).set 9 (regs.getD 9 0 + regs.getD 2 0)) :=
  subEval_while_move1 2 9 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(wffstack,3.topwff.inc).0` (State `428`):
adds register `3` into `2` and zeroes `3`. -/
theorem subEval_428 :
    SubEval 428 (fun regs => (regs.set 3 0).set 2 (regs.getD 2 0 + regs.getD 3 0)) :=
  subEval_while_move1 3 2 (by decide) (by decide) (by decide) rfl (by decide) (by decide)
    rfl rfl rfl (by decide) rfl (by decide) (by decide) rfl rfl rfl

/-- `while_decnz(nextproof,67).0` (State `382`):
adds register `1` into `8` and `0` and zeroes `1`. -/
theorem subEval_382 :
    SubEval 382 (fun regs =>
      ((regs.set 1 0).set 8 (regs.getD 8 0 + regs.getD 1 0)).set
        0 (regs.getD 0 0 + regs.getD 1 0)) :=
  subEval_while_move2 1 8 0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param1,113).0` (State `386`): adds register `5` into `8` and `9` and zeroes `5`. -/
theorem subEval_386 :
    SubEval 386 (fun regs =>
      ((regs.set 5 0).set 8 (regs.getD 8 0 + regs.getD 5 0)).set
        9 (regs.getD 9 0 + regs.getD 5 0)) :=
  subEval_while_move2 5 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param1,42).0` (State `387`): adds register `5` into `2` and `8` and zeroes `5`. -/
theorem subEval_387 :
    SubEval 387 (fun regs =>
      ((regs.set 5 0).set 2 (regs.getD 2 0 + regs.getD 5 0)).set
        8 (regs.getD 8 0 + regs.getD 5 0)) :=
  subEval_while_move2 5 2 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param1,99).0` (State `388`): adds register `5` into `8` and `2` and zeroes `5`. -/
theorem subEval_388 :
    SubEval 388 (fun regs =>
      ((regs.set 5 0).set 8 (regs.getD 8 0 + regs.getD 5 0)).set
        2 (regs.getD 2 0 + regs.getD 5 0)) :=
  subEval_while_move2 5 8 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param2,113).0` (State `392`): adds register `6` into `8` and `9` and zeroes `6`. -/
theorem subEval_392 :
    SubEval 392 (fun regs =>
      ((regs.set 6 0).set 8 (regs.getD 8 0 + regs.getD 6 0)).set
        9 (regs.getD 9 0 + regs.getD 6 0)) :=
  subEval_while_move2 6 8 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param2,42).0` (State `393`): adds register `6` into `2` and `8` and zeroes `6`. -/
theorem subEval_393 :
    SubEval 393 (fun regs =>
      ((regs.set 6 0).set 2 (regs.getD 2 0 + regs.getD 6 0)).set
        8 (regs.getD 8 0 + regs.getD 6 0)) :=
  subEval_while_move2 6 2 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param2,96).0` (State `394`): adds register `6` into `8` and `10` and zeroes `6`. -/
theorem subEval_394 :
    SubEval 394 (fun regs =>
      ((regs.set 6 0).set 8 (regs.getD 8 0 + regs.getD 6 0)).set
        10 (regs.getD 10 0 + regs.getD 6 0)) :=
  subEval_while_move2 6 8 10 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param3,42).0` (State `396`): adds register `7` into `2` and `8` and zeroes `7`. -/
theorem subEval_396 :
    SubEval 396 (fun regs =>
      ((regs.set 7 0).set 2 (regs.getD 2 0 + regs.getD 7 0)).set
        8 (regs.getD 8 0 + regs.getD 7 0)) :=
  subEval_while_move2 7 2 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(param3,96).0` (State `397`): adds register `7` into `8` and `10` and zeroes `7`. -/
theorem subEval_397 :
    SubEval 397 (fun regs =>
      ((regs.set 7 0).set 8 (regs.getD 8 0 + regs.getD 7 0)).set
        10 (regs.getD 10 0 + regs.getD 7 0)) :=
  subEval_while_move2 7 8 10 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(scratch1,9).0` (State `412`):
adds register `8` into `2` and `9` and zeroes `8`. -/
theorem subEval_412 :
    SubEval 412 (fun regs =>
      ((regs.set 8 0).set 2 (regs.getD 2 0 + regs.getD 8 0)).set
        9 (regs.getD 9 0 + regs.getD 8 0)) :=
  subEval_while_move2 8 2 9 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-- `while_decnz(topwff,21).0` (State `422`):
adds register `2` into `3` and `8` and zeroes `2`. -/
theorem subEval_422 :
    SubEval 422 (fun regs =>
      ((regs.set 2 0).set 3 (regs.getD 3 0 + regs.getD 2 0)).set
        8 (regs.getD 8 0 + regs.getD 2 0)) :=
  subEval_while_move2 2 3 8 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl rfl (by decide) (by decide) rfl rfl
    rfl (by decide) (by decide) rfl rfl

/-! ## Section 1: Cantor Pairing Subroutines (`329..336`) -/

/-- Inner body `332` of `pair(scratch1, topwff, wffstack)`:
increments `scratch1` (`8`) and moves `wffstack` (`3`) into `topwff` (`2`). -/
theorem subEval_332 :
    SubEval 332 (fun regs =>
      let r₀ := regs.set 8 (regs.getD 8 0 + 1)
      (r₀.set 3 0).set 2 (r₀.getD 2 0 + r₀.getD 3 0)) :=
  subEval_inc_seq (q₀ := 62) rfl (by decide) (by decide) rfl rfl (by decide) subEval_428

/-- Inner body `336` of `pair(scratch2, scratch1, topwff)`:
increments `scratch2` (`9`) and moves `topwff` (`2`) into `scratch1` (`8`). -/
theorem subEval_336 :
    SubEval 336 (fun regs =>
      let r₀ := regs.set 9 (regs.getD 9 0 + 1)
      (r₀.set 2 0).set 8 (r₀.getD 8 0 + r₀.getD 2 0)) :=
  subEval_inc_seq (q₀ := 64) rfl (by decide) (by decide) rfl rfl (by decide) subEval_425

/-- Parametric Cantor pairing subroutine `pair(out, r1, r2)` covering states `329` and `333`. -/
theorem subEval_pair {q q_move2 q1 q_dec q2 q3 : Fin 432} (out r1 r2 : ℕ)
    (hout : out < 11) (hr1 : r1 < 11) (hr2 : r2 < 11)
    (hne12 : r1 ≠ r2) (hne1o : r1 ≠ out) (hne2o : r2 ≠ out)
    (htr0 : refTrans q 0 = some (0, .right, q_move2)) (hq_move2 : 96 ≤ q_move2.val)
    (htr1 : refTrans q 1 = some (1, .right, q1)) (hq1 : 96 ≤ q1.val)
    (htr10 : refTrans q1 0 = some (0, .right, q_dec))
    (hdec49 : 49 ≤ q_dec.val) (hdec70 : q_dec.val ≤ 70) (hdec : isLeafInc q_dec = false)
    (hlr_dec : leafReg q_dec = r2)
    (htr11 : refTrans q1 1 = some (1, .right, q2)) (hq2 : 96 ≤ q2.val)
    (htr20 : refTrans q2 0 = some (0, .right, q3)) (hq3 : 96 ≤ q3.val)
    (htr21 : refTrans q2 1 = some (0, .left, 94))
    (hmove2 : SubEval q_move2 (fun regs =>
      ((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
        out (regs.getD out 0 + regs.getD r1 0)))
    (hbody : SubEval q3 (fun regs =>
      let r₀ := regs.set out (regs.getD out 0 + 1)
      (r₀.set r2 0).set r1 (r₀.getD r1 0 + r₀.getD r2 0))) :
    SubEval q (regPairOp out r1 r2) := by
  intro P hP
  have hP0 : walkInternal 126 (P ++ [0]) = some q_move2 := walkInternal_snoc hP htr0 hq_move2
  have hP1 : walkInternal 126 (P ++ [1]) = some q1 := walkInternal_snoc hP htr1 hq1
  have hP11 : walkInternal 126 (P ++ [1] ++ [1]) = some q2 := walkInternal_snoc hP1 htr11 hq2
  have hP110 : walkInternal 126 (P ++ [1] ++ [1] ++ [0]) = some q3 :=
    walkInternal_snoc hP11 htr20 hq3
  have hev10 : evalStack (P ++ [1]) = .decnz r2 (P ++ [1] ++ [1]) (retStack P) := by
    have h := evalStack_leaf0_of_walkInternal hP1 htr10 hdec49 hdec70
    simpa [hdec, hlr_dec] using h
  have hev21 : evalStack (P ++ [1] ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h :=
      evalStack_continue1_of_walkInternal (P := P ++ [1] ++ [1]) (k := 2) (by omega) hP11 htr21
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (n : ℕ) (regs : List ℕ), regs.length = 11 →
      regs.getD r1 0 + regs.getD r2 0 = n →
      ∃ s ≥ 1, zfReg11NSteps s ⟨trimZeros P, regs⟩ =
        some ⟨retStack P,
          ((regs.set r1 0).set r2 0).set out (triLoop n (regs.getD out 0 + regs.getD r1 0))⟩ ∧
        (((regs.set r1 0).set r2 0).set
          out (triLoop n (regs.getD out 0 + regs.getD r1 0))).length = 11 := by
    intro n
    induction n with
    | zero =>
      intro regs hlen hn
      obtain ⟨s₀, hs₀, hsteps₀, hlen₀⟩ := hmove2 (P ++ [0]) hP0 regs hlen
      rw [trimZeros_append_zero, retStack_append_zero] at hsteps₀
      dsimp only at hsteps₀
      let regs₁ := ((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
        out (regs.getD out 0 + regs.getD r1 0)
      change zfReg11NSteps s₀ ⟨trimZeros P, regs⟩ = some ⟨P ++ [1], regs₁⟩ at hsteps₀
      have hr2_zero : regs₁.getD r2 0 = 0 := by
        dsimp [regs₁]
        rw [getD_set_ne _ _ hne2o.symm,
          getD_set_self _ r2 (regs.getD r2 0 + regs.getD r1 0) (by simp; omega)]
        omega
      have hstep1 := zfReg11Step_of_decnz_zero (regs := regs₁) hev10 hr2_zero
      have hregs_eq : regs₁ =
          ((regs.set r1 0).set r2 0).set out (triLoop 0 (regs.getD out 0 + regs.getD r1 0)) := by
        dsimp [regs₁, triLoop]
        have hsum : regs.getD r2 0 + regs.getD r1 0 = 0 := by omega
        rw [hsum]
      rw [hregs_eq] at hsteps₀ hstep1
      exact ⟨s₀ + 1, by omega, zfReg11NSteps_bind_eq hsteps₀ (zfReg11Step_one hstep1),
        by simp [hlen]⟩
    | succ m ih =>
      intro regs hlen hn
      obtain ⟨s₀, hs₀, hsteps₀, hlen₀⟩ := hmove2 (P ++ [0]) hP0 regs hlen
      rw [trimZeros_append_zero, retStack_append_zero] at hsteps₀
      dsimp only at hsteps₀
      let regs₁ := ((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
        out (regs.getD out 0 + regs.getD r1 0)
      change zfReg11NSteps s₀ ⟨trimZeros P, regs⟩ = some ⟨P ++ [1], regs₁⟩ at hsteps₀
      have hr2_succ : regs₁.getD r2 0 = m + 1 := by
        dsimp [regs₁]
        rw [getD_set_ne _ _ hne2o.symm,
          getD_set_self _ r2 (regs.getD r2 0 + regs.getD r1 0) (by simp; omega)]
        omega
      have hstep1 := zfReg11Step_of_decnz_succ (regs := regs₁) hev10 hr2_succ
      obtain ⟨s₃, hs₃, hsteps₃, hlen₃⟩ :=
        hbody (P ++ [1] ++ [1] ++ [0]) hP110 (regs₁.set r2 m) (by simp [regs₁, hlen])
      rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps₃
      dsimp only at hsteps₃
      let regs₂ := ((regs.set r1 m).set r2 0).set out (regs.getD out 0 + regs.getD r1 0 + 1)
      have hbody_eq :
          (let r₀ := (regs₁.set r2 m).set out ((regs₁.set r2 m).getD out 0 + 1)
           (r₀.set r2 0).set r1 (r₀.getD r1 0 + r₀.getD r2 0)) = regs₂ := by
        dsimp only [regs₁, regs₂]
        have hout_get :
            ((((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
              out (regs.getD out 0 + regs.getD r1 0)).set r2 m).getD out 0 =
            regs.getD out 0 + regs.getD r1 0 := by
          rw [getD_set_ne _ _ hne2o,
            getD_set_self _ out (regs.getD out 0 + regs.getD r1 0) (by simp; omega)]
        rw [hout_get]
        have hr0_eq :
            ((((regs.set r1 0).set r2 (regs.getD r2 0 + regs.getD r1 0)).set
              out (regs.getD out 0 + regs.getD r1 0)).set r2 m).set
              out (regs.getD out 0 + regs.getD r1 0 + 1) =
            ((regs.set r1 0).set r2 m).set out (regs.getD out 0 + regs.getD r1 0 + 1) := by
          rw [set_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0) m hne2o.symm,
            List.set_set, List.set_set]
        rw [hr0_eq]
        have hr1_get :
            (((regs.set r1 0).set r2 m).set
              out (regs.getD out 0 + regs.getD r1 0 + 1)).getD r1 0 = 0 := by
          rw [getD_set_ne _ _ hne1o.symm, getD_set_ne _ _ hne12.symm,
            getD_set_self regs r1 0 (by omega)]
        have hr2_get :
            (((regs.set r1 0).set r2 m).set
              out (regs.getD out 0 + regs.getD r1 0 + 1)).getD r2 0 = m := by
          rw [getD_set_ne _ _ hne2o.symm, getD_set_self _ r2 m (by simp; omega)]
        rw [hr1_get, hr2_get, Nat.zero_add]
        rw [set_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0 + 1) 0 hne2o.symm,
          List.set_set,
          set_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0 + 1) m hne1o.symm,
          set_comm_of_ne (regs.set r1 0) 0 m hne12.symm,
          List.set_set]
      rw [hbody_eq] at hsteps₃
      have hstep_jmp := zfReg11Step_of_jump (regs := regs₂) hev21
      have hlen₂ : regs₂.length = 11 := by simp [regs₂, hlen]
      have hr1_₂ : regs₂.getD r1 0 = m := by
        dsimp [regs₂]
        rw [getD_set_ne _ _ hne1o.symm, getD_set_ne _ _ hne12.symm,
          getD_set_self regs r1 m (by omega)]
      have hr2_₂ : regs₂.getD r2 0 = 0 := by
        dsimp [regs₂]
        rw [getD_set_ne _ _ hne2o.symm, getD_set_self _ r2 0 (by simp; omega)]
      have hout_₂ : regs₂.getD out 0 = regs.getD out 0 + regs.getD r1 0 + 1 := by
        dsimp [regs₂]
        exact getD_set_self _ out (regs.getD out 0 + regs.getD r1 0 + 1) (by simp; omega)
      obtain ⟨s_ih, hs_ih, hsteps_ih, _⟩ := ih regs₂ hlen₂ (by omega)
      have hfinal_eq :
          ((regs₂.set r1 0).set r2 0).set out (triLoop m (regs₂.getD out 0 + regs₂.getD r1 0)) =
          ((regs.set r1 0).set r2 0).set
            out (triLoop (m + 1) (regs.getD out 0 + regs.getD r1 0)) := by
        rw [hout_₂, hr1_₂]
        have htri : triLoop m (regs.getD out 0 + regs.getD r1 0 + 1 + m) =
            triLoop (m + 1) (regs.getD out 0 + regs.getD r1 0) := by
          simp only [triLoop]
          congr 1
          omega
        rw [htri]
        dsimp only [regs₂]
        rw [set_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0 + 1) 0 hne1o.symm,
          set_comm_of_ne (regs.set r1 m) 0 0 hne12.symm,
          List.set_set,
          set_comm_of_ne _ (regs.getD out 0 + regs.getD r1 0 + 1) 0 hne2o.symm,
          List.set_set, List.set_set]
      rw [hfinal_eq] at hsteps_ih
      have hchain1 := zfReg11NSteps_bind_eq hsteps₀ (step_zfReg11NSteps hstep1 hsteps₃)
      have hchain2 := zfReg11NSteps_bind_eq hchain1 (step_zfReg11NSteps hstep_jmp hsteps_ih)
      exact ⟨(s₀ + (s₃ + 1)) + (s_ih + 1), by omega, hchain2, by simp [hlen]⟩
  intro regs hlen
  exact hloop (regs.getD r1 0 + regs.getD r2 0) regs hlen rfl

/-- `pair(scratch1, topwff, wffstack).0` (State `329`): Cantor-pairs `2` and `3` into `8`. -/
theorem subEval_329 : SubEval 329 (regPairOp 8 2 3) :=
  subEval_pair 8 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl subEval_422 subEval_332

/-- `pair(scratch2, scratch1, topwff).0` (State `333`): Cantor-pairs `8` and `2` into `9`. -/
theorem subEval_333 : SubEval 333 (regPairOp 9 8 2) :=
  subEval_pair 9 8 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) rfl subEval_412 subEval_336

/-! ## Section 2: Cantor Unpairing Subroutines (`348..357`) -/

/-- General functional specification of `unpair(out1, out2, rin)` on an 11-register bank `regs`
for arbitrary initial values of `out1` and `out2`. -/
def regUnpairGen (out1 out2 rin : ℕ) (regs : List ℕ) : List ℕ :=
  let p := unpairLoop (regs.getD rin 0) (regs.getD out1 0, regs.getD out2 0)
  ((regs.set rin 0).set out1 p.1).set out2 p.2

theorem regUnpairGen_eq_regUnpairOp {out1 out2 rin : ℕ} {regs : List ℕ}
    (h1 : regs.getD out1 0 = 0) (h2 : regs.getD out2 0 = 0) :
    regUnpairGen out1 out2 rin regs = regUnpairOp out1 out2 rin regs := by
  unfold regUnpairGen regUnpairOp
  rw [h1, h2]

/-- Parametric Cantor unpairing subroutine `unpair(out1, 9, rin)` covering states
`352, 353, 354`. -/
theorem subEval_unpair {q q_dec q1 q_inc1 q2 q3 q_move : Fin 432} (out1 rin : ℕ)
    (hout1 : out1 < 11) (hrin : rin < 11)
    (hne_in_1 : rin ≠ out1) (hne_in_9 : rin ≠ 9) (hne_1_9 : out1 ≠ 9)
    (htr0 : refTrans q 0 = some (0, .right, q_dec))
    (hdec49 : 49 ≤ q_dec.val) (hdec70 : q_dec.val ≤ 70) (hdec : isLeafInc q_dec = false)
    (hlr_dec : leafReg q_dec = rin)
    (htr1 : refTrans q 1 = some (1, .right, q1)) (hq1 : 96 ≤ q1.val)
    (htr10 : refTrans q1 0 = some (0, .right, q_inc1))
    (hinc49 : 49 ≤ q_inc1.val) (hinc70 : q_inc1.val ≤ 70) (hinc : isLeafInc q_inc1 = true)
    (hlr_inc : leafReg q_inc1 = out1)
    (htr11 : refTrans q1 1 = some (1, .right, q2)) (hq2 : 96 ≤ q2.val)
    (htr20 : refTrans q2 0 = some (0, .right, 348))
    (htr21 : refTrans q2 1 = some (1, .right, q3)) (hq3 : 96 ≤ q3.val)
    (htr30 : refTrans q3 0 = some (0, .right, q_move)) (hq_move : 96 ≤ q_move.val)
    (htr31 : refTrans q3 1 = some (0, .left, 95))
    (hmove : SubEval q_move (fun regs =>
      (regs.set out1 0).set 9 (regs.getD 9 0 + regs.getD out1 0))) :
    SubEval q (regUnpairGen out1 9 rin) := by
  intro P hP
  have hP1 : walkInternal 126 (P ++ [1]) = some q1 := walkInternal_snoc hP htr1 hq1
  have hP11 : walkInternal 126 (P ++ [1] ++ [1]) = some q2 := walkInternal_snoc hP1 htr11 hq2
  have hP110 : walkInternal 126 (P ++ [1] ++ [1] ++ [0]) = some 348 :=
    walkInternal_snoc hP11 htr20 (by decide)
  have hP111 : walkInternal 126 (P ++ [1] ++ [1] ++ [1]) = some q3 :=
    walkInternal_snoc hP11 htr21 hq3
  have hP1110 : walkInternal 126 (P ++ [1] ++ [1] ++ [1] ++ [0]) = some q_move :=
    walkInternal_snoc hP111 htr30 hq_move
  have hev0 : evalStack (trimZeros P) = .decnz rin (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP htr0 hdec49 hdec70]
    simp [hdec, hlr_dec]
  have hev10 : evalStack (P ++ [1]) = .inc out1 (P ++ [1] ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hP1 htr10 hinc49 hinc70
    simpa [hinc, hlr_inc] using h
  have hev11 : evalStack (P ++ [1] ++ [1]) =
      .decnz 9 (P ++ [1] ++ [1] ++ [0] ++ [1]) (P ++ [1] ++ [1] ++ [1]) := by
    have htrim := evalStack_trimZeros_of_walkInternal hP110
    rw [trimZeros_append_zero, trimZeros_append_one] at htrim
    have hleaf := evalStack_leaf0_of_walkInternal (q' := 63) hP110 rfl (by decide) (by decide)
    rw [htrim, hleaf, retStack_append_zero]
    rfl
  have hev1101 : evalStack (P ++ [1] ++ [1] ++ [0] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal
      (P := P ++ [1] ++ [1] ++ [0]) (k := 2) (by omega) hP110 rfl
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hev1111 : evalStack (P ++ [1] ++ [1] ++ [1] ++ [1]) = .jump (trimZeros P) := by
    have h := evalStack_continue1_of_walkInternal
      (P := P ++ [1] ++ [1] ++ [1]) (k := 3) (by omega) hP111 htr31
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hloop : ∀ (z : ℕ) (regs : List ℕ), regs.length = 11 → regs.getD rin 0 = z →
      ∃ s ≥ 1, zfReg11NSteps s ⟨trimZeros P, regs⟩ =
        some ⟨retStack P, regUnpairGen out1 9 rin regs⟩ ∧
        (regUnpairGen out1 9 rin regs).length = 11 := by
    intro z
    induction z with
    | zero =>
      intro regs hlen hz
      have hstep := zfReg11Step_of_decnz_zero hev0 hz
      have hset : regUnpairGen out1 9 rin regs = regs := by
        unfold regUnpairGen
        rw [hz]
        dsimp [unpairLoop]
        rw [set_eq_self_of_getD_eq hz, set_getD_self, set_getD_self]
      rw [hset]
      exact ⟨1, le_refl 1, zfReg11Step_one hstep, hlen⟩
    | succ z ih =>
      intro regs hlen hz
      have hstep1 := zfReg11Step_of_decnz_succ hev0 hz
      let regs₁ := (regs.set rin z).set out1 (regs.getD out1 0 + 1)
      have hstep2 : zfReg11Step ⟨P ++ [1], regs.set rin z⟩ = some ⟨P ++ [1] ++ [1], regs₁⟩ := by
        rw [zfReg11Step_of_inc hev10, getD_set_ne _ _ hne_in_1]
      have hr9_₁ : regs₁.getD 9 0 = regs.getD 9 0 := by
        dsimp [regs₁]
        rw [getD_set_ne _ _ hne_1_9, getD_set_ne _ _ hne_in_9]
      rcases hy : regs.getD 9 0 with _ | y
      · -- Case `regs.getD 9 0 = 0`
        have hstep3 := zfReg11Step_of_decnz_zero (regs := regs₁) hev11 (by rw [hr9_₁, hy])
        obtain ⟨sm, hsm, hsteps_m, _⟩ :=
          hmove (P ++ [1] ++ [1] ++ [1] ++ [0]) hP1110 regs₁ (by simp [regs₁, hlen])
        rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps_m
        dsimp only at hsteps_m
        let regs₂ := ((regs.set rin z).set out1 0).set 9 (regs.getD out1 0 + 1)
        have hm_eq :
            (regs₁.set out1 0).set 9 (regs₁.getD 9 0 + regs₁.getD out1 0) = regs₂ := by
          rw [hr9_₁, hy, Nat.zero_add]
          dsimp [regs₁, regs₂]
          have hout1_get : ((regs.set rin z).set out1 (regs.getD out1 0 + 1)).getD out1 0 =
              regs.getD out1 0 + 1 :=
            getD_set_self _ out1 (regs.getD out1 0 + 1) (by simp; omega)
          rw [hout1_get, List.set_set]
        rw [hm_eq] at hsteps_m
        have hstep_jmp := zfReg11Step_of_jump (regs := regs₂) hev1111
        have hlen₂ : regs₂.length = 11 := by simp [regs₂, hlen]
        have hrin_₂ : regs₂.getD rin 0 = z := by
          dsimp [regs₂]
          rw [getD_set_ne _ _ hne_in_9.symm, getD_set_ne _ _ hne_in_1.symm,
            getD_set_self regs rin z (by omega)]
        obtain ⟨s_ih, hs_ih, hsteps_ih, _⟩ := ih regs₂ hlen₂ hrin_₂
        have hgen_eq : regUnpairGen out1 9 rin regs₂ = regUnpairGen out1 9 rin regs := by
          unfold regUnpairGen
          have hout1_₂ : regs₂.getD out1 0 = 0 := by
            dsimp [regs₂]
            rw [getD_set_ne _ _ hne_1_9.symm, getD_set_self _ out1 0 (by simp; omega)]
          have hr9_₂ : regs₂.getD 9 0 = regs.getD out1 0 + 1 := by
            dsimp [regs₂]
            exact getD_set_self _ 9 (regs.getD out1 0 + 1) (by simp; omega)
          have hloop_step :
              unpairLoop (z + 1) (regs.getD out1 0, 0) = unpairLoop z (0, regs.getD out1 0 + 1) :=
            rfl
          rw [hrin_₂, hout1_₂, hr9_₂, hz, hy, hloop_step]
          dsimp only [regs₂]
          rw [set_comm_of_ne _ (regs.getD out1 0 + 1) 0 hne_in_9.symm,
            set_comm_of_ne (regs.set rin z) 0 0 hne_in_1.symm,
            List.set_set,
            set_comm_of_ne _ (regs.getD out1 0 + 1) _ hne_1_9.symm,
            List.set_set, List.set_set]
        rw [hgen_eq] at hsteps_ih
        have hchain1 := step_zfReg11NSteps hstep1 (step_zfReg11NSteps hstep2
          (step_zfReg11NSteps hstep3 hsteps_m))
        have hchain2 := zfReg11NSteps_bind_eq hchain1 (step_zfReg11NSteps hstep_jmp hsteps_ih)
        exact ⟨(sm + 3) + (s_ih + 1), by omega, hchain2, by simp [regUnpairGen, hlen]⟩
      · -- Case `regs.getD 9 0 = y + 1`
        have hstep3 := zfReg11Step_of_decnz_succ (regs := regs₁) hev11 (by rw [hr9_₁, hy])
        let regs₂ := regs₁.set 9 y
        have hstep_jmp := zfReg11Step_of_jump (regs := regs₂) hev1101
        have hlen₂ : regs₂.length = 11 := by simp [regs₂, regs₁, hlen]
        have hrin_₂ : regs₂.getD rin 0 = z := by
          dsimp [regs₂, regs₁]
          rw [getD_set_ne _ _ hne_in_9.symm, getD_set_ne _ _ hne_in_1.symm,
            getD_set_self regs rin z (by omega)]
        obtain ⟨s_ih, hs_ih, hsteps_ih, _⟩ := ih regs₂ hlen₂ hrin_₂
        have hgen_eq : regUnpairGen out1 9 rin regs₂ = regUnpairGen out1 9 rin regs := by
          unfold regUnpairGen
          have hout1_₂ : regs₂.getD out1 0 = regs.getD out1 0 + 1 := by
            dsimp [regs₂, regs₁]
            rw [getD_set_ne _ _ hne_1_9.symm,
              getD_set_self _ out1 (regs.getD out1 0 + 1) (by simp; omega)]
          have hr9_₂ : regs₂.getD 9 0 = y := by
            dsimp [regs₂, regs₁]
            exact getD_set_self _ 9 y (by simp; omega)
          have hloop_step :
              unpairLoop (z + 1) (regs.getD out1 0, y + 1) =
              unpairLoop z (regs.getD out1 0 + 1, y) := rfl
          rw [hrin_₂, hout1_₂, hr9_₂, hz, hy, hloop_step]
          dsimp only [regs₂, regs₁]
          rw [set_comm_of_ne _ y 0 hne_in_9.symm,
            set_comm_of_ne (regs.set rin z) (regs.getD out1 0 + 1) 0 hne_in_1.symm,
            List.set_set,
            set_comm_of_ne _ y _ hne_1_9.symm,
            List.set_set, List.set_set]
        rw [hgen_eq] at hsteps_ih
        have hchain := step_zfReg11NSteps hstep1 (step_zfReg11NSteps hstep2
          (step_zfReg11NSteps hstep3 (step_zfReg11NSteps hstep_jmp hsteps_ih)))
        exact ⟨s_ih + 4, by omega, hchain, by simp [regUnpairGen, hlen]⟩
  intro regs hlen
  exact hloop (regs.getD rin 0) regs hlen rfl

/-- `unpair(scratch1, scratch2, prooflist).0` (State `352`): unpairs `0` into `8` and `9`. -/
theorem subEval_352 : SubEval 352 (regUnpairGen 8 9 0) :=
  subEval_unpair 8 0 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl rfl (by decide) rfl (by decide) rfl subEval_409

/-- `unpair(scratch1, scratch2, wffstack).0` (State `353`): unpairs `3` into `8` and `9`. -/
theorem subEval_353 : SubEval 353 (regUnpairGen 8 9 3) :=
  subEval_unpair 8 3 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl rfl (by decide) rfl (by decide) rfl subEval_409

/-- `unpair(topwff, scratch2, wffstack).0` (State `354`): unpairs `3` into `2` and `9`. -/
theorem subEval_354 : SubEval 354 (regUnpairGen 2 9 3) :=
  subEval_unpair 2 3 (by decide) (by decide)
    (by decide) (by decide) (by decide)
    rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl (by decide) (by decide) rfl rfl
    rfl (by decide) rfl rfl (by decide) rfl (by decide) rfl subEval_427

/-! ## Section 3: Composite RPN Formula Subroutines -/

/-- Register-bank operation of `main().n_149.0` (State `310`). -/
def reg310Op (regs : List ℕ) : List ℕ :=
  let r := regUnpairGen 8 9 0 regs
  (r.set 9 0).set 0 (r.getD 0 0 + r.getD 9 0)

/-- `main().n_149.0` (State `310`): unpairs `prooflist` (`0`) into `scratch1` (`8`) and
`prooflist` (`0`) via `scratch2` (`9`). -/
theorem subEval_310 : SubEval 310 reg310Op := by
  unfold reg310Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_352 subEval_416

/-- Register-bank operation of `n_165.0` (State `328`). -/
def reg328Op (regs : List ℕ) : List ℕ :=
  let r := regUnpairGen 8 9 3 regs
  (r.set 9 0).set 3 (r.getD 3 0 + r.getD 9 0)

/-- `n_165.0` (State `328`): unpairs `wffstack` (`3`) into `scratch1` (`8`) and
`wffstack` (`3`) via `scratch2` (`9`). -/
theorem subEval_328 : SubEval 328 reg328Op := by
  unfold reg328Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_353 subEval_419

/-- Register-bank operation of `cons().1` (State `97`). -/
def reg97Op (regs : List ℕ) : List ℕ :=
  let r := regPairOp 9 8 2 regs
  (r.set 9 0).set 2 (r.getD 2 0 + r.getD 9 0)

/-- `cons().1` (State `97`): pairs `scratch1` (`8`) and `topwff` (`2`) into `topwff` (`2`)
via `scratch2` (`9`). -/
theorem subEval_97 : SubEval 97 reg97Op := by
  unfold reg97Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_333 subEval_418

/-- Register-bank operation of `cons()` (State `96`). -/
def regConsOp (regs : List ℕ) : List ℕ :=
  reg97Op (reg328Op regs)

/-- `cons().0` (State `96`): pops from `wffstack` (`3`) into `scratch1` (`8`) and pairs with
`topwff` (`2`). -/
theorem subEval_96 : SubEval 96 regConsOp := by
  unfold regConsOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_328 subEval_97

/-- Register-bank operation of `pushwff()` (State `343`). -/
def regPushwffOp (regs : List ℕ) : List ℕ :=
  let r := regPairOp 8 2 3 regs
  (r.set 8 0).set 3 (r.getD 3 0 + r.getD 8 0)

/-- `pushwff().0` (State `343`): pairs `topwff` (`2`) and `wffstack` (`3`) into `wffstack` (`3`)
and zeroes `topwff` (`2`). -/
theorem subEval_343 : SubEval 343 regPushwffOp := by
  unfold regPushwffOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_329 subEval_411

/-- Register-bank operation of `v_1_()` (State `358`). -/
def regV1Op (regs : List ℕ) : List ℕ :=
  let r := regPushwffOp regs
  r.set 2 (r.getD 2 0 + 1)

/-- `v_1_().0` (State `358`): `pushwff(); inc topwff`. -/
theorem subEval_358 : SubEval 358 regV1Op := by
  unfold regV1Op
  exact subEval_seq_inc (q₁ := 68) rfl (by decide) rfl (by decide) (by decide) rfl subEval_343

/-- Register-bank operation of `v_2_()` (State `359`). -/
def regV2Op (regs : List ℕ) : List ℕ :=
  let r := regV1Op regs
  r.set 2 (r.getD 2 0 + 1)

/-- `v_2_().0` (State `359`): `v_1_(); inc topwff`. -/
theorem subEval_359 : SubEval 359 regV2Op := by
  unfold regV2Op
  exact subEval_seq_inc (q₁ := 68) rfl (by decide) rfl (by decide) (by decide) rfl subEval_358

/-- Register-bank operation of `v_3_()` (State `360`). -/
def regV3Op (regs : List ℕ) : List ℕ :=
  let r := regV2Op regs
  r.set 2 (r.getD 2 0 + 1)

/-- `v_3_().0` (State `360`): `v_2_(); inc topwff`. -/
theorem subEval_360 : SubEval 360 regV3Op := by
  unfold regV3Op
  exact subEval_seq_inc (q₁ := 68) rfl (by decide) rfl (by decide) (by decide) rfl subEval_359

/-- Register-bank operation of `v_4_()` (State `361`). -/
def regV4Op (regs : List ℕ) : List ℕ :=
  let r := regV3Op regs
  r.set 2 (r.getD 2 0 + 1)

/-- `v_4_().0` (State `361`): `v_3_(); inc topwff`. -/
theorem subEval_361 : SubEval 361 regV4Op := by
  unfold regV4Op
  exact subEval_seq_inc (q₁ := 68) rfl (by decide) rfl (by decide) (by decide) rfl subEval_360

/-- Register-bank operation of `weq().1` (State `369`). -/
def reg369Op (regs : List ℕ) : List ℕ :=
  regConsOp (regPushwffOp regs)

/-- `weq().1` (State `369`): `pushwff(); cons()`. -/
theorem subEval_369 : SubEval 369 reg369Op := by
  unfold reg369Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_343 subEval_96

/-- Register-bank operation of `weq()` (State `368`). -/
def regWeqOp (regs : List ℕ) : List ℕ :=
  reg369Op (regConsOp regs)

/-- `weq().0` (State `368`): `cons(); pushwff(); cons()`. -/
theorem subEval_368 : SubEval 368 regWeqOp := by
  unfold regWeqOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_96 subEval_369

/-- Register-bank operation of `wel().1` (State `367`). -/
def reg367Op (regs : List ℕ) : List ℕ :=
  regConsOp (regV1Op regs)

/-- `wel().1` (State `367`): `v_1_(); cons()`. -/
theorem subEval_367 : SubEval 367 reg367Op := by
  unfold reg367Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_358 subEval_96

/-- Register-bank operation of `wel()` (State `366`). -/
def regWelOp (regs : List ℕ) : List ℕ :=
  reg367Op (regConsOp regs)

/-- `wel().0` (State `366`): `cons(); v_1_(); cons()`. -/
theorem subEval_366 : SubEval 366 regWelOp := by
  unfold regWelOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_96 subEval_367

/-- Register-bank operation of `wim().1` (State `430`). -/
def reg430Op (regs : List ℕ) : List ℕ :=
  regConsOp (regV2Op regs)

/-- `wim().1` (State `430`): `v_2_(); cons()`. -/
theorem subEval_430 : SubEval 430 reg430Op := by
  unfold reg430Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_359 subEval_96

/-- Register-bank operation of `wim()` (State `429`). -/
def regWimOp (regs : List ℕ) : List ℕ :=
  reg430Op (regConsOp regs)

/-- `wim().0` (State `429`): `cons(); v_2_(); cons()`. -/
theorem subEval_429 : SubEval 429 regWimOp := by
  unfold regWimOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_96 subEval_430

/-- Register-bank operation of `wn()` (State `431`). -/
def regWnOp (regs : List ℕ) : List ℕ :=
  regConsOp (regV3Op regs)

/-- `wn().0` (State `431`): `v_3_(); cons()`. -/
theorem subEval_431 : SubEval 431 regWnOp := by
  unfold regWnOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_360 subEval_96

/-- Register-bank operation of `wal().1` (State `365`). -/
def reg365Op (regs : List ℕ) : List ℕ :=
  regConsOp (regV4Op regs)

/-- `wal().1` (State `365`): `v_4_(); cons()`. -/
theorem subEval_365 : SubEval 365 reg365Op := by
  unfold reg365Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_361 subEval_96

/-- Register-bank operation of `wal()` (State `364`). -/
def regWalOp (regs : List ℕ) : List ℕ :=
  reg365Op (regConsOp regs)

/-- `wal().0` (State `364`): `cons(); v_4_(); cons()`. -/
theorem subEval_364 : SubEval 364 regWalOp := by
  unfold regWalOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_96 subEval_365

/-- Register-bank operation of `wex().1` (State `371`). -/
def reg371Op (regs : List ℕ) : List ℕ :=
  regWnOp (regWalOp regs)

/-- `wex().1` (State `371`): `wal(); wn()`. -/
theorem subEval_371 : SubEval 371 reg371Op := by
  unfold reg371Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_364 subEval_431

/-- Register-bank operation of `wex()` (State `370`). -/
def regWexOp (regs : List ℕ) : List ℕ :=
  reg371Op (regWnOp regs)

/-- `wex().0` (State `370`): `wn(); wal(); wn()`. -/
theorem subEval_370 : SubEval 370 regWexOp := by
  unfold regWexOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_431 subEval_371

/-- Register-bank operation of `wa().1` (State `363`). -/
def reg363Op (regs : List ℕ) : List ℕ :=
  regWnOp (regWimOp regs)

/-- `wa().1` (State `363`): `wim(); wn()`. -/
theorem subEval_363 : SubEval 363 reg363Op := by
  unfold reg363Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_429 subEval_431

/-- Register-bank operation of `wa()` (State `362`). -/
def regWaOp (regs : List ℕ) : List ℕ :=
  reg363Op (regWnOp regs)

/-- `wa().0` (State `362`): `wn(); wim(); wn()`. -/
theorem subEval_362 : SubEval 362 regWaOp := by
  unfold regWaOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_431 subEval_363

/-- Register-bank operation of `par1().1` (State `338`). -/
def reg338Op (regs : List ℕ) : List ℕ :=
  let r := ((regs.set 5 0).set 2 (regs.getD 2 0 + regs.getD 5 0)).set
    8 (regs.getD 8 0 + regs.getD 5 0)
  (r.set 8 0).set 5 (r.getD 5 0 + r.getD 8 0)

/-- `par1().1` (State `338`): copies `param1` (`5`) into `topwff` (`2`) via `scratch1` (`8`). -/
theorem subEval_338 : SubEval 338 reg338Op := by
  unfold reg338Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_387 subEval_403

/-- Register-bank operation of `par1()` (State `337`). -/
def regPar1Op (regs : List ℕ) : List ℕ :=
  reg338Op (regPushwffOp regs)

/-- `par1().0` (State `337`): `pushwff(); topwff = param1`. -/
theorem subEval_337 : SubEval 337 regPar1Op := by
  unfold regPar1Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_343 subEval_338

/-- Register-bank operation of `par2().1` (State `340`). -/
def reg340Op (regs : List ℕ) : List ℕ :=
  let r := ((regs.set 6 0).set 2 (regs.getD 2 0 + regs.getD 6 0)).set
    8 (regs.getD 8 0 + regs.getD 6 0)
  (r.set 8 0).set 6 (r.getD 6 0 + r.getD 8 0)

/-- `par2().1` (State `340`): copies `param2` (`6`) into `topwff` (`2`) via `scratch1` (`8`). -/
theorem subEval_340 : SubEval 340 reg340Op := by
  unfold reg340Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_393 subEval_405

/-- Register-bank operation of `par2()` (State `339`). -/
def regPar2Op (regs : List ℕ) : List ℕ :=
  reg340Op (regPushwffOp regs)

/-- `par2().0` (State `339`): `pushwff(); topwff = param2`. -/
theorem subEval_339 : SubEval 339 regPar2Op := by
  unfold regPar2Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_343 subEval_340

/-- Register-bank operation of `par3().1` (State `342`). -/
def reg342Op (regs : List ℕ) : List ℕ :=
  let r := ((regs.set 7 0).set 2 (regs.getD 2 0 + regs.getD 7 0)).set
    8 (regs.getD 8 0 + regs.getD 7 0)
  (r.set 8 0).set 7 (r.getD 7 0 + r.getD 8 0)

/-- `par3().1` (State `342`): copies `param3` (`7`) into `topwff` (`2`) via `scratch1` (`8`). -/
theorem subEval_342 : SubEval 342 reg342Op := by
  unfold reg342Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_396 subEval_407

/-- Register-bank operation of `par3()` (State `341`). -/
def regPar3Op (regs : List ℕ) : List ℕ :=
  reg342Op (regPushwffOp regs)

/-- `par3().0` (State `341`): `pushwff(); topwff = param3`. -/
theorem subEval_341 : SubEval 341 regPar3Op := by
  unfold regPar3Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_343 subEval_342

/-! ## Section 4: `WffState` Register-Bank Embedding & Simp Lemmas -/

/-- Embed `WffState` along with `(prooflist, nextproof)` into the 11-register bank with
zeroed scratch registers `8, 9, 10`. -/
def wffStateToRegs (pl np : ℕ) (s : WffState) : List ℕ :=
  [pl, np, s.topwff, s.wffstack, s.axiomcode, s.param1, s.param2, s.param3, 0, 0, 0]

@[simp]
theorem wffStateToRegs_length (pl np : ℕ) (s : WffState) :
    (wffStateToRegs pl np s).length = 11 := rfl

@[simp]
theorem regPushwffOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regPushwffOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnVk 0 s) := by
  simp [regPushwffOp, regPairOp, wffStateToRegs, rpnVk, pairLoop_eq_cantorPair]

@[simp]
theorem regV1Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regV1Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnVk 1 s) := by
  unfold regV1Op
  rw [regPushwffOp_wffStateToRegs]
  rfl

@[simp]
theorem regV2Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regV2Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnVk 2 s) := by
  unfold regV2Op
  rw [regV1Op_wffStateToRegs]
  rfl

@[simp]
theorem regV3Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regV3Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnVk 3 s) := by
  unfold regV3Op
  rw [regV2Op_wffStateToRegs]
  rfl

@[simp]
theorem regV4Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regV4Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnVk 4 s) := by
  unfold regV4Op
  rw [regV3Op_wffStateToRegs]
  rfl

@[simp]
theorem regConsOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regConsOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnCons s) := by
  simp [regConsOp, reg97Op, reg328Op, regUnpairGen, regPairOp, wffStateToRegs, rpnCons,
    unpairLoop_zero_zero, pairLoop_eq_cantorPair]

@[simp]
theorem reg369Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    reg369Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnCons (rpnVk 0 s)) := by
  simp [reg369Op]

@[simp]
theorem regWeqOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regWeqOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWeq s) := by
  simp [regWeqOp, rpnWeq]

@[simp]
theorem reg367Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    reg367Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnCons (rpnVk 1 s)) := by
  simp [reg367Op]

@[simp]
theorem regWelOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regWelOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWel s) := by
  simp [regWelOp, rpnWel]

@[simp]
theorem reg430Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    reg430Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnCons (rpnVk 2 s)) := by
  simp [reg430Op]

@[simp]
theorem regWimOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regWimOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWim s) := by
  simp [regWimOp, rpnWim]

@[simp]
theorem regWnOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regWnOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWn s) := by
  simp [regWnOp, rpnWn]

@[simp]
theorem reg365Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    reg365Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnCons (rpnVk 4 s)) := by
  simp [reg365Op]

@[simp]
theorem regWalOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regWalOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWal s) := by
  simp [regWalOp, rpnWal]

@[simp]
theorem reg371Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    reg371Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWn (rpnWal s)) := by
  simp [reg371Op]

@[simp]
theorem regWexOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regWexOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWex s) := by
  simp [regWexOp, rpnWex]

@[simp]
theorem reg363Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    reg363Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWn (rpnWim s)) := by
  simp [reg363Op]

@[simp]
theorem regWaOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regWaOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnWa s) := by
  simp [regWaOp, rpnWa]

@[simp]
theorem regPar1Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regPar1Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnPar1 s) := by
  unfold regPar1Op
  rw [regPushwffOp_wffStateToRegs]
  simp [reg338Op, wffStateToRegs, rpnVk, rpnPar1]

@[simp]
theorem regPar2Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regPar2Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnPar2 s) := by
  unfold regPar2Op
  rw [regPushwffOp_wffStateToRegs]
  simp [reg340Op, wffStateToRegs, rpnVk, rpnPar2]

@[simp]
theorem regPar3Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regPar3Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnPar3 s) := by
  unfold regPar3Op
  rw [regPushwffOp_wffStateToRegs]
  simp [reg342Op, wffStateToRegs, rpnVk, rpnPar3]

@[simp]
theorem reg310Op_eval (pl np top stk ac p1 p2 p3 s3 : ℕ) :
    reg310Op [pl, np, top, stk, ac, p1, p2, p3, 0, 0, s3] =
      [(cantorUnpair pl).2, np, top, stk, ac, p1, p2, p3, (cantorUnpair pl).1, 0, s3] := by
  simp [reg310Op, regUnpairGen, unpairLoop_zero_zero]

@[simp]
theorem reg328Op_eval (pl np top stk ac p1 p2 p3 s3 : ℕ) :
    reg328Op [pl, np, top, stk, ac, p1, p2, p3, 0, 0, s3] =
      [pl, np, top, (cantorUnpair stk).2, ac, p1, p2, p3, (cantorUnpair stk).1, 0, s3] := by
  simp [reg328Op, regUnpairGen, unpairLoop_zero_zero]

/-! ## Section 1: Generic Conditional Subroutine Combinator (`subEval_cond`) -/

/-- Generic conditional subroutine combinator: if `q` transitions on `0` to a condition-checker
node `q₀` (`96 ≤ q₀.val`) and on `1` to a `then`-branch `q₁` (`96 ≤ q₁.val`) with `SubEval q₁ f₁`,
and `q₀` at `P ++ [0]` either exits normally to `retStack (P ++ [0]) = P ++ [1]` when `cond regs`
holds or breaks 1 level to `(popBreakRev 1 (P ++ [0]).reverse).reverse = retStack P` when
`cond regs` is false, then `q` satisfies
`SubEval q (fun regs => if cond regs then f₁ (f₀ regs) else f₀ regs)`. -/
theorem subEval_cond {q q₀ q₁ : Fin 432} {cond : List ℕ → Prop} [DecidablePred cond]
    {f₀ f₁ : List ℕ → List ℕ}
    (htr0 : refTrans q 0 = some (0, .right, q₀)) (hq₀ : 96 ≤ q₀.val)
    (htr1 : refTrans q 1 = some (1, .right, q₁)) (hq₁ : 96 ≤ q₁.val)
    (h0 : ∀ (Q : List (Fin 2)), walkInternal 126 Q = some q₀ →
      ∀ (regs : List ℕ), regs.length = 11 →
        ∃ s ≥ 1,
          zfReg11NSteps s ⟨trimZeros Q, regs⟩ =
            some ⟨if cond regs then retStack Q else (popBreakRev 1 Q.reverse).reverse,
                  f₀ regs⟩ ∧
          (f₀ regs).length = 11)
    (h1 : SubEval q₁ f₁) :
    SubEval q (fun regs => if cond regs then f₁ (f₀ regs) else f₀ regs) := by
  intro P hP regs hlen
  have hP0 : walkInternal 126 (P ++ [0]) = some q₀ := walkInternal_snoc hP htr0 hq₀
  have hP1 : walkInternal 126 (P ++ [1]) = some q₁ := walkInternal_snoc hP htr1 hq₁
  obtain ⟨s₀, hs₀, hsteps₀, hlen₀⟩ := h0 (P ++ [0]) hP0 regs hlen
  have hbrk : (popBreakRev 1 (P ++ [0]).reverse).reverse = retStack P := by
    simp [retStack]
  rw [trimZeros_append_zero, retStack_append_zero, hbrk] at hsteps₀
  by_cases hc : cond regs
  · simp only [hc, ↓reduceIte] at hsteps₀ ⊢
    obtain ⟨s₁, hs₁, hsteps₁, hlen₁⟩ := h1 (P ++ [1]) hP1 (f₀ regs) hlen₀
    rw [trimZeros_append_one, retStack_append_one] at hsteps₁
    exact ⟨s₀ + s₁, by omega, zfReg11NSteps_bind_eq hsteps₀ hsteps₁, hlen₁⟩
  · simp only [hc, ↓reduceIte] at hsteps₀ ⊢
    exact ⟨s₀, hs₀, hsteps₀, hlen₀⟩

/-! ## Section 2: `if_not_decnz(prooflist, 72).0` (States `122..125`) -/

/-- `if_not_decnz(prooflist, 72).2` (State `125`): adds `scratch1` (`8`) into `nextproof` (`1`),
zeroes `8`, and increments `nextproof` (`1`). -/
theorem subEval_125 :
    SubEval 125 (fun regs =>
      (regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0 + 1)) := by
  refine (subEval_seq_inc rfl (by decide) rfl (by decide) (by decide) rfl subEval_401).congr ?_
  intro regs hlen
  change ((regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0)).set 1
    (((regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0)).getD 1 0 + 1) =
    (regs.set 8 0).set 1 (regs.getD 1 0 + regs.getD 8 0 + 1)
  rw [getD_set_self _ 1 _ (by simp [hlen]), List.set_set]

/-- `if_not_decnz(prooflist, 72).1` (State `124`): copies `nextproof` (`1`) to `prooflist` (`0`)
and increments `nextproof` (`1`) via `scratch1` (`8`). -/
def reg124Op (regs : List ℕ) : List ℕ :=
  let r := ((regs.set 1 0).set 8 (regs.getD 8 0 + regs.getD 1 0)).set 0
    (regs.getD 0 0 + regs.getD 1 0)
  (r.set 8 0).set 1 (r.getD 1 0 + r.getD 8 0 + 1)

theorem subEval_124 : SubEval 124 reg124Op := by
  unfold reg124Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_382 subEval_125

/-- `if_not_decnz(prooflist, 72).0` (State `122`): if `prooflist` (`0`) is `0`, reloads `prooflist`
from `nextproof` (`1`) and increments `nextproof` (`1`); otherwise decrements `prooflist` (`0`). -/
def reg122Op (regs : List ℕ) : List ℕ :=
  if regs.getD 0 0 = 0 then
    reg124Op regs
  else
    regs.set 0 (regs.getD 0 0 - 1)

theorem subEval_122 : SubEval 122 reg122Op := by
  intro P hP regs hlen
  unfold reg122Op
  have hP0 : walkInternal 126 (P ++ [0]) = some 123 :=
    walkInternal_snoc hP rfl (by decide)
  have hP1 : walkInternal 126 (P ++ [1]) = some 124 :=
    walkInternal_snoc hP rfl (by decide)
  have hev0 : evalStack (trimZeros P) = .decnz 0 (P ++ [0] ++ [1]) (P ++ [1]) := by
    rw [← trimZeros_append_zero P, evalStack_trimZeros_of_walkInternal hP0,
      evalStack_leaf0_of_walkInternal hP0 rfl (by decide) (by decide)]
    simp [isLeafInc, leafReg]
  rcases hv : regs.getD 0 0 with _ | v
  · -- Case `regs.getD 0 0 = 0`
    have hstep1 := zfReg11Step_of_decnz_zero hev0 hv
    obtain ⟨s, hs, hsteps, hlen'⟩ := subEval_124 (P ++ [1]) hP1 regs hlen
    rw [trimZeros_append_one, retStack_append_one] at hsteps
    exact ⟨s + 1, by omega, step_zfReg11NSteps hstep1 hsteps, hlen'⟩
  · -- Case `regs.getD 0 0 = v + 1`
    have hstep1 := zfReg11Step_of_decnz_succ hev0 hv
    have hev_brk : evalStack (P ++ [0] ++ [1]) = .jump (retStack P) := by
      have h := evalStack_break1_of_walkInternal (P := P ++ [0]) (k := 1) (by decide) hP0 rfl
      simpa [retStack] using h
    have hstep2 := zfReg11Step_of_jump (regs := regs.set 0 v) hev_brk
    exact ⟨2, by omega, step_zfReg11NSteps hstep1 (zfReg11Step_one hstep2), by simp [hlen]⟩

/-! ## Section 3: `if_decnz(axiomcode, 63).0` (`110..111`) & `select().0` (`344..347`) -/

/-- `if_decnz(axiomcode, 63).1` (State `111`): clears `topwff` (`2`) and moves `scratch1` (`8`)
into `topwff` (`2`). -/
theorem subEval_111 :
    SubEval 111 (fun regs => (regs.set 8 0).set 2 (regs.getD 8 0)) := by
  refine (subEval_seq rfl (by decide) rfl (by decide) subEval_421 subEval_410).congr ?_
  intro regs hlen
  have hget2 : (regs.set 2 0).getD 2 0 = 0 := getD_set_self regs 2 0 (by omega)
  have hget8 : (regs.set 2 0).getD 8 0 = regs.getD 8 0 := getD_set_ne regs 0 (by decide)
  rw [hget2, hget8, Nat.zero_add,
    set_comm_of_ne regs 0 0 (by decide), List.set_set]

/-- `if_decnz(axiomcode, 63).0` (State `110`): if `axiomcode` (`4`) is `0`, does nothing;
otherwise decrements `axiomcode` (`4`) and moves `scratch1` (`8`) into `topwff` (`2`). -/
def reg110Op (regs : List ℕ) : List ℕ :=
  if regs.getD 4 0 = 0 then
    regs
  else
    ((regs.set 4 (regs.getD 4 0 - 1)).set 8 0).set 2 (regs.getD 8 0)

theorem subEval_110 : SubEval 110 reg110Op := by
  intro P hP regs hlen
  unfold reg110Op
  have hP1 : walkInternal 126 (P ++ [1]) = some 111 :=
    walkInternal_snoc hP rfl (by decide)
  have hev0 : evalStack (trimZeros P) = .decnz 4 (P ++ [1]) (retStack P) := by
    rw [evalStack_trimZeros_of_walkInternal hP,
      evalStack_leaf0_of_walkInternal hP rfl (by decide) (by decide)]
    simp [isLeafInc, leafReg]
  rcases hv : regs.getD 4 0 with _ | v
  · -- Case `regs.getD 4 0 = 0`
    have hstep := zfReg11Step_of_decnz_zero hev0 hv
    exact ⟨1, le_refl 1, zfReg11Step_one hstep, hlen⟩
  · -- Case `regs.getD 4 0 = v + 1`
    have hstep1 := zfReg11Step_of_decnz_succ hev0 hv
    obtain ⟨s, hs, hsteps, hlen'⟩ :=
      subEval_111 (P ++ [1]) hP1 (regs.set 4 v) (by simp [hlen])
    rw [trimZeros_append_one, retStack_append_one] at hsteps
    dsimp only at hsteps hlen'
    have hget8 : (regs.set 4 v).getD 8 0 = regs.getD 8 0 := getD_set_ne regs v (by decide)
    rw [hget8] at hsteps hlen'
    exact ⟨s + 1, by omega, step_zfReg11NSteps hstep1 hsteps, hlen'⟩

/-- `select().3` (State `347`): runs `if_decnz(axiomcode, 63)` (`110`) followed by clearing
`scratch1` (`8`). -/
def reg347Op (regs : List ℕ) : List ℕ :=
  (reg110Op regs).set 8 0

theorem subEval_347 : SubEval 347 reg347Op := by
  unfold reg347Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_110 subEval_398

/-- `select().2` (State `346`): moves `scratch2` (`9`) into `wffstack` (`3`) and runs `347`. -/
def reg346Op (regs : List ℕ) : List ℕ :=
  reg347Op ((regs.set 9 0).set 3 (regs.getD 3 0 + regs.getD 9 0))

theorem subEval_346 : SubEval 346 reg346Op := by
  unfold reg346Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_419 subEval_347

/-- `select().1` (State `345`): unpairs `wffstack` (`3`) into `(topwff, scratch2)` via `354`
and runs `346`. -/
def reg345Op (f354 : List ℕ → List ℕ) (regs : List ℕ) : List ℕ :=
  reg346Op (f354 regs)

theorem subEval_345 {f354 : List ℕ → List ℕ} (h354 : SubEval 354 f354) :
    SubEval 345 (reg345Op f354) := by
  unfold reg345Op
  exact subEval_seq rfl (by decide) rfl (by decide) h354 subEval_346

/-- `select().0` (State `344`): moves `topwff` (`2`) into `scratch1` (`8`) and runs `345`. -/
def regSelectGenOp (f354 : List ℕ → List ℕ) (regs : List ℕ) : List ℕ :=
  reg345Op f354 ((regs.set 2 0).set 8 (regs.getD 8 0 + regs.getD 2 0))

theorem subEval_344 {f354 : List ℕ → List ℕ} (h354 : SubEval 354 f354) :
    SubEval 344 (regSelectGenOp f354) := by
  unfold regSelectGenOp
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_425 (subEval_345 h354)

/-! ## Section 4: `cparam().n_91.0` (`98..105`) and `cparam` (`106, 108`) -/

/-- `cparam().n_91.5` (State `103`): increments `axiomcode` (`4`) twice. -/
theorem subEval_103 :
    SubEval 103 (fun regs => regs.set 4 (regs.getD 4 0 + 2)) := by
  refine (subEval_inc_inc (q₀ := 50) (q₁ := 50)
    rfl (by decide) (by decide) rfl rfl (by decide) (by decide) rfl).congr ?_
  intro regs hlen
  change (regs.set 4 (regs.getD 4 0 + 1)).set 4
    ((regs.set 4 (regs.getD 4 0 + 1)).getD 4 0 + 1) = regs.set 4 (regs.getD 4 0 + 2)
  rw [getD_set_self regs 4 _ (by omega), List.set_set]

/-- `cparam().n_91.7` (State `105`): increments `axiomcode` (`4`) and then runs `328`
(`pop_to_scratch1`). -/
theorem subEval_105 {f328 : List ℕ → List ℕ} (h328 : SubEval 328 f328) :
    SubEval 105 (fun regs => f328 (regs.set 4 (regs.getD 4 0 + 1))) :=
  subEval_inc_seq (q₀ := 50) (q₁ := 328) rfl (by decide) (by decide) rfl rfl (by decide) h328

/-- `cparam().n_91.0` (State `98`): condition-checker for `axiomcode == 1`.
At call-stack prefix `Q` (`walkInternal 126 Q = some 98`):
- If `regs.getD 4 0 = 1`: restores `axiomcode = 1`, executes `328` (`f328 regs`), and exits
  normally to `retStack Q` (`= P ++ [1]` when `Q = P ++ [0]`).
- If `regs.getD 4 0 ≠ 1`: leaves `regs` unchanged and breaks 1 level to
  `(popBreakRev 1 Q.reverse).reverse` (`= retStack P` when `Q = P ++ [0]`). -/
theorem subEval_98 {f328 : List ℕ → List ℕ} (h328 : SubEval 328 f328)
    (Q : List (Fin 2)) (hQ : walkInternal 126 Q = some 98)
    (regs : List ℕ) (hlen : regs.length = 11) :
    ∃ s ≥ 1,
      zfReg11NSteps s ⟨trimZeros Q, regs⟩ =
        some ⟨if regs.getD 4 0 = 1 then retStack Q else (popBreakRev 1 Q.reverse).reverse,
              if regs.getD 4 0 = 1 then f328 regs else regs⟩ ∧
      (if regs.getD 4 0 = 1 then f328 regs else regs).length = 11 := by
  have hQ0 : walkInternal 126 (Q ++ [0]) = some 99 :=
    walkInternal_snoc hQ rfl (by decide)
  have hQ01 : walkInternal 126 (Q ++ [0] ++ [1]) = some 100 :=
    walkInternal_snoc hQ0 rfl (by decide)
  have hQ010 : walkInternal 126 (Q ++ [0] ++ [1] ++ [0]) = some 101 :=
    walkInternal_snoc hQ01 rfl (by decide)
  have hQ0101 : walkInternal 126 (Q ++ [0] ++ [1] ++ [0] ++ [1]) = some 102 :=
    walkInternal_snoc hQ010 rfl (by decide)
  have hQ01010 : walkInternal 126 (Q ++ [0] ++ [1] ++ [0] ++ [1] ++ [0]) = some 103 :=
    walkInternal_snoc hQ0101 rfl (by decide)
  have hQ011 : walkInternal 126 (Q ++ [0] ++ [1] ++ [1]) = some 104 :=
    walkInternal_snoc hQ01 rfl (by decide)
  have hQ0110 : walkInternal 126 (Q ++ [0] ++ [1] ++ [1] ++ [0]) = some 105 :=
    walkInternal_snoc hQ011 rfl (by decide)
  have hev99 : evalStack (trimZeros Q) = .decnz 4 (Q ++ [0] ++ [1]) (Q ++ [1]) := by
    rw [← trimZeros_append_zero Q, evalStack_trimZeros_of_walkInternal hQ0,
      evalStack_leaf0_of_walkInternal hQ0 rfl (by decide) (by decide)]
    simp [isLeafInc, leafReg]
  have hev98_brk : evalStack (Q ++ [1]) = .jump (popBreakRev 1 Q.reverse).reverse :=
    evalStack_break1_of_walkInternal (k := 1) (by decide) hQ rfl
  have hev101 : evalStack (Q ++ [0] ++ [1]) =
      .decnz 4 (Q ++ [0] ++ [1] ++ [0] ++ [1]) (Q ++ [0] ++ [1] ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hQ010 rfl (by decide) (by decide)
    rw [← evalStack_trimZeros_of_walkInternal hQ010, trimZeros_append_zero,
      trimZeros_append_one, retStack_append_zero] at h
    exact h
  rcases hv : regs.getD 4 0 with _ | _ | v
  · -- Case `regs.getD 4 0 = 0`
    simp only [Nat.zero_ne_one, ↓reduceIte]
    have hstep1 := zfReg11Step_of_decnz_zero hev99 hv
    have hstep2 := zfReg11Step_of_jump (regs := regs) hev98_brk
    exact ⟨2, by omega, step_zfReg11NSteps hstep1 (zfReg11Step_one hstep2), hlen⟩
  · -- Case `regs.getD 4 0 = 1`
    simp only [↓reduceIte]
    have hstep1 := zfReg11Step_of_decnz_succ hev99 hv
    have hv0 : (regs.set 4 0).getD 4 0 = 0 := getD_set_self regs 4 0 (by omega)
    have hstep2 := zfReg11Step_of_decnz_zero hev101 hv0
    obtain ⟨s, hs, hsteps_105, hlen_105⟩ :=
      subEval_105 h328 (Q ++ [0] ++ [1] ++ [1] ++ [0]) hQ0110 (regs.set 4 0) (by simp [hlen])
    rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps_105
    dsimp only [leafReg] at hsteps_105 hlen_105
    have hrestore : (regs.set 4 0).set 4 ((regs.set 4 0).getD 4 0 + 1) = regs := by
      rw [hv0, List.set_set, set_eq_self_of_getD_eq hv]
    rw [hrestore] at hsteps_105 hlen_105
    have hev104_brk : evalStack (Q ++ [0] ++ [1] ++ [1] ++ [1]) = .jump (retStack Q) := by
      have h := evalStack_break1_of_walkInternal (P := Q ++ [0] ++ [1] ++ [1])
        (k := 1) (by decide) hQ011 rfl
      simpa [retStack] using h
    have hstep4 := zfReg11Step_of_jump (regs := f328 regs) hev104_brk
    have hchain := step_zfReg11NSteps hstep1
      (step_zfReg11NSteps hstep2 (zfReg11NSteps_bind_eq hsteps_105 (zfReg11Step_one hstep4)))
    exact ⟨s + 1 + 2, by omega, hchain, hlen_105⟩
  · -- Case `regs.getD 4 0 = v + 2`
    have hne : v + 1 + 1 ≠ 1 := by omega
    simp only [hne, ↓reduceIte]
    have hstep1 := zfReg11Step_of_decnz_succ hev99 hv
    have hv1 : (regs.set 4 (v + 1)).getD 4 0 = v + 1 := getD_set_self regs 4 (v + 1) (by omega)
    have hstep2 := zfReg11Step_of_decnz_succ hev101 hv1
    rw [List.set_set] at hstep2
    obtain ⟨s, hs, hsteps_103, _⟩ :=
      subEval_103 (Q ++ [0] ++ [1] ++ [0] ++ [1] ++ [0]) hQ01010 (regs.set 4 v) (by simp [hlen])
    rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps_103
    dsimp only at hsteps_103
    have hrestore : (regs.set 4 v).set 4 ((regs.set 4 v).getD 4 0 + 2) = regs := by
      rw [getD_set_self regs 4 v (by omega), List.set_set, set_eq_self_of_getD_eq hv]
    rw [hrestore] at hsteps_103
    have hev102_brk : evalStack (Q ++ [0] ++ [1] ++ [0] ++ [1] ++ [1]) = .jump (Q ++ [1]) := by
      have h := evalStack_break1_of_walkInternal (P := Q ++ [0] ++ [1] ++ [0] ++ [1])
        (k := 1) (by decide) hQ0101 rfl
      simpa using h
    have hstep4 := zfReg11Step_of_jump (regs := regs) hev102_brk
    have hstep5 := zfReg11Step_of_jump (regs := regs) hev98_brk
    have hchain := step_zfReg11NSteps hstep1
      (step_zfReg11NSteps hstep2
        (zfReg11NSteps_bind_eq hsteps_103 (step_zfReg11NSteps hstep4 (zfReg11Step_one hstep5))))
    exact ⟨s + 2 + 2, by omega, hchain, hlen⟩

/-- `cparam(param2).1` (State `107`): clears `param2` (`6`) and moves `scratch1` (`8`) into
`param2` (`6`). -/
theorem subEval_107 :
    SubEval 107 (fun regs => (regs.set 8 0).set 6 (regs.getD 8 0)) := by
  refine (subEval_seq rfl (by decide) rfl (by decide) subEval_391 subEval_405).congr ?_
  intro regs hlen
  have hget6 : (regs.set 6 0).getD 6 0 = 0 := getD_set_self regs 6 0 (by omega)
  have hget8 : (regs.set 6 0).getD 8 0 = regs.getD 8 0 := getD_set_ne regs 0 (by decide)
  rw [hget6, hget8, Nat.zero_add,
    set_comm_of_ne regs 0 0 (by decide), List.set_set]

/-- `cparam(param2).0` (State `106`): if `axiomcode == 1`, runs `328` (`pop_to_scratch1`) and
moves `scratch1` (`8`) into `param2` (`6`); otherwise leaves `regs` unchanged. -/
theorem subEval_106 {f328 : List ℕ → List ℕ} (h328 : SubEval 328 f328) :
    SubEval 106 (fun regs =>
      if regs.getD 4 0 = 1 then
        let r := f328 regs
        (r.set 8 0).set 6 (r.getD 8 0)
      else
        regs) := by
  refine (subEval_cond (cond := fun regs => regs.getD 4 0 = 1)
    rfl (by decide) rfl (by decide) (subEval_98 h328) subEval_107).congr ?_
  intro regs _hlen
  split_ifs <;> rfl

/-- `cparam(param3).1` (State `109`): clears `param3` (`7`) and moves `scratch1` (`8`) into
`param3` (`7`). -/
theorem subEval_109 :
    SubEval 109 (fun regs => (regs.set 8 0).set 7 (regs.getD 8 0)) := by
  refine (subEval_seq rfl (by decide) rfl (by decide) subEval_395 subEval_407).congr ?_
  intro regs hlen
  have hget7 : (regs.set 7 0).getD 7 0 = 0 := getD_set_self regs 7 0 (by omega)
  have hget8 : (regs.set 7 0).getD 8 0 = regs.getD 8 0 := getD_set_ne regs 0 (by decide)
  rw [hget7, hget8, Nat.zero_add,
    set_comm_of_ne regs 0 0 (by decide), List.set_set]

/-- `cparam(param3).0` (State `108`): if `axiomcode == 1`, runs `328` (`pop_to_scratch1`) and
moves `scratch1` (`8`) into `param3` (`7`); otherwise leaves `regs` unchanged. -/
theorem subEval_108 {f328 : List ℕ → List ℕ} (h328 : SubEval 328 f328) :
    SubEval 108 (fun regs =>
      if regs.getD 4 0 = 1 then
        let r := f328 regs
        (r.set 8 0).set 7 (r.getD 8 0)
      else
        regs) := by
  refine (subEval_cond (cond := fun regs => regs.getD 4 0 = 1)
    rfl (by decide) rfl (by decide) (subEval_98 h328) subEval_109).congr ?_
  intro regs _hlen
  split_ifs <;> rfl

/-! ## Section 5: `if_eq().n_111.0` (States `112..118`), `119`, `121`, and `298` -/

/-- `if_eq().n_111.0` (State `112`): equality comparison loop on `scratch2` (`9`) and
`scratch3` (`10`).
At call-stack prefix `Q` (`walkInternal 126 Q = some 112`):
- Always zeroes both `scratch2` (`9`) and `scratch3` (`10`).
- If `regs.getD 9 0 = regs.getD 10 0`: exits normally to `retStack Q`
  (`= P ++ [1]` when `Q = P ++ [0]`).
- If `regs.getD 9 0 ≠ regs.getD 10 0`: breaks 1 level out of `Q` to
  `(popBreakRev 1 Q.reverse).reverse` (`= retStack P` when `Q = P ++ [0]`). -/
theorem subEval_112 (Q : List (Fin 2)) (hQ : walkInternal 126 Q = some 112) :
    ∀ (regs : List ℕ), regs.length = 11 →
      ∃ s ≥ 1,
        zfReg11NSteps s ⟨trimZeros Q, regs⟩ =
          some ⟨if regs.getD 9 0 = regs.getD 10 0 then retStack Q
                else (popBreakRev 1 Q.reverse).reverse,
                (regs.set 9 0).set 10 0⟩ ∧
        ((regs.set 9 0).set 10 0).length = 11 := by
  have hQ0 : walkInternal 126 (Q ++ [0]) = some 113 :=
    walkInternal_snoc hQ rfl (by decide)
  have hQ01 : walkInternal 126 (Q ++ [0] ++ [1]) = some 114 :=
    walkInternal_snoc hQ0 rfl (by decide)
  have hQ010 : walkInternal 126 (Q ++ [0] ++ [1] ++ [0]) = some 115 :=
    walkInternal_snoc hQ01 rfl (by decide)
  have hQ011 : walkInternal 126 (Q ++ [0] ++ [1] ++ [1]) = some 116 :=
    walkInternal_snoc hQ01 rfl (by decide)
  have hQ0110 : walkInternal 126 (Q ++ [0] ++ [1] ++ [1] ++ [0]) = some 415 :=
    walkInternal_snoc hQ011 rfl (by decide)
  have hQ1 : walkInternal 126 (Q ++ [1]) = some 117 :=
    walkInternal_snoc hQ rfl (by decide)
  have hQ11 : walkInternal 126 (Q ++ [1] ++ [1]) = some 118 :=
    walkInternal_snoc hQ1 rfl (by decide)
  have hQ110 : walkInternal 126 (Q ++ [1] ++ [1] ++ [0]) = some 420 :=
    walkInternal_snoc hQ11 rfl (by decide)
  have hev113 : evalStack (trimZeros Q) = .decnz 9 (Q ++ [0] ++ [1]) (Q ++ [1]) := by
    rw [← trimZeros_append_zero Q, evalStack_trimZeros_of_walkInternal hQ0,
      evalStack_leaf0_of_walkInternal hQ0 rfl (by decide) (by decide)]
    simp [isLeafInc, leafReg]
  have hev115 : evalStack (Q ++ [0] ++ [1]) =
      .decnz 10 (Q ++ [0] ++ [1] ++ [0] ++ [1]) (Q ++ [0] ++ [1] ++ [1]) := by
    have h := evalStack_leaf0_of_walkInternal hQ010 rfl (by decide) (by decide)
    rw [← evalStack_trimZeros_of_walkInternal hQ010, trimZeros_append_zero,
      trimZeros_append_one, retStack_append_zero] at h
    exact h
  have hev115_cont : evalStack (Q ++ [0] ++ [1] ++ [0] ++ [1]) = .jump (trimZeros Q) := by
    have h := evalStack_continue1_of_walkInternal (P := Q ++ [0] ++ [1] ++ [0])
      (k := 1) (by decide) hQ010 rfl
    simpa [popContinueRev_zero_eq_dropLeadingZeros, trimZeros] using h
  have hev116_brk : evalStack (Q ++ [0] ++ [1] ++ [1] ++ [1]) =
      .jump (popBreakRev 1 Q.reverse).reverse := by
    have h := evalStack_break1_of_walkInternal (P := Q ++ [0] ++ [1] ++ [1])
      (k := 2) (by decide) hQ011 rfl
    simpa using h
  have hev117 : evalStack (Q ++ [1]) = .decnz 10 (Q ++ [1] ++ [1]) (retStack Q) := by
    have h := evalStack_leaf0_of_walkInternal hQ1 rfl (by decide) (by decide)
    simpa [isLeafInc, leafReg] using h
  have hev118_brk : evalStack (Q ++ [1] ++ [1] ++ [1]) =
      .jump (popBreakRev 1 Q.reverse).reverse := by
    have h := evalStack_break1_of_walkInternal (P := Q ++ [1] ++ [1])
      (k := 1) (by decide) hQ11 rfl
    simpa using h
  have hloop : ∀ (v : ℕ) (regs : List ℕ), regs.length = 11 → regs.getD 9 0 = v →
      ∃ s ≥ 1,
        zfReg11NSteps s ⟨trimZeros Q, regs⟩ =
          some ⟨if v = regs.getD 10 0 then retStack Q
                else (popBreakRev 1 Q.reverse).reverse,
                (regs.set 9 0).set 10 0⟩ ∧
        ((regs.set 9 0).set 10 0).length = 11 := by
    intro v
    induction v with
    | zero =>
      intro regs hlen hv
      have hstep1 := zfReg11Step_of_decnz_zero hev113 hv
      rcases hw : regs.getD 10 0 with _ | w
      · -- `v = 0` and `regs.getD 10 0 = 0`
        simp only [↓reduceIte]
        have hstep2 := zfReg11Step_of_decnz_zero hev117 hw
        have hset : (regs.set 9 0).set 10 0 = regs := by
          rw [set_eq_self_of_getD_eq hv, set_eq_self_of_getD_eq hw]
        rw [hset]
        exact ⟨2, by omega, step_zfReg11NSteps hstep1 (zfReg11Step_one hstep2), hlen⟩
      · -- `v = 0` and `regs.getD 10 0 = w + 1`
        have hne : 0 ≠ w + 1 := by omega
        simp only [hne, ↓reduceIte]
        have hstep2 := zfReg11Step_of_decnz_succ hev117 hw
        obtain ⟨s, hs, hsteps_420, _⟩ :=
          subEval_420 (Q ++ [1] ++ [1] ++ [0]) hQ110 (regs.set 10 w) (by simp [hlen])
        rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps_420
        dsimp only at hsteps_420
        rw [List.set_set] at hsteps_420
        have hstep4 := zfReg11Step_of_jump (regs := regs.set 10 0) hev118_brk
        have hset9 : (regs.set 9 0).set 10 0 = regs.set 10 0 := by
          rw [set_eq_self_of_getD_eq hv]
        rw [hset9]
        have hchain := step_zfReg11NSteps hstep1
          (step_zfReg11NSteps hstep2 (zfReg11NSteps_bind_eq hsteps_420 (zfReg11Step_one hstep4)))
        exact ⟨s + 1 + 2, by omega, hchain, by simp [hlen]⟩
    | succ v ih =>
      intro regs hlen hv
      have hstep1 := zfReg11Step_of_decnz_succ hev113 hv
      rcases hw : regs.getD 10 0 with _ | w
      · -- `regs.getD 9 0 = v + 1` and `regs.getD 10 0 = 0`
        have hne : v + 1 ≠ 0 := by omega
        simp only [hne, ↓reduceIte]
        have hw' : (regs.set 9 v).getD 10 0 = 0 := by
          rw [getD_set_ne _ _ (by decide), hw]
        have hstep2 := zfReg11Step_of_decnz_zero hev115 hw'
        obtain ⟨s, hs, hsteps_415, _⟩ :=
          subEval_415 (Q ++ [0] ++ [1] ++ [1] ++ [0]) hQ0110 (regs.set 9 v) (by simp [hlen])
        rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps_415
        dsimp only at hsteps_415
        rw [List.set_set] at hsteps_415
        have hstep4 := zfReg11Step_of_jump (regs := regs.set 9 0) hev116_brk
        have hset10 : (regs.set 9 0).set 10 0 = regs.set 9 0 := by
          have hw0 : (regs.set 9 0).getD 10 0 = 0 := by
            rw [getD_set_ne _ _ (by decide), hw]
          exact set_eq_self_of_getD_eq hw0
        rw [hset10]
        have hchain := step_zfReg11NSteps hstep1
          (step_zfReg11NSteps hstep2 (zfReg11NSteps_bind_eq hsteps_415 (zfReg11Step_one hstep4)))
        exact ⟨s + 1 + 2, by omega, hchain, by simp [hlen]⟩
      · -- `regs.getD 9 0 = v + 1` and `regs.getD 10 0 = w + 1`
        have hw' : (regs.set 9 v).getD 10 0 = w + 1 := by
          rw [getD_set_ne _ _ (by decide), hw]
        have hstep2 := zfReg11Step_of_decnz_succ hev115 hw'
        let regs₁ := (regs.set 9 v).set 10 w
        have hstep3 := zfReg11Step_of_jump (regs := regs₁) hev115_cont
        have hlen₁ : regs₁.length = 11 := by simp [regs₁, hlen]
        have hv₁ : regs₁.getD 9 0 = v := by
          dsimp only [regs₁]
          rw [getD_set_ne _ _ (by decide), getD_set_self regs 9 v (by omega)]
        have hw₁ : regs₁.getD 10 0 = w := by
          dsimp only [regs₁]
          exact getD_set_self (regs.set 9 v) 10 w (by simp [hlen])
        obtain ⟨s, hs, hsteps_ih, _⟩ := ih regs₁ hlen₁ hv₁
        have hset_eq : (regs₁.set 9 0).set 10 0 = (regs.set 9 0).set 10 0 := by
          dsimp only [regs₁]
          rw [set_comm_of_ne (regs.set 9 v) w 0 (by decide), List.set_set, List.set_set]
        have heq_iff : (v = w) ↔ (v + 1 = w + 1) := by omega
        rw [hw₁, hset_eq] at hsteps_ih
        have hcond_eq : (if v = w then retStack Q else (popBreakRev 1 Q.reverse).reverse) =
            (if v + 1 = w + 1 then retStack Q else (popBreakRev 1 Q.reverse).reverse) := by
          simp only [heq_iff]
        rw [hcond_eq] at hsteps_ih
        have hchain := step_zfReg11NSteps hstep1
          (step_zfReg11NSteps hstep2 (step_zfReg11NSteps hstep3 hsteps_ih))
        exact ⟨s + 3, by omega, hchain, by simp [hlen]⟩
  intro regs hlen
  exact hloop (regs.getD 9 0) regs hlen rfl

/-- `if_eq(scratch2, scratch3, 102).1` (State `120`): adds `param1` (`5`) into `topwff` (`2`)
while preserving `param1` (`5`) via `scratch1` (`8`). -/
def reg120Op (regs : List ℕ) : List ℕ :=
  let r := ((regs.set 5 0).set 8 (regs.getD 8 0 + regs.getD 5 0)).set 2
    (regs.getD 2 0 + regs.getD 5 0)
  (r.set 8 0).set 5 (r.getD 5 0 + r.getD 8 0)

theorem subEval_120 : SubEval 120 reg120Op := by
  unfold reg120Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_388 subEval_403

/-- `if_eq(scratch2, scratch3, 102).0` (State `119`): compares `scratch2` (`9`) and
`scratch3` (`10`),
zeroing both; if equal, adds `param1` (`5`) into `topwff` (`2`) via `120`. -/
def reg119Op (regs : List ℕ) : List ℕ :=
  if regs.getD 9 0 = regs.getD 10 0 then
    reg120Op ((regs.set 9 0).set 10 0)
  else
    (regs.set 9 0).set 10 0

theorem subEval_119 : SubEval 119 reg119Op :=
  subEval_cond (cond := fun regs => regs.getD 9 0 = regs.getD 10 0)
    rfl (by decide) rfl (by decide) subEval_112 subEval_120

/-- `if_eq(scratch2, scratch3, 61).0` (State `121`): compares `scratch2` (`9`) and
`scratch3` (`10`),
zeroing both; if equal, clears `topwff` (`2`) to `0`. -/
def reg121Op (regs : List ℕ) : List ℕ :=
  if regs.getD 9 0 = regs.getD 10 0 then
    ((regs.set 9 0).set 10 0).set 2 0
  else
    (regs.set 9 0).set 10 0

theorem subEval_121 : SubEval 121 reg121Op :=
  subEval_cond (cond := fun regs => regs.getD 9 0 = regs.getD 10 0)
    rfl (by decide) rfl (by decide) subEval_112 subEval_421

/-- `main().n_140.1` (State `299`): moves `scratch1` (`8`) into `param1` (`5`) and runs `121`. -/
def reg299Op (regs : List ℕ) : List ℕ :=
  reg121Op ((regs.set 8 0).set 5 (regs.getD 5 0 + regs.getD 8 0))

theorem subEval_299 : SubEval 299 reg299Op := by
  unfold reg299Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_403 subEval_121

/-- `main().n_140.0` (State `298`): copies `param3` (`7`) into `scratch1` (`8`) and
`scratch3` (`10`)
(zeroing `7`), moves `scratch1` (`8`) into `param1` (`5`), and compares `scratch2` (`9`) with
`scratch3` (`10`), clearing `topwff` (`2`) if equal. -/
def reg298Op (regs : List ℕ) : List ℕ :=
  reg299Op (((regs.set 7 0).set 8 (regs.getD 8 0 + regs.getD 7 0)).set 10
    (regs.getD 10 0 + regs.getD 7 0))

theorem subEval_298 : SubEval 298 reg298Op := by
  unfold reg298Op
  exact subEval_seq rfl (by decide) rfl (by decide) subEval_397 subEval_299

/-- Concrete `select()` operation on the 11-register bank. -/
def regSelectOp (regs : List ℕ) : List ℕ :=
  regSelectGenOp (regUnpairGen 2 9 3) regs

theorem subEval_344_inst : SubEval 344 regSelectOp :=
  subEval_344 subEval_354

/-- Concrete `cparam(param2)` operation on the 11-register bank. -/
def regCparam2Op (regs : List ℕ) : List ℕ :=
  if regs.getD 4 0 = 1 then
    let r := reg328Op regs
    (r.set 8 0).set 6 (r.getD 8 0)
  else
    regs

theorem subEval_106_inst : SubEval 106 regCparam2Op :=
  subEval_106 subEval_328

/-- Concrete `cparam(param3)` operation on the 11-register bank. -/
def regCparam3Op (regs : List ℕ) : List ℕ :=
  if regs.getD 4 0 = 1 then
    let r := reg328Op regs
    (r.set 8 0).set 7 (r.getD 8 0)
  else
    regs

theorem subEval_108_inst : SubEval 108 regCparam3Op :=
  subEval_108 subEval_328

@[simp]
theorem regSelectOp_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regSelectOp (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnSelect s) := by
  unfold regSelectOp regSelectGenOp reg345Op reg346Op reg347Op reg110Op regUnpairGen
    wffStateToRegs rpnSelect
  simp only [List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.set_cons_zero, List.set_cons_succ, Nat.zero_add, unpairLoop_zero_zero]
  rcases s.axiomcode with _ | ac <;> rfl

@[simp]
theorem regCparam2Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regCparam2Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnCparam2 s) := by
  unfold regCparam2Op wffStateToRegs rpnCparam2
  change (if s.axiomcode = 1 then
    let r := reg328Op
      [pl, np, s.topwff, s.wffstack, s.axiomcode, s.param1, s.param2, s.param3, 0, 0, 0]
    (r.set 8 0).set 6 (r.getD 8 0)
  else [pl, np, s.topwff, s.wffstack, s.axiomcode, s.param1, s.param2, s.param3, 0, 0, 0]) = _
  rw [reg328Op_eval]
  split_ifs <;> rfl

@[simp]
theorem regCparam3Op_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regCparam3Op (wffStateToRegs pl np s) = wffStateToRegs pl np (rpnCparam3 s) := by
  unfold regCparam3Op wffStateToRegs rpnCparam3
  change (if s.axiomcode = 1 then
    let r := reg328Op
      [pl, np, s.topwff, s.wffstack, s.axiomcode, s.param1, s.param2, s.param3, 0, 0, 0]
    (r.set 8 0).set 7 (r.getD 8 0)
  else [pl, np, s.topwff, s.wffstack, s.axiomcode, s.param1, s.param2, s.param3, 0, 0, 0]) = _
  rw [reg328Op_eval]
  split_ifs <;> rfl


set_option maxRecDepth 200000

/-! ## 1. Generic Spine-Step Combinators & Spine Walk Lemmas (`k = 0..134`) -/

/-- Generic spine-step lemma: if `main().k` (`walkInternal 126 (List.replicate k 1) = some q_k`)
transitions on `0` to subroutine node `q_sub` (`96 ≤ q_sub.val`) with `SubEval q_sub f`, then
starting from `⟨List.replicate k 1, regs⟩` reaches `⟨List.replicate (k + 1) 1, f regs⟩` in
`s ≥ 1` steps of `zfReg11Step`. -/
theorem spine_step_of_subEval {k : ℕ} {q_k q_sub : Fin 432} {f : List ℕ → List ℕ}
    (hwalk : walkInternal 126 (List.replicate k 1) = some q_k)
    (htr0 : refTrans q_k 0 = some (0, .right, q_sub))
    (hq_sub : 96 ≤ q_sub.val)
    (hsub : SubEval q_sub f)
    (regs : List ℕ) (hlen : regs.length = 11) :
    ∃ s ≥ 1, zfReg11NSteps s ⟨List.replicate k 1, regs⟩ =
      some ⟨List.replicate (k + 1) 1, f regs⟩ ∧ (f regs).length = 11 := by
  have hwalk0 : walkInternal 126 (List.replicate k 1 ++ [0]) = some q_sub :=
    walkInternal_snoc hwalk htr0 hq_sub
  obtain ⟨s, hs, hsteps, hflen⟩ := hsub (List.replicate k 1 ++ [0]) hwalk0 regs hlen
  rw [trimZeros_append_zero, trimZeros_replicate_one, retStack_append_zero,
    ← List.replicate_succ'] at hsteps
  exact ⟨s, hs, hsteps, hflen⟩

/-- Register-level spine segment evaluation from `List.replicate k₁ 1` to `List.replicate k₂ 1`. -/
def RegSpineEval (k₁ k₂ : ℕ) (f : List ℕ → List ℕ) : Prop :=
  ∀ (regs : List ℕ), regs.length = 11 →
    ∃ s ≥ 1, zfReg11NSteps s ⟨List.replicate k₁ 1, regs⟩ =
      some ⟨List.replicate k₂ 1, f regs⟩ ∧ (f regs).length = 11

theorem regSpineEval_step {k k' : ℕ} {q_k q_sub : Fin 432} {f : List ℕ → List ℕ}
    (hwalk : walkInternal 126 (List.replicate k 1) = some q_k)
    (htr0 : refTrans q_k 0 = some (0, .right, q_sub))
    (hq_sub : 96 ≤ q_sub.val)
    (hsub : SubEval q_sub f)
    (hk : k + 1 = k' := by rfl) :
    RegSpineEval k k' f := by
  subst hk
  exact spine_step_of_subEval hwalk htr0 hq_sub hsub

theorem regSpineEval_trans {k₁ k₂ k₃ : ℕ} {f₁ f₂ f : List ℕ → List ℕ}
    (h1 : RegSpineEval k₁ k₂ f₁) (h2 : RegSpineEval k₂ k₃ f₂)
    (heq : (fun regs => f₂ (f₁ regs)) = f := by rfl) :
    RegSpineEval k₁ k₃ f := by
  subst heq
  intro regs hlen
  obtain ⟨s₁, hs₁, hsteps₁, hlen₁⟩ := h1 regs hlen
  obtain ⟨s₂, hs₂, hsteps₂, hlen₂⟩ := h2 (f₁ regs) hlen₁
  exact ⟨s₁ + s₂, by omega, zfReg11NSteps_bind_eq hsteps₁ hsteps₂, hlen₂⟩

theorem walkInternal_spine_succ {k : ℕ} {q_k q_next : Fin 432}
    (hk : walkInternal 126 (List.replicate k 1) = some q_k)
    (htr1 : refTrans q_k 1 = some (1, .right, q_next))
    (hq_next : 96 ≤ q_next.val) :
    walkInternal 126 (List.replicate (k + 1) 1) = some q_next := by
  rw [List.replicate_succ']
  exact walkInternal_snoc hk htr1 hq_next

theorem walkInternal_spine_0 : walkInternal 126 (List.replicate 0 1) = some 126 := rfl
theorem walkInternal_spine_1 : walkInternal 126 (List.replicate 1 1) = some 127 :=
  walkInternal_spine_succ walkInternal_spine_0 rfl (by decide)
theorem walkInternal_spine_2 : walkInternal 126 (List.replicate 2 1) = some 176 :=
  walkInternal_spine_succ walkInternal_spine_1 rfl (by decide)
theorem walkInternal_spine_3 : walkInternal 126 (List.replicate 3 1) = some 187 :=
  walkInternal_spine_succ walkInternal_spine_2 rfl (by decide)
theorem walkInternal_spine_4 : walkInternal 126 (List.replicate 4 1) = some 198 :=
  walkInternal_spine_succ walkInternal_spine_3 rfl (by decide)
theorem walkInternal_spine_5 : walkInternal 126 (List.replicate 5 1) = some 209 :=
  walkInternal_spine_succ walkInternal_spine_4 rfl (by decide)
theorem walkInternal_spine_6 : walkInternal 126 (List.replicate 6 1) = some 220 :=
  walkInternal_spine_succ walkInternal_spine_5 rfl (by decide)
theorem walkInternal_spine_7 : walkInternal 126 (List.replicate 7 1) = some 231 :=
  walkInternal_spine_succ walkInternal_spine_6 rfl (by decide)
theorem walkInternal_spine_8 : walkInternal 126 (List.replicate 8 1) = some 242 :=
  walkInternal_spine_succ walkInternal_spine_7 rfl (by decide)
theorem walkInternal_spine_9 : walkInternal 126 (List.replicate 9 1) = some 253 :=
  walkInternal_spine_succ walkInternal_spine_8 rfl (by decide)
theorem walkInternal_spine_10 : walkInternal 126 (List.replicate 10 1) = some 128 :=
  walkInternal_spine_succ walkInternal_spine_9 rfl (by decide)
theorem walkInternal_spine_11 : walkInternal 126 (List.replicate 11 1) = some 139 :=
  walkInternal_spine_succ walkInternal_spine_10 rfl (by decide)
theorem walkInternal_spine_12 : walkInternal 126 (List.replicate 12 1) = some 150 :=
  walkInternal_spine_succ walkInternal_spine_11 rfl (by decide)
theorem walkInternal_spine_13 : walkInternal 126 (List.replicate 13 1) = some 161 :=
  walkInternal_spine_succ walkInternal_spine_12 rfl (by decide)
theorem walkInternal_spine_14 : walkInternal 126 (List.replicate 14 1) = some 170 :=
  walkInternal_spine_succ walkInternal_spine_13 rfl (by decide)
theorem walkInternal_spine_15 : walkInternal 126 (List.replicate 15 1) = some 171 :=
  walkInternal_spine_succ walkInternal_spine_14 rfl (by decide)
theorem walkInternal_spine_16 : walkInternal 126 (List.replicate 16 1) = some 172 :=
  walkInternal_spine_succ walkInternal_spine_15 rfl (by decide)
theorem walkInternal_spine_17 : walkInternal 126 (List.replicate 17 1) = some 173 :=
  walkInternal_spine_succ walkInternal_spine_16 rfl (by decide)
theorem walkInternal_spine_18 : walkInternal 126 (List.replicate 18 1) = some 174 :=
  walkInternal_spine_succ walkInternal_spine_17 rfl (by decide)
theorem walkInternal_spine_19 : walkInternal 126 (List.replicate 19 1) = some 175 :=
  walkInternal_spine_succ walkInternal_spine_18 rfl (by decide)
theorem walkInternal_spine_20 : walkInternal 126 (List.replicate 20 1) = some 177 :=
  walkInternal_spine_succ walkInternal_spine_19 rfl (by decide)
theorem walkInternal_spine_21 : walkInternal 126 (List.replicate 21 1) = some 178 :=
  walkInternal_spine_succ walkInternal_spine_20 rfl (by decide)
theorem walkInternal_spine_22 : walkInternal 126 (List.replicate 22 1) = some 179 :=
  walkInternal_spine_succ walkInternal_spine_21 rfl (by decide)
theorem walkInternal_spine_23 : walkInternal 126 (List.replicate 23 1) = some 180 :=
  walkInternal_spine_succ walkInternal_spine_22 rfl (by decide)
theorem walkInternal_spine_24 : walkInternal 126 (List.replicate 24 1) = some 181 :=
  walkInternal_spine_succ walkInternal_spine_23 rfl (by decide)
theorem walkInternal_spine_25 : walkInternal 126 (List.replicate 25 1) = some 182 :=
  walkInternal_spine_succ walkInternal_spine_24 rfl (by decide)
theorem walkInternal_spine_26 : walkInternal 126 (List.replicate 26 1) = some 183 :=
  walkInternal_spine_succ walkInternal_spine_25 rfl (by decide)
theorem walkInternal_spine_27 : walkInternal 126 (List.replicate 27 1) = some 184 :=
  walkInternal_spine_succ walkInternal_spine_26 rfl (by decide)
theorem walkInternal_spine_28 : walkInternal 126 (List.replicate 28 1) = some 185 :=
  walkInternal_spine_succ walkInternal_spine_27 rfl (by decide)
theorem walkInternal_spine_29 : walkInternal 126 (List.replicate 29 1) = some 186 :=
  walkInternal_spine_succ walkInternal_spine_28 rfl (by decide)
theorem walkInternal_spine_30 : walkInternal 126 (List.replicate 30 1) = some 188 :=
  walkInternal_spine_succ walkInternal_spine_29 rfl (by decide)
theorem walkInternal_spine_31 : walkInternal 126 (List.replicate 31 1) = some 189 :=
  walkInternal_spine_succ walkInternal_spine_30 rfl (by decide)
theorem walkInternal_spine_32 : walkInternal 126 (List.replicate 32 1) = some 190 :=
  walkInternal_spine_succ walkInternal_spine_31 rfl (by decide)
theorem walkInternal_spine_33 : walkInternal 126 (List.replicate 33 1) = some 191 :=
  walkInternal_spine_succ walkInternal_spine_32 rfl (by decide)
theorem walkInternal_spine_34 : walkInternal 126 (List.replicate 34 1) = some 192 :=
  walkInternal_spine_succ walkInternal_spine_33 rfl (by decide)
theorem walkInternal_spine_35 : walkInternal 126 (List.replicate 35 1) = some 193 :=
  walkInternal_spine_succ walkInternal_spine_34 rfl (by decide)
theorem walkInternal_spine_36 : walkInternal 126 (List.replicate 36 1) = some 194 :=
  walkInternal_spine_succ walkInternal_spine_35 rfl (by decide)
theorem walkInternal_spine_37 : walkInternal 126 (List.replicate 37 1) = some 195 :=
  walkInternal_spine_succ walkInternal_spine_36 rfl (by decide)
theorem walkInternal_spine_38 : walkInternal 126 (List.replicate 38 1) = some 196 :=
  walkInternal_spine_succ walkInternal_spine_37 rfl (by decide)
theorem walkInternal_spine_39 : walkInternal 126 (List.replicate 39 1) = some 197 :=
  walkInternal_spine_succ walkInternal_spine_38 rfl (by decide)
theorem walkInternal_spine_40 : walkInternal 126 (List.replicate 40 1) = some 199 :=
  walkInternal_spine_succ walkInternal_spine_39 rfl (by decide)
theorem walkInternal_spine_41 : walkInternal 126 (List.replicate 41 1) = some 200 :=
  walkInternal_spine_succ walkInternal_spine_40 rfl (by decide)
theorem walkInternal_spine_42 : walkInternal 126 (List.replicate 42 1) = some 201 :=
  walkInternal_spine_succ walkInternal_spine_41 rfl (by decide)
theorem walkInternal_spine_43 : walkInternal 126 (List.replicate 43 1) = some 202 :=
  walkInternal_spine_succ walkInternal_spine_42 rfl (by decide)
theorem walkInternal_spine_44 : walkInternal 126 (List.replicate 44 1) = some 203 :=
  walkInternal_spine_succ walkInternal_spine_43 rfl (by decide)
theorem walkInternal_spine_45 : walkInternal 126 (List.replicate 45 1) = some 204 :=
  walkInternal_spine_succ walkInternal_spine_44 rfl (by decide)
theorem walkInternal_spine_46 : walkInternal 126 (List.replicate 46 1) = some 205 :=
  walkInternal_spine_succ walkInternal_spine_45 rfl (by decide)
theorem walkInternal_spine_47 : walkInternal 126 (List.replicate 47 1) = some 206 :=
  walkInternal_spine_succ walkInternal_spine_46 rfl (by decide)
theorem walkInternal_spine_48 : walkInternal 126 (List.replicate 48 1) = some 207 :=
  walkInternal_spine_succ walkInternal_spine_47 rfl (by decide)
theorem walkInternal_spine_49 : walkInternal 126 (List.replicate 49 1) = some 208 :=
  walkInternal_spine_succ walkInternal_spine_48 rfl (by decide)
theorem walkInternal_spine_50 : walkInternal 126 (List.replicate 50 1) = some 210 :=
  walkInternal_spine_succ walkInternal_spine_49 rfl (by decide)
theorem walkInternal_spine_51 : walkInternal 126 (List.replicate 51 1) = some 211 :=
  walkInternal_spine_succ walkInternal_spine_50 rfl (by decide)
theorem walkInternal_spine_52 : walkInternal 126 (List.replicate 52 1) = some 212 :=
  walkInternal_spine_succ walkInternal_spine_51 rfl (by decide)
theorem walkInternal_spine_53 : walkInternal 126 (List.replicate 53 1) = some 213 :=
  walkInternal_spine_succ walkInternal_spine_52 rfl (by decide)
theorem walkInternal_spine_54 : walkInternal 126 (List.replicate 54 1) = some 214 :=
  walkInternal_spine_succ walkInternal_spine_53 rfl (by decide)
theorem walkInternal_spine_55 : walkInternal 126 (List.replicate 55 1) = some 215 :=
  walkInternal_spine_succ walkInternal_spine_54 rfl (by decide)
theorem walkInternal_spine_56 : walkInternal 126 (List.replicate 56 1) = some 216 :=
  walkInternal_spine_succ walkInternal_spine_55 rfl (by decide)
theorem walkInternal_spine_57 : walkInternal 126 (List.replicate 57 1) = some 217 :=
  walkInternal_spine_succ walkInternal_spine_56 rfl (by decide)
theorem walkInternal_spine_58 : walkInternal 126 (List.replicate 58 1) = some 218 :=
  walkInternal_spine_succ walkInternal_spine_57 rfl (by decide)
theorem walkInternal_spine_59 : walkInternal 126 (List.replicate 59 1) = some 219 :=
  walkInternal_spine_succ walkInternal_spine_58 rfl (by decide)
theorem walkInternal_spine_60 : walkInternal 126 (List.replicate 60 1) = some 221 :=
  walkInternal_spine_succ walkInternal_spine_59 rfl (by decide)
theorem walkInternal_spine_61 : walkInternal 126 (List.replicate 61 1) = some 222 :=
  walkInternal_spine_succ walkInternal_spine_60 rfl (by decide)
theorem walkInternal_spine_62 : walkInternal 126 (List.replicate 62 1) = some 223 :=
  walkInternal_spine_succ walkInternal_spine_61 rfl (by decide)
theorem walkInternal_spine_63 : walkInternal 126 (List.replicate 63 1) = some 224 :=
  walkInternal_spine_succ walkInternal_spine_62 rfl (by decide)
theorem walkInternal_spine_64 : walkInternal 126 (List.replicate 64 1) = some 225 :=
  walkInternal_spine_succ walkInternal_spine_63 rfl (by decide)
theorem walkInternal_spine_65 : walkInternal 126 (List.replicate 65 1) = some 226 :=
  walkInternal_spine_succ walkInternal_spine_64 rfl (by decide)
theorem walkInternal_spine_66 : walkInternal 126 (List.replicate 66 1) = some 227 :=
  walkInternal_spine_succ walkInternal_spine_65 rfl (by decide)
theorem walkInternal_spine_67 : walkInternal 126 (List.replicate 67 1) = some 228 :=
  walkInternal_spine_succ walkInternal_spine_66 rfl (by decide)
theorem walkInternal_spine_68 : walkInternal 126 (List.replicate 68 1) = some 229 :=
  walkInternal_spine_succ walkInternal_spine_67 rfl (by decide)
theorem walkInternal_spine_69 : walkInternal 126 (List.replicate 69 1) = some 230 :=
  walkInternal_spine_succ walkInternal_spine_68 rfl (by decide)
theorem walkInternal_spine_70 : walkInternal 126 (List.replicate 70 1) = some 232 :=
  walkInternal_spine_succ walkInternal_spine_69 rfl (by decide)
theorem walkInternal_spine_71 : walkInternal 126 (List.replicate 71 1) = some 233 :=
  walkInternal_spine_succ walkInternal_spine_70 rfl (by decide)
theorem walkInternal_spine_72 : walkInternal 126 (List.replicate 72 1) = some 234 :=
  walkInternal_spine_succ walkInternal_spine_71 rfl (by decide)
theorem walkInternal_spine_73 : walkInternal 126 (List.replicate 73 1) = some 235 :=
  walkInternal_spine_succ walkInternal_spine_72 rfl (by decide)
theorem walkInternal_spine_74 : walkInternal 126 (List.replicate 74 1) = some 236 :=
  walkInternal_spine_succ walkInternal_spine_73 rfl (by decide)
theorem walkInternal_spine_75 : walkInternal 126 (List.replicate 75 1) = some 237 :=
  walkInternal_spine_succ walkInternal_spine_74 rfl (by decide)
theorem walkInternal_spine_76 : walkInternal 126 (List.replicate 76 1) = some 238 :=
  walkInternal_spine_succ walkInternal_spine_75 rfl (by decide)
theorem walkInternal_spine_77 : walkInternal 126 (List.replicate 77 1) = some 239 :=
  walkInternal_spine_succ walkInternal_spine_76 rfl (by decide)
theorem walkInternal_spine_78 : walkInternal 126 (List.replicate 78 1) = some 240 :=
  walkInternal_spine_succ walkInternal_spine_77 rfl (by decide)
theorem walkInternal_spine_79 : walkInternal 126 (List.replicate 79 1) = some 241 :=
  walkInternal_spine_succ walkInternal_spine_78 rfl (by decide)
theorem walkInternal_spine_80 : walkInternal 126 (List.replicate 80 1) = some 243 :=
  walkInternal_spine_succ walkInternal_spine_79 rfl (by decide)
theorem walkInternal_spine_81 : walkInternal 126 (List.replicate 81 1) = some 244 :=
  walkInternal_spine_succ walkInternal_spine_80 rfl (by decide)
theorem walkInternal_spine_82 : walkInternal 126 (List.replicate 82 1) = some 245 :=
  walkInternal_spine_succ walkInternal_spine_81 rfl (by decide)
theorem walkInternal_spine_83 : walkInternal 126 (List.replicate 83 1) = some 246 :=
  walkInternal_spine_succ walkInternal_spine_82 rfl (by decide)
theorem walkInternal_spine_84 : walkInternal 126 (List.replicate 84 1) = some 247 :=
  walkInternal_spine_succ walkInternal_spine_83 rfl (by decide)
theorem walkInternal_spine_85 : walkInternal 126 (List.replicate 85 1) = some 248 :=
  walkInternal_spine_succ walkInternal_spine_84 rfl (by decide)
theorem walkInternal_spine_86 : walkInternal 126 (List.replicate 86 1) = some 249 :=
  walkInternal_spine_succ walkInternal_spine_85 rfl (by decide)
theorem walkInternal_spine_87 : walkInternal 126 (List.replicate 87 1) = some 250 :=
  walkInternal_spine_succ walkInternal_spine_86 rfl (by decide)
theorem walkInternal_spine_88 : walkInternal 126 (List.replicate 88 1) = some 251 :=
  walkInternal_spine_succ walkInternal_spine_87 rfl (by decide)
theorem walkInternal_spine_89 : walkInternal 126 (List.replicate 89 1) = some 252 :=
  walkInternal_spine_succ walkInternal_spine_88 rfl (by decide)
theorem walkInternal_spine_90 : walkInternal 126 (List.replicate 90 1) = some 254 :=
  walkInternal_spine_succ walkInternal_spine_89 rfl (by decide)
theorem walkInternal_spine_91 : walkInternal 126 (List.replicate 91 1) = some 255 :=
  walkInternal_spine_succ walkInternal_spine_90 rfl (by decide)
theorem walkInternal_spine_92 : walkInternal 126 (List.replicate 92 1) = some 256 :=
  walkInternal_spine_succ walkInternal_spine_91 rfl (by decide)
theorem walkInternal_spine_93 : walkInternal 126 (List.replicate 93 1) = some 257 :=
  walkInternal_spine_succ walkInternal_spine_92 rfl (by decide)
theorem walkInternal_spine_94 : walkInternal 126 (List.replicate 94 1) = some 258 :=
  walkInternal_spine_succ walkInternal_spine_93 rfl (by decide)
theorem walkInternal_spine_95 : walkInternal 126 (List.replicate 95 1) = some 259 :=
  walkInternal_spine_succ walkInternal_spine_94 rfl (by decide)
theorem walkInternal_spine_96 : walkInternal 126 (List.replicate 96 1) = some 260 :=
  walkInternal_spine_succ walkInternal_spine_95 rfl (by decide)
theorem walkInternal_spine_97 : walkInternal 126 (List.replicate 97 1) = some 261 :=
  walkInternal_spine_succ walkInternal_spine_96 rfl (by decide)
theorem walkInternal_spine_98 : walkInternal 126 (List.replicate 98 1) = some 262 :=
  walkInternal_spine_succ walkInternal_spine_97 rfl (by decide)
theorem walkInternal_spine_99 : walkInternal 126 (List.replicate 99 1) = some 263 :=
  walkInternal_spine_succ walkInternal_spine_98 rfl (by decide)
theorem walkInternal_spine_100 : walkInternal 126 (List.replicate 100 1) = some 129 :=
  walkInternal_spine_succ walkInternal_spine_99 rfl (by decide)
theorem walkInternal_spine_101 : walkInternal 126 (List.replicate 101 1) = some 130 :=
  walkInternal_spine_succ walkInternal_spine_100 rfl (by decide)
theorem walkInternal_spine_102 : walkInternal 126 (List.replicate 102 1) = some 131 :=
  walkInternal_spine_succ walkInternal_spine_101 rfl (by decide)
theorem walkInternal_spine_103 : walkInternal 126 (List.replicate 103 1) = some 132 :=
  walkInternal_spine_succ walkInternal_spine_102 rfl (by decide)
theorem walkInternal_spine_104 : walkInternal 126 (List.replicate 104 1) = some 133 :=
  walkInternal_spine_succ walkInternal_spine_103 rfl (by decide)
theorem walkInternal_spine_105 : walkInternal 126 (List.replicate 105 1) = some 134 :=
  walkInternal_spine_succ walkInternal_spine_104 rfl (by decide)
theorem walkInternal_spine_106 : walkInternal 126 (List.replicate 106 1) = some 135 :=
  walkInternal_spine_succ walkInternal_spine_105 rfl (by decide)
theorem walkInternal_spine_107 : walkInternal 126 (List.replicate 107 1) = some 136 :=
  walkInternal_spine_succ walkInternal_spine_106 rfl (by decide)
theorem walkInternal_spine_108 : walkInternal 126 (List.replicate 108 1) = some 137 :=
  walkInternal_spine_succ walkInternal_spine_107 rfl (by decide)
theorem walkInternal_spine_109 : walkInternal 126 (List.replicate 109 1) = some 138 :=
  walkInternal_spine_succ walkInternal_spine_108 rfl (by decide)
theorem walkInternal_spine_110 : walkInternal 126 (List.replicate 110 1) = some 140 :=
  walkInternal_spine_succ walkInternal_spine_109 rfl (by decide)
theorem walkInternal_spine_111 : walkInternal 126 (List.replicate 111 1) = some 141 :=
  walkInternal_spine_succ walkInternal_spine_110 rfl (by decide)
theorem walkInternal_spine_112 : walkInternal 126 (List.replicate 112 1) = some 142 :=
  walkInternal_spine_succ walkInternal_spine_111 rfl (by decide)
theorem walkInternal_spine_113 : walkInternal 126 (List.replicate 113 1) = some 143 :=
  walkInternal_spine_succ walkInternal_spine_112 rfl (by decide)
theorem walkInternal_spine_114 : walkInternal 126 (List.replicate 114 1) = some 144 :=
  walkInternal_spine_succ walkInternal_spine_113 rfl (by decide)
theorem walkInternal_spine_115 : walkInternal 126 (List.replicate 115 1) = some 145 :=
  walkInternal_spine_succ walkInternal_spine_114 rfl (by decide)
theorem walkInternal_spine_116 : walkInternal 126 (List.replicate 116 1) = some 146 :=
  walkInternal_spine_succ walkInternal_spine_115 rfl (by decide)
theorem walkInternal_spine_117 : walkInternal 126 (List.replicate 117 1) = some 147 :=
  walkInternal_spine_succ walkInternal_spine_116 rfl (by decide)
theorem walkInternal_spine_118 : walkInternal 126 (List.replicate 118 1) = some 148 :=
  walkInternal_spine_succ walkInternal_spine_117 rfl (by decide)
theorem walkInternal_spine_119 : walkInternal 126 (List.replicate 119 1) = some 149 :=
  walkInternal_spine_succ walkInternal_spine_118 rfl (by decide)
theorem walkInternal_spine_120 : walkInternal 126 (List.replicate 120 1) = some 151 :=
  walkInternal_spine_succ walkInternal_spine_119 rfl (by decide)
theorem walkInternal_spine_121 : walkInternal 126 (List.replicate 121 1) = some 152 :=
  walkInternal_spine_succ walkInternal_spine_120 rfl (by decide)
theorem walkInternal_spine_122 : walkInternal 126 (List.replicate 122 1) = some 153 :=
  walkInternal_spine_succ walkInternal_spine_121 rfl (by decide)
theorem walkInternal_spine_123 : walkInternal 126 (List.replicate 123 1) = some 154 :=
  walkInternal_spine_succ walkInternal_spine_122 rfl (by decide)
theorem walkInternal_spine_124 : walkInternal 126 (List.replicate 124 1) = some 155 :=
  walkInternal_spine_succ walkInternal_spine_123 rfl (by decide)
theorem walkInternal_spine_125 : walkInternal 126 (List.replicate 125 1) = some 156 :=
  walkInternal_spine_succ walkInternal_spine_124 rfl (by decide)
theorem walkInternal_spine_126 : walkInternal 126 (List.replicate 126 1) = some 157 :=
  walkInternal_spine_succ walkInternal_spine_125 rfl (by decide)
theorem walkInternal_spine_127 : walkInternal 126 (List.replicate 127 1) = some 158 :=
  walkInternal_spine_succ walkInternal_spine_126 rfl (by decide)
theorem walkInternal_spine_128 : walkInternal 126 (List.replicate 128 1) = some 159 :=
  walkInternal_spine_succ walkInternal_spine_127 rfl (by decide)
theorem walkInternal_spine_129 : walkInternal 126 (List.replicate 129 1) = some 160 :=
  walkInternal_spine_succ walkInternal_spine_128 rfl (by decide)
theorem walkInternal_spine_130 : walkInternal 126 (List.replicate 130 1) = some 162 :=
  walkInternal_spine_succ walkInternal_spine_129 rfl (by decide)
theorem walkInternal_spine_131 : walkInternal 126 (List.replicate 131 1) = some 163 :=
  walkInternal_spine_succ walkInternal_spine_130 rfl (by decide)
theorem walkInternal_spine_132 : walkInternal 126 (List.replicate 132 1) = some 164 :=
  walkInternal_spine_succ walkInternal_spine_131 rfl (by decide)
theorem walkInternal_spine_133 : walkInternal 126 (List.replicate 133 1) = some 165 :=
  walkInternal_spine_succ walkInternal_spine_132 rfl (by decide)
theorem walkInternal_spine_134 : walkInternal 126 (List.replicate 134 1) = some 166 :=
  walkInternal_spine_succ walkInternal_spine_133 rfl (by decide)

/-! ## 2. `WffState`-Level Subroutine Composition (`WffSubEval`) -/

/-- `WffState`-level subroutine evaluation specification for node `q ∈ {96..431}`. -/
def WffSubEval (q : Fin 432) (op : WffState → WffState) : Prop :=
  ∀ (P : List (Fin 2)),
    walkInternal 126 P = some q →
    ∀ (pl np : ℕ) (s : WffState),
      ∃ steps ≥ 1, zfReg11NSteps steps ⟨trimZeros P, wffStateToRegs pl np s⟩ =
        some ⟨retStack P, wffStateToRegs pl np (op s)⟩

theorem wffSubEval_of_subEval {q : Fin 432} {f : List ℕ → List ℕ} {op : WffState → WffState}
    (hsub : SubEval q f)
    (heq : ∀ pl np s, f (wffStateToRegs pl np s) = wffStateToRegs pl np (op s)) :
    WffSubEval q op := by
  intro P hP pl np s
  obtain ⟨steps, hsteps, heval, _⟩ := hsub P hP (wffStateToRegs pl np s) rfl
  rw [heq pl np s] at heval
  exact ⟨steps, hsteps, heval⟩

theorem wffSubEval_seq {q q0 q1 : Fin 432} {op0 op1 op : WffState → WffState}
    (htr0 : refTrans q 0 = some (0, .right, q0)) (hq0 : 96 ≤ q0.val)
    (htr1 : refTrans q 1 = some (1, .right, q1)) (hq1 : 96 ≤ q1.val)
    (h0 : WffSubEval q0 op0) (h1 : WffSubEval q1 op1)
    (heq : (fun s => op1 (op0 s)) = op := by rfl) :
    WffSubEval q op := by
  subst heq
  intro P hP pl np s
  have hP0 : walkInternal 126 (P ++ [0]) = some q0 := walkInternal_snoc hP htr0 hq0
  have hP1 : walkInternal 126 (P ++ [1]) = some q1 := walkInternal_snoc hP htr1 hq1
  obtain ⟨s0, hs0, hsteps0⟩ := h0 (P ++ [0]) hP0 pl np s
  rw [trimZeros_append_zero, retStack_append_zero] at hsteps0
  obtain ⟨s1, hs1, hsteps1⟩ := h1 (P ++ [1]) hP1 pl np (op0 s)
  rw [trimZeros_append_one, retStack_append_one] at hsteps1
  exact ⟨s0 + s1, by omega, zfReg11NSteps_bind_eq hsteps0 hsteps1⟩

/-! ### 17 Leaf `WffSubEval` Lemmas -/

theorem wffSubEval_106 : WffSubEval 106 rpnCparam2 :=
  wffSubEval_of_subEval subEval_106_inst regCparam2Op_wffStateToRegs

theorem wffSubEval_108 : WffSubEval 108 rpnCparam3 :=
  wffSubEval_of_subEval subEval_108_inst regCparam3Op_wffStateToRegs

theorem wffSubEval_337 : WffSubEval 337 rpnPar1 :=
  wffSubEval_of_subEval subEval_337 regPar1Op_wffStateToRegs

theorem wffSubEval_339 : WffSubEval 339 rpnPar2 :=
  wffSubEval_of_subEval subEval_339 regPar2Op_wffStateToRegs

theorem wffSubEval_341 : WffSubEval 341 rpnPar3 :=
  wffSubEval_of_subEval subEval_341 regPar3Op_wffStateToRegs

theorem wffSubEval_343 : WffSubEval 343 (rpnVk 0) :=
  wffSubEval_of_subEval subEval_343 regPushwffOp_wffStateToRegs

theorem wffSubEval_344 : WffSubEval 344 rpnSelect :=
  wffSubEval_of_subEval subEval_344_inst regSelectOp_wffStateToRegs

theorem wffSubEval_358 : WffSubEval 358 (rpnVk 1) :=
  wffSubEval_of_subEval subEval_358 regV1Op_wffStateToRegs

theorem wffSubEval_359 : WffSubEval 359 (rpnVk 2) :=
  wffSubEval_of_subEval subEval_359 regV2Op_wffStateToRegs

theorem wffSubEval_360 : WffSubEval 360 (rpnVk 3) :=
  wffSubEval_of_subEval subEval_360 regV3Op_wffStateToRegs

theorem wffSubEval_362 : WffSubEval 362 rpnWa :=
  wffSubEval_of_subEval subEval_362 regWaOp_wffStateToRegs

theorem wffSubEval_364 : WffSubEval 364 rpnWal :=
  wffSubEval_of_subEval subEval_364 regWalOp_wffStateToRegs

theorem wffSubEval_366 : WffSubEval 366 rpnWel :=
  wffSubEval_of_subEval subEval_366 regWelOp_wffStateToRegs

theorem wffSubEval_368 : WffSubEval 368 rpnWeq :=
  wffSubEval_of_subEval subEval_368 regWeqOp_wffStateToRegs

theorem wffSubEval_370 : WffSubEval 370 rpnWex :=
  wffSubEval_of_subEval subEval_370 regWexOp_wffStateToRegs

theorem wffSubEval_429 : WffSubEval 429 rpnWim :=
  wffSubEval_of_subEval subEval_429 regWimOp_wffStateToRegs

theorem wffSubEval_431 : WffSubEval 431 rpnWn :=
  wffSubEval_of_subEval subEval_431 regWnOp_wffStateToRegs

/-! ### 61 Composite Node `WffSubEval` Lemmas (`264..327` except `298, 299, 310`) -/
abbrev wffOp_321 (s : WffState) : WffState := rpnPar2 (rpnPar1 s)
theorem wffSubEval_321 : WffSubEval 321 wffOp_321 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_337 wffSubEval_339
abbrev wffOp_306 (s : WffState) : WffState := wffOp_321 (rpnSelect s)
theorem wffSubEval_306 : WffSubEval 306 wffOp_306 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_344 wffSubEval_321
abbrev wffOp_285 (s : WffState) : WffState := rpnPar3 (rpnPar1 s)
theorem wffSubEval_285 : WffSubEval 285 wffOp_285 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_337 wffSubEval_341
abbrev wffOp_284 (s : WffState) : WffState := wffOp_285 (rpnWeq s)
theorem wffSubEval_284 : WffSubEval 284 wffOp_284 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_368 wffSubEval_285
abbrev wffOp_283 (s : WffState) : WffState := wffOp_284 (wffOp_306 s)
theorem wffSubEval_283 : WffSubEval 283 wffOp_283 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_306 wffSubEval_284
abbrev wffOp_324 (s : WffState) : WffState := rpnPar3 (rpnPar2 s)
theorem wffSubEval_324 : WffSubEval 324 wffOp_324 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_339 wffSubEval_341
abbrev wffOp_320 (s : WffState) : WffState := rpnSelect (rpnWim s)
theorem wffSubEval_320 : WffSubEval 320 wffOp_320 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_429 wffSubEval_344
abbrev wffOp_305 (s : WffState) : WffState := wffOp_320 (rpnWim s)
theorem wffSubEval_305 : WffSubEval 305 wffOp_305 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_429 wffSubEval_320
abbrev wffOp_295 (s : WffState) : WffState := rpnPar1 (wffOp_305 s)
theorem wffSubEval_295 : WffSubEval 295 wffOp_295 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_305 wffSubEval_337
abbrev wffOp_287 (s : WffState) : WffState := rpnPar2 (wffOp_295 s)
theorem wffSubEval_287 : WffSubEval 287 wffOp_287 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_295 wffSubEval_339
abbrev wffOp_271 (s : WffState) : WffState := rpnPar1 (rpnPar3 s)
theorem wffSubEval_271 : WffSubEval 271 wffOp_271 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_341 wffSubEval_337
abbrev wffOp_270 (s : WffState) : WffState := wffOp_271 (rpnWeq s)
theorem wffSubEval_270 : WffSubEval 270 wffOp_270 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_368 wffSubEval_271
abbrev wffOp_269 (s : WffState) : WffState := wffOp_270 (wffOp_287 s)
theorem wffSubEval_269 : WffSubEval 269 wffOp_269 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_287 wffSubEval_270
abbrev wffOp_268 (s : WffState) : WffState := wffOp_269 (rpnWel s)
theorem wffSubEval_268 : WffSubEval 268 wffOp_268 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_366 wffSubEval_269
abbrev wffOp_267 (s : WffState) : WffState := wffOp_268 (wffOp_324 s)
theorem wffSubEval_267 : WffSubEval 267 wffOp_267 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_324 wffSubEval_268
abbrev wffOp_266 (s : WffState) : WffState := wffOp_267 (rpnWel s)
theorem wffSubEval_266 : WffSubEval 266 wffOp_266 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_366 wffSubEval_267
abbrev wffOp_265 (s : WffState) : WffState := wffOp_266 (wffOp_283 s)
theorem wffSubEval_265 : WffSubEval 265 wffOp_265 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_283 wffSubEval_266
abbrev wffOp_264 (s : WffState) : WffState := wffOp_265 (rpnWim s)
theorem wffSubEval_264 : WffSubEval 264 wffOp_264 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_429 wffSubEval_265
abbrev wffOp_325 (s : WffState) : WffState := rpnWal (rpnPar3 s)
theorem wffSubEval_325 : WffSubEval 325 wffOp_325 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_341 wffSubEval_364
abbrev wffOp_296 (s : WffState) : WffState := wffOp_325 (rpnPar1 s)
theorem wffSubEval_296 : WffSubEval 296 wffOp_296 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_337 wffSubEval_325
abbrev wffOp_276 (s : WffState) : WffState := rpnWal (wffOp_296 s)
theorem wffSubEval_276 : WffSubEval 276 wffOp_276 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_296 wffSubEval_364
abbrev wffOp_275 (s : WffState) : WffState := wffOp_276 (rpnPar2 s)
theorem wffSubEval_275 : WffSubEval 275 wffOp_275 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_339 wffSubEval_276
abbrev wffOp_274 (s : WffState) : WffState := wffOp_275 (rpnWal s)
theorem wffSubEval_274 : WffSubEval 274 wffOp_274 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_364 wffSubEval_275
abbrev wffOp_273 (s : WffState) : WffState := wffOp_274 (wffOp_325 s)
theorem wffSubEval_273 : WffSubEval 273 wffOp_273 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_325 wffSubEval_274
abbrev wffOp_272 (s : WffState) : WffState := wffOp_273 (wffOp_306 s)
theorem wffSubEval_272 : WffSubEval 272 wffOp_272 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_306 wffSubEval_273
abbrev wffOp_327 (s : WffState) : WffState := rpnWel ((rpnVk 0) s)
theorem wffSubEval_327 : WffSubEval 327 wffOp_327 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_343 wffSubEval_366
abbrev wffOp_307 (s : WffState) : WffState := wffOp_327 ((rpnVk 3) s)
theorem wffSubEval_307 : WffSubEval 307 wffOp_307 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_360 wffSubEval_327
abbrev wffOp_309 (s : WffState) : WffState := rpnWal (rpnPar1 s)
theorem wffSubEval_309 : WffSubEval 309 wffOp_309 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_337 wffSubEval_364
abbrev wffOp_308 (s : WffState) : WffState := wffOp_309 ((rpnVk 1) s)
theorem wffSubEval_308 : WffSubEval 308 wffOp_308 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_358 wffSubEval_309
abbrev wffOp_318 (s : WffState) : WffState := rpnWex (rpnWa s)
theorem wffSubEval_318 : WffSubEval 318 wffOp_318 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_362 wffSubEval_370
abbrev wffOp_279 (s : WffState) : WffState := wffOp_318 (wffOp_308 s)
theorem wffSubEval_279 : WffSubEval 279 wffOp_279 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_308 wffSubEval_318
abbrev wffOp_278 (s : WffState) : WffState := wffOp_279 (wffOp_307 s)
theorem wffSubEval_278 : WffSubEval 278 wffOp_278 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_307 wffSubEval_279
abbrev wffOp_277 (s : WffState) : WffState := wffOp_278 ((rpnVk 3) s)
theorem wffSubEval_277 : WffSubEval 277 wffOp_277 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_360 wffSubEval_278
abbrev wffOp_323 (s : WffState) : WffState := rpnWel ((rpnVk 1) s)
theorem wffSubEval_323 : WffSubEval 323 wffOp_323 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_358 wffSubEval_366
abbrev wffOp_304 (s : WffState) : WffState := wffOp_323 ((rpnVk 2) s)
theorem wffSubEval_304 : WffSubEval 304 wffOp_304 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_359 wffSubEval_323
abbrev wffOp_288 (s : WffState) : WffState := rpnWim (wffOp_304 s)
theorem wffSubEval_288 : WffSubEval 288 wffOp_288 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_304 wffSubEval_429
abbrev wffOp_315 (s : WffState) : WffState := rpnWex (rpnWal s)
theorem wffSubEval_315 : WffSubEval 315 wffOp_315 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_364 wffSubEval_370
abbrev wffOp_282 (s : WffState) : WffState := (rpnVk 1) (rpnSelect s)
theorem wffSubEval_282 : WffSubEval 282 wffOp_282 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_344 wffSubEval_358
abbrev wffOp_281 (s : WffState) : WffState := wffOp_282 (wffOp_315 s)
theorem wffSubEval_281 : WffSubEval 281 wffOp_281 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_315 wffSubEval_282
abbrev wffOp_280 (s : WffState) : WffState := wffOp_281 (wffOp_288 s)
theorem wffSubEval_280 : WffSubEval 280 wffOp_280 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_288 wffSubEval_281
abbrev wffOp_326 (s : WffState) : WffState := rpnPar1 (rpnPar1 s)
theorem wffSubEval_326 : WffSubEval 326 wffOp_326 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_337 wffSubEval_337
abbrev wffOp_294 (s : WffState) : WffState := wffOp_326 (wffOp_320 s)
theorem wffSubEval_294 : WffSubEval 294 wffOp_294 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_320 wffSubEval_326
abbrev wffOp_286 (s : WffState) : WffState := rpnPar2 (wffOp_294 s)
theorem wffSubEval_286 : WffSubEval 286 wffOp_286 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_294 wffSubEval_339
abbrev wffOp_289 (s : WffState) : WffState := wffOp_307 (rpnWel s)
theorem wffSubEval_289 : WffSubEval 289 wffOp_289 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_366 wffSubEval_307
abbrev wffOp_290 (s : WffState) : WffState := wffOp_304 ((rpnVk 2) s)
theorem wffSubEval_290 : WffSubEval 290 wffOp_290 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_359 wffSubEval_304
abbrev wffOp_293 (s : WffState) : WffState := rpnWal (rpnWa s)
theorem wffSubEval_293 : WffSubEval 293 wffOp_293 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_362 wffSubEval_364
abbrev wffOp_292 (s : WffState) : WffState := wffOp_293 (rpnWim s)
theorem wffSubEval_292 : WffSubEval 292 wffOp_292 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_429 wffSubEval_293
abbrev wffOp_291 (s : WffState) : WffState := wffOp_292 (rpnWel s)
theorem wffSubEval_291 : WffSubEval 291 wffOp_291 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_366 wffSubEval_292
abbrev wffOp_297 (s : WffState) : WffState := rpnWel (wffOp_321 s)
theorem wffSubEval_297 : WffSubEval 297 wffOp_297 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_321 wffSubEval_366
abbrev wffOp_322 (s : WffState) : WffState := rpnWim (rpnWeq s)
theorem wffSubEval_322 : WffSubEval 322 wffOp_322 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_368 wffSubEval_429
abbrev wffOp_300 (s : WffState) : WffState := wffOp_322 ((rpnVk 1) s)
theorem wffSubEval_300 : WffSubEval 300 wffOp_300 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_358 wffSubEval_322
abbrev wffOp_301 (s : WffState) : WffState := wffOp_323 ((rpnVk 0) s)
theorem wffSubEval_301 : WffSubEval 301 wffOp_301 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_343 wffSubEval_323
abbrev wffOp_303 (s : WffState) : WffState := rpnWeq ((rpnVk 0) s)
theorem wffSubEval_303 : WffSubEval 303 wffOp_303 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_343 wffSubEval_368
abbrev wffOp_302 (s : WffState) : WffState := wffOp_303 ((rpnVk 1) s)
theorem wffSubEval_302 : WffSubEval 302 wffOp_302 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_358 wffSubEval_303
abbrev wffOp_311 (s : WffState) : WffState := rpnWim (rpnPar3 s)
theorem wffSubEval_311 : WffSubEval 311 wffOp_311 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_341 wffSubEval_429
abbrev wffOp_312 (s : WffState) : WffState := rpnWim (rpnPar1 s)
theorem wffSubEval_312 : WffSubEval 312 wffOp_312 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_337 wffSubEval_429
abbrev wffOp_313 (s : WffState) : WffState := rpnWim (rpnWal s)
theorem wffSubEval_313 : WffSubEval 313 wffOp_313 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_364 wffSubEval_429
abbrev wffOp_314 (s : WffState) : WffState := (rpnVk 0) ((rpnVk 2) s)
theorem wffSubEval_314 : WffSubEval 314 wffOp_314 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_359 wffSubEval_343
abbrev wffOp_316 (s : WffState) : WffState := (rpnVk 2) ((rpnVk 1) s)
theorem wffSubEval_316 : WffSubEval 316 wffOp_316 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_358 wffSubEval_359
abbrev wffOp_317 (s : WffState) : WffState := (rpnVk 2) ((rpnVk 3) s)
theorem wffSubEval_317 : WffSubEval 317 wffOp_317 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_360 wffSubEval_359
abbrev wffOp_319 (s : WffState) : WffState := rpnWal (rpnWim s)
theorem wffSubEval_319 : WffSubEval 319 wffOp_319 :=
  wffSubEval_seq rfl (by decide) rfl (by decide) wffSubEval_429 wffSubEval_364
/-! ## 3. `WffState`-Level Spine Composition (`WffSpineEval`, `k = 13..133`) -/

/-- `WffState`-level spine evaluation from `List.replicate k₁ 1` to `List.replicate k₂ 1`. -/
def WffSpineEval (k₁ k₂ : ℕ) (op : WffState → WffState) : Prop :=
  ∀ (pl np : ℕ) (s : WffState),
    ∃ steps ≥ 1, zfReg11NSteps steps ⟨List.replicate k₁ 1, wffStateToRegs pl np s⟩ =
      some ⟨List.replicate k₂ 1, wffStateToRegs pl np (op s)⟩

theorem wffSpineEval_step {k k' : ℕ} {q_k q_sub : Fin 432} {op : WffState → WffState}
    (hwalk : walkInternal 126 (List.replicate k 1) = some q_k)
    (htr0 : refTrans q_k 0 = some (0, .right, q_sub))
    (hq_sub : 96 ≤ q_sub.val)
    (hsub : WffSubEval q_sub op)
    (hk : k + 1 = k' := by rfl) :
    WffSpineEval k k' op := by
  subst hk
  intro pl np s
  have hwalk0 : walkInternal 126 (List.replicate k 1 ++ [0]) = some q_sub :=
    walkInternal_snoc hwalk htr0 hq_sub
  obtain ⟨steps, hsteps, heval⟩ := hsub (List.replicate k 1 ++ [0]) hwalk0 pl np s
  rw [trimZeros_append_zero, trimZeros_replicate_one, retStack_append_zero,
    ← List.replicate_succ'] at heval
  exact ⟨steps, hsteps, heval⟩

theorem wffSpineEval_trans {k₁ k₂ k₃ : ℕ} {op₁ op₂ op : WffState → WffState}
    (h1 : WffSpineEval k₁ k₂ op₁) (h2 : WffSpineEval k₂ k₃ op₂)
    (heq : (fun s => op₂ (op₁ s)) = op := by rfl) :
    WffSpineEval k₁ k₃ op := by
  subst heq
  intro pl np s
  obtain ⟨s₁, hs₁, heval₁⟩ := h1 pl np s
  obtain ⟨s₂, hs₂, heval₂⟩ := h2 pl np (op₁ s)
  exact ⟨s₁ + s₂, by omega, zfReg11NSteps_bind_eq heval₁ heval₂⟩

theorem wffSpineEval_of_regSpineEval {k₁ k₂ : ℕ} {f : List ℕ → List ℕ} {op : WffState → WffState}
    (h : RegSpineEval k₁ k₂ f)
    (heq : ∀ pl np s, f (wffStateToRegs pl np s) = wffStateToRegs pl np (op s)) :
    WffSpineEval k₁ k₂ op := by
  intro pl np s
  obtain ⟨steps, hsteps, heval, _⟩ := h (wffStateToRegs pl np s) rfl
  rw [heq pl np s] at heval
  exact ⟨steps, hsteps, heval⟩

/-! ### Special Multi-Step Spine Blocks (`18..22`, `56..59`, `59..62`) -/

theorem wffSpineEval_18_22 : WffSpineEval 18 22 rpnDetCheck := by
  refine wffSpineEval_of_regSpineEval
    (regSpineEval_trans (regSpineEval_step walkInternal_spine_18 rfl (by decide) subEval_427) <|
     regSpineEval_trans (regSpineEval_step walkInternal_spine_19 rfl (by decide) subEval_394) <|
     regSpineEval_trans (regSpineEval_step walkInternal_spine_20 rfl (by decide) subEval_405) <|
     regSpineEval_step walkInternal_spine_21 rfl (by decide) subEval_119) ?_
  intro pl np s
  simp only [wffStateToRegs, reg119Op, reg120Op, rpnDetCheck, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.set_cons_zero, List.set_cons_succ, Nat.zero_add]
  split_ifs <;> rfl

theorem wffSpineEval_56_59 : WffSpineEval 56 59 rpnB6aCheck1 := by
  refine wffSpineEval_of_regSpineEval
    (regSpineEval_trans (regSpineEval_step walkInternal_spine_56 rfl (by decide) subEval_386) <|
     regSpineEval_trans (regSpineEval_step walkInternal_spine_57 rfl (by decide) subEval_403) <|
     regSpineEval_step walkInternal_spine_58 rfl (by decide) subEval_298) ?_
  intro pl np s
  simp only [wffStateToRegs, reg298Op, reg299Op, reg121Op, rpnB6aCheck1, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.set_cons_zero, List.set_cons_succ, Nat.zero_add]
  split_ifs <;> rfl

theorem wffSpineEval_59_62 : WffSpineEval 59 62 rpnB6aCheck2 := by
  refine wffSpineEval_of_regSpineEval
    (regSpineEval_trans (regSpineEval_step walkInternal_spine_59 rfl (by decide) subEval_392) <|
     regSpineEval_trans (regSpineEval_step walkInternal_spine_60 rfl (by decide) subEval_405) <|
     regSpineEval_step walkInternal_spine_61 rfl (by decide) subEval_298) ?_
  intro pl np s
  simp only [wffStateToRegs, reg298Op, reg299Op, reg121Op, rpnB6aCheck2, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    List.set_cons_zero, List.set_cons_succ, Nat.zero_add]
  split_ifs <;> rfl

/-! ### 20-Clause Sequence (`rpnWadeAllClausesOp`) and `wffSpineEval_13_133` -/

def rpnWadeClauseDET (s : WffState) : WffState :=
  rpnSelect (rpnDetCheck (rpnWim (rpnPar1 (rpnPar3 (rpnCparam2 (rpnCparam3 s))))))

def rpnWadeClauseB6a (s : WffState) : WffState :=
  let s1 :=
    rpnWim (rpnWal (rpnWeq (rpnPar2 (rpnPar1 (rpnPar3 (rpnWeq (rpnPar2 (rpnPar1 s))))))))
  let s2 :=
    rpnWa (rpnWim (rpnWal (rpnWel (rpnPar2 (rpnPar1 (rpnPar3 (rpnWel (rpnPar2 (rpnPar1 s1)))))))))
  rpnSelect (rpnB6aCheck2 (rpnB6aCheck1 s2))

def rpnWadeAllClausesOp (s : WffState) : WffState :=
  let s0 := rpnVk 0 s
  rpnClauseINF (rpnClauseUNI (rpnClausePOW (rpnClauseREP (rpnClauseEXT
    (rpnClauseB8c (rpnClauseB8b (rpnClauseB8a (rpnClauseB7 (rpnClauseB6c
      (rpnClauseB6b (rpnWadeClauseB6a (rpnClauseB8b (rpnClauseB6b (rpnClauseB4
        (rpnClauseB3 (rpnClauseB2 (rpnClauseB1 (rpnClauseGEN (rpnWadeClauseDET s0)))))))))))))))))))

def rpnWadeAllClauses (top stk ac p1 p2 p3 : ℕ) : WffState :=
  rpnWadeAllClausesOp ⟨top, stk, ac, p1, p2, p3⟩
abbrev wffSpineOp_13_24 (s : WffState) : WffState :=
  let s1 := rpnPar3 (rpnCparam2 (rpnCparam3 ((rpnVk 0) (s))))
  rpnCparam3 (rpnSelect (rpnDetCheck (wffOp_312 (s1))))
theorem wffSpineEval_13_24 : WffSpineEval 13 24 wffSpineOp_13_24 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_13 rfl (by decide) wffSubEval_343) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_14 rfl (by decide) wffSubEval_108) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_15 rfl (by decide) wffSubEval_106) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_16 rfl (by decide) wffSubEval_341) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_17 rfl (by decide) wffSubEval_312) <|
  wffSpineEval_trans wffSpineEval_18_22 <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_22 rfl (by decide) wffSubEval_344) <|
  (wffSpineEval_step walkInternal_spine_23 rfl (by decide) wffSubEval_108)
abbrev wffSpineOp_24_32 (s : WffState) : WffState :=
  wffOp_295 (wffOp_311 (rpnPar1 (wffOp_311 (rpnPar2 (rpnWim (wffOp_306 (wffOp_296 (s))))))))
theorem wffSpineEval_24_32 : WffSpineEval 24 32 wffSpineOp_24_32 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_24 rfl (by decide) wffSubEval_296) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_25 rfl (by decide) wffSubEval_306) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_26 rfl (by decide) wffSubEval_429) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_27 rfl (by decide) wffSubEval_339) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_28 rfl (by decide) wffSubEval_311) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_29 rfl (by decide) wffSubEval_337) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_30 rfl (by decide) wffSubEval_311) <|
  (wffSpineEval_step walkInternal_spine_31 rfl (by decide) wffSubEval_295)
abbrev wffSpineOp_32_40 (s : WffState) : WffState :=
  wffOp_311 (wffOp_287 (rpnPar2 (rpnWn (wffOp_294 (rpnPar1 (wffOp_312 (rpnWn (s))))))))
theorem wffSpineEval_32_40 : WffSpineEval 32 40 wffSpineOp_32_40 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_32 rfl (by decide) wffSubEval_431) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_33 rfl (by decide) wffSubEval_312) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_34 rfl (by decide) wffSubEval_337) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_35 rfl (by decide) wffSubEval_294) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_36 rfl (by decide) wffSubEval_431) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_37 rfl (by decide) wffSubEval_339) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_38 rfl (by decide) wffSubEval_287) <|
  (wffSpineEval_step walkInternal_spine_39 rfl (by decide) wffSubEval_311)
abbrev wffSpineOp_40_48 (s : WffState) : WffState :=
  wffOp_264 (wffOp_272 (rpnWim (rpnWim (wffOp_296 (rpnWal (wffOp_321 (rpnWal (s))))))))
theorem wffSpineEval_40_48 : WffSpineEval 40 48 wffSpineOp_40_48 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_40 rfl (by decide) wffSubEval_364) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_41 rfl (by decide) wffSubEval_321) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_42 rfl (by decide) wffSubEval_364) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_43 rfl (by decide) wffSubEval_296) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_44 rfl (by decide) wffSubEval_429) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_45 rfl (by decide) wffSubEval_429) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_46 rfl (by decide) wffSubEval_272) <|
  (wffSpineEval_step walkInternal_spine_47 rfl (by decide) wffSubEval_264)
abbrev wffSpineOp_48_56 (s : WffState) : WffState :=
  rpnWa (wffOp_313 (wffOp_297 (rpnPar3 (wffOp_297 (wffOp_313 (rpnWeq (rpnPar2 (s))))))))
theorem wffSpineEval_48_56 : WffSpineEval 48 56 wffSpineOp_48_56 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_48 rfl (by decide) wffSubEval_339) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_49 rfl (by decide) wffSubEval_368) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_50 rfl (by decide) wffSubEval_313) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_51 rfl (by decide) wffSubEval_297) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_52 rfl (by decide) wffSubEval_341) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_53 rfl (by decide) wffSubEval_297) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_54 rfl (by decide) wffSubEval_313) <|
  (wffSpineEval_step walkInternal_spine_55 rfl (by decide) wffSubEval_362)
abbrev wffSpineOp_56_68 (s : WffState) : WffState :=
  rpnWeq (wffOp_286 (rpnPar2 (wffOp_315 (wffOp_286 (wffOp_272 (rpnB6aCheck2 (rpnB6aCheck1 (s))))))))
theorem wffSpineEval_56_68 : WffSpineEval 56 68 wffSpineOp_56_68 :=
  wffSpineEval_trans wffSpineEval_56_59 <|
  wffSpineEval_trans wffSpineEval_59_62 <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_62 rfl (by decide) wffSubEval_272) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_63 rfl (by decide) wffSubEval_286) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_64 rfl (by decide) wffSubEval_315) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_65 rfl (by decide) wffSubEval_339) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_66 rfl (by decide) wffSubEval_286) <|
  (wffSpineEval_step walkInternal_spine_67 rfl (by decide) wffSubEval_368)
abbrev wffSpineOp_68_76 (s : WffState) : WffState :=
  rpnPar3 (rpnWel (wffOp_264 (wffOp_322 (wffOp_324 (rpnWeq (wffOp_283 (rpnWex (s))))))))
theorem wffSpineEval_68_76 : WffSpineEval 68 76 wffSpineOp_68_76 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_68 rfl (by decide) wffSubEval_370) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_69 rfl (by decide) wffSubEval_283) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_70 rfl (by decide) wffSubEval_368) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_71 rfl (by decide) wffSubEval_324) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_72 rfl (by decide) wffSubEval_322) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_73 rfl (by decide) wffSubEval_264) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_74 rfl (by decide) wffSubEval_366) <|
  (wffSpineEval_step walkInternal_spine_75 rfl (by decide) wffSubEval_341)
abbrev wffSpineOp_76_84 (s : WffState) : WffState :=
  wffOp_304 (wffOp_288 (rpnWel (wffOp_314 ((rpnVk 2) (wffOp_305 (rpnWel (rpnPar2 (s))))))))
theorem wffSpineEval_76_84 : WffSpineEval 76 84 wffSpineOp_76_84 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_76 rfl (by decide) wffSubEval_339) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_77 rfl (by decide) wffSubEval_366) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_78 rfl (by decide) wffSubEval_305) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_79 rfl (by decide) wffSubEval_359) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_80 rfl (by decide) wffSubEval_314) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_81 rfl (by decide) wffSubEval_366) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_82 rfl (by decide) wffSubEval_288) <|
  (wffSpineEval_step walkInternal_spine_83 rfl (by decide) wffSubEval_304)
abbrev wffSpineOp_84_92 (s : WffState) : WffState :=
  wffOp_308 (wffOp_316 ((rpnVk 3) (rpnSelect (wffOp_300 ((rpnVk 0) (wffOp_291 (wffOp_314 (s))))))))
theorem wffSpineEval_84_92 : WffSpineEval 84 92 wffSpineOp_84_92 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_84 rfl (by decide) wffSubEval_314) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_85 rfl (by decide) wffSubEval_291) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_86 rfl (by decide) wffSubEval_343) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_87 rfl (by decide) wffSubEval_300) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_88 rfl (by decide) wffSubEval_344) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_89 rfl (by decide) wffSubEval_360) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_90 rfl (by decide) wffSubEval_316) <|
  (wffSpineEval_step walkInternal_spine_91 rfl (by decide) wffSubEval_308)
abbrev wffSpineOp_92_100 (s : WffState) : WffState :=
  rpnWim (wffOp_277 (wffOp_290 ((rpnVk 1) (rpnWal (wffOp_315 (wffOp_300 ((rpnVk 2) (s))))))))
theorem wffSpineEval_92_100 : WffSpineEval 92 100 wffSpineOp_92_100 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_92 rfl (by decide) wffSubEval_359) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_93 rfl (by decide) wffSubEval_300) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_94 rfl (by decide) wffSubEval_315) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_95 rfl (by decide) wffSubEval_364) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_96 rfl (by decide) wffSubEval_358) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_97 rfl (by decide) wffSubEval_290) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_98 rfl (by decide) wffSubEval_277) <|
  (wffSpineEval_step walkInternal_spine_99 rfl (by decide) wffSubEval_429)
abbrev wffSpineOp_100_108 (s : WffState) : WffState :=
  wffOp_317 ((rpnVk 3) (wffOp_316 (wffOp_320 (wffOp_315 (rpnWa (wffOp_288 (wffOp_277 (s))))))))
theorem wffSpineEval_100_108 : WffSpineEval 100 108 wffSpineOp_100_108 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_100 rfl (by decide) wffSubEval_277) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_101 rfl (by decide) wffSubEval_288) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_102 rfl (by decide) wffSubEval_362) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_103 rfl (by decide) wffSubEval_315) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_104 rfl (by decide) wffSubEval_320) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_105 rfl (by decide) wffSubEval_316) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_106 rfl (by decide) wffSubEval_360) <|
  (wffSpineEval_step walkInternal_spine_107 rfl (by decide) wffSubEval_317)
abbrev wffSpineOp_108_116 (s : WffState) : WffState :=
  wffOp_318 (wffOp_289 ((rpnVk 3) (wffOp_317 ((rpnVk 2) (wffOp_280 (wffOp_319 (wffOp_289 (s))))))))
theorem wffSpineEval_108_116 : WffSpineEval 108 116 wffSpineOp_108_116 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_108 rfl (by decide) wffSubEval_289) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_109 rfl (by decide) wffSubEval_319) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_110 rfl (by decide) wffSubEval_280) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_111 rfl (by decide) wffSubEval_359) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_112 rfl (by decide) wffSubEval_317) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_113 rfl (by decide) wffSubEval_360) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_114 rfl (by decide) wffSubEval_289) <|
  (wffSpineEval_step walkInternal_spine_115 rfl (by decide) wffSubEval_318)
abbrev wffSpineOp_116_124 (s : WffState) : WffState :=
  rpnWel (wffOp_316 ((rpnVk 1) (wffOp_290 (wffOp_301 ((rpnVk 0) (wffOp_301 (wffOp_280 (s))))))))
theorem wffSpineEval_116_124 : WffSpineEval 116 124 wffSpineOp_116_124 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_116 rfl (by decide) wffSubEval_280) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_117 rfl (by decide) wffSubEval_301) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_118 rfl (by decide) wffSubEval_343) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_119 rfl (by decide) wffSubEval_301) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_120 rfl (by decide) wffSubEval_290) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_121 rfl (by decide) wffSubEval_358) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_122 rfl (by decide) wffSubEval_316) <|
  (wffSpineEval_step walkInternal_spine_123 rfl (by decide) wffSubEval_366)
abbrev wffSpineOp_124_132 (s : WffState) : WffState :=
  wffOp_318 (wffOp_319 (wffOp_318 (wffOp_291 (wffOp_316 (wffOp_302 (rpnWim (wffOp_302 (s))))))))
theorem wffSpineEval_124_132 : WffSpineEval 124 132 wffSpineOp_124_132 :=
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_124 rfl (by decide) wffSubEval_302) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_125 rfl (by decide) wffSubEval_429) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_126 rfl (by decide) wffSubEval_302) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_127 rfl (by decide) wffSubEval_316) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_128 rfl (by decide) wffSubEval_291) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_129 rfl (by decide) wffSubEval_318) <|
  wffSpineEval_trans (wffSpineEval_step walkInternal_spine_130 rfl (by decide) wffSubEval_319) <|
  (wffSpineEval_step walkInternal_spine_131 rfl (by decide) wffSubEval_318)
abbrev wffSpineOp_132_133 (s : WffState) : WffState :=
  rpnSelect (s)
theorem wffSpineEval_132_133 : WffSpineEval 132 133 wffSpineOp_132_133 :=
  (wffSpineEval_step walkInternal_spine_132 rfl (by decide) wffSubEval_344)
theorem wffSpineEval_13_133 : WffSpineEval 13 133 rpnWadeAllClausesOp :=
  wffSpineEval_trans wffSpineEval_13_24 <|
  wffSpineEval_trans wffSpineEval_24_32 <|
  wffSpineEval_trans wffSpineEval_32_40 <|
  wffSpineEval_trans wffSpineEval_40_48 <|
  wffSpineEval_trans wffSpineEval_48_56 <|
  wffSpineEval_trans wffSpineEval_56_68 <|
  wffSpineEval_trans wffSpineEval_68_76 <|
  wffSpineEval_trans wffSpineEval_76_84 <|
  wffSpineEval_trans wffSpineEval_84_92 <|
  wffSpineEval_trans wffSpineEval_92_100 <|
  wffSpineEval_trans wffSpineEval_100_108 <|
  wffSpineEval_trans wffSpineEval_108_116 <|
  wffSpineEval_trans wffSpineEval_116_124 <|
  wffSpineEval_trans wffSpineEval_124_132 <|
  wffSpineEval_132_133
/-! ## 4. Unpair Header (`k = 0..13`) and Full Spine Body (`k = 0..133`) -/

/-- Register invariant at the start of each `main()` iteration (`stack = []`):
11 registers with scratch registers `8, 9, 10` cleared to `0`. -/
def RegsInv (regs : List ℕ) : Prop :=
  regs.length = 11 ∧ regs.getD 8 0 = 0 ∧ regs.getD 9 0 = 0 ∧ regs.getD 10 0 = 0

theorem regsInv_init : RegsInv zfRegInit.regs :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem regs_eq_of_regsInv {regs : List ℕ} (hInv : RegsInv regs) :
    regs = [regs.getD 0 0, regs.getD 1 0, regs.getD 2 0, regs.getD 3 0,
            regs.getD 4 0, regs.getD 5 0, regs.getD 6 0, regs.getD 7 0, 0, 0, 0] := by
  rcases hInv with ⟨hlen, h8, h9, h10⟩
  rcases regs with _ | ⟨r0, _ | ⟨r1, _ | ⟨r2, _ | ⟨r3, _ | ⟨r4, _ | ⟨r5, _ |
    ⟨r6, _ | ⟨r7, _ | ⟨r8, _ | ⟨r9, _ | ⟨r10, _ | _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    try (simp at hlen; done)
  dsimp [List.getD] at h8 h9 h10
  subst h8 h9 h10
  rfl

def regHeader05Op (regs : List ℕ) : List ℕ :=
  ((((reg122Op regs).set 4 0).set 5 0).set 6 0).set 7 0

theorem regSpineEval_0_5 : RegSpineEval 0 5 regHeader05Op :=
  regSpineEval_trans (regSpineEval_step walkInternal_spine_0 rfl (by decide) subEval_122) <|
  regSpineEval_trans (regSpineEval_step walkInternal_spine_1 rfl (by decide) subEval_381) <|
  regSpineEval_trans (regSpineEval_step walkInternal_spine_2 rfl (by decide) subEval_385) <|
  regSpineEval_trans (regSpineEval_step walkInternal_spine_3 rfl (by decide) subEval_391) <|
  regSpineEval_step walkInternal_spine_4 rfl (by decide) subEval_395

theorem regHeader05Op_eval (pl np top stk ac0 p1_0 p2_0 p3_0 : ℕ) :
    regHeader05Op [pl, np, top, stk, ac0, p1_0, p2_0, p3_0, 0, 0, 0] =
      [if pl = 0 then np else pl - 1, if pl = 0 then np + 1 else np,
       top, stk, 0, 0, 0, 0, 0, 0, 0] := by
  by_cases hpl : pl = 0 <;>
    simp [regHeader05Op, reg122Op, reg124Op, hpl, List.getD]

def regUnpairMoveOp (r : ℕ) (regs : List ℕ) : List ℕ :=
  let u := reg310Op regs
  (u.set 8 0).set r (u.getD r 0 + u.getD 8 0)

theorem regSpineEval_5_7 : RegSpineEval 5 7 (regUnpairMoveOp 4) :=
  regSpineEval_trans (regSpineEval_step walkInternal_spine_5 rfl (by decide) subEval_310) <|
  regSpineEval_step walkInternal_spine_6 rfl (by decide) subEval_399

theorem regSpineEval_7_9 : RegSpineEval 7 9 (regUnpairMoveOp 5) :=
  regSpineEval_trans (regSpineEval_step walkInternal_spine_7 rfl (by decide) subEval_310) <|
  regSpineEval_step walkInternal_spine_8 rfl (by decide) subEval_403

theorem regSpineEval_9_11 : RegSpineEval 9 11 (regUnpairMoveOp 6) :=
  regSpineEval_trans (regSpineEval_step walkInternal_spine_9 rfl (by decide) subEval_310) <|
  regSpineEval_step walkInternal_spine_10 rfl (by decide) subEval_405

theorem regSpineEval_11_13 : RegSpineEval 11 13 (regUnpairMoveOp 7) :=
  regSpineEval_trans (regSpineEval_step walkInternal_spine_11 rfl (by decide) subEval_310) <|
  regSpineEval_step walkInternal_spine_12 rfl (by decide) subEval_407

theorem regSpineEval_0_13 :
    RegSpineEval 0 13 (fun regs =>
      regUnpairMoveOp 7 (regUnpairMoveOp 6 (regUnpairMoveOp 5
        (regUnpairMoveOp 4 (regHeader05Op regs))))) :=
  regSpineEval_trans regSpineEval_0_5 <|
  regSpineEval_trans regSpineEval_5_7 <|
  regSpineEval_trans regSpineEval_7_9 <|
  regSpineEval_trans regSpineEval_9_11 <|
  regSpineEval_11_13

/-- Complete evaluation of the unpair header (`main().0` through `main().12`, `k = 0..13`). -/
theorem unpair_header_eval {regs : List ℕ} (hInv : RegsInv regs) :
    let prooflist₁ := if regs.getD 0 0 = 0 then regs.getD 1 0 else regs.getD 0 0 - 1
    let nextproof' := if regs.getD 0 0 = 0 then regs.getD 1 0 + 1 else regs.getD 1 0
    let u1 := cantorUnpair prooflist₁
    let ac := u1.1
    let u2 := cantorUnpair u1.2
    let p1 := u2.1
    let u3 := cantorUnpair u2.2
    let p2 := u3.1
    let u4 := cantorUnpair u3.2
    let p3 := u4.1
    let prooflist' := u4.2
    ∃ s ≥ 1, zfReg11NSteps s ⟨[], regs⟩ =
      some ⟨List.replicate 13 1,
        wffStateToRegs prooflist' nextproof' ⟨regs.getD 2 0, regs.getD 3 0, ac, p1, p2, p3⟩⟩ := by
  intro prooflist₁ nextproof' u1 ac u2 p1 u3 p2 u4 p3 prooflist'
  obtain ⟨s, hs, hsteps, _⟩ := regSpineEval_0_13 regs hInv.1
  dsimp only [List.replicate] at hsteps
  have h05 : regHeader05Op regs =
      [prooflist₁, nextproof', regs.getD 2 0, regs.getD 3 0, 0, 0, 0, 0, 0, 0, 0] := by
    conv_lhs => rw [regs_eq_of_regsInv hInv]
    exact regHeader05Op_eval _ _ _ _ _ _ _ _
  rw [h05] at hsteps
  simp only [regUnpairMoveOp, reg310Op_eval, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.set_cons_zero, List.set_cons_succ,
    Nat.zero_add] at hsteps
  exact ⟨s, hs, hsteps⟩

/-- Complete evaluation of the main spine body (`k = 0..133`), combining `unpair_header_eval`
(`k = 0..13`) and `wffSpineEval_13_133` (`k = 13..133`). -/
theorem spine_0_133_eval {regs : List ℕ} (hInv : RegsInv regs) :
    let prooflist₁ := if regs.getD 0 0 = 0 then regs.getD 1 0 else regs.getD 0 0 - 1
    let nextproof' := if regs.getD 0 0 = 0 then regs.getD 1 0 + 1 else regs.getD 1 0
    let u1 := cantorUnpair prooflist₁
    let ac := u1.1
    let u2 := cantorUnpair u1.2
    let p1 := u2.1
    let u3 := cantorUnpair u2.2
    let p2 := u3.1
    let u4 := cantorUnpair u3.2
    let p3 := u4.1
    let prooflist' := u4.2
    let out := rpnWadeAllClauses (regs.getD 2 0) (regs.getD 3 0) ac p1 p2 p3
    ∃ s ≥ 1, zfReg11NSteps s ⟨[], regs⟩ =
      some ⟨List.replicate 133 1, wffStateToRegs prooflist' nextproof' out⟩ := by
  intro prooflist₁ nextproof' u1 ac u2 p1 u3 p2 u4 p3 prooflist' out
  obtain ⟨s₁, hs₁, hsteps₁⟩ := unpair_header_eval hInv
  obtain ⟨s₂, hs₂, hsteps₂⟩ :=
    wffSpineEval_13_133 prooflist' nextproof' ⟨regs.getD 2 0, regs.getD 3 0, ac, p1, p2, p3⟩
  exact ⟨s₁ + s₂, by omega, zfReg11NSteps_bind_eq hsteps₁ hsteps₂⟩
/-! ## 5. Halt Check at Spine End (`k = 133, 134`) & Main-Loop Simulation -/
theorem refTrans_165_0 : refTrans 165 0 = some (0, .right, 67) := rfl
theorem refTrans_165_1 : refTrans 165 1 = some (1, .right, 166) := rfl

theorem refTrans_166_0 : refTrans 166 0 = some (0, .right, 167) := rfl
theorem refTrans_166_1 : refTrans 166 1 = none := rfl

theorem refTrans_167_0 : refTrans 167 0 = some (0, .right, 67) := rfl
theorem refTrans_167_1 : refTrans 167 1 = some (1, .right, 168) := rfl

theorem refTrans_168_0 : refTrans 168 0 = some (0, .right, 169) := rfl
theorem refTrans_168_1 : refTrans 168 1 = some (0, .left, 90) := rfl

theorem refTrans_169_0 : refTrans 169 0 = some (0, .right, 68) := rfl
theorem refTrans_169_1 : refTrans 169 1 = some (1, .right, 68) := rfl

theorem evalStack_spine_133 :
    evalStack (List.replicate 133 1) = .decnz 2 (List.replicate 134 1) [] := by
  have h := evalStack_leaf0_of_walkInternal walkInternal_spine_133 refTrans_165_0
    (by decide) (by decide)
  rw [← List.replicate_succ', retStack_replicate_one] at h
  exact h

theorem evalStack_spine_134 :
    evalStack (List.replicate 134 1) =
      .decnz 2 (List.replicate 134 1 ++ [0] ++ [1]) (List.replicate 135 1) := by
  have h167 : walkInternal 126 (List.replicate 134 1 ++ [0]) = some 167 :=
    walkInternal_snoc walkInternal_spine_134 refTrans_166_0 (by decide)
  have htrim := evalStack_trimZeros_of_walkInternal h167
  rw [trimZeros_append_zero, trimZeros_replicate_one] at htrim
  have h := evalStack_leaf0_of_walkInternal h167 refTrans_167_0 (by decide) (by decide)
  rw [retStack_append_zero, ← List.replicate_succ'] at h
  rw [htrim]
  exact h

theorem evalStack_spine_135 :
    evalStack (List.replicate 135 1) = .halt := by decide

theorem subEval_169 :
    SubEval 169 (fun regs => regs.set 2 (regs.getD 2 0 + 2)) := by
  refine (subEval_inc_inc refTrans_169_0 (by decide) (by decide) rfl
    refTrans_169_1 (by decide) (by decide) rfl).congr ?_
  intro regs hlen
  change (regs.set 2 (regs.getD 2 0 + 1)).set 2
    ((regs.set 2 (regs.getD 2 0 + 1)).getD 2 0 + 1) = regs.set 2 (regs.getD 2 0 + 2)
  rw [getD_set_self regs 2 (regs.getD 2 0 + 1) (by omega), List.set_set]

theorem evalStack_168_break :
    evalStack (List.replicate 134 1 ++ [0] ++ [1] ++ [1]) = .jump [] := by
  have h167 : walkInternal 126 (List.replicate 134 1 ++ [0]) = some 167 :=
    walkInternal_snoc walkInternal_spine_134 refTrans_166_0 (by decide)
  have h168 : walkInternal 126 (List.replicate 134 1 ++ [0] ++ [1]) = some 168 :=
    walkInternal_snoc h167 refTrans_167_1 (by decide)
  have hev := evalStack_break1_of_walkInternal (k := 1) (by decide) h168 refTrans_168_1
  have hpop :
      (popBreakRev 1 (List.replicate 134 (1 : Fin 2) ++ [0] ++ [1]).reverse).reverse = [] := by
    decide
  rw [hev, hpop]

/-- Halt check at the end of `main()` (`main().133` and `main().134`, states `165..169`):
- If `regs.getD 2 0 = 1` (`topwff = 1`), `zfReg11Step` halts in 2 steps at `List.replicate 135 1`.
- If `regs.getD 2 0 ≠ 1` (`topwff ≠ 1`), `zfReg11Step` returns to the loop head `⟨[], regs⟩`
  with all registers restored. -/
theorem halt_check_eval (regs : List ℕ) (hlen : regs.length = 11) :
    (regs.getD 2 0 = 1 →
      ∃ s ch, zfReg11NSteps s ⟨List.replicate 133 1, regs⟩ = some ch ∧ zfReg11Step ch = none) ∧
    (regs.getD 2 0 ≠ 1 →
      ∃ s ≥ 1, zfReg11NSteps s ⟨List.replicate 133 1, regs⟩ = some ⟨[], regs⟩) := by
  constructor
  · intro h1
    have hstep1 : zfReg11Step ⟨List.replicate 133 1, regs⟩ =
        some ⟨List.replicate 134 1, regs.set 2 0⟩ :=
      zfReg11Step_of_decnz_succ evalStack_spine_133 h1
    have hz : (regs.set 2 0).getD 2 0 = 0 := getD_set_self regs 2 0 (by omega)
    have hstep2 : zfReg11Step ⟨List.replicate 134 1, regs.set 2 0⟩ =
        some ⟨List.replicate 135 1, regs.set 2 0⟩ :=
      zfReg11Step_of_decnz_zero evalStack_spine_134 hz
    have hhalt : zfReg11Step ⟨List.replicate 135 1, regs.set 2 0⟩ = none := by
      unfold zfReg11Step; dsimp only; rw [evalStack_spine_135]
    exact ⟨2, ⟨List.replicate 135 1, regs.set 2 0⟩,
      step_zfReg11NSteps hstep1 (zfReg11Step_one hstep2), hhalt⟩
  · intro hne1
    rcases hv : regs.getD 2 0 with _ | _ | v
    · have hstep1 : zfReg11Step ⟨List.replicate 133 1, regs⟩ = some ⟨[], regs⟩ :=
        zfReg11Step_of_decnz_zero evalStack_spine_133 hv
      exact ⟨1, le_refl 1, zfReg11Step_one hstep1⟩
    · exact absurd hv hne1
    · have hstep1 : zfReg11Step ⟨List.replicate 133 1, regs⟩ =
          some ⟨List.replicate 134 1, regs.set 2 (v + 1)⟩ :=
        zfReg11Step_of_decnz_succ evalStack_spine_133 hv
      have hv1 : (regs.set 2 (v + 1)).getD 2 0 = v + 1 :=
        getD_set_self regs 2 (v + 1) (by omega)
      have hstep2 : zfReg11Step ⟨List.replicate 134 1, regs.set 2 (v + 1)⟩ =
          some ⟨List.replicate 134 1 ++ [0] ++ [1], (regs.set 2 (v + 1)).set 2 v⟩ :=
        zfReg11Step_of_decnz_succ evalStack_spine_134 hv1
      rw [List.set_set] at hstep2
      have h167 : walkInternal 126 (List.replicate 134 1 ++ [0]) = some 167 :=
        walkInternal_snoc walkInternal_spine_134 refTrans_166_0 (by decide)
      have h168 : walkInternal 126 (List.replicate 134 1 ++ [0] ++ [1]) = some 168 :=
        walkInternal_snoc h167 refTrans_167_1 (by decide)
      have h169 : walkInternal 126 (List.replicate 134 1 ++ [0] ++ [1] ++ [0]) = some 169 :=
        walkInternal_snoc h168 refTrans_168_0 (by decide)
      obtain ⟨s₃, hs₃, hsteps3, _⟩ :=
        subEval_169 (List.replicate 134 1 ++ [0] ++ [1] ++ [0]) h169
          (regs.set 2 v) (by simp [hlen])
      rw [trimZeros_append_zero, trimZeros_append_one, retStack_append_zero] at hsteps3
      dsimp only at hsteps3
      rw [getD_set_self regs 2 v (by omega), List.set_set, set_eq_self_of_getD_eq hv] at hsteps3
      have hstep4 : zfReg11Step ⟨List.replicate 134 1 ++ [0] ++ [1] ++ [1], regs⟩ =
          some ⟨[], regs⟩ :=
        zfReg11Step_of_jump evalStack_168_break
      have hchain :=
        step_zfReg11NSteps hstep1
          (step_zfReg11NSteps hstep2
            (zfReg11NSteps_bind_eq hsteps3 (zfReg11Step_one hstep4)))
      exact ⟨s₃ + 1 + 1 + 1, by omega, hchain⟩

/-! ## 3. Full Main-Loop Simulation (`zfRegHalts_iff_mainLoopHalts_of_body`) -/

theorem zfReg11NSteps_of_halt {c : ZfRegCfg} (h : zfReg11Step c = none) {k : ℕ} (hk : 1 ≤ k) :
    zfReg11NSteps k c = none := by
  cases k with
  | zero => omega
  | succ k => simp [zfReg11NSteps_succ, h]

/-- Single full iteration of `main()` (combining `hBody` and `halt_check_eval`):
either `zfMainStep (regsToMainCfg regs) = none` and `zfReg11Step` halts from `⟨[], regs⟩`,
or `zfMainStep (regsToMainCfg regs) = some c'` and `zfReg11Step` reaches `⟨[], regs'⟩` in
`s ≥ 1` steps with `RegsInv regs'` and `regsToMainCfg regs' = c'`. -/
theorem main_iter_sim
    (hBody : ∀ regs : List ℕ, RegsInv regs →
      ∃ s ≥ 1, ∃ regs' : List ℕ,
        zfReg11NSteps s ⟨[], regs⟩ = some ⟨List.replicate 133 1, regs'⟩ ∧
        RegsInv regs' ∧
        regsToMainCfg regs' = zfMainNext (regsToMainCfg regs))
    {regs : List ℕ} (hInv : RegsInv regs) :
    match zfMainStep (regsToMainCfg regs) with
    | none =>
      ∃ s ch, zfReg11NSteps s ⟨[], regs⟩ = some ch ∧ zfReg11Step ch = none
    | some c' =>
      ∃ s ≥ 1, ∃ regs' : List ℕ,
        zfReg11NSteps s ⟨[], regs⟩ = some ⟨[], regs'⟩ ∧
        RegsInv regs' ∧
        regsToMainCfg regs' = c' := by
  obtain ⟨s₁, hs₁, regs', hsteps₁, hInv', hnext⟩ := hBody regs hInv
  have htop_eq : (zfMainNext (regsToMainCfg regs)).topwff = regs'.getD 2 0 := by
    rw [← hnext]; rfl
  have hhalt := halt_check_eval regs' hInv'.1
  unfold zfMainStep
  by_cases h1 : (zfMainNext (regsToMainCfg regs)).topwff = 1
  · simp only [h1, ↓reduceIte]
    rw [htop_eq] at h1
    obtain ⟨s₂, ch, hsteps₂, hnone⟩ := hhalt.1 h1
    exact ⟨s₁ + s₂, ch, zfReg11NSteps_bind_eq hsteps₁ hsteps₂, hnone⟩
  · simp only [h1, ↓reduceIte]
    rw [htop_eq] at h1
    obtain ⟨s₂, hs₂, hsteps₂⟩ := hhalt.2 h1
    exact ⟨s₁ + s₂, by omega, regs', zfReg11NSteps_bind_eq hsteps₁ hsteps₂, hInv', hnext⟩

/-- Multi-step forward simulation of `zfMainNSteps` by `zfReg11NSteps`. -/
theorem zfMainNSteps_sim
    (hBody : ∀ regs : List ℕ, RegsInv regs →
      ∃ s ≥ 1, ∃ regs' : List ℕ,
        zfReg11NSteps s ⟨[], regs⟩ = some ⟨List.replicate 133 1, regs'⟩ ∧
        RegsInv regs' ∧
        regsToMainCfg regs' = zfMainNext (regsToMainCfg regs)) :
    ∀ (n : ℕ) {regs : List ℕ} {c_end : ZfMainCfg},
      RegsInv regs →
      zfMainNSteps n (regsToMainCfg regs) = some c_end →
      ∃ s regs_end,
        zfReg11NSteps s ⟨[], regs⟩ = some ⟨[], regs_end⟩ ∧
        RegsInv regs_end ∧
        regsToMainCfg regs_end = c_end := by
  intro n
  induction n with
  | zero =>
    intro regs c_end hInv hn
    injection hn with hn'
    subst hn'
    exact ⟨0, regs, rfl, hInv, rfl⟩
  | succ n ih =>
    intro regs c_end hInv hn
    unfold zfMainNSteps at hn
    have hiter := main_iter_sim hBody hInv
    rcases hs : zfMainStep (regsToMainCfg regs) with _ | c₁
    · rw [hs] at hn; cases hn
    · rw [hs] at hiter
      rw [hs, Option.bind_some] at hn
      obtain ⟨s₁, _, regs₁, hsteps₁, hInv₁, hc₁⟩ := hiter
      rw [← hc₁] at hn
      obtain ⟨s₂, regs_end, hsteps₂, hInv_end, hc_end⟩ := ih hInv₁ hn
      exact ⟨s₁ + s₂, regs_end, zfReg11NSteps_bind_eq hsteps₁ hsteps₂, hInv_end, hc_end⟩

/-- Backward simulation by strong induction on the step count `N` of `zfReg11NSteps`. -/
theorem mainLoopHalts_of_zfReg11NSteps_halt
    (hBody : ∀ regs : List ℕ, RegsInv regs →
      ∃ s ≥ 1, ∃ regs' : List ℕ,
        zfReg11NSteps s ⟨[], regs⟩ = some ⟨List.replicate 133 1, regs'⟩ ∧
        RegsInv regs' ∧
        regsToMainCfg regs' = zfMainNext (regsToMainCfg regs)) :
    ∀ (N : ℕ) {regs : List ℕ} {ch : ZfRegCfg},
      RegsInv regs →
      zfReg11NSteps N ⟨[], regs⟩ = some ch →
      zfReg11Step ch = none →
      ∃ n cm, zfMainNSteps n (regsToMainCfg regs) = some cm ∧ zfMainStep cm = none := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro regs ch hInv hN hnone
    have hiter := main_iter_sim hBody hInv
    rcases hs : zfMainStep (regsToMainCfg regs) with _ | c'
    · exact ⟨0, regsToMainCfg regs, rfl, hs⟩
    · rw [hs] at hiter
      obtain ⟨s, hs_pos, regs', hsteps, hInv', hc'⟩ := hiter
      have hle : s ≤ N := by
        by_contra hlt
        have hgt : 1 ≤ s - N := by omega
        have hsplit : s = N + (s - N) := by omega
        rw [hsplit, zfReg11NSteps_add, hN, Option.bind_some,
          zfReg11NSteps_of_halt hnone hgt] at hsteps
        cases hsteps
      have hsplit : N = s + (N - s) := by omega
      rw [hsplit, zfReg11NSteps_add, hsteps, Option.bind_some] at hN
      obtain ⟨n, cm, hn, hcm_none⟩ := ih (N - s) (by omega) hInv' hN hnone
      rw [hc'] at hn
      exact ⟨n + 1, cm, by simp [zfMainNSteps, hs, hn], hcm_none⟩

/-- Complete halting equivalence between `ZfRegHalts` and `MainLoopHalts` given the single-iteration
spine body theorem `hBody`. -/
theorem zfRegHalts_iff_mainLoopHalts_of_body
    (hBody : ∀ regs : List ℕ, RegsInv regs →
      ∃ s ≥ 1, ∃ regs' : List ℕ,
        zfReg11NSteps s ⟨[], regs⟩ = some ⟨List.replicate 133 1, regs'⟩ ∧
        RegsInv regs' ∧
        regsToMainCfg regs' = zfMainNext (regsToMainCfg regs)) :
    ZfRegHalts ↔ MainLoopHalts := by
  rw [zfRegHalts_iff_exists_zfReg11NSteps, mainLoopHalts_iff_exists_zfMainNSteps]
  have hInit_cfg : regsToMainCfg zfRegInit.regs = zfMainInit := rfl
  constructor
  · rintro ⟨N, ch, hN, hnone⟩
    obtain ⟨n, cm, hn, hcm_none⟩ :=
      mainLoopHalts_of_zfReg11NSteps_halt hBody N regsInv_init hN hnone
    rw [hInit_cfg] at hn
    exact ⟨n, cm, hn, hcm_none⟩
  · rintro ⟨n, cm, hn, hcm_none⟩
    rw [← hInit_cfg] at hn
    obtain ⟨s₁, regs_end, hsteps₁, hInv_end, hc_end⟩ :=
      zfMainNSteps_sim hBody n regsInv_init hn
    have hiter := main_iter_sim hBody hInv_end
    rw [hc_end, hcm_none] at hiter
    obtain ⟨s₂, ch, hsteps₂, hnone⟩ := hiter
    exact ⟨s₁ + s₂, ch, zfReg11NSteps_bind_eq hsteps₁ hsteps₂, hnone⟩


theorem rpnWadeAllClauses_eq_rpnAllClauses (top stk ac p1 p2 p3 : ℕ) :
    rpnWadeAllClauses top stk ac p1 p2 p3 = rpnAllClauses top stk ac p1 p2 p3 := rfl

theorem regsToMainCfg_wffStateToRegs (pl np : ℕ) (s : WffState) :
    regsToMainCfg (wffStateToRegs pl np s) = ⟨pl, np, s.topwff, s.wffstack⟩ := rfl

theorem regsToMainCfg_wffStateToRegs_rpnAllClauses (pl np top stk ac p1 p2 p3 : ℕ) :
    regsToMainCfg (wffStateToRegs pl np (rpnWadeAllClauses top stk ac p1 p2 p3)) =
      let res := zfClauseDispatch top stk ac p1 p2 p3
      ⟨pl, np, res.1, res.2⟩ := by
  rw [rpnWadeAllClauses_eq_rpnAllClauses, regsToMainCfg_wffStateToRegs]
  have h := rpnAllClauses_eq_zfClauseDispatch top stk ac p1 p2 p3
  dsimp only at h
  rw [Prod.mk.injEq] at h
  rw [h.1, h.2]

/-- Single-iteration main-spine evaluation from `⟨[], regs⟩` to `⟨List.replicate 133 1, regs'⟩`
bridging `spine_0_133_eval` and `rpnAllClauses_eq_zfClauseDispatch`. -/
theorem spine_body_eval (regs : List ℕ) (hInv : RegsInv regs) :
    ∃ s ≥ 1, ∃ regs' : List ℕ,
      zfReg11NSteps s ⟨[], regs⟩ = some ⟨List.replicate 133 1, regs'⟩ ∧
      RegsInv regs' ∧
      regsToMainCfg regs' = zfMainNext (regsToMainCfg regs) := by
  obtain ⟨s, hs, hsteps⟩ := spine_0_133_eval hInv
  refine ⟨s, hs, _, hsteps, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  rw [regsToMainCfg_wffStateToRegs_rpnAllClauses]
  rfl

/-- **Main Theorem of `Subroutines.lean`**: the 11-register call-stack machine `ZfRegHalts` halts
if and only if the `zf_432_wade.tm` main loop `MainLoopHalts` halts. -/
theorem zfRegHalts_iff_mainLoopHalts :
    ZfRegHalts ↔ MainLoopHalts :=
  zfRegHalts_iff_mainLoopHalts_of_body spine_body_eval

end ConjectureMachines.Semantics.Zf
