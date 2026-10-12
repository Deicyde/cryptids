/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Riemann120.Backend
public import Cryptids.Semantics.Riemann120.Program
public import Cryptids.Semantics.Riemann120.Analytic

/-!
# Lockstep Dispatcher Simulation & Top-Level RH Bridge for `riemann120`

This file proves:
1. Lockstep tree-walk & gadget simulation between `riemann121` and `rhRegStep` on
   `rhRootCfg 3821 bits regs (regsTape extra)`, yielding
   `halts_riemann121_iff_rhRegHalts : Halts riemann121 ↔ RhRegHalts`.
2. Exact alignment between `ConjectureMachines.Riemann120.Layer2` (`Program.lean`) and
   `Riemann120Analytic` (`Analytic.lean`).
3. The end-to-end halting theorem `halts_riemann120_iff_not_riemannHypothesis_of_large`.
-/

@[expose] public section

namespace ConjectureMachines.Riemann120

open Turing StateTransition ConjectureMachines
open ConjectureMachines.Riemann120.Backend
open ConjectureMachines.Riemann120.Layer2
  (RhInstr TreeOutcome walkTape outcomeToInstr evalStack
   padTo popBreakRev popContinueRev applyBreak applyContinue
   isLeafState isLeafInc leafReg leafReg_lt_5
   allValidStacks isValidStack isValidStack_nil rhRegStep_preserves_isValidStack
   RhRegCfg rhRegInit rhRegStep rhRegNSteps RhRegHalts
   mem_eval_rhRegStep_iff_rhRegNSteps
   rhRegHalts_iff_exists_shuniaCounterexample)
open ConjectureMachines.Riemann543.Layer1
  (nSteps nSteps_add nSteps_bind_eq step_nSteps step_one
   nSteps_eval_dom nSteps_of_halt mem_eval_iff_nSteps fin2_cases
   Tape.mkL append_replicate_cons append_reverse_cons
   encodeReg encodeRegs encodeRegs_append regsTape regsTape_cons)
open ConjectureMachines.Semantics.Zf.Layer1
  (rootLeft stackLeft)
open Riemann120Analytic
  (shuniaPrimorial quarterClockStep ShuniaCounterexampleExact
   shuniaCounterexampleExact_iff
   exists_shuniaCounterexampleExact_iff_not_riemannHypothesis_of_large)

set_option maxRecDepth 200000

/-!
## 1. Universal Tree-Walk Soundness and Stack Pop (`break` / `continue`) Helpers
-/

theorem step_mk'_none {q : Fin 121} {a : Fin 2}
    (h : Riemann120.rh121Trans q a = none) (L R : ListBlank (Fin 2)) :
    step riemann121 ⟨q, Tape.mk' L (R.cons a)⟩ = none := by
  simp [step, rh121Trans_eq, h, Tape.mk']

/-- Configuration during the rightward decision-DAG walk from `main.0` (`State 27`). -/
def treeWalkCfg (q : Fin 121) (walked rem : List (Fin 2))
    (L₀ R_tail : ListBlank (Fin 2)) : Cfg 121 2 :=
  ⟨q, Tape.mk' (ListBlank.append walked.reverse L₀) (ListBlank.append rem R_tail)⟩

/-- Universal Tree-Walk Soundness for `riemann121`: executes `walkTape q walked rem`
without inspecting or modifying `L₀` or `R_tail`. -/
theorem walkTape_sound (q : Fin 121) (walked rem : List (Fin 2))
    (L₀ R_tail : ListBlank (Fin 2)) :
    match walkTape q walked rem with
    | .halt q_h walked_h rem_h =>
      ∃ s, walked_h.length = walked.length + s ∧
        ∃ ch, ch = treeWalkCfg q_h walked_h rem_h L₀ R_tail ∧
          nSteps riemann121 s (treeWalkCfg q walked rem L₀ R_tail) = some ch ∧
          step riemann121 ch = none
    | .jumpLeft q' walked_j rem' =>
      (∃ b, walked_j ++ (b :: rem') = walked ++ rem) ∧
      ∃ s, 1 ≤ s ∧
        nSteps riemann121 s (treeWalkCfg q walked rem L₀ R_tail) =
          some ⟨q', Tape.mkL (ListBlank.append walked_j.reverse L₀)
            (ListBlank.append (0 :: rem') R_tail)⟩
    | .regLeaf q' walked_l rem' =>
      walked_l ++ rem' = walked ++ rem ∧
      ∃ s, 1 ≤ s ∧
        nSteps riemann121 s (treeWalkCfg q walked rem L₀ R_tail) =
          some (treeWalkCfg q' walked_l rem' L₀ R_tail)
    | .outOfFuel => True := by
  induction rem generalizing q walked with
  | nil => trivial
  | cons b rem' ih =>
    simp only [walkTape]
    rcases htr : rh121Trans q b with _ | ⟨w, d, q'⟩
    · refine ⟨0, Nat.add_zero _, treeWalkCfg q walked (b :: rem') L₀ R_tail, rfl, rfl, ?_⟩
      exact step_mk'_none htr (ListBlank.append walked.reverse L₀)
        (ListBlank.append rem' R_tail)
    · cases d with
      | left =>
        by_cases hw : (w == 0) = true
        · simp only [hw, ↓reduceIte]
          have hw0 : w = 0 := beq_iff_eq.mp hw
          subst hw0
          refine ⟨⟨b, rfl⟩, 1, le_refl 1, ?_⟩
          exact step_one (step_mk'_left htr (ListBlank.append walked.reverse L₀)
            (ListBlank.append rem' R_tail))
        · simp [hw]
      | right =>
        by_cases hw : (w == b) = true
        · simp only [hw, ↓reduceIte]
          have hwb : w = b := beq_iff_eq.mp hw
          subst hwb
          have hstep1 : step riemann121 (treeWalkCfg q walked (w :: rem') L₀ R_tail) =
              some (treeWalkCfg q' (walked ++ [w]) rem' L₀ R_tail) := by
            simpa [treeWalkCfg, append_reverse_cons] using
              step_mk'_right htr (ListBlank.append walked.reverse L₀)
                (ListBlank.append rem' R_tail)
          by_cases hleaf : isLeafState q' = true
          · simp only [hleaf, ↓reduceIte]
            exact ⟨by simp, 1, le_refl 1, step_one hstep1⟩
          · simp only [hleaf, Bool.false_eq_true, ↓reduceIte]
            have hrec := ih q' (walked ++ [w])
            rcases hout : walkTape q' (walked ++ [w]) rem' with
              ⟨q_h, w_h, r_h⟩ | ⟨q_j, w_j, r_j⟩ | ⟨q_l, w_l, r_l⟩ | _
            · rw [hout] at hrec
              obtain ⟨s, hlen, ch, hch, hs, hnone⟩ := hrec
              refine ⟨s + 1, ?_, ch, hch, step_nSteps hstep1 hs, hnone⟩
              rw [List.length_append, List.length_singleton] at hlen
              omega
            · rw [hout] at hrec
              obtain ⟨⟨b', heq⟩, s, hs_pos, hs⟩ := hrec
              exact ⟨⟨b', by simpa using heq⟩, s + 1, by omega, step_nSteps hstep1 hs⟩
            · rw [hout] at hrec
              obtain ⟨heq, s, hs_pos, hs⟩ := hrec
              exact ⟨by simpa using heq, s + 1, by omega, step_nSteps hstep1 hs⟩
            · trivial
        · simp [hw]

/-- `6.break.k` states (`0 ↦ 19`, `1 ↦ 91`). -/
def breakState : ℕ → Fin 121
  | 0 => 19
  | _ => 91

/-- `6.continue.k` states (`0 ↦ 10`, `1 ↦ 37`, `2 ↦ 97`). -/
def continueState : ℕ → Fin 121
  | 0 => 10
  | 1 => 37
  | _ => 97

theorem breakState_trans_one (k : ℕ) (hk : k ≤ 1) :
    Riemann120.rh121Trans (breakState k) 1 = some (0, .left, breakState k) := by
  revert k hk; decide

theorem breakState_trans_zero_one :
    Riemann120.rh121Trans (breakState 1) 0 = some (0, .left, breakState 0) := by
  rfl

theorem continueState_trans_zero (k : ℕ) (hk : k ≤ 2) :
    Riemann120.rh121Trans (continueState k) 0 = some (0, .left, continueState k) := by
  revert k hk; decide

theorem continueState_trans_one (k : ℕ) (hk : k ≤ 1) :
    Riemann120.rh121Trans (continueState (k + 1)) 1 = some (0, .left, continueState k) := by
  revert k hk; decide

theorem popBreakRev_length_le (k : ℕ) (rev : List (Fin 2)) :
    (popBreakRev k rev).length ≤ rev.length := by
  induction rev generalizing k with
  | nil => cases k <;> simp [popBreakRev]
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · cases k with
      | zero => simp [popBreakRev]
      | succ k' => have := ih k'; simp [popBreakRev]; omega
    · cases k with
      | zero => have := ih 0; simp [popBreakRev]; omega
      | succ k' => have := ih (k' + 1); simp [popBreakRev]; omega

theorem popContinueRev_length_le (k : ℕ) (rev : List (Fin 2)) :
    (popContinueRev k rev).length ≤ rev.length := by
  induction rev generalizing k with
  | nil => cases k <;> simp [popContinueRev]
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · cases k with
      | zero => have := ih 0; simp [popContinueRev]; omega
      | succ k' => have := ih (k' + 1); simp [popContinueRev]; omega
    · cases k with
      | zero => simp [popContinueRev]
      | succ k' => have := ih k'; simp [popContinueRev]; omega

theorem popBreakRev_of_count_eq (k : ℕ) (rev : List (Fin 2)) (h : rev.count 0 = k) :
    popBreakRev k rev = [] ∧ popBreakRev k (rev ++ [0]) = [1] := by
  induction rev generalizing k with
  | nil =>
    simp only [List.count_nil] at h
    subst h
    exact ⟨rfl, rfl⟩
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · rw [List.count_cons_self] at h
      subst h
      simpa [popBreakRev] using ih (xs.count 0) rfl
    · have h' : xs.count 0 = k := by simpa using h
      cases k with
      | zero => simpa [popBreakRev] using ih 0 h'
      | succ k' => simpa [popBreakRev] using ih (k' + 1) h'

theorem break_scan_to_21 (k : ℕ) (hk1 : k ≤ 1) (rev : List (Fin 2))
    (h0 : k + 1 ≤ rev.count 0) (L R : ListBlank (Fin 2)) :
    let w' := (popBreakRev k rev).reverse
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨breakState k, Tape.mkL (ListBlank.append rev L) R⟩ =
      some ⟨21, Tape.mk' (ListBlank.append w'.reverse L)
        (ListBlank.append (List.replicate (rev.length - w'.length) 0) R)⟩ := by
  induction rev generalizing k R with
  | nil => simp at h0
  | cons b xs ih =>
    intro w'
    rcases fin2_cases b with rfl | rfl
    · cases k with
      | zero =>
        have hstep : step riemann121
            ⟨19, Tape.mkL ((ListBlank.append xs L).cons 0) R⟩ =
            some ⟨21, Tape.mk' ((ListBlank.append xs L).cons 1) R⟩ :=
          step_mkL_right (by rfl) _ _
        have hw'_rev : w'.reverse = 1 :: xs := by simp [w', popBreakRev]
        have hsub : (0 :: xs).length - w'.length = 0 := by
          have : w'.length = (0 :: xs).length := by
            rw [← List.length_reverse, hw'_rev]; rfl
          omega
        refine ⟨1, le_refl 1, ?_⟩
        rw [hw'_rev, hsub, List.replicate_zero, ListBlank.append, ListBlank.append]
        exact step_one hstep
      | succ k' =>
        have hk'0 : k' = 0 := by omega
        subst hk'0
        have hstep : step riemann121
            ⟨breakState 1, Tape.mkL ((ListBlank.append xs L).cons 0) R⟩ =
            some ⟨breakState 0, Tape.mkL (ListBlank.append xs L) (R.cons 0)⟩ :=
          step_mkL_left breakState_trans_zero_one _ _
        have h0' : 1 ≤ xs.count 0 := by rw [List.count_cons_self] at h0; omega
        obtain ⟨s, hs1, hs⟩ := ih 0 (by decide) h0' (R.cons 0)
        have hw'_eq : (popBreakRev 0 xs).reverse = w' := by simp [w', popBreakRev]
        have hlen_le : w'.length ≤ xs.length := by
          rw [← hw'_eq, List.length_reverse]
          exact popBreakRev_length_le 0 xs
        have hsub : (0 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by
          simp; omega
        rw [hw'_eq, append_replicate_cons, ← hsub] at hs
        exact ⟨s + 1, by omega, step_nSteps hstep hs⟩
    · have hstep : step riemann121
          ⟨breakState k, Tape.mkL ((ListBlank.append xs L).cons 1) R⟩ =
          some ⟨breakState k, Tape.mkL (ListBlank.append xs L) (R.cons 0)⟩ :=
        step_mkL_left (breakState_trans_one k hk1) _ _
      have h0' : k + 1 ≤ xs.count 0 := by simpa using h0
      obtain ⟨s, hs1, hs⟩ := ih k hk1 h0' (R.cons 0)
      have hw'_eq : (popBreakRev k xs).reverse = w' := by
        cases k <;> simp [w', popBreakRev]
      have hlen_le : w'.length ≤ xs.length := by
        rw [← hw'_eq, List.length_reverse]
        exact popBreakRev_length_le k xs
      have hsub : (1 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by
        simp; omega
      rw [hw'_eq, append_replicate_cons, ← hsub] at hs
      exact ⟨s + 1, by omega, step_nSteps hstep hs⟩

theorem continue_scan_to_10 (k : ℕ) (hk2 : k ≤ 2) (rev : List (Fin 2))
    (h1 : k + 1 ≤ rev.count 1) (L R : ListBlank (Fin 2)) :
    let w' := (popContinueRev k rev).reverse
    ∃ s, nSteps riemann121 s
      ⟨continueState k, Tape.mkL (ListBlank.append rev L) R⟩ =
      some ⟨10, Tape.mkL (ListBlank.append w'.reverse L)
        (ListBlank.append (List.replicate (rev.length - w'.length) 0) R)⟩ := by
  induction rev generalizing k R with
  | nil => simp at h1
  | cons b xs ih =>
    intro w'
    rcases fin2_cases b with rfl | rfl
    · have hstep : step riemann121
          ⟨continueState k, Tape.mkL ((ListBlank.append xs L).cons 0) R⟩ =
          some ⟨continueState k, Tape.mkL (ListBlank.append xs L) (R.cons 0)⟩ :=
        step_mkL_left (continueState_trans_zero k hk2) _ _
      have h1' : k + 1 ≤ xs.count 1 := by simpa using h1
      obtain ⟨s, hs⟩ := ih k hk2 h1' (R.cons 0)
      have hw'_eq : (popContinueRev k xs).reverse = w' := by
        cases k <;> simp [w', popContinueRev]
      have hlen_le : w'.length ≤ xs.length := by
        rw [← hw'_eq, List.length_reverse]
        exact popContinueRev_length_le k xs
      have hsub : (0 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by
        simp; omega
      rw [hw'_eq, append_replicate_cons, ← hsub] at hs
      exact ⟨s + 1, step_nSteps hstep hs⟩
    · cases k with
      | zero =>
        have hw'_rev : w'.reverse = 1 :: xs := by simp [w', popContinueRev]
        have hsub : (1 :: xs).length - w'.length = 0 := by
          have : w'.length = (1 :: xs).length := by
            rw [← List.length_reverse, hw'_rev]
          omega
        refine ⟨0, ?_⟩
        rw [hw'_rev, hsub, List.replicate_zero, ListBlank.append]
        rfl
      | succ k' =>
        have hk'1 : k' ≤ 1 := by omega
        have hk'2 : k' ≤ 2 := by omega
        have hstep : step riemann121
            ⟨continueState (k' + 1), Tape.mkL ((ListBlank.append xs L).cons 1) R⟩ =
            some ⟨continueState k', Tape.mkL (ListBlank.append xs L) (R.cons 0)⟩ :=
          step_mkL_left (continueState_trans_one k' hk'1) _ _
        have h1' : k' + 1 ≤ xs.count 1 := by rw [List.count_cons_self] at h1; omega
        obtain ⟨s, hs⟩ := ih k' hk'2 h1' (R.cons 0)
        have hw'_eq : (popContinueRev k' xs).reverse = w' := by
          simp [w', popContinueRev]
        have hlen_le : w'.length ≤ xs.length := by
          rw [← hw'_eq, List.length_reverse]
          exact popContinueRev_length_le k' xs
        have hsub : (1 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by
          simp; omega
        rw [hw'_eq, append_replicate_cons, ← hsub] at hs
        exact ⟨s + 1, step_nSteps hstep hs⟩

theorem append_replicate_zeros_eq (d z : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append (List.replicate d (0 : Fin 2)) (ListBlank.append (List.replicate z 0) R) =
      ListBlank.append (List.replicate (d + z) 0) R := by
  rw [← ListBlank.append_assoc, ← List.replicate_add]

theorem break_cleanup_to_root (k : ℕ) (hk1 : k ≤ 1) (padTotal : ℕ)
    (walked : List (Fin 2)) (hk0 : k ≤ walked.count 0)
    (hw_le : walked.length ≤ padTotal)
    (z m : ℕ) (hz_eq : z + m = padTotal - walked.length)
    (hno4 : NoFourZeros ([1, 1, 0] ++ (popBreakRev k walked.reverse).reverse) = true)
    (regs_all : List ℕ) :
    let w' := (popBreakRev k walked.reverse).reverse
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨breakState k, Tape.mkL (stackLeft walked)
        (ListBlank.append (List.replicate z 0)
          (ListBlank.append (encodeReg m) (regsTape regs_all)))⟩ =
      some (rhRootCfg padTotal w' regs_all default) := by
  intro w'
  by_cases hlt : k + 1 ≤ walked.count 0
  · have hlt_rev : k + 1 ≤ walked.reverse.count 0 := by rw [List.count_reverse]; exact hlt
    obtain ⟨s₁, hs₁_pos, hs₁⟩ := break_scan_to_21 k hk1 walked.reverse hlt_rev rootLeft
      (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) (regsTape regs_all)))
    rw [List.length_reverse, append_replicate_zeros_eq] at hs₁
    change nSteps riemann121 s₁ _ =
      some ⟨21, Tape.mk' (stackLeft w')
        (ListBlank.append (List.replicate (walked.length - w'.length + z) 0)
          (ListBlank.append (encodeReg m) (regsTape regs_all)))⟩ at hs₁
    obtain ⟨s₂, hs₂_pos, hcl⟩ := cleanup_to_main w' hno4
      (walked.length - w'.length + z) m (regsTape regs_all)
    have hlen_le : w'.length ≤ walked.length := by
      have := popBreakRev_length_le k walked.reverse
      simpa [w'] using this
    have hpad_eq : walked.length - w'.length + z + m = padTotal - w'.length := by omega
    rw [hpad_eq] at hcl
    have hroot_eq : ⟨27, Tape.mk' rootLeft
        (ListBlank.append w'
          (ListBlank.append (List.replicate (padTotal - w'.length) 0)
            (ListBlank.append [1, 0] (regsTape regs_all))))⟩ =
        rhRootCfg padTotal w' regs_all default := by
      rw [rhRootCfg_default_eq, regsTape_cons]; rfl
    rw [hroot_eq] at hcl
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hcl⟩
  · have heq : walked.reverse.count 0 = k := by rw [List.count_reverse]; omega
    obtain ⟨hw'_nil, hpop_0⟩ := popBreakRev_of_count_eq k walked.reverse heq
    have hw' : w' = [] := by simp [w', hw'_nil]
    have hstack_eq : stackLeft walked =
        ListBlank.append (walked.reverse ++ [0])
          ((default : ListBlank (Fin 2)).cons 1 |>.cons 1) := by
      unfold stackLeft rootLeft
      rw [ListBlank.append_assoc]; rfl
    have hcnt_0 : k + 1 ≤ (walked.reverse ++ [0]).count 0 := by
      rw [List.count_append, heq]
      change k + 1 ≤ k + 1; omega
    obtain ⟨s₁, hs₁_pos, hs₁⟩ := break_scan_to_21 k hk1 (walked.reverse ++ [0]) hcnt_0
      ((default : ListBlank (Fin 2)).cons 1 |>.cons 1)
      (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) (regsTape regs_all)))
    rw [← hstack_eq] at hs₁
    have hrev_1 : (popBreakRev k (walked.reverse ++ [0])).reverse.reverse = [1] := by
      rw [List.reverse_reverse, hpop_0]
    have hsub_len : (walked.reverse ++ [0]).length -
        (popBreakRev k (walked.reverse ++ [0])).reverse.length = walked.length := by
      rw [List.length_reverse, hpop_0, List.length_append, List.length_reverse]; simp
    rw [hrev_1, hsub_len, append_replicate_zeros_eq] at hs₁
    change nSteps riemann121 s₁ _ =
      some ⟨21, Tape.mk' (((default : ListBlank (Fin 2)).cons 1 |>.cons 1).cons 1)
        (ListBlank.append (List.replicate (walked.length + z) 0)
          (ListBlank.append (encodeReg m) (regsTape regs_all)))⟩ at hs₁
    obtain ⟨s₂, hs₂_pos, hcl⟩ := cleanup_to_10
      (((default : ListBlank (Fin 2)).cons 1 |>.cons 1).cons 1)
      (walked.length + z) m (regsTape regs_all)
    obtain ⟨s₃, hs₃_pos, hret⟩ := continue0_reaches_main0 1 [] (by decide)
      (ListBlank.append (List.replicate (walked.length + z + m) 0)
        (ListBlank.append [1, 0] (regsTape regs_all)))
    have hL111 : ListBlank.append ([1, 1, 1] ++ [] : List (Fin 2)).reverse default =
        (((default : ListBlank (Fin 2)).cons 1 |>.cons 1).cons 1) := rfl
    rw [hL111, ListBlank.append] at hret
    have hpad_eq : walked.length + z + m = padTotal - ([] : List (Fin 2)).length := by
      simp; omega
    rw [hpad_eq] at hcl hret
    have hroot_eq : ⟨27, Tape.mk' rootLeft
        (ListBlank.append (List.replicate (padTotal - ([] : List (Fin 2)).length) 0)
          (ListBlank.append [1, 0] (regsTape regs_all)))⟩ =
        rhRootCfg padTotal [] regs_all default := by
      rw [rhRootCfg_default_eq, regsTape_cons]; rfl
    rw [hroot_eq] at hret
    rw [hw']
    exact ⟨s₁ + (s₂ + s₃), by omega, nSteps_bind_eq hs₁ (nSteps_bind_eq hcl hret)⟩

theorem popContinueRev_of_count_eq (k : ℕ) (rev : List (Fin 2)) (h : rev.count 1 = k) :
    popContinueRev k rev = [] ∧ popContinueRev k (rev ++ [0, 1]) = [1] := by
  induction rev generalizing k with
  | nil =>
    simp only [List.count_nil] at h
    subst h
    exact ⟨rfl, rfl⟩
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · have h' : xs.count 1 = k := by simpa using h
      cases k with
      | zero => simpa [popContinueRev] using ih 0 h'
      | succ k' => simpa [popContinueRev] using ih (k' + 1) h'
    · rw [List.count_cons_self] at h
      subst h
      simpa [popContinueRev] using ih (xs.count 1) rfl

theorem continue0_root11_to_main0 (R₀ : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨10, Tape.mkL (((default : ListBlank (Fin 2)).cons 1).cons 1) (R₀.cons 0)⟩ =
      some ⟨27, Tape.mk' rootLeft R₀⟩ := by
  have h1 : step riemann121
      ⟨10, Tape.mkL (((default : ListBlank (Fin 2)).cons 1).cons 1) (R₀.cons 0)⟩ =
      some ⟨12, Tape.mkL ((default : ListBlank (Fin 2)).cons 1) ((R₀.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step riemann121
      ⟨12, Tape.mkL ((default : ListBlank (Fin 2)).cons 1) ((R₀.cons 0).cons 1)⟩ =
      some ⟨12, Tape.mkL default (ListBlank.append [1, 1, 0] R₀)⟩ :=
    step_mkL_left (by rfl) _ _
  have h3 := rhRun_bounce_default 0 (by decide) (ListBlank.append [1, 1, 0] R₀)
  have h4 := root_scan_to_main 0 R₀
  exact ⟨_, by omega, step_nSteps h1 (step_nSteps h2 (nSteps_bind_eq h3 h4))⟩

theorem continue_return_to_root (k : ℕ) (hk2 : k ≤ 2) (padTotal : ℕ)
    (walked : List (Fin 2)) (hk1 : k ≤ walked.count 1)
    (hw_le : walked.length ≤ padTotal)
    (hno4 : NoFourZeros ([1, 1, 0] ++ (popContinueRev k walked.reverse).reverse) = true)
    (regs_all : List ℕ) :
    let w' := (popContinueRev k walked.reverse).reverse
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨continueState k, Tape.mkL (stackLeft walked)
        (ListBlank.append (List.replicate (padTotal - walked.length) 0)
          (regsTape (0 :: regs_all)))⟩ =
      some (rhRootCfg padTotal w' regs_all default) := by
  intro w'
  by_cases hlt : k + 1 ≤ walked.count 1
  · have hk1_rev : k + 1 ≤ walked.reverse.count 1 := by rw [List.count_reverse]; exact hlt
    obtain ⟨s₁, hs₁⟩ := continue_scan_to_10 k hk2 walked.reverse hk1_rev rootLeft
      (ListBlank.append (List.replicate (padTotal - walked.length) 0) (regsTape (0 :: regs_all)))
    rw [List.length_reverse, append_replicate_zeros_eq] at hs₁
    change nSteps riemann121 s₁ _ =
      some ⟨10, Tape.mkL (stackLeft w')
        (ListBlank.append
          (List.replicate (walked.length - w'.length + (padTotal - walked.length)) 0)
          (regsTape (0 :: regs_all)))⟩ at hs₁
    have hlen_le : w'.length ≤ walked.length := by
      have := popContinueRev_length_le k walked.reverse
      simpa [w'] using this
    have hpad_eq : walked.length - w'.length + (padTotal - walked.length) =
        padTotal - w'.length := by omega
    rw [hpad_eq] at hs₁
    obtain ⟨s₂, hs₂_pos, hret⟩ := continue0_return w' hno4
      (ListBlank.append (List.replicate (padTotal - w'.length) 0) (regsTape (0 :: regs_all)))
    rw [← rhRootCfg_default_eq] at hret
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hret⟩
  · have heq : walked.reverse.count 1 = k := by rw [List.count_reverse]; omega
    obtain ⟨hw'_nil, hpop_1⟩ := popContinueRev_of_count_eq k walked.reverse heq
    have hw' : w' = [] := by simp [w', hw'_nil]
    have hstack_eq : stackLeft walked =
        ListBlank.append (walked.reverse ++ [0, 1])
          ((default : ListBlank (Fin 2)).cons 1) := by
      unfold stackLeft rootLeft
      rw [ListBlank.append_assoc]; rfl
    have hcnt_1 : k + 1 ≤ (walked.reverse ++ [0, 1]).count 1 := by
      rw [List.count_append, heq]
      change k + 1 ≤ k + 1; omega
    obtain ⟨s₁, hs₁⟩ := continue_scan_to_10 k hk2 (walked.reverse ++ [0, 1]) hcnt_1
      ((default : ListBlank (Fin 2)).cons 1)
      (ListBlank.append (List.replicate (padTotal - walked.length) 0) (regsTape (0 :: regs_all)))
    rw [← hstack_eq] at hs₁
    have hrev_1 : (popContinueRev k (walked.reverse ++ [0, 1])).reverse.reverse = [1] := by
      rw [List.reverse_reverse, hpop_1]
    have hsub_len : (walked.reverse ++ [0, 1]).length -
        (popContinueRev k (walked.reverse ++ [0, 1])).reverse.length = walked.length + 1 := by
      rw [List.length_reverse, hpop_1, List.length_append, List.length_reverse]; rfl
    rw [hrev_1, hsub_len, append_replicate_zeros_eq] at hs₁
    have hpad_succ : (walked.length + 1) + (padTotal - walked.length) = padTotal + 1 := by omega
    rw [hpad_succ, List.replicate_succ, ListBlank.append] at hs₁
    obtain ⟨s₂, hs₂_pos, hret⟩ := continue0_root11_to_main0
      (ListBlank.append (List.replicate padTotal 0) (regsTape (0 :: regs_all)))
    have hroot_eq : ⟨27, Tape.mk' rootLeft
        (ListBlank.append (List.replicate padTotal 0) (regsTape (0 :: regs_all)))⟩ =
        rhRootCfg padTotal [] regs_all default := by
      rw [rhRootCfg_default_eq]; rfl
    rw [hroot_eq] at hret
    rw [hw']
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hret⟩

/-!
## 2. Finite Certificate on `allValidStacks` & Step Simulation (`halts_riemann121_iff_rhRegHalts`)
-/

/-- Computable certificate verifying all stack / padding / `NoFourZeros` conditions across
all 121 reachable call stacks `bits ∈ allValidStacks`. -/
def validStackDispatchCheck (bits : List (Fin 2)) : Bool :=
  (bits.length ≤ 18) &&
  match walkTape 27 [] (bits ++ List.replicate 18 0) with
  | .halt _ walked_h _ => 1 ≤ walked_h.length
  | .jumpLeft q' walked rem' =>
    (walked.length ≤ 36) &&
    (0 :: rem' == List.replicate (1 + rem'.length) 0) &&
    (padTo bits walked.length == walked) &&
    if q' == 19 then
      NoFourZeros ([1, 1, 0] ++ applyBreak bits walked.length 0)
    else if q' == 91 then
      (1 ≤ walked.count 0) &&
      NoFourZeros ([1, 1, 0] ++ applyBreak bits walked.length 1)
    else if q' == 10 then
      NoFourZeros ([1, 1, 0] ++ applyContinue bits walked.length 0)
    else if q' == 37 then
      (1 ≤ walked.count 1) &&
      NoFourZeros ([1, 1, 0] ++ applyContinue bits walked.length 1)
    else if q' == 97 then
      (2 ≤ walked.count 1) &&
      NoFourZeros ([1, 1, 0] ++ applyContinue bits walked.length 2)
    else false
  | .regLeaf q' walked_l rem_l =>
    let r := leafReg q'
    (walked_l.length ≤ 36) &&
    (rem_l == List.replicate rem_l.length 0) &&
    (padTo bits walked_l.length == walked_l) &&
    (Riemann120.rh121Trans q' 0 == some (1, .right, 6)) &&
    NoFourZeros ([1, 1, 0] ++ walked_l) &&
    (walkTape 27 [] walked_l == .regLeaf q' walked_l []) &&
    NoFourZeros ([1, 1, 0] ++ applyBreak bits walked_l.length 0) &&
    (if isLeafInc q' then
      q' == regIncStage3 r
     else
      (q' == regDecnzStage3 r) &&
      (1 ≤ walked_l.count 0) &&
      NoFourZeros ([1, 1, 0] ++ applyBreak bits walked_l.length 1))
  | .outOfFuel => false

theorem validStackDispatchCheck_all :
    ∀ bits ∈ allValidStacks, validStackDispatchCheck bits = true := by
  decide

theorem rhRootCfg_regsTape_eq (padTotal : ℕ) (bits : List (Fin 2)) (regs extra : List ℕ) :
    rhRootCfg padTotal bits regs (regsTape extra) =
      rhRootCfg padTotal bits (regs ++ extra) default := by
  unfold rhRootCfg regsTape
  rw [encodeRegs_append]
  simp only [List.append_assoc, ListBlank.append_assoc]

theorem rhRootCfg_eq_treeWalkCfg {bits : List (Fin 2)} (hbits : bits.length ≤ 18)
    (regs_all : List ℕ) :
    rhRootCfg 3821 bits regs_all default =
      treeWalkCfg 27 [] (bits ++ List.replicate 18 0) rootLeft
        (ListBlank.append (List.replicate (3803 - bits.length) 0)
          (regsTape (0 :: regs_all))) := by
  rw [rhRootCfg_default_eq]
  unfold treeWalkCfg
  have hsub : 3821 - bits.length = 18 + (3803 - bits.length) := by omega
  rw [hsub, List.replicate_add]
  simp only [List.reverse_nil, ListBlank.append_assoc, ListBlank.append]

theorem regs_append_getElem {regs extra : List ℕ} {r : ℕ}
    (hlen : regs.length = 5) (hr : r < 5) :
    (regs ++ extra)[r]'(by simp [hlen]; omega) = regs.getD r 0 := by
  have hr' : r < regs.length := by omega
  rw [List.getElem_append_left hr']
  simp [List.getD_eq_getElem?_getD, hr']

theorem regs_append_set {regs extra : List ℕ} {r v : ℕ}
    (hlen : regs.length = 5) (hr : r < 5) :
    (regs ++ extra).set r v = regs.set r v ++ extra :=
  List.set_append_left (i := r) (x := v) (by omega)

theorem rhRegStep_valid {bits bits' : List (Fin 2)} {regs regs' : List ℕ}
    (hv : isValidStack bits = true)
    (hstep : rhRegStep ⟨bits, regs⟩ = some ⟨bits', regs'⟩) :
    isValidStack bits' = true :=
  @rhRegStep_preserves_isValidStack ⟨bits, regs⟩ ⟨bits', regs'⟩ hv hstep

theorem rhRegStep_of_evalStack {bits : List (Fin 2)} {regs : List ℕ} :
    rhRegStep ⟨bits, regs⟩ =
      match evalStack bits with
      | .halt => none
      | .jump stack' => some ⟨stack', regs⟩
      | .inc r stack_succ => some ⟨stack_succ, regs.set r (regs.getD r 0 + 1)⟩
      | .decnz r stack_succ stack_fail =>
        if regs.getD r 0 == 0 then some ⟨stack_fail, regs⟩
        else some ⟨stack_succ, regs.set r (regs.getD r 0 - 1)⟩ := rfl

/-- Lockstep single-step simulation from `rhRootCfg 3821 bits regs (regsTape extra)`:
- If `evalStack bits = .halt`, `riemann121` halts in `s ≥ 1` steps (`step riemann121 ch = none`).
- If `rhRegStep ⟨bits, regs⟩ = some ⟨bits', regs'⟩`, `riemann121` reaches
  `rhRootCfg 3821 bits' regs' (regsTape extra')` in `s ≥ 1` steps for some `extra' : List ℕ`. -/
theorem rhRootCfg_step_sim {bits : List (Fin 2)} (hvalid : isValidStack bits = true)
    {regs : List ℕ} (hregs : regs.length = 5) (extra : List ℕ) :
    (evalStack bits = .halt →
      ∃ s ≥ 1, ∃ ch,
        nSteps riemann121 s (rhRootCfg 3821 bits regs (regsTape extra)) = some ch ∧
        step riemann121 ch = none) ∧
    (∀ bits' regs', rhRegStep ⟨bits, regs⟩ = some ⟨bits', regs'⟩ →
      isValidStack bits' = true ∧
      regs'.length = 5 ∧
      ∃ s ≥ 1, ∃ extra' : List ℕ,
        nSteps riemann121 s (rhRootCfg 3821 bits regs (regsTape extra)) =
          some (rhRootCfg 3821 bits' regs' (regsTape extra'))) := by
  have hmem : bits ∈ allValidStacks := List.contains_iff_mem.mp hvalid
  have hchk := validStackDispatchCheck_all bits hmem
  unfold validStackDispatchCheck at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hbits_le, hchk⟩ := hchk
  set regs_all := regs ++ extra
  set R_extra := ListBlank.append (List.replicate (3803 - bits.length) 0)
    (regsTape (0 :: regs_all))
  have hroot_tw := rhRootCfg_eq_treeWalkCfg hbits_le regs_all
  have hw := walkTape_sound 27 [] (bits ++ List.replicate 18 0) rootLeft R_extra
  rcases hout : walkTape 27 [] (bits ++ List.replicate 18 0) with
    ⟨q_h, walked_h, rem_h⟩ | ⟨q', walked, rem'⟩ | ⟨q', walked_l, rem_l⟩ | _
  · rw [hout] at hw hchk
    simp only [decide_eq_true_eq] at hchk
    obtain ⟨s, hlen_s, ch, _, hs, hnone⟩ := hw
    have hs1 : 1 ≤ s := by rw [List.length_nil] at hlen_s; omega
    have hev : evalStack bits = .halt := by
      unfold evalStack; rw [hout]; rfl
    constructor
    · intro _
      refine ⟨s, hs1, ch, ?_, hnone⟩
      rw [rhRootCfg_regsTape_eq, hroot_tw]
      exact hs
    · intro bits' regs' hstep
      rw [rhRegStep_of_evalStack, hev] at hstep
      cases hstep
  · rw [hout] at hw hchk
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨hw_le, hrem0⟩, hpad_eq⟩, hq_cases⟩ := hchk
    obtain ⟨⟨b, hwalk_eq⟩, s₁, hs₁_pos, hs₁⟩ := hw
    have hw_len_eq : walked.length + (1 + rem'.length) = bits.length + 18 := by
      have h := congrArg List.length hwalk_eq
      simp only [List.length_append, List.length_cons, List.length_nil,
        List.length_replicate] at h
      omega
    have hR_jump : ListBlank.append (0 :: rem') R_extra =
        ListBlank.append (List.replicate (3821 - walked.length) 0)
          (regsTape (0 :: regs_all)) := by
      rw [hrem0]
      simp only [R_extra, ← ListBlank.append_assoc, ← List.replicate_add]
      congr 2; omega
    rw [hR_jump] at hs₁
    change nSteps riemann121 s₁ _ =
      some ⟨q', Tape.mkL (stackLeft walked)
        (ListBlank.append (List.replicate (3821 - walked.length) 0)
          (regsTape (0 :: regs_all)))⟩ at hs₁
    have hw3821 : walked.length ≤ 3821 := by omega
    have hev_base : evalStack bits = outcomeToInstr bits (.jumpLeft q' walked rem') := by
      unfold evalStack; rw [hout]
    have hbreak_case : ∀ k : ℕ, k ≤ 1 → q' = breakState k → k ≤ walked.count 0 →
        NoFourZeros ([1, 1, 0] ++ applyBreak bits walked.length k) = true →
        ∃ s ≥ 1,
          nSteps riemann121 s (rhRootCfg 3821 bits regs (regsTape extra)) =
            some (rhRootCfg 3821 (applyBreak bits walked.length k) regs (regsTape extra)) := by
      intro k hk1 hq_eq hk0 hno4
      subst hq_eq
      have hw'_eq : (popBreakRev k walked.reverse).reverse =
          applyBreak bits walked.length k := by
        simp [applyBreak, hpad_eq]
      rw [← hw'_eq] at hno4
      obtain ⟨s₂, hs₂_pos, hcl⟩ := break_cleanup_to_root k hk1 3821 walked hk0 hw3821
        (3821 - walked.length) 0 (by omega) hno4 regs_all
      have henc0 : ListBlank.append (encodeReg 0) (regsTape regs_all) =
          regsTape (0 :: regs_all) := by
        rw [regsTape_cons]
      rw [henc0] at hcl
      refine ⟨s₁ + s₂, by omega, ?_⟩
      rw [rhRootCfg_regsTape_eq, rhRootCfg_regsTape_eq, hroot_tw, ← hw'_eq]
      exact nSteps_bind_eq hs₁ hcl
    have hcont_case : ∀ k : ℕ, k ≤ 2 → q' = continueState k → k ≤ walked.count 1 →
        NoFourZeros ([1, 1, 0] ++ applyContinue bits walked.length k) = true →
        ∃ s ≥ 1,
          nSteps riemann121 s (rhRootCfg 3821 bits regs (regsTape extra)) =
            some (rhRootCfg 3821 (applyContinue bits walked.length k) regs (regsTape extra)) := by
      intro k hk2 hq_eq hk1_cnt hno4
      subst hq_eq
      have hw'_eq : (popContinueRev k walked.reverse).reverse =
          applyContinue bits walked.length k := by
        simp [applyContinue, hpad_eq]
      rw [← hw'_eq] at hno4
      obtain ⟨s₂, hs₂_pos, hcl⟩ := continue_return_to_root k hk2 3821 walked hk1_cnt hw3821
        hno4 regs_all
      refine ⟨s₁ + s₂, by omega, ?_⟩
      rw [rhRootCfg_regsTape_eq, rhRootCfg_regsTape_eq, hroot_tw, ← hw'_eq]
      exact nSteps_bind_eq hs₁ hcl
    by_cases h19 : q' = 19
    · subst h19
      simp only [↓reduceIte] at hq_cases
      have hev : evalStack bits = .jump (applyBreak bits walked.length 0) := hev_base
      constructor
      · intro hh; rw [hev] at hh; cases hh
      · intro bits' regs' hstep
        have hv' := rhRegStep_valid hvalid hstep
        rw [rhRegStep_of_evalStack, hev] at hstep
        rcases Option.some.inj hstep with ⟨rfl, rfl⟩
        obtain ⟨s, hs, hst⟩ := hbreak_case 0 (by decide) rfl (by omega) hq_cases
        exact ⟨hv', hregs, s, hs, extra, hst⟩
    · simp only [h19, ↓reduceIte] at hq_cases
      by_cases h91 : q' = 91
      · subst h91
        simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hq_cases
        have hev : evalStack bits = .jump (applyBreak bits walked.length 1) := hev_base
        constructor
        · intro hh; rw [hev] at hh; cases hh
        · intro bits' regs' hstep
          have hv' := rhRegStep_valid hvalid hstep
          rw [rhRegStep_of_evalStack, hev] at hstep
          rcases Option.some.inj hstep with ⟨rfl, rfl⟩
          obtain ⟨s, hs, hst⟩ := hbreak_case 1 (by decide) rfl hq_cases.1 hq_cases.2
          exact ⟨hv', hregs, s, hs, extra, hst⟩
      · simp only [h91, ↓reduceIte] at hq_cases
        by_cases h10 : q' = 10
        · subst h10
          simp only [↓reduceIte] at hq_cases
          have hev : evalStack bits = .jump (applyContinue bits walked.length 0) := hev_base
          constructor
          · intro hh; rw [hev] at hh; cases hh
          · intro bits' regs' hstep
            have hv' := rhRegStep_valid hvalid hstep
            rw [rhRegStep_of_evalStack, hev] at hstep
            rcases Option.some.inj hstep with ⟨rfl, rfl⟩
            obtain ⟨s, hs, hst⟩ := hcont_case 0 (by decide) rfl (by omega) hq_cases
            exact ⟨hv', hregs, s, hs, extra, hst⟩
        · simp only [h10, ↓reduceIte] at hq_cases
          by_cases h37 : q' = 37
          · subst h37
            simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hq_cases
            have hev : evalStack bits = .jump (applyContinue bits walked.length 1) := hev_base
            constructor
            · intro hh; rw [hev] at hh; cases hh
            · intro bits' regs' hstep
              have hv' := rhRegStep_valid hvalid hstep
              rw [rhRegStep_of_evalStack, hev] at hstep
              rcases Option.some.inj hstep with ⟨rfl, rfl⟩
              obtain ⟨s, hs, hst⟩ := hcont_case 1 (by decide) rfl hq_cases.1 hq_cases.2
              exact ⟨hv', hregs, s, hs, extra, hst⟩
          · simp only [h37, ↓reduceIte] at hq_cases
            by_cases h97 : q' = 97
            · subst h97
              simp only [↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hq_cases
              have hev : evalStack bits = .jump (applyContinue bits walked.length 2) := hev_base
              constructor
              · intro hh; rw [hev] at hh; cases hh
              · intro bits' regs' hstep
                have hv' := rhRegStep_valid hvalid hstep
                rw [rhRegStep_of_evalStack, hev] at hstep
                rcases Option.some.inj hstep with ⟨rfl, rfl⟩
                obtain ⟨s, hs, hst⟩ := hcont_case 2 (by decide) rfl hq_cases.1 hq_cases.2
                exact ⟨hv', hregs, s, hs, extra, hst⟩
            · simp only [h97, ↓reduceIte] at hq_cases
              cases hq_cases
  · rw [hout] at hw hchk
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hchk
    obtain ⟨⟨⟨⟨⟨⟨⟨hw_le, hrem0⟩, hpad_eq⟩, hq0⟩, hno4_w⟩, hw_pass2⟩, hno4_b0⟩, hleaf_kind⟩ := hchk
    obtain ⟨hwalk_eq, s₁, hs₁_pos, hs₁⟩ := hw
    set r := leafReg q'
    have hr5 : r < 5 := leafReg_lt_5 q'
    have hr_all : r < regs_all.length := by simp [regs_all, hregs]; omega
    have hw_len_eq : walked_l.length + rem_l.length = bits.length + 18 := by
      have h := congrArg List.length hwalk_eq
      simp only [List.length_append, List.length_nil, List.length_replicate] at h
      omega
    set p := 3821 - walked_l.length - 2
    have hR_leaf : ListBlank.append rem_l R_extra =
        ((ListBlank.append (List.replicate (p + 1) 0)
          (ListBlank.append [1, 0] (regsTape regs_all))).cons 0) := by
      rw [hrem0, append_replicate_zeros_eq]
      have hcnt : rem_l.length + (3803 - bits.length) = (p + 1) + 1 := by omega
      rw [hcnt, List.replicate_succ, ListBlank.append, regsTape_cons]
      rfl
    have hs₁' : nSteps riemann121 s₁ (treeWalkCfg 27 [] (bits ++ List.replicate 18 0) rootLeft
        R_extra) = some ⟨q', Tape.mk' (stackLeft walked_l) (ListBlank.append rem_l R_extra)⟩ :=
      hs₁
    rw [hR_leaf] at hs₁'
    have hstep_q' : step riemann121
        ⟨q', Tape.mk' (stackLeft walked_l)
          ((ListBlank.append (List.replicate (p + 1) 0)
            (ListBlank.append [1, 0] (regsTape regs_all))).cons 0)⟩ =
        some ⟨6, Tape.mk' ((stackLeft walked_l).cons 1)
          (ListBlank.append (List.replicate (p + 1) 0)
            (ListBlank.append [1, 0] (regsTape regs_all)))⟩ :=
      step_mk'_right hq0 _ _
    obtain ⟨s_prep, hs_prep_pos, hprep⟩ :=
      prep_pass1_eval walked_l hno4_w p (regsTape regs_all)
    have hprep_eq : ListBlank.append (walked_l ++ [1, 0] ++ encodeReg p) (regsTape regs_all) =
        ListBlank.append walked_l ((regsTape (p :: regs_all)).cons 0 |>.cons 1) := by
      rw [regsTape_cons]
      simp only [List.append_assoc, ListBlank.append_assoc, ListBlank.append]
    rw [hprep_eq] at hprep
    have hw2 := walkTape_sound 27 [] walked_l rootLeft
      ((regsTape (p :: regs_all)).cons 0 |>.cons 1)
    rw [hw_pass2] at hw2
    obtain ⟨_, s₂, hs₂_pos, hs₂⟩ := hw2
    unfold treeWalkCfg at hs₂
    simp only [List.reverse_nil, ListBlank.append] at hs₂
    change nSteps riemann121 s₂
      ⟨27, Tape.mk' rootLeft
        (ListBlank.append walked_l ((regsTape (p :: regs_all)).cons 0 |>.cons 1))⟩ =
      some ⟨q', Tape.mk' (stackLeft walked_l)
        ((regsTape (p :: regs_all)).cons 0 |>.cons 1)⟩ at hs₂
    have hpass12 := nSteps_bind_eq hs₁' (step_nSteps hstep_q' (nSteps_bind_eq hprep hs₂))
    have hw3821 : walked_l.length ≤ 3821 := by omega
    have hw'_b0 : (popBreakRev 0 walked_l.reverse).reverse =
        applyBreak bits walked_l.length 0 := by
      simp [applyBreak, hpad_eq]
    have hev_leaf : evalStack bits = outcomeToInstr bits (.regLeaf q' walked_l rem_l) := by
      unfold evalStack; rw [hout]
    constructor
    · intro hh
      rw [hev_leaf] at hh
      by_cases hinc : isLeafInc q' = true <;> simp [outcomeToInstr, hinc] at hh
    · intro bits' regs' hstep
      have hv' := rhRegStep_valid hvalid hstep
      by_cases hinc : isLeafInc q' = true
      · simp only [hinc, ↓reduceIte, beq_iff_eq] at hleaf_kind
        have hev : evalStack bits = .inc r (applyBreak bits walked_l.length 0) := by
          rw [hev_leaf]; simp [outcomeToInstr, hinc, r]
        rw [rhRegStep_of_evalStack, hev] at hstep
        rcases Option.some.inj hstep with ⟨rfl, rfl⟩
        rw [hleaf_kind] at hpass12
        obtain ⟨s₃, hs₃_pos, hp2⟩ := stage3_inc_pass2 r hr5 p regs_all hr_all (stackLeft walked_l)
        have hR2 : ((regsTape (p :: regs_all.set r (regs_all[r] + 1))).cons 0 |>.cons 0) =
            ListBlank.append (List.replicate 2 0)
              (ListBlank.append (encodeReg p)
                (regsTape (regs_all.set r (regs_all[r] + 1)))) := by
          rw [regsTape_cons]; rfl
        rw [hR2] at hp2
        rw [← hw'_b0] at hno4_b0
        obtain ⟨s₄, hs₄_pos, hcl⟩ := break_cleanup_to_root 0 (by decide) 3821 walked_l
          (by omega) hw3821 2 p (by omega) hno4_b0 (regs_all.set r (regs_all[r] + 1))
        have htot := nSteps_bind_eq hpass12 (nSteps_bind_eq hp2 hcl)
        rw [← hroot_tw, ← rhRootCfg_regsTape_eq] at htot
        have hregs_eq : regs_all.set r (regs_all[r] + 1) =
            regs.set r (regs.getD r 0 + 1) ++ extra := by
          rw [regs_append_getElem hregs hr5, regs_append_set hregs hr5]
        rw [hregs_eq, hw'_b0, ← rhRootCfg_regsTape_eq] at htot
        exact ⟨hv', by simp [hregs], _, by omega, extra, htot⟩
      · simp only [hinc, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
          beq_iff_eq, decide_eq_true_eq] at hleaf_kind
        obtain ⟨⟨hq_eq, hw_cnt0⟩, hno4_b1⟩ := hleaf_kind
        have hev : evalStack bits = .decnz r (applyBreak bits walked_l.length 0)
            (applyBreak bits walked_l.length 1) := by
          rw [hev_leaf]; simp [outcomeToInstr, hinc, r]
        rw [hq_eq] at hpass12
        have hget : regs_all[r] = regs.getD r 0 := regs_append_getElem hregs hr5
        by_cases hz : regs.getD r 0 = 0
        · have hbeq : (regs.getD r 0 == 0) = true := beq_iff_eq.mpr hz
          rw [rhRegStep_of_evalStack, hev] at hstep
          dsimp only at hstep
          rw [hbeq] at hstep
          rcases Option.some.inj hstep with ⟨rfl, rfl⟩
          have hz_all : regs_all[r] = 0 := by rw [hget, hz]
          obtain ⟨s₃, hs₃_pos, hp2⟩ := stage3_decnz_pass2_zero r hr5 p regs_all hr_all hz_all
            (stackLeft walked_l)
          have hR2 : ((regsTape (p :: regs_all)).cons 0 |>.cons 0) =
              ListBlank.append (List.replicate 2 0)
                (ListBlank.append (encodeReg p) (regsTape regs_all)) := by
            rw [regsTape_cons]; rfl
          rw [hR2] at hp2
          have hw'_b1 : (popBreakRev 1 walked_l.reverse).reverse =
              applyBreak bits walked_l.length 1 := by
            simp [applyBreak, hpad_eq]
          rw [← hw'_b1] at hno4_b1
          obtain ⟨s₄, hs₄_pos, hcl⟩ := break_cleanup_to_root 1 (by decide) 3821 walked_l
            hw_cnt0 hw3821 2 p (by omega) hno4_b1 regs_all
          have htot := nSteps_bind_eq hpass12 (nSteps_bind_eq hp2 hcl)
          rw [← hroot_tw, ← rhRootCfg_regsTape_eq, hw'_b1, ← rhRootCfg_regsTape_eq] at htot
          exact ⟨hv', hregs, _, by omega, extra, htot⟩
        · have hbeq : (regs.getD r 0 == 0) = false := beq_eq_false_iff_ne.mpr hz
          rw [rhRegStep_of_evalStack, hev] at hstep
          dsimp only at hstep
          rw [hbeq] at hstep
          rcases Option.some.inj hstep with ⟨rfl, rfl⟩
          have hpos_all : 0 < regs_all[r] := by omega
          obtain ⟨s₃, hs₃_pos, hp2⟩ := stage3_decnz_pass2_pos r hr5 p regs_all hr_all hpos_all
            (stackLeft walked_l)
          have hR2 : ((regsTape (p :: (regs_all.set r (regs_all[r] - 1) ++ [0]))).cons 0 |>.cons 0)
              = ListBlank.append (List.replicate 2 0)
                (ListBlank.append (encodeReg p)
                  (regsTape (regs_all.set r (regs_all[r] - 1) ++ [0]))) := by
            rw [regsTape_cons]; rfl
          rw [hR2] at hp2
          rw [← hw'_b0] at hno4_b0
          obtain ⟨s₄, hs₄_pos, hcl⟩ := break_cleanup_to_root 0 (by decide) 3821 walked_l
            (by omega) hw3821 2 p (by omega) hno4_b0
            (regs_all.set r (regs_all[r] - 1) ++ [0])
          have htot := nSteps_bind_eq hpass12 (nSteps_bind_eq hp2 hcl)
          have hregs_eq : regs_all.set r (regs_all[r] - 1) ++ [0] =
              regs.set r (regs.getD r 0 - 1) ++ (extra ++ [0]) := by
            rw [← List.append_assoc, ← hget, regs_append_set hregs hr5]
          rw [← hroot_tw, ← rhRootCfg_regsTape_eq, hregs_eq, hw'_b0,
            ← rhRootCfg_regsTape_eq] at htot
          exact ⟨hv', by simp [hregs], _, by omega, extra ++ [0], htot⟩
  · rw [hout] at hchk; cases hchk

theorem rhReg_eval_dom_of_tm_halt :
    ∀ N {c : RhRegCfg} {extra : List ℕ} {ch : Cfg 121 2},
      isValidStack c.stack = true →
      c.regs.length = 5 →
      nSteps riemann121 N (rhRootCfg 3821 c.stack c.regs (regsTape extra)) = some ch →
      step riemann121 ch = none →
      (StateTransition.eval rhRegStep c).Dom := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro c extra ch hv hregs hN hnone
    have hsim := rhRootCfg_step_sim hv hregs extra
    rcases hs : rhRegStep c with _ | c'
    · rw [Part.dom_iff_mem]
      exact ⟨c, StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, hs⟩⟩
    · obtain ⟨hv', hregs', s, hs_pos, extra', hsteps⟩ := hsim.2 c'.stack c'.regs hs
      have hle : s ≤ N := by
        by_contra hlt
        have hgt : 1 ≤ s - N := by omega
        have hsplit : s = N + (s - N) := by omega
        rw [hsplit, nSteps_add, hN, Option.bind_some, nSteps_of_halt hnone hgt] at hsteps
        cases hsteps
      have hsplit : N = s + (N - s) := by omega
      rw [hsplit, nSteps_add, hsteps, Option.bind_some] at hN
      have hDom' := ih (N - s) (by omega) hv' hregs' hN hnone
      have hreach : Reaches rhRegStep c c' :=
        Relation.ReflTransGen.head hs Relation.ReflTransGen.refl
      rwa [StateTransition.reaches_eval hreach]

theorem tm_eval_dom_of_rhReg_halt {c : RhRegCfg} {extra : List ℕ}
    (hv : isValidStack c.stack = true) (hregs : c.regs.length = 5)
    (hDom : (StateTransition.eval rhRegStep c).Dom) :
    (StateTransition.eval (step riemann121)
      (rhRootCfg 3821 c.stack c.regs (regsTape extra))).Dom := by
  rw [Part.dom_iff_mem] at hDom ⊢
  obtain ⟨ch_reg, hmem⟩ := hDom
  obtain ⟨n, hn, hnone⟩ := mem_eval_rhRegStep_iff_rhRegNSteps.mp hmem
  have hrun : ∀ m {c₀ : RhRegCfg} {ext₀ : List ℕ},
      isValidStack c₀.stack = true → c₀.regs.length = 5 →
      rhRegNSteps m c₀ = some ch_reg →
      isValidStack ch_reg.stack = true ∧
      ch_reg.regs.length = 5 ∧
      ∃ T ext_f,
        nSteps riemann121 T (rhRootCfg 3821 c₀.stack c₀.regs (regsTape ext₀)) =
          some (rhRootCfg 3821 ch_reg.stack ch_reg.regs (regsTape ext_f)) := by
    intro m
    induction m with
    | zero =>
      intro c₀ ext₀ hv₀ hr₀ hm
      injection hm with heq
      subst heq
      exact ⟨hv₀, hr₀, 0, ext₀, rfl⟩
    | succ m ih =>
      intro c₀ ext₀ hv₀ hr₀ hm
      unfold rhRegNSteps at hm
      rcases hs : rhRegStep c₀ with _ | c₁
      · simp [hs] at hm
      · rw [hs, Option.bind_some] at hm
        obtain ⟨hv₁, hr₁, s₁, _, ext₁, hst₁⟩ :=
          (rhRootCfg_step_sim hv₀ hr₀ ext₀).2 c₁.stack c₁.regs hs
        obtain ⟨hvf, hrf, T, ext_f, hT⟩ := ih hv₁ hr₁ hm
        exact ⟨hvf, hrf, s₁ + T, ext_f, nSteps_bind_eq hst₁ hT⟩
  obtain ⟨hvf, hrf, T, ext_f, hT⟩ := hrun n hv hregs hn
  have hhalt_ev : evalStack ch_reg.stack = .halt := by
    rw [rhRegStep_of_evalStack] at hnone
    rcases hev : evalStack ch_reg.stack with _ | _ | ⟨_, _⟩ | ⟨r_d, _, _⟩
    · rfl
    · rw [hev] at hnone; cases hnone
    · rw [hev] at hnone; cases hnone
    · rw [hev] at hnone
      by_cases hz : (ch_reg.regs.getD r_d 0 == 0) = true <;>
        simp only [hz, ↓reduceIte, Bool.false_eq_true] at hnone <;>
        cases hnone
  obtain ⟨s_h, _, ch_tm, hs_h, htm_none⟩ :=
    (rhRootCfg_step_sim hvf hrf ext_f).1 hhalt_ev
  exact ⟨ch_tm, mem_eval_iff_nSteps.mpr ⟨T + s_h, nSteps_bind_eq hT hs_h, htm_none⟩⟩

/-- **Lockstep Simulation Theorem**: `riemann121` halts on the blank tape if and only if
the 5-register abstract machine `RhRegHalts` halts from `rhRegInit`. -/
theorem halts_riemann121_iff_rhRegHalts : Halts riemann121 ↔ RhRegHalts := by
  obtain ⟨s_boot, hboot⟩ := boot_reaches_main0
  unfold ConjectureMachines.Halts RhRegHalts
  rw [nSteps_eval_dom hboot]
  constructor
  · intro hDom
    rw [Part.dom_iff_mem] at hDom
    obtain ⟨ch, hmem⟩ := hDom
    obtain ⟨N, hN, hnone⟩ := mem_eval_iff_nSteps.mp hmem
    exact rhReg_eval_dom_of_tm_halt N isValidStack_nil rfl hN hnone
  · intro hDom
    exact tm_eval_dom_of_rhReg_halt isValidStack_nil rfl hDom

theorem exists_shuniaCounterexample_iff_shuniaCounterexampleExact :
    (∃ n ≥ 2, ShuniaCounterexample n) ↔ ∃ n, ShuniaCounterexampleExact n :=
  ⟨fun ⟨n, hn2, hce⟩ => ⟨n, shuniaCounterexampleExact_iff.mpr ⟨hn2, hce⟩⟩,
   fun ⟨n, hce⟩ =>
    let ⟨hn2, hce'⟩ := shuniaCounterexampleExact_iff.mp hce
    ⟨n, hn2, hce'⟩⟩

/-!
## 4. Top-Level Bridge Theorem (`halts_riemann120_iff_not_riemannHypothesis_of_large`)
-/

/-- **Top-Level Halting Bridge Theorem for `riemann120`**:
Given the explicit large-`n` RH bound (`21845 < n`), the 120-state Turing machine
`riemann120` halts on the blank tape if and only if the Riemann Hypothesis is false. -/
theorem halts_riemann120_iff_not_riemannHypothesis_of_large
    (hLarge : RiemannHypothesis → ∀ n : ℕ, 21845 < n →
      (n : ℝ) - Chebyshev.theta n ≤
        ((quarterClockStep (n - 1) + 1) * 2 ^ quarterClockStep (n - 1) : ℝ) * Real.log n) :
    Halts riemann120 ↔ ¬ RiemannHypothesis :=
  halts_riemann120_iff_halts_riemann121
    |>.trans halts_riemann121_iff_rhRegHalts
    |>.trans rhRegHalts_iff_exists_shuniaCounterexample
    |>.trans exists_shuniaCounterexample_iff_shuniaCounterexampleExact
    |>.trans (exists_shuniaCounterexampleExact_iff_not_riemannHypothesis_of_large hLarge)

end ConjectureMachines.Riemann120

end

