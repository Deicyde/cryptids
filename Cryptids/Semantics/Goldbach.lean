/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Goldbach24
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Semantics of the Goldbach Turing Machines (`goldbach_25` and `goldbach_24`)

This file proves that the 25-state baseline Turing machine `reference` (`goldbach_25`) and the
24-state compressed Turing machine `candidate` (`goldbach_24`) halt on the blank tape if and only
if Goldbach's conjecture is false (i.e., there exists an even integer $n > 2$ that cannot be
written as the sum of two primes).

## Provenance and Attribution

* **Original 27-state (26-state reachable) Goldbach Turing machine (2016)**:
  Published anonymously in a GitHub Gist
  (<https://gist.github.com/anonymous/a64213f391339236c2fe31f8749a0df6>) and popularized by
  Scott Aaronson and the Busy Beaver Challenge community
  (<https://wiki.bbchallenge.org/wiki/Cryptids>).
* **25-state optimization and first Lean 4 verification (2024)**:
  Yijun Leng optimized the machine from 26 reachable states to 25 states (`goldbach_25`, the
  `reference` machine here) and formalized its correctness in Lean 4 in
  <https://github.com/lengyijun/goldbach_tm> (released under the Apache-2.0 license).
* **24-state compression and halting-equivalence proof (2026)**:
  Maxence Faldor (using Gemini Argon) found the 24-state machine `candidate` (`goldbach_24`) and
  proved `Halts candidate ↔ Halts reference` in `Cryptids.Goldbach24`.
* **This file**:
  An independent, self-contained proof in Lean 4 by Maxence Faldor and Moritz Firsching (using
  Gemini Argon), built directly on top of the symbolic execution primitives in
  `Cryptids.Goldbach24`, establishing `Halts reference ↔ ¬ GoldbachConjecture` and consequently
  `Halts candidate ↔ ¬ GoldbachConjecture`.
-/

@[expose] public section

namespace ConjectureMachines.Goldbach24.Semantics

open Turing StateTransition
open ConjectureMachines.Goldbach24

/-- **Goldbach's Conjecture**: every even integer greater than 2 is the sum of two primes. -/
def GoldbachConjecture : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-!
## 1. Canonical Configurations of `reference`
-/

/-- Configuration at State `0`: about to test primality of `p` (`1 ≤ p`), with partner `q + 1` on
the left (`is_right = true`) or `q` on the right (`is_right = false`). -/
def cfg0 (is_right : Bool) (q p : ℕ) : Cfg 25 2 :=
  ⟨0, Tape.mk' ((LBase1 is_right q).cons 0)
    (ListBlank.append (List.replicate p 1) ((REnd1 is_right q).cons 0))⟩

/-- Configuration at State `6`: testing whether divisor `d = k + 2` divides `p = k + 3 + r`. -/
def cfg6 (is_right : Bool) (q k r : ℕ) : Cfg 25 2 :=
  ⟨6, Tape.mk'
    ((ListBlank.append (List.replicate (k + 2) 1) ((LBase1 is_right q).cons 0)).cons 1)
    (ListBlank.append (List.replicate r 1) ((REnd1 is_right q).cons 0))⟩

/-- Configuration at State `11`: inner division loop with counter `(A, B)` (`A + B = k + 1`),
processed unary block `m`, and remaining unary block `r`. -/
def cfg11 (is_right : Bool) (q A B m r : ℕ) : Cfg 25 2 :=
  ⟨11, Tape.mk' (counterTape A B (LBase1 is_right q))
    ((ListBlank.append (List.replicate m 1)
      ((ListBlank.append (List.replicate r 1) ((REnd1 is_right q).cons 0)).cons 0)).cons 1)⟩

/-- Exit configuration of the primality test for `p`: State `5` if `is_prime = true`,
State `16` if `is_prime = false`. -/
def cfgExit (is_right is_prime : Bool) (q p : ℕ) : Cfg 25 2 :=
  ⟨if is_prime then 5 else 16, Tape.mkL ((LBase1 is_right q).cons 0)
    (ListBlank.append (List.replicate p 1) ((REnd1 is_right q).cons 0))⟩

/-!
## 2. Inner Division Loop (`cfg11`) and Trial Division (`cfg6`)
-/

theorem cfg11_step_b0 (is_right : Bool) (q A m r' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps reference s (cfg11 is_right q A 0 m (r' + 1)) =
        some (cfg11 is_right q 0 A (m + 1) r') := by
  have h := nSteps_pass_11_b0 (M := reference) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    A m (LBase1 is_right q) (ListBlank.append (List.replicate r' 1) ((REnd1 is_right q).cons 0))
  exact ⟨_, by omega, h⟩

theorem cfg11_step_bsucc (is_right : Bool) (q A b m r' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps reference s (cfg11 is_right q A (b + 1) m (r' + 1)) =
        some (cfg11 is_right q (A + 1) b (m + 1) r') := by
  have h := nSteps_pass_11_bsucc (M := reference) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    A b m (LBase1 is_right q) (ListBlank.append (List.replicate r' 1) ((REnd1 is_right q).cons 0))
  exact ⟨_, by omega, h⟩

theorem cfg11_drain (is_right : Bool) (q k r A B m : ℕ)
    (hAB : A + B = k + 1) (hdvd : (k + 2) ∣ B + m + 2) :
    ∃ A' B', A' + B' = k + 1 ∧ (k + 2) ∣ B' + (m + r) + 2 ∧
      ∃ s, nSteps reference s (cfg11 is_right q A B m r) =
        some (cfg11 is_right q A' B' (m + r) 0) := by
  induction r generalizing A B m with
  | zero =>
    exact ⟨A, B, hAB, by simpa using hdvd, 0, rfl⟩
  | succ r' ih =>
    cases B with
    | zero =>
      obtain ⟨s₁, _, hs₁⟩ := cfg11_step_b0 is_right q A m r'
      have hdvd' : (k + 2) ∣ A + (m + 1) + 2 := by
        have h_eq : A + (m + 1) + 2 = (0 + m + 2) + (k + 2) := by omega
        rw [h_eq]
        exact Nat.dvd_add_self_right.mpr hdvd
      obtain ⟨A', B', hAB', hdvd'', s₂, hs₂⟩ := ih 0 A (m + 1) (by omega) hdvd'
      have h_mr : m + 1 + r' = m + (r' + 1) := by omega
      rw [h_mr] at hdvd'' hs₂
      exact ⟨A', B', hAB', hdvd'', s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩
    | succ b =>
      obtain ⟨s₁, _, hs₁⟩ := cfg11_step_bsucc is_right q A b m r'
      have hdvd' : (k + 2) ∣ b + (m + 1) + 2 := by
        have h_eq : b + (m + 1) + 2 = b + 1 + m + 2 := by omega
        rwa [h_eq]
      obtain ⟨A', B', hAB', hdvd'', s₂, hs₂⟩ := ih (A + 1) b (m + 1) (by omega) hdvd'
      have h_mr : m + 1 + r' = m + (r' + 1) := by omega
      rw [h_mr] at hdvd'' hs₂
      exact ⟨A', B', hAB', hdvd'', s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩

theorem cfg6_step_enter (is_right : Bool) (q k r' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps reference s (cfg6 is_right q k (r' + 1)) =
        some (cfg11 is_right q 1 k 0 r') := by
  have h1 := sim_state6_d_ref k (LBase1 is_right q)
    (ListBlank.append (List.replicate r' 1) ((REnd1 is_right q).cons 0))
  have h10_to_11 (L_b R_m : ListBlank (Fin 2)) :
      nSteps reference (1 + k)
        ⟨10, Tape.mk' ((L_b.cons 0).cons 1)
          (ListBlank.append (0 :: (List.replicate k 0 ++ [1])) R_m)⟩ =
        some ⟨11, Tape.mk' (counterTape 1 k L_b) (R_m.cons 1)⟩ := by
    rw [ListBlank.append, ListBlank.append_assoc, ListBlank.append, ListBlank.append]
    refine nSteps_bind_eq (step_one
      (step_mk'_right (M := reference) (q := 10) (q' := 11) (a := 0) (b := 0) rfl _ _)) ?_
    exact nSteps_mk'_right_scan (M := reference) (q := 11) (a := 0) (b := 1) rfl k _ _
  have h := nSteps_bind_eq h1 (h10_to_11 (LBase1 is_right q) _)
  exact ⟨_, by omega, h⟩

theorem cfg6_pass_succ_dvd (is_right : Bool) (q k r' : ℕ)
    (hdvd : (k + 2) ∣ (k + 4 + r')) :
    ∃ s, 1 ≤ s ∧
      nSteps reference s (cfg6 is_right q k (r' + 1)) =
        some (cfgExit is_right false q (k + 4 + r')) := by
  obtain ⟨s₀, hs₀1, hs₀⟩ := cfg6_step_enter is_right q k r'
  obtain ⟨A', B', hAB', hdvd', s₁, hs₁⟩ :=
    cfg11_drain is_right q k r' 1 k 0 (by omega) (by simp)
  simp only [Nat.zero_add] at hdvd' hs₁
  have hB0 : B' = 0 := by
    have h_eq1 : k + 4 + r' = (r' + 2) + (k + 2) := by omega
    have h_eq2 : B' + r' + 2 = B' + (r' + 2) := by omega
    rw [h_eq1, Nat.dvd_add_self_right] at hdvd
    rw [h_eq2] at hdvd'
    exact Nat.eq_zero_of_dvd_of_lt ((Nat.dvd_add_iff_left hdvd).mpr hdvd') (by omega)
  subst hB0
  have h_fin := nSteps_pass_11_to_16 (M := reference) rfl rfl rfl rfl rfl rfl rfl rfl rfl
    A' r' (LBase1 is_right q) (REnd1 is_right q)
  have h_p : A' + r' + 3 = k + 4 + r' := by omega
  have h_fin' : nSteps reference ((1 + (r' + 1)) + ((1 + ((r' + 1) + 1)) + (2 + (A' + 1))))
      (cfg11 is_right q A' 0 r' 0) = some (cfgExit is_right false q (k + 4 + r')) := by
    unfold cfg11 cfgExit
    simpa [List.replicate_zero, ListBlank.append, h_p] using h_fin
  exact ⟨_, by omega, nSteps_bind_eq hs₀ (nSteps_bind_eq hs₁ h_fin')⟩

theorem cfg6_pass_succ_not_dvd (is_right : Bool) (q k r' : ℕ)
    (hdvd : ¬ (k + 2) ∣ (k + 4 + r')) :
    ∃ s, 1 ≤ s ∧
      nSteps reference s (cfg6 is_right q k (r' + 1)) =
        some (cfg6 is_right q (k + 1) r') := by
  obtain ⟨s₀, hs₀1, hs₀⟩ := cfg6_step_enter is_right q k r'
  obtain ⟨A', B', hAB', hdvd', s₁, hs₁⟩ :=
    cfg11_drain is_right q k r' 1 k 0 (by omega) (by simp)
  simp only [Nat.zero_add] at hdvd' hs₁
  cases B' with
  | zero =>
    exfalso
    apply hdvd
    have h_eq1 : k + 4 + r' = (r' + 2) + (k + 2) := by omega
    rw [h_eq1, Nat.dvd_add_self_right]
    simpa using hdvd'
  | succ b =>
    have h_fin := nSteps_pass_11_to_6 (M := reference)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      A' b r' (LBase1 is_right q) (REnd1 is_right q)
    have h_k : A' + b + 3 = (k + 1) + 2 := by omega
    have h_fin' :
        nSteps reference ((1 + (r' + 1)) + ((1 + ((r' + 1) + 1)) + (1 + (b + (1 + ((b + 1) + 2))))))
          (cfg11 is_right q A' (b + 1) r' 0) = some (cfg6 is_right q (k + 1) r') := by
      unfold cfg11 cfg6
      simpa [List.replicate_zero, ListBlank.append, h_k] using h_fin
    exact ⟨_, by omega, nSteps_bind_eq hs₀ (nSteps_bind_eq hs₁ h_fin')⟩

/-- No integer in `[k + 2, p)` divides `p`. -/
def NoFactorFrom (k p : ℕ) : Prop :=
  ∀ d, k + 2 ≤ d → d < p → ¬ d ∣ p

open Classical in
theorem cfg6_eval (is_right : Bool) (q k r : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps reference s (cfg6 is_right q k r) =
        some (cfgExit is_right (decide (NoFactorFrom k (k + 3 + r))) q (k + 3 + r)) := by
  induction r generalizing k with
  | zero =>
    have h_nf : NoFactorFrom k (k + 3 + 0) := by
      intro d hd1 hd2 hdvd
      have hd_eq : d = k + 2 := by omega
      subst hd_eq
      have h1 : (k + 2) ∣ 1 := by
        have h_add : (k + 2) ∣ (k + 2) + 1 := hdvd
        exact (Nat.dvd_add_right (dvd_refl (k + 2))).mp h_add
      have := Nat.le_of_dvd (by omega) h1
      omega
    rw [decide_eq_true h_nf]
    have h1 := sim_state6_accept_ref k (LBase1 is_right q) (REnd1 is_right q)
    have h_cnt :
        (ListBlank.append (List.replicate (k + 2) 1) ((LBase1 is_right q).cons 0)).cons 1 =
        ListBlank.append (List.replicate (k + 3) 1) ((LBase1 is_right q).cons 0) := rfl
    refine ⟨1 + (k + 3), by omega, ?_⟩
    unfold cfg6 cfgExit
    simp only [Nat.add_zero, List.replicate_zero, ListBlank.append, ↓reduceIte]
    refine nSteps_bind_eq (step_one h1) ?_
    rw [h_cnt]
    exact nSteps_mkL_left_scan (M := reference) (q := 5) (a := 1) (b := 1) rfl (k + 3) _ _
  | succ r' ih =>
    have h_arith : k + 3 + (r' + 1) = k + 4 + r' := by omega
    rw [h_arith]
    by_cases hdvd : (k + 2) ∣ (k + 4 + r')
    · have h_nf : ¬ NoFactorFrom k (k + 4 + r') := fun h => h (k + 2) (by omega) (by omega) hdvd
      rw [decide_eq_false h_nf]
      exact cfg6_pass_succ_dvd is_right q k r' hdvd
    · obtain ⟨s₁, hs₁1, hs₁⟩ := cfg6_pass_succ_not_dvd is_right q k r' hdvd
      obtain ⟨s₂, _, hs₂⟩ := ih (k + 1)
      have h_arith2 : k + 1 + 3 + r' = k + 4 + r' := by omega
      rw [h_arith2] at hs₂
      have h_iff : NoFactorFrom k (k + 4 + r') ↔ NoFactorFrom (k + 1) (k + 4 + r') := by
        constructor
        · intro h d hd1 hd2
          exact h d (by omega) hd2
        · intro h d hd1 hd2
          rcases Nat.eq_or_lt_of_le hd1 with rfl | hd_gt
          · exact hdvd
          · exact h d (by omega) hd2
      have h_dec : decide (NoFactorFrom k (k + 4 + r')) =
          decide (NoFactorFrom (k + 1) (k + 4 + r')) := by
        simp [h_iff]
      rw [h_dec]
      exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

/-!
## 3. Complete Primality Test (`cfg0` → `cfgExit`)
-/

open Classical in
theorem cfg0_eval (is_right : Bool) (q p : ℕ) (hp : 1 ≤ p) :
    ∃ s, 1 ≤ s ∧
      nSteps reference s (cfg0 is_right q p) =
        some (cfgExit is_right (decide (Nat.Prime p)) q p) := by
  rcases Nat.eq_or_lt_of_le hp with rfl | hp2
  · rw [decide_eq_false Nat.not_prime_one]
    obtain ⟨h1, _⟩ := sim_state0_p1 ((LBase1 is_right q).cons 0) ((LBase2 is_right q).cons 0)
      (REnd1 is_right q) (REnd2 is_right q)
    refine ⟨2 + 1, by omega, ?_⟩
    unfold cfg0 cfgExit
    exact nSteps_bind_eq h1 (step_one
      (step_mkL_left (M := reference) (q := 16) (q' := 16) (a := 1) (b := 1) rfl _ _))
  · rcases Nat.eq_or_lt_of_le hp2 with rfl | hp3
    · rw [decide_eq_true Nat.prime_two]
      obtain ⟨h1, _⟩ := sim_state0_p2 ((LBase1 is_right q).cons 0) ((LBase2 is_right q).cons 0)
        (REnd1 is_right q) (REnd2 is_right q)
      refine ⟨3 + 2, by omega, ?_⟩
      unfold cfg0 cfgExit
      exact nSteps_bind_eq h1 (step_nSteps
        (step_mkL_left (M := reference) (q := 5) (q' := 5) (a := 1) (b := 1) rfl _ _)
        (step_one (step_mkL_left (M := reference) (q := 5) (q' := 5) (a := 1) (b := 1) rfl _ _)))
    · obtain ⟨r0, rfl⟩ : ∃ r0, p = r0 + 3 := ⟨p - 3, by omega⟩
      obtain ⟨h1, _⟩ := sim_state0_p_ge3 ((LBase1 is_right q).cons 0) ((LBase2 is_right q).cons 0)
        (ListBlank.append (List.replicate r0 1) ((REnd1 is_right q).cons 0))
        (ListBlank.append (List.replicate r0 1) ((REnd2 is_right q).cons 0))
      have h_enter : nSteps reference 3 (cfg0 is_right q (r0 + 3)) =
          some (cfg6 is_right q 0 r0) := h1
      obtain ⟨s₂, _, hs₂⟩ := cfg6_eval is_right q 0 r0
      have h_prime_iff : Nat.Prime (r0 + 3) ↔ NoFactorFrom 0 (0 + 3 + r0) := by
        rw [Nat.prime_def_lt']
        have h_eq : 0 + 3 + r0 = r0 + 3 := by omega
        rw [h_eq]
        exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      have h_dec : decide (Nat.Prime (r0 + 3)) = decide (NoFactorFrom 0 (0 + 3 + r0)) := by
        simp [h_prime_iff]
      have h_eq : 0 + 3 + r0 = r0 + 3 := by omega
      rw [h_dec]
      rw [h_eq] at hs₂ ⊢
      exact ⟨3 + s₂, by omega, nSteps_bind_eq h_enter hs₂⟩

/-!
## 4. Exit Transitions (`cfgExit`) and Goldbach Partition Search
-/

theorem cfgExit_tt (q p : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps reference s (cfgExit true true q p) =
        some (cfg0 false p (q + 1)) := by
  have h_scan (Q P : ℕ) :
      nSteps reference (1 + (Q + 1))
        ⟨5, Tape.mkL ((ListBlank.append (List.replicate Q 1) (B0.cons 0)).cons 0)
          (ListBlank.append (List.replicate P 1) B0)⟩ =
        some ⟨0, Tape.mk' (B0.cons 0)
          (ListBlank.append (List.replicate Q 1)
            ((ListBlank.append (List.replicate P 1) B0).cons 0))⟩ := by
    refine nSteps_bind_eq (step_one (step_mkL_left rfl _ _)) ?_
    refine nSteps_bind_eq (nSteps_mkL_left_scan rfl Q _ _) ?_
    exact step_one (step_mkL_right rfl _ _)
  have h : nSteps reference (1 + ((q + 1) + 1)) (cfgExit true true q p) =
      some (cfg0 false p (q + 1)) := by
    unfold cfgExit cfg0
    simpa [LBase1, REnd1, B0_cons_zero] using h_scan (q + 1) p
  exact ⟨_, by omega, h⟩

theorem cfgExit_tf_succ (q' p : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps reference s (cfgExit true false (q' + 1) p) =
        some (cfg0 true q' (p + 1)) := by
  have hr1 := nSteps_state16_to_19_right (M := reference) rfl rfl rfl 0
    (ListBlank.append (List.replicate (q' + 1) 1) B0)
    (ListBlank.append (List.replicate p 1) B0)
  obtain ⟨hr2, _⟩ := sim_state19_to_0_mkL
    (ListBlank.append (List.replicate q' 1) B0)
    (ListBlank.append (List.replicate (q' + 1) 1) B0)
    (ListBlank.append (List.replicate (p + 1) 1) B0)
    (ListBlank.append (List.replicate (p + 2) 1) B0)
  have h : nSteps reference (2 + 2) (cfgExit true false (q' + 1) p) =
      some (cfg0 true q' (p + 1)) := by
    unfold cfgExit cfg0
    simpa [LBase1, REnd1, B0_cons_zero, List.replicate_succ, ListBlank.append] using
      nSteps_bind_eq hr1 hr2
  exact ⟨_, by omega, h⟩

theorem cfgExit_tf_zero (p : ℕ) :
    ∃ s c, nSteps reference s (cfgExit true false 0 p) = some c ∧
      step reference c = none := by
  have hr : nSteps reference 2 (cfgExit true false 0 p) =
      some ⟨19, Tape.mkL B0
        (((ListBlank.append (List.replicate p 1) B0).cons 1).cons 0)⟩ := by
    unfold cfgExit
    simpa [LBase1, REnd1, B0_cons_zero] using
      nSteps_state16_to_19_right (M := reference) rfl rfl rfl 0 B0
        (ListBlank.append (List.replicate p 1) B0)
  have h_none : step reference ⟨19, Tape.mkL B0
      (((ListBlank.append (List.replicate p 1) B0).cons 1).cons 0)⟩ = none := by
    rw [← B0_cons_zero]; simp [step, Tape.mkL]; rfl
  exact ⟨2, _, hr, h_none⟩

theorem cfgExit_ft (q p : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps reference s (cfgExit false true q p) =
        some (cfg0 false 0 (p + q + 2)) := by
  have hr := sim_state5_to_0_left_from_0_ref p q B0 B0
  have h : nSteps reference (3 + (p + (1 + ((p + 1) + 1)))) (cfgExit false true q p) =
      some (cfg0 false 0 (p + q + 2)) := by
    unfold cfgExit cfg0
    simpa [LBase1, REnd1, B0_cons_zero] using hr
  exact ⟨_, by omega, h⟩

theorem cfgExit_ff_succ (q p' : ℕ) :
    ∃ s, 1 ≤ s ∧
      nSteps reference s (cfgExit false false q (p' + 2)) =
        some (cfg0 true p' (q + 1)) := by
  have hr1 : nSteps reference (p' + 7)
      ⟨16, Tape.mkL B0
        (ListBlank.append (List.replicate (p' + 2) 1)
          ((ListBlank.append (List.replicate q 1) B0).cons 0))⟩ =
      some ⟨19, Tape.mkL (ListBlank.append (List.replicate (p' + 1) 1) B0)
        ((ListBlank.append (List.replicate (q + 1) 1) B0).cons 0)⟩ := by
    simpa [B0_cons_zero, List.replicate_succ, ListBlank.append,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      nSteps_state16_to_19_left (M := reference) rfl rfl rfl rfl rfl rfl rfl 0 (p' + 1) B0
        (ListBlank.append (List.replicate q 1) B0)
  obtain ⟨hr2, _⟩ := sim_state19_to_0_mkL
    (ListBlank.append (List.replicate p' 1) B0)
    (ListBlank.append (List.replicate (p' + 1) 1) B0)
    (ListBlank.append (List.replicate (q + 1) 1) B0)
    (ListBlank.append (List.replicate (q + 2) 1) B0)
  have h : nSteps reference ((p' + 7) + 2) (cfgExit false false q (p' + 2)) =
      some (cfg0 true p' (q + 1)) := by
    unfold cfgExit cfg0
    simpa [LBase1, REnd1, B0_cons_zero, List.replicate_succ, ListBlank.append] using
      nSteps_bind_eq hr1 hr2
  exact ⟨_, by omega, h⟩

theorem cfgExit_ff_one (q : ℕ) :
    ∃ s c, nSteps reference s (cfgExit false false q 1) = some c ∧
      step reference c = none := by
  have hr : nSteps reference 6 (cfgExit false false q 1) =
      some ⟨19, Tape.mkL B0
        ((ListBlank.append (List.replicate (q + 1) 1) B0).cons 0)⟩ := by
    unfold cfgExit
    simpa [LBase1, REnd1, B0_cons_zero, List.replicate_succ, ListBlank.append] using
      nSteps_state16_to_19_left (M := reference) rfl rfl rfl rfl rfl rfl rfl 0 0 B0
        (ListBlank.append (List.replicate q 1) B0)
  have h_none : step reference ⟨19, Tape.mkL B0
      ((ListBlank.append (List.replicate (q + 1) 1) B0).cons 0)⟩ = none := by
    rw [← B0_cons_zero]; simp [step, Tape.mkL]; rfl
  exact ⟨6, _, hr, h_none⟩

/-- Canonical start configuration for stage `w` (testing Goldbach partitions of `2 * w + 4`). -/
def stageCfg (w : ℕ) : Cfg 25 2 :=
  cfg0 true (2 * w + 2) 1

theorem cfg0_partner_pass (w q p : ℕ) (hp : 1 ≤ p) (hsum : q + p = 2 * w + 3)
    (hp_prime : Nat.Prime p) (hq_prime : Nat.Prime (q + 1)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s (cfg0 true q p) = some (stageCfg (w + 1)) := by
  obtain ⟨s₁, hs₁1, hs₁⟩ := cfg0_eval true q p hp
  rw [decide_eq_true hp_prime] at hs₁
  obtain ⟨s₂, _, hs₂⟩ := cfgExit_tt q p
  obtain ⟨s₃, _, hs₃⟩ := cfg0_eval false p (q + 1) (by omega)
  rw [decide_eq_true hq_prime] at hs₃
  obtain ⟨s₄, _, hs₄⟩ := cfgExit_ft p (q + 1)
  have h_sum2 : (q + 1) + p + 2 = (2 * (w + 1) + 2) + 2 := by omega
  rw [h_sum2] at hs₄
  obtain ⟨s₅, _, hs₅⟩ := cfg0_eval false 0 ((2 * (w + 1) + 2) + 2) (by omega)
  have h_not_prime : ¬ Nat.Prime ((2 * (w + 1) + 2) + 2) := by
    intro hpr
    have h_dvd : 2 ∣ (2 * (w + 1) + 2) + 2 := ⟨w + 3, by omega⟩
    rcases (Nat.dvd_prime hpr).mp h_dvd with h2 | h2 <;> omega
  rw [decide_eq_false h_not_prime] at hs₅
  obtain ⟨s₆, _, hs₆⟩ := cfgExit_ff_succ 0 (2 * (w + 1) + 2)
  exact ⟨_, by omega,
    nSteps_bind_eq hs₁ (nSteps_bind_eq hs₂ (nSteps_bind_eq hs₃
      (nSteps_bind_eq hs₄ (nSteps_bind_eq hs₅ hs₆))))⟩

theorem cfg0_partner_fail_succ (q' p : ℕ) (hp : 1 ≤ p)
    (hfail : ¬ (Nat.Prime p ∧ Nat.Prime (q' + 2))) :
    ∃ s, 1 ≤ s ∧ nSteps reference s (cfg0 true (q' + 1) p) = some (cfg0 true q' (p + 1)) := by
  obtain ⟨s₁, hs₁1, hs₁⟩ := cfg0_eval true (q' + 1) p hp
  by_cases hp_prime : Nat.Prime p
  · have hq_not_prime : ¬ Nat.Prime (q' + 2) := fun hq => hfail ⟨hp_prime, hq⟩
    rw [decide_eq_true hp_prime] at hs₁
    obtain ⟨s₂, _, hs₂⟩ := cfgExit_tt (q' + 1) p
    obtain ⟨s₃, _, hs₃⟩ := cfg0_eval false p (q' + 2) (by omega)
    rw [decide_eq_false hq_not_prime] at hs₃
    obtain ⟨s₄, _, hs₄⟩ := cfgExit_ff_succ p q'
    exact ⟨_, by omega, nSteps_bind_eq hs₁ (nSteps_bind_eq hs₂ (nSteps_bind_eq hs₃ hs₄))⟩
  · rw [decide_eq_false hp_prime] at hs₁
    obtain ⟨s₂, _, hs₂⟩ := cfgExit_tf_succ q' p
    exact ⟨_, by omega, nSteps_bind_eq hs₁ hs₂⟩

theorem cfg0_partner_fail_zero (p : ℕ) (hp : 1 ≤ p) :
    ∃ s c, nSteps reference s (cfg0 true 0 p) = some c ∧ step reference c = none := by
  obtain ⟨s₁, _, hs₁⟩ := cfg0_eval true 0 p hp
  by_cases hp_prime : Nat.Prime p
  · rw [decide_eq_true hp_prime] at hs₁
    obtain ⟨s₂, _, hs₂⟩ := cfgExit_tt 0 p
    obtain ⟨s₃, _, hs₃⟩ := cfg0_eval false p 1 (by omega)
    rw [decide_eq_false Nat.not_prime_one] at hs₃
    obtain ⟨s₄, c, hs₄, hnone⟩ := cfgExit_ff_one p
    exact ⟨_, c, nSteps_bind_eq hs₁ (nSteps_bind_eq hs₂ (nSteps_bind_eq hs₃ hs₄)), hnone⟩
  · rw [decide_eq_false hp_prime] at hs₁
    obtain ⟨s₂, c, hs₂, hnone⟩ := cfgExit_tf_zero p
    exact ⟨_, c, nSteps_bind_eq hs₁ hs₂, hnone⟩

theorem search_advance (w q p : ℕ) (hp : 1 ≤ p) (hsum : q + p = 2 * w + 3)
    {q' : ℕ} (hq' : q' ≤ q) (hq1 : Nat.Prime (q' + 1)) (hp1 : Nat.Prime (2 * w + 3 - q')) :
    ∃ s, 1 ≤ s ∧ nSteps reference s (cfg0 true q p) = some (stageCfg (w + 1)) := by
  induction q generalizing p with
  | zero =>
    have hq'0 : q' = 0 := by omega
    subst hq'0
    exact absurd hq1 Nat.not_prime_one
  | succ q0 ih =>
    by_cases hcurr : Nat.Prime p ∧ Nat.Prime (q0 + 2)
    · exact cfg0_partner_pass w (q0 + 1) p hp hsum hcurr.1 hcurr.2
    · have hq'_le : q' ≤ q0 := by
        rcases Nat.eq_or_lt_of_le hq' with rfl | hlt
        · exfalso
          apply hcurr
          have hp_eq : p = 2 * w + 3 - (q0 + 1) := by omega
          rw [hp_eq]
          exact ⟨hp1, hq1⟩
        · omega
      obtain ⟨s₁, hs₁1, hs₁⟩ := cfg0_partner_fail_succ q0 p hp hcurr
      obtain ⟨s₂, _, hs₂⟩ := ih (p + 1) (by omega) (by omega) hq'_le
      exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

theorem search_halt (w q p : ℕ) (hp : 1 ≤ p) (hsum : q + p = 2 * w + 3)
    (hno : ∀ q' ≤ q, ¬ (Nat.Prime (q' + 1) ∧ Nat.Prime (2 * w + 3 - q'))) :
    ∃ s c, nSteps reference s (cfg0 true q p) = some c ∧ step reference c = none := by
  induction q generalizing p with
  | zero =>
    exact cfg0_partner_fail_zero p hp
  | succ q0 ih =>
    have hcurr : ¬ (Nat.Prime p ∧ Nat.Prime (q0 + 2)) := by
      intro ⟨hp_pr, hq_pr⟩
      have hp_eq : p = 2 * w + 3 - (q0 + 1) := by omega
      rw [hp_eq] at hp_pr
      exact hno (q0 + 1) (by omega) ⟨hq_pr, hp_pr⟩
    obtain ⟨s₁, _, hs₁⟩ := cfg0_partner_fail_succ q0 p hp hcurr
    obtain ⟨s₂, c, hs₂, hnone⟩ := ih (p + 1) (by omega) (by omega)
      (fun q' hq' => hno q' (by omega))
    exact ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hnone⟩

/-- Whether `n` can be written as the sum of two primes. -/
def HasGoldbachPair (n : ℕ) : Prop :=
  ∃ a b : ℕ, Nat.Prime a ∧ Nat.Prime b ∧ a + b = n

theorem stage_advance (w : ℕ) (h : HasGoldbachPair (2 * w + 4)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s (stageCfg w) = some (stageCfg (w + 1)) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  have ha2 : 2 ≤ a := ha.two_le
  have hb2 : 2 ≤ b := hb.two_le
  have hq' : a - 1 ≤ 2 * w + 2 := by omega
  have ha_eq : a - 1 + 1 = a := by omega
  have hb_eq : 2 * w + 3 - (a - 1) = b := by omega
  refine search_advance w (2 * w + 2) 1 (by omega) (by omega) hq' ?_ ?_
  · rwa [ha_eq]
  · rwa [hb_eq]

theorem stage_halt (w : ℕ) (h : ¬ HasGoldbachPair (2 * w + 4)) :
    ∃ s c, nSteps reference s (stageCfg w) = some c ∧ step reference c = none := by
  refine search_halt w (2 * w + 2) 1 (by omega) (by omega) ?_
  intro q' hq' ⟨hq1, hp1⟩
  exact h ⟨q' + 1, 2 * w + 3 - q', hq1, hp1, by omega⟩

/-!
## 5. Multi-Stage Execution and Main Equivalence Theorems
-/

theorem reaches_imp_nSteps {M : Machine 25 2} {a b : Cfg 25 2}
    (h : Reaches (step M) a b) : ∃ k, nSteps M k a = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, nSteps_bind_eq hk (step_one hstep)⟩

theorem nSteps_eq_none_of_step_none {M : Machine 25 2} {k : ℕ} (s : ℕ) {a b : Cfg 25 2}
    (hk : nSteps M k a = some b) (hnone : step M b = none) (hks : k < s) :
    nSteps M s a = none := by
  have hs : s = k + ((s - k - 1) + 1) := by omega
  rw [hs, nSteps_add, hk, Option.bind_some, nSteps_succ, hnone, Option.bind_none]

theorem stage_iter_all (hall : ∀ w, HasGoldbachPair (2 * w + 4)) (N : ℕ) :
    ∃ s, N ≤ s ∧ nSteps reference s (stageCfg 0) = some (stageCfg N) := by
  induction N with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ N ih =>
    obtain ⟨s₁, hs₁N, hs₁⟩ := ih
    obtain ⟨s₂, hs₂1, hs₂⟩ := stage_advance N (hall N)
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

theorem stage_reach_or_halt (w : ℕ) :
    (∃ s, nSteps reference s (stageCfg 0) = some (stageCfg w)) ∨
    (∃ s c, nSteps reference s (stageCfg 0) = some c ∧ step reference c = none) := by
  induction w with
  | zero => exact Or.inl ⟨0, rfl⟩
  | succ w ih =>
    rcases ih with ⟨s₁, hs₁⟩ | hhalt
    · by_cases hw : HasGoldbachPair (2 * w + 4)
      · obtain ⟨s₂, _, hs₂⟩ := stage_advance w hw
        exact Or.inl ⟨s₁ + s₂, nSteps_bind_eq hs₁ hs₂⟩
      · obtain ⟨s₂, c, hs₂, hnone⟩ := stage_halt w hw
        exact Or.inr ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hnone⟩
    · exact Or.inr hhalt

theorem halts_reference_iff_exists_counterexample :
    Halts reference ↔ ∃ w : ℕ, ¬ HasGoldbachPair (2 * w + 4) := by
  unfold Halts
  rw [nSteps_eval_dom boot_chk0_ref]
  change (eval (step reference) (stageCfg 0)).Dom ↔ _
  constructor
  · intro hdom
    by_contra hall
    push Not at hall
    rw [Part.dom_iff_mem] at hdom
    obtain ⟨b, hb⟩ := hdom
    rw [StateTransition.mem_eval] at hb
    obtain ⟨hreach, hnone⟩ := hb
    obtain ⟨k, hk⟩ := reaches_imp_nSteps hreach
    obtain ⟨s, hks, hs⟩ := stage_iter_all hall (k + 1)
    have h_eq_none := nSteps_eq_none_of_step_none s hk hnone (by omega)
    rw [h_eq_none] at hs
    cases hs
  · rintro ⟨w, hw⟩
    have h_halt : ∃ s c, nSteps reference s (stageCfg 0) = some c ∧ step reference c = none := by
      rcases stage_reach_or_halt w with ⟨s₁, hs₁⟩ | hhalt
      · obtain ⟨s₂, c, hs₂, hnone⟩ := stage_halt w hw
        exact ⟨s₁ + s₂, c, nSteps_bind_eq hs₁ hs₂, hnone⟩
      · exact hhalt
    obtain ⟨s, c, hs, hnone⟩ := h_halt
    rw [Part.dom_iff_mem]
    exact ⟨c, StateTransition.mem_eval.mpr ⟨nSteps_reaches hs, hnone⟩⟩

theorem goldbachConjecture_iff_all_stages :
    GoldbachConjecture ↔ ∀ w : ℕ, HasGoldbachPair (2 * w + 4) := by
  constructor
  · intro hG w
    obtain ⟨p, q, hp, hq, hn⟩ := hG (2 * w + 4) (by omega) ⟨w + 2, by omega⟩
    exact ⟨p, q, hp, hq, hn.symm⟩
  · intro hall n hn2 ⟨k, hk⟩
    have hk2 : 2 ≤ k := by omega
    obtain ⟨a, b, ha, hb, hab⟩ := hall (k - 2)
    have h_eq : 2 * (k - 2) + 4 = n := by omega
    exact ⟨a, b, ha, hb, by omega⟩

/-- The 25-state baseline machine `reference` (`goldbach_25`) halts on the blank tape
if and only if Goldbach's conjecture is false. -/
theorem halts_reference_iff_not_goldbach :
    Halts reference ↔ ¬ GoldbachConjecture := by
  rw [halts_reference_iff_exists_counterexample, goldbachConjecture_iff_all_stages]
  push Not
  rfl

/-- The 24-state machine `candidate` (`goldbach_24`) halts on the blank tape
if and only if Goldbach's conjecture is false. -/
theorem halts_candidate_iff_not_goldbach :
    Halts candidate ↔ ¬ GoldbachConjecture :=
  candidate_equivalent.trans halts_reference_iff_not_goldbach

end ConjectureMachines.Goldbach24.Semantics
