/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Riemann.DigammaBinet
public import Cryptids.Semantics.Riemann.HorizontalBounds
public import Cryptids.Semantics.Riemann.VonMangoldtCount
public import Cryptids.Semantics.Riemann.WeightedStieltjes
public import Cryptids.Semantics.Riemann.ExplicitLarge
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.NumberTheory.Chebyshev

/-!
# Sharp Circle-Average Riemann–von Mangoldt Bound (`a_rvM = 3 / 4`) & Large-`n` `θ` Bound

This standalone Lean 4 file proves (completely verified from Mathlib principles):

1. **Part 1 (`weightedZeroCountingFunction_le_three_fourths`)**:
   Using Jensen's circle-average identity on `closedBall (2 + y * I) 5` (`R = 5`, `r = 5 / 2`),
   the functional equation `riemannZeta_one_sub` on the left half-circle, the Mean Value Theorem
   along `[1 / 2, u]` with `norm_digamma_sub_log_le_two_div_norm`, and Euler reflection on
   `Re w = 1 / 2`, we prove for all `t ≥ 6` under `RiemannHypothesis`:
   $$(N_w(t) : \mathbb{R}) \le \frac{3}{4} t \log t + 4 t.$$

2. **Part 2 (`theta_sub_lt_quarterClock_of_ge_21846`)**:
   Feeding `a_rvM = 3 / 4`, `C = 13 / 5`, `D = 0`, `A = 1`, `B = 85`,
   `h = (9 / 50) * √x * (log x) ^ 2`, and `T = (37 / 2) * √x / log x` into
   `abs_psi_sub_self_le_weighted_riemannVonMangoldt_six_neg_one_fourth`, combined with
   `Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi` and `quarterClock`, we prove for all
   `n ≥ 21846`:
   $$(n : \mathbb{R}) - \theta(n)
     < \bigl((\text{quarterClock}(n - 1) + 1) \cdot 2^{\text{quarterClock}(n - 1)}\bigr) \log n.$$
-/

@[expose] public section

set_option linter.style.setOption false
set_option linter.flexible false

namespace ConjectureMachines.Riemann120.VonMangoldt

open Complex Finset Filter MeasureTheory Set Metric MeromorphicOn ComplexConjugate
open scoped Real Topology ArithmeticFunction LSeries.notation

open ConjectureMachines.Semantics.Riemann
open ConjectureMachines.Semantics.Riemann.VonMangoldtCount
open ConjectureMachines.Semantics.Riemann.HorizontalBounds
open ConjectureMachines.Semantics.Riemann.DigammaBinet
open ConjectureMachines.Semantics.Riemann.WeightedStieltjes

/-!
## Section 1: Circle-Average Jensen Inequality & Dirichlet Series Bound (`Re s > 1`)
-/

/-- Circle-average form of Jensen's zero-multiplicity bound on `closedBall c |r|` inside
`closedBall c |R|` (`0 < r < R`):
`∑ᶠ u, divisor f (closedBall c |r|) u * log (R / r) ≤ circleAverage (log ‖f ·‖) c R - log ‖f c‖`. -/
lemma sum_divisor_le_circleAverage_sub_log_norm {c : ℂ} {r R : ℝ} {f : ℂ → ℂ}
    (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|)) (hr : 0 < r) (hrR : r < R) (h₂f : f c ≠ 0) :
    ((∑ᶠ u, divisor f (closedBall c |r|) u : ℤ) : ℝ) * Real.log (R / r) ≤
      Real.circleAverage (fun x ↦ Real.log ‖f x‖) c R - Real.log ‖f c‖ := by
  have hR_pos : 0 < R := hr.trans hrR
  have hR_ne : R ≠ 0 := hR_pos.ne'
  have hjensen := h₁f.circleAverage_log_norm hR_ne h₂f
  have hcast : ((∑ᶠ u, divisor f (closedBall c |r|) u : ℤ) : ℝ) =
      ∑ᶠ u, (divisor f (closedBall c |r|) u : ℝ) :=
    map_finsum (Int.castRingHom ℝ) ((divisor _ _).finiteSupport (isCompact_closedBall ..))
  rw [hcast, finsum_mul]
  refine (finsum_le_finsum ?_ ?_ fun u ↦ ?_).trans
    (le_of_eq (eq_sub_of_add_eq hjensen.symm))
  · exact (divisor f (closedBall c |r|)).finiteSupport (isCompact_closedBall ..) |>.subset
      fun _ _ ↦ by simp_all
  · exact (divisor f (closedBall c |R|)).finiteSupport (isCompact_closedBall ..) |>.subset
      fun _ _ ↦ by simp_all
  · by_cases h1 : u ∈ closedBall c |R|
    · by_cases h2 : u ∈ closedBall c |r|
      · simp only [h₁f.mono (closedBall_subset_closedBall (abs_le_abs_of_nonneg hr.le hrR.le)),
          h2, AnalyticOnNhd.divisor_apply, h₁f, h1]
        by_cases h3 : u = c
        · rw [h3, (h₁f c (by simp)).analyticOrderAt_eq_zero.mpr h₂f]
          simp
        · simp +singlePass only [← Real.log_abs]
          gcongr 2
          · simp
          · have : ‖c - u‖ ≠ 0 := by simpa [sub_eq_zero] using Ne.symm h3
            simpa [field, abs_div, hR_pos, abs_of_pos hr, dist_eq_norm'] using h2
      · simp only [h2, not_false_eq_true, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
          Int.cast_zero, zero_mul]
        refine mul_nonneg (mod_cast h₁f.divisor_nonneg ..) ?_
        apply Real.log_abs _ ▸ Real.log_nonneg
        simp only [mem_closedBall, dist_eq_norm', abs_of_pos hR_pos] at h1
        simp only [mem_closedBall, dist_eq_norm', not_le, abs_of_pos hr] at h2
        have : ‖c - u‖ ≠ 0 := (hr.trans h2).ne'
        simpa [field, abs_of_pos hR_pos, hR_pos.le] using h1
    · have hnot : u ∉ closedBall c |r| := fun h ↦
        h1 (closedBall_subset_closedBall (abs_le_abs_of_nonneg hr.le hrR.le) h)
      simp [h1, hnot]

/-- For every `s : ℂ` with `1 < s.re`, `‖riemannZeta s‖ ≤ 1 / (s.re - 1) + 2`. -/
lemma norm_riemannZeta_le_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ 1 / (s.re - 1) + 2 := by
  have hs_sum : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  have h_sum_re : LSeriesSummable 1 (s.re : ℂ) := LSeriesSummable_one_iff.mpr (by simpa using hs)
  have h_re_sum : Summable (fun n : ℕ ↦ (LSeries.term 1 (s.re : ℂ) n).re) :=
    (Complex.hasSum_re h_sum_re.hasSum).summable
  have h_term : ∀ n : ℕ, ‖LSeries.term 1 s n‖ ≤ (LSeries.term 1 (s.re : ℂ) n).re := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [LSeries.term_of_ne_zero hn, Pi.one_apply, norm_div, norm_one,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      have h_eq : (1 : ℂ) / (n : ℂ) ^ (s.re : ℂ) = ((1 / (n : ℝ) ^ s.re : ℝ) : ℂ) := by
        rw [show (n : ℂ) = ((n : ℝ) : ℂ) from rfl, ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
        push_cast
        rfl
      rw [h_eq, Complex.ofReal_re]
  have h1 : ‖riemannZeta s‖ ≤ ∑' n : ℕ, (LSeries.term 1 (s.re : ℂ) n).re := by
    rw [← LSeries_one_eq_riemannZeta hs]
    exact (norm_tsum_le_tsum_norm hs_sum.norm).trans
      (Summable.tsum_le_tsum h_term hs_sum.norm h_re_sum)
  have h2 : (∑' n : ℕ, (LSeries.term 1 (s.re : ℂ) n).re) = (riemannZeta (s.re : ℂ)).re := by
    rw [(Complex.hasSum_re h_sum_re.hasSum).tsum_eq]
    change (L 1 (s.re : ℂ)).re = _
    rw [LSeries_one_eq_riemannZeta (by simpa using hs)]
  have h3 : (riemannZeta (s.re : ℂ)).re ≤ ‖riemannZeta (s.re : ℂ)‖ := re_le_norm _
  have h4 : ‖riemannZeta (s.re : ℂ)‖ ≤ 1 / (s.re - 1) + 2 := by
    have h_pos : 0 < (s.re : ℂ).re := by simp; linarith
    have h_ne1 : (s.re : ℂ) ≠ 1 := by exact_mod_cast hs.ne'
    have h_b := norm_riemannZeta_le h_pos h_ne1
    have h_sub : ‖(s.re : ℂ) - 1‖ = s.re - 1 := by
      rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_of_nonneg (by linarith)]
    have h_norm : ‖(s.re : ℂ)‖ = s.re := by
      rw [norm_real, Real.norm_of_nonneg (by linarith)]
    rw [h_sub, h_norm, ofReal_re, div_self (by linarith)] at h_b
    linarith
  linarith

/-!
## Section 2: Stirling + Euler Reflection Bound via MVT along Horizontal Segments
-/

/-- Real derivative along a horizontal line `x ↦ log (normSq (Gamma (x + v * I)))`:
for `x > 0`, `HasDerivAt (fun x : ℝ ↦ Real.log (normSq (Gamma (x + v * I))))`
equals `2 * (Complex.digamma (x + v * I)).re`. -/
lemma hasDerivAt_log_normSq_Gamma_horiz (v : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ ↦ Real.log (Complex.normSq (Complex.Gamma ((t : ℂ) + (v : ℂ) * I))))
      (2 * (Complex.digamma ((x : ℂ) + (v : ℂ) * I)).re) x := by
  let s : ℂ := (x : ℂ) + (v : ℂ) * I
  let f : ℝ → ℂ := fun t ↦ Complex.Gamma ((t : ℂ) + (v : ℂ) * I)
  have hs_re : 0 < s.re := by simp [s, hx]
  have hs_gam_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs_re
  have hs_nsq_pos : 0 < Complex.normSq (Complex.Gamma s) := Complex.normSq_pos.mpr hs_gam_ne
  have hs_diff : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma s (ne_neg_natCast_of_re_pos hs_re)
  have h_in : HasDerivAt (fun t : ℝ ↦ (t : ℂ) + (v : ℂ) * I) 1 x :=
    (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((v : ℂ) * I)
  have h_re : HasDerivAt (fun t : ℝ ↦ (f t).re) (deriv Complex.Gamma s).re x := by
    convert Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hs_diff.hasDerivAt.scomp x h_in) using 1
    · rfl
    · simp
  have h_im : HasDerivAt (fun t : ℝ ↦ (f t).im) (deriv Complex.Gamma s).im x := by
    convert Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hs_diff.hasDerivAt.scomp x h_in) using 1
    · rfl
    · simp
  have h_nsq : HasDerivAt (fun t : ℝ ↦ Complex.normSq (f t))
      (2 * (Complex.Gamma s).re * (deriv Complex.Gamma s).re +
        2 * (Complex.Gamma s).im * (deriv Complex.Gamma s).im) x := by
    have h_eq : (fun t : ℝ ↦ Complex.normSq (f t)) =
        fun t : ℝ ↦ (f t).re ^ 2 + (f t).im ^ 2 := by
      ext t
      rw [Complex.normSq_apply]
      ring
    rw [h_eq]
    refine ((h_re.pow 2).add (h_im.pow 2)).congr_deriv ?_
    change 2 * (Complex.Gamma s).re ^ 1 * (deriv Complex.Gamma s).re +
      2 * (Complex.Gamma s).im ^ 1 * (deriv Complex.Gamma s).im = _
    ring
  refine (h_nsq.log hs_nsq_pos.ne').congr_deriv ?_
  have hdig : Complex.digamma s = deriv Complex.Gamma s / Complex.Gamma s := by
    rw [Complex.digamma_def, logDeriv_apply]
  change _ / Complex.normSq (Complex.Gamma s) = 2 * (Complex.digamma s).re
  rw [hdig, Complex.div_re]
  field_simp [hs_nsq_pos.ne']

/-- On the critical line `Re s = 1 / 2`, Euler reflection gives
`normSq (Gamma (1 / 2 + v * I)) ≤ 2 * π * exp (-π * |v|)`. -/
lemma normSq_Gamma_half_add_mul_I_le (v : ℝ) :
    Complex.normSq (Complex.Gamma ((1 / 2 : ℂ) + (v : ℂ) * I)) ≤
      2 * Real.pi * Real.exp (-Real.pi * |v|) := by
  let s : ℂ := (1 / 2 : ℂ) + (v : ℂ) * I
  have h_conj : (1 : ℂ) - s = conj s := by
    apply Complex.ext
    · simp [s]; norm_num
    · simp [s]
  have h_refl := Complex.Gamma_mul_Gamma_one_sub s
  rw [h_conj, Complex.Gamma_conj, Complex.mul_conj] at h_refl
  have h_norm := congrArg norm h_refl
  rw [norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _), norm_div,
    norm_real, Real.norm_of_nonneg Real.pi_pos.le] at h_norm
  have h_sin_eq : Complex.sin (↑Real.pi * s) = (Real.cosh (Real.pi * v) : ℂ) := by
    have h_arg : (↑Real.pi : ℂ) * s = ↑(Real.pi / 2) + ↑(Real.pi * v) * I := by
      simp [s]
      ring
    rw [h_arg, Complex.sin_add, ← Complex.ofReal_sin, Real.sin_pi_div_two,
      ← Complex.ofReal_cos, Real.cos_pi_div_two]
    simp [Complex.cos_mul_I]
  rw [h_sin_eq, norm_real, Real.norm_of_nonneg (Real.cosh_pos _).le] at h_norm
  rw [h_norm, div_le_iff₀ (Real.cosh_pos _)]
  have h_exp : Real.exp (Real.pi * |v|) ≤ 2 * Real.cosh (Real.pi * v) := by
    rcases le_or_gt 0 v with hv | hv
    · rw [abs_of_nonneg hv, Real.cosh_eq]
      have : 0 ≤ Real.exp (-(Real.pi * v)) := Real.exp_nonneg _
      linarith
    · rw [abs_of_neg hv, Real.cosh_eq]
      have h1 : Real.exp (Real.pi * -v) = Real.exp (-(Real.pi * v)) := by ring_nf
      rw [h1]
      have : 0 ≤ Real.exp (Real.pi * v) := Real.exp_nonneg _
      linarith
  have h_prod : Real.exp (-Real.pi * |v|) * Real.exp (Real.pi * |v|) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have h_step := mul_le_mul_of_nonneg_left h_exp
    (by positivity : 0 ≤ Real.pi * Real.exp (-Real.pi * |v|))
  calc
    Real.pi = Real.pi * (Real.exp (-Real.pi * |v|) * Real.exp (Real.pi * |v|)) := by
      rw [h_prod]; ring
    _ = Real.pi * Real.exp (-Real.pi * |v|) * Real.exp (Real.pi * |v|) := by ring
    _ ≤ Real.pi * Real.exp (-Real.pi * |v|) * (2 * Real.cosh (Real.pi * v)) := h_step
    _ = 2 * Real.pi * Real.exp (-Real.pi * |v|) * Real.cosh (Real.pi * v) := by ring

/-- Upper bound `‖Complex.cos (π * w / 2)‖ ≤ Real.exp (Real.pi * |w.im| / 2)`. -/
lemma norm_cos_pi_mul_div_two_le (w : ℂ) :
    ‖Complex.cos (↑Real.pi * w / 2)‖ ≤ Real.exp (Real.pi * |w.im| / 2) := by
  let z : ℂ := ↑Real.pi * w / 2
  have hz_im : z.im = Real.pi * w.im / 2 := by
    simp [z]
  have h_two : ‖(2 : ℂ)‖ = 2 := by simp
  rw [show (↑Real.pi : ℂ) * w / 2 = z from rfl, Complex.cos, norm_div, h_two]
  have h1 : ‖Complex.exp (z * I)‖ ≤ Real.exp (Real.pi * |w.im| / 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have him : (z * I).re = -z.im := by simp
    rw [him, hz_im]
    have habs : -w.im ≤ |w.im| := neg_le_abs w.im
    nlinarith [Real.pi_pos]
  have h2 : ‖Complex.exp (-z * I)‖ ≤ Real.exp (Real.pi * |w.im| / 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have him : (-z * I).re = z.im := by simp
    rw [him, hz_im]
    have habs : w.im ≤ |w.im| := le_abs_self w.im
    nlinarith [Real.pi_pos]
  have htri : ‖Complex.exp (z * I) + Complex.exp (-z * I)‖ ≤
      ‖Complex.exp (z * I)‖ + ‖Complex.exp (-z * I)‖ := norm_add_le _ _
  linarith

/-- Elementary rational bound `(8 / 3 : ℝ) ≤ Real.exp 1`. -/
lemma eight_thirds_le_exp_one : (8 / 3 : ℝ) ≤ Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1) 4
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial,
    Nat.cast_one, Nat.cast_mul, one_pow, zero_add] at h
  linarith

/-- Elementary rational bound `(65 / 24 : ℝ) ≤ Real.exp 1`. -/
lemma sixty_five_twenty_fourths_le_exp_one : (65 / 24 : ℝ) ≤ Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1) 5
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial,
    Nat.cast_one, Nat.cast_mul, one_pow, zero_add] at h
  linarith

/-- Key numerical absorption inequality:
`(17 / 8 : ℝ) * Real.exp (29 / 30) ≤ 2 * Real.pi`. -/
lemma seventeen_eighths_mul_exp_29_div_30_le_two_pi :
    (17 / 8 : ℝ) * Real.exp (29 / 30) ≤ 2 * Real.pi := by
  have h_log : (29 / 30 : ℝ) ≤ (7 / 5) * Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have h_exp5 : (Real.exp (29 / 30)) ^ (5 : ℕ) ≤ (2 : ℝ) ^ (7 : ℕ) := by
    rw [← Real.exp_nat_mul]
    have h2 : Real.exp ((7 : ℕ) * Real.log 2) = (2 : ℝ) ^ (7 : ℕ) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [← h2]
    exact Real.exp_le_exp.mpr (by push_cast; linarith)
  have h_pow5 : ((17 / 8 : ℝ) * Real.exp (29 / 30)) ^ (5 : ℕ) ≤ (2 * Real.pi) ^ (5 : ℕ) := by
    calc
      ((17 / 8 : ℝ) * Real.exp (29 / 30)) ^ (5 : ℕ)
        = (17 / 8 : ℝ) ^ (5 : ℕ) * (Real.exp (29 / 30)) ^ (5 : ℕ) := mul_pow _ _ 5
      _ ≤ (17 / 8 : ℝ) ^ (5 : ℕ) * (2 : ℝ) ^ (7 : ℕ) :=
          mul_le_mul_of_nonneg_left h_exp5 (by positivity)
      _ ≤ (2 * (3141592 / 1000000 : ℝ)) ^ (5 : ℕ) := by norm_num
      _ ≤ (2 * Real.pi) ^ (5 : ℕ) :=
          pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_d6]) 5
  exact le_of_pow_le_pow_left₀ (n := 5) (by norm_num) (by positivity) h_pow5

/-- **Sharp Functional-Equation Factor Bound (`1 / 2 ≤ w.re ≤ 4`, `3 ≤ |w.im| ≤ |y| + 5`)**:
For `8 ≤ |y|` and `w : ℂ` with `1 / 2 ≤ w.re ≤ 4` and `3 ≤ |w.im| ≤ |y| + 5`,
`‖2 * (2 * π) ^ (-w) * cos (π * w / 2) * Gamma w‖ ≤
  2 * Real.exp ((w.re - 1 / 2) * (Real.log |y| - 3 / 10))`. -/
lemma norm_chi_factor_le {y : ℝ} (hy : 8 ≤ |y|) {w : ℂ}
    (hu_lo : 1 / 2 ≤ w.re) (hu_hi : w.re ≤ 4)
    (hv_lo : 3 ≤ |w.im|) (hv_hi : |w.im| ≤ |y| + 5) :
    ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w) * Complex.cos (↑Real.pi * w / 2) * Complex.Gamma w‖ ≤
      2 * Real.exp ((w.re - 1 / 2) * (Real.log |y| - 3 / 10)) := by
  set u : ℝ := w.re
  set v : ℝ := w.im
  let φ : ℝ → ℝ := fun t ↦ Real.log (Complex.normSq (Complex.Gamma ((t : ℂ) + (v : ℂ) * I)))
  have hφ_diff : ∀ t ∈ Icc (1 / 2 : ℝ) u,
      HasDerivAt φ (2 * (Complex.digamma ((t : ℂ) + (v : ℂ) * I)).re) t :=
    fun t ht ↦ hasDerivAt_log_normSq_Gamma_horiz v (by linarith [ht.1])
  have hφ_step : φ u - φ (1 / 2) ≤ 2 * (u - 1 / 2) * (Real.log (|v| + u) + 2 / |v|) := by
    rcases eq_or_lt_of_le hu_lo with h_eq | h_lt
    · rw [← h_eq, sub_self, sub_self, mul_zero, zero_mul]
    · obtain ⟨ξ, hξ_mem, hξ_eq⟩ := exists_hasDerivAt_eq_slope φ
        (fun t ↦ 2 * (Complex.digamma ((t : ℂ) + (v : ℂ) * I)).re) h_lt
        (fun t ht ↦ (hφ_diff t ht).continuousAt.continuousWithinAt)
        (fun t ht ↦ hφ_diff t (Ioo_subset_Icc_self ht))
      have hξ_pos : 0 < ξ := by linarith [hξ_mem.1]
      let zξ : ℂ := (ξ : ℂ) + (v : ℂ) * I
      have hzξ_re : 0 < zξ.re := by simp [zξ, hξ_pos]
      have hzξ_norm_lo : |v| ≤ ‖zξ‖ := by
        have h := Complex.abs_im_le_norm zξ
        simpa [zξ] using h
      have hzξ_norm_hi : ‖zξ‖ ≤ |v| + u := by
        have h1 : ‖zξ‖ ≤ ‖(ξ : ℂ)‖ + ‖(v : ℂ) * I‖ := norm_add_le _ _
        have h2 : ‖(ξ : ℂ)‖ = ξ := by rw [norm_real, Real.norm_of_nonneg hξ_pos.le]
        have h3 : ‖(v : ℂ) * I‖ = |v| := by
          rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
        linarith [hξ_mem.2]
      have hdig_b := norm_digamma_sub_log_le_two_div_norm hzξ_re
      have hdig_re : (Complex.digamma zξ).re ≤ Real.log (|v| + u) + 2 / |v| := by
        have h1 : (Complex.digamma zξ - Complex.log zξ).re ≤
            ‖Complex.digamma zξ - Complex.log zξ‖ := Complex.re_le_norm _
        have h2 : (Complex.log zξ).re = Real.log ‖zξ‖ := Complex.log_re zξ
        have h3 : Real.log ‖zξ‖ ≤ Real.log (|v| + u) :=
          Real.log_le_log (by linarith) hzξ_norm_hi
        have h4 : 2 / ‖zξ‖ ≤ 2 / |v| :=
          div_le_div_of_nonneg_left (by norm_num) (by linarith) hzξ_norm_lo
        simp only [Complex.sub_re, h2] at h1
        linarith
      rw [eq_div_iff (by linarith : u - 1 / 2 ≠ 0)] at hξ_eq
      nlinarith
  have hw_eq : (u : ℂ) + (v : ℂ) * I = w := Complex.re_add_im w
  have hw_gam_pos : 0 < ‖Complex.Gamma w‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by linarith))
  have hφ_u : φ u = 2 * Real.log ‖Complex.Gamma w‖ := by
    dsimp [φ]
    rw [hw_eq, Complex.normSq_eq_norm_sq, Real.log_pow]
    ring
  have hφ_half : φ (1 / 2) ≤ Real.log (2 * Real.pi) - Real.pi * |v| := by
    dsimp [φ]
    have hcast : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; rfl
    rw [hcast]
    have hnsq := normSq_Gamma_half_add_mul_I_le v
    have hpos : 0 < Complex.normSq (Complex.Gamma ((1 / 2 : ℂ) + (v : ℂ) * I)) :=
      Complex.normSq_pos.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp))
    have hlog := Real.log_le_log hpos hnsq
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hlog
    linarith
  have h_log_gam : Real.log ‖Complex.Gamma w‖ ≤
      (1 / 2) * Real.log (2 * Real.pi) - (Real.pi / 2) * |v| +
        (u - 1 / 2) * (Real.log (|v| + u) + 2 / |v|) := by
    linarith
  have h_gam_norm : ‖Complex.Gamma w‖ ≤
      Real.exp ((1 / 2) * Real.log (2 * Real.pi) - (Real.pi / 2) * |v| +
        (u - 1 / 2) * (Real.log (|v| + u) + 2 / |v|)) := by
    rw [← Real.exp_log hw_gam_pos]
    exact Real.exp_le_exp.mpr h_log_gam
  have h_2pi : ‖(2 * ↑Real.pi : ℂ) ^ (-w)‖ = Real.exp (-u * Real.log (2 * Real.pi)) := by
    have hcast : (2 * ↑Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
      Real.rpow_def_of_pos (by positivity)]
    have hre : (-w).re = -u := by simp [u]
    rw [hre]
    ring_nf
  have h_cos := norm_cos_pi_mul_div_two_le w
  have h_two : ‖(2 : ℂ)‖ = 2 := by simp
  rw [norm_mul, norm_mul, norm_mul, h_two, h_2pi]
  have h_prod :
      2 * Real.exp (-u * Real.log (2 * Real.pi)) * ‖Complex.cos (↑Real.pi * w / 2)‖ *
          ‖Complex.Gamma w‖ ≤
        2 * Real.exp ((u - 1 / 2) *
          (Real.log (|v| + u) + 2 / |v| - Real.log (2 * Real.pi))) := by
    calc
      2 * Real.exp (-u * Real.log (2 * Real.pi)) * ‖Complex.cos (↑Real.pi * w / 2)‖ *
          ‖Complex.Gamma w‖
        ≤ 2 * Real.exp (-u * Real.log (2 * Real.pi)) * Real.exp (Real.pi * |v| / 2) *
            Real.exp ((1 / 2) * Real.log (2 * Real.pi) - (Real.pi / 2) * |v| +
              (u - 1 / 2) * (Real.log (|v| + u) + 2 / |v|)) := by
            gcongr
      _ = 2 * Real.exp ((u - 1 / 2) *
            (Real.log (|v| + u) + 2 / |v| - Real.log (2 * Real.pi))) := by
            rw [mul_assoc (2 : ℝ), mul_assoc, ← Real.exp_add, ← Real.exp_add]
            congr 2
            ring
  refine h_prod.trans ?_
  have h_inner :
      Real.log (|v| + u) + 2 / |v| - Real.log (2 * Real.pi) ≤ Real.log |y| - 3 / 10 := by
    have h_vu : |v| + u ≤ (17 / 8) * |y| := by linarith
    have h_l1 : Real.log (|v| + u) ≤ Real.log ((17 / 8) * |y|) :=
      Real.log_le_log (by linarith) h_vu
    have h_l2 : Real.log ((17 / 8) * |y|) = Real.log (17 / 8) + Real.log |y| :=
      Real.log_mul (by norm_num) (by linarith)
    have h_div : 2 / |v| ≤ 2 / 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hv_lo
    have h_sum_exp : Real.log (17 / 8) + 29 / 30 ≤ Real.log (2 * Real.pi) := by
      rw [← Real.log_exp (29 / 30), ← Real.log_mul (by norm_num) (Real.exp_pos _).ne']
      exact Real.log_le_log (by positivity) seventeen_eighths_mul_exp_29_div_30_le_two_pi
    linarith
  have h_exp_le :
      Real.exp ((u - 1 / 2) * (Real.log (|v| + u) + 2 / |v| - Real.log (2 * Real.pi))) ≤
        Real.exp ((u - 1 / 2) * (Real.log |y| - 3 / 10)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h_inner (by linarith))
  linarith

/-!
## Section 3: Circle Majorant on `sphere (2 + y * I) 5` (`|y| ≥ 8`)
-/

/-- Trigonometric identity `Real.cos θ = -Real.sin (θ - π / 2)`. -/
lemma cos_eq_neg_sin_sub_pi_div_two (θ : ℝ) :
    Real.cos θ = -Real.sin (θ - Real.pi / 2) := by
  have h : θ - Real.pi / 2 = -(Real.pi / 2 - θ) := by ring
  rw [h, Real.sin_neg, Real.sin_pi_div_two_sub, neg_neg]

/-- Geometry bounds for any point `z ∈ closedBall (2 + y * I) 5` when `8 ≤ |y|`. -/
lemma closedBall_five_bounds {y : ℝ} (hy : 8 ≤ |y|) {z : ℂ}
    (hz : z ∈ closedBall (2 + (y : ℂ) * I) 5) :
    -3 ≤ z.re ∧ z.re ≤ 7 ∧
      |y| - 5 ≤ |z.im| ∧ |z.im| ≤ |y| + 5 ∧
      ‖z - 1‖ ≤ (13 / 8) * ‖(1 : ℂ) + (y : ℂ) * I‖ ∧
      ‖z‖ ≤ (15 / 8) * |y| := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hK : 8 ≤ ‖(1 : ℂ) + (y : ℂ) * I‖ :=
    hy.trans (one_and_abs_le_norm_one_add_mul_I y).2
  have hre_diff : |z.re - 2| ≤ 5 := by
    simpa using (Complex.abs_re_le_norm (z - (2 + (y : ℂ) * I))).trans hz
  have him_diff : |z.im - y| ≤ 5 := by
    simpa using (Complex.abs_im_le_norm (z - (2 + (y : ℂ) * I))).trans hz
  have hz_sub1 : ‖z - 1‖ ≤ (13 / 8) * ‖(1 : ℂ) + (y : ℂ) * I‖ := by
    have hd : z - 1 = (z - (2 + (y : ℂ) * I)) + ((1 : ℂ) + (y : ℂ) * I) := by ring
    have ht : ‖z - 1‖ ≤ ‖z - (2 + (y : ℂ) * I)‖ + ‖(1 : ℂ) + (y : ℂ) * I‖ := by
      rw [hd]
      exact norm_add_le (z - (2 + (y : ℂ) * I)) ((1 : ℂ) + (y : ℂ) * I)
    linarith
  have hz_norm : ‖z‖ ≤ (15 / 8) * |y| := by
    have hd : z = (z - (2 + (y : ℂ) * I)) + ((2 : ℂ) + (y : ℂ) * I) := by ring
    have ht1 : ‖z‖ ≤ ‖z - (2 + (y : ℂ) * I)‖ + ‖(2 : ℂ) + (y : ℂ) * I‖ := by
      conv_lhs => rw [hd]
      exact norm_add_le (z - (2 + (y : ℂ) * I)) ((2 : ℂ) + (y : ℂ) * I)
    have ht2 : ‖(2 : ℂ) + (y : ℂ) * I‖ ≤ 2 + |y| := by
      have h1 : ‖(2 : ℂ)‖ = 2 := by simp
      have h2 : ‖(y : ℂ) * I‖ = |y| := by
        rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
      linarith [norm_add_le (2 : ℂ) ((y : ℂ) * I)]
    linarith
  have him_lo : |y| - 5 ≤ |z.im| := by
    have h := abs_sub_abs_le_abs_sub y z.im
    have hsym : |y - z.im| = |z.im - y| := abs_sub_comm y z.im
    linarith
  have him_hi : |z.im| ≤ |y| + 5 := by
    have h := abs_sub_abs_le_abs_sub z.im y
    linarith
  exact ⟨by linarith [(abs_le.mp hre_diff).1], by linarith [(abs_le.mp hre_diff).2],
    him_lo, him_hi, hz_sub1, hz_norm⟩

/-- On any point `z ∈ closedBall (2 + y * I) 5` with `z.re ≤ 1 / 2` and `8 ≤ |y|`,
`‖riemannZeta₁ z‖ = ‖z - 1‖ * ‖(2 : ℂ) * (2 * π) ^ (-(1 - z)) * cos (π * (1 - z) / 2) *
  Gamma (1 - z)‖ * ‖riemannZeta (1 - z)‖`. -/
lemma norm_riemannZeta₁_eq_functional_of_re_le_half {y : ℝ} (hy : 8 ≤ |y|) {z : ℂ}
    (hz : z ∈ closedBall (2 + (y : ℂ) * I) 5) (hz_re : z.re ≤ 1 / 2) :
    ‖riemannZeta₁ z‖ =
      ‖z - 1‖ *
        ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-(1 - z)) * Complex.cos (↑Real.pi * (1 - z) / 2) *
          Complex.Gamma (1 - z)‖ *
        ‖riemannZeta (1 - z)‖ := by
  obtain ⟨_, _, him_lo, _, _, _⟩ := closedBall_five_bounds hy hz
  have hz_im_pos : 3 ≤ |z.im| := by linarith
  have hz_ne1 : z ≠ 1 := by
    rintro rfl
    simp at hz_re
    linarith
  have hz_sub_ne : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne1
  have hzeta1 : riemannZeta₁ z = (z - 1) * riemannZeta z := by
    rw [riemannZeta_eq_inv_sub_mul hz_ne1, ← mul_assoc, mul_inv_cancel₀ hz_sub_ne, one_mul]
  let w : ℂ := 1 - z
  have hw_sub : 1 - w = z := sub_sub_cancel 1 z
  have h1w_ne_nat : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n heq
    have hre := congrArg Complex.re heq
    simp [w] at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hw_ne1 : w ≠ 1 := by
    intro heq
    have him := congrArg Complex.im heq
    simp [w] at him
    rw [him] at hz_im_pos
    norm_num at hz_im_pos
  have hfe : riemannZeta z =
      ((2 : ℂ) * (2 * ↑Real.pi) ^ (-w) * Complex.cos (↑Real.pi * w / 2) * Complex.Gamma w) *
        riemannZeta w := by
    have h := riemannZeta_one_sub h1w_ne_nat hw_ne1
    rw [hw_sub] at h
    rw [h]
    ring
  rw [hzeta1, hfe, norm_mul, norm_mul, ← mul_assoc]

/-- Symmetric piecewise circle majorant `circleMaj y θ` on `[0, 2 * π]`. -/
noncomputable def circleMaj (y θ : ℝ) : ℝ :=
  if θ ≤ Real.pi / 2 + 1 / 10 then 3
  else if θ ≤ Real.pi / 2 + 4 / 25 then 4
  else if θ ≤ Real.pi / 2 + 31 / 100 then Real.log |y| + 4
  else if θ ≤ Real.pi / 2 + 11 / 25 then (17 / 10) * Real.log |y| + 4
  else if θ ≤ Real.pi / 2 + 13 / 25 then
    (-3 / 2 - 5 * Real.cos θ) * (Real.log |y| - 3 / 10) + 6
  else if θ ≤ 3 * Real.pi / 2 - 13 / 25 then
    (-3 / 2 - 5 * Real.cos θ) * (Real.log |y| - 3 / 10) + 4
  else if θ ≤ 3 * Real.pi / 2 - 11 / 25 then
    (-3 / 2 - 5 * Real.cos θ) * (Real.log |y| - 3 / 10) + 6
  else if θ ≤ 3 * Real.pi / 2 - 31 / 100 then (17 / 10) * Real.log |y| + 4
  else if θ ≤ 3 * Real.pi / 2 - 4 / 25 then Real.log |y| + 4
  else if θ ≤ 3 * Real.pi / 2 - 1 / 10 then 4
  else 3

set_option maxHeartbeats 1200000 in
-- Explicit numerical interval and contour integral bounds.
/-- Pointwise bound on `sphere (2 + y * I) 5` (`|y| ≥ 8`, `θ ∈ [0, 2 * π]`):
`Real.log ‖riemannZeta₁ (circleMap (2 + y * I) 5 θ)‖ - Real.log ‖riemannZeta₁ (2 + y * I)‖`
`≤ circleMaj y θ`. -/
lemma log_norm_riemannZeta₁_sub_le_circleMaj {y θ : ℝ} (hy : 8 ≤ |y|) (_hθ0 : 0 ≤ θ)
    (_hθ2pi : θ ≤ 2 * Real.pi) :
    Real.log ‖riemannZeta₁ (circleMap (2 + (y : ℂ) * I) 5 θ)‖ -
        Real.log ‖riemannZeta₁ (2 + (y : ℂ) * I)‖ ≤
      circleMaj y θ := by
  let c : ℂ := 2 + (y : ℂ) * I
  let z : ℂ := circleMap c 5 θ
  let K : ℝ := ‖(1 : ℂ) + (y : ℂ) * I‖
  have hK : 8 ≤ K := hy.trans (one_and_abs_le_norm_one_add_mul_I y).2
  have hc_ge : 1 / 3 * K ≤ ‖riemannZeta₁ c‖ := by
    have hc_ne1 : c ≠ 1 := by intro h; have := congrArg Complex.re h; simp [c] at this
    have hc_eq : riemannZeta₁ c = ((1 : ℂ) + (y : ℂ) * I) * riemannZeta c := by
      have hs : c - 1 = (1 : ℂ) + (y : ℂ) * I := by simp [c]; ring
      rw [riemannZeta_eq_inv_sub_mul hc_ne1, ← hs]
      exact (mul_inv_cancel_left₀ (sub_ne_zero.mpr hc_ne1) _).symm
    rw [hc_eq, norm_mul, mul_comm (1 / 3 : ℝ) K]
    exact mul_le_mul_of_nonneg_left
      (one_third_le_norm_riemannZeta_of_re_eq_two (s := c) (by simp [c])) (by positivity)
  have hc_pos : 0 < ‖riemannZeta₁ c‖ := by linarith
  have hz_mem : z ∈ closedBall c 5 :=
    sphere_subset_closedBall (by simp [z])
  obtain ⟨hz_re_lo, hz_re_hi, hz_im_lo, hz_im_hi, hz_sub1, hz_norm⟩ :=
    closedBall_five_bounds hy hz_mem
  have hz_re_eq : z.re = 2 + 5 * Real.cos θ := by
    simp [z, circleMap, c, Complex.exp_mul_I, Complex.cos_ofReal_re]
  have hexp1 : (8 / 3 : ℝ) ≤ Real.exp 1 := eight_thirds_le_exp_one
  have hexp1_fine : (65 / 24 : ℝ) ≤ Real.exp 1 := sixty_five_twenty_fourths_le_exp_one
  have hlog_y_ge2 : 2 ≤ Real.log |y| := by
    have h8 : (2 : ℝ) ^ (3 : ℕ) ≤ |y| := by norm_num; linarith
    have hl := Real.log_le_log (by positivity) h8
    rw [Real.log_pow] at hl
    push_cast at hl
    linarith [Real.log_two_gt_d9]
  have hlog_y_nonneg : 0 ≤ Real.log |y| := by linarith
  have to_log_bound : ∀ (M0 B : ℝ), 0 ≤ M0 → 3 * M0 ≤ Real.exp B → 0 ≤ B →
      ‖riemannZeta₁ z‖ ≤ M0 * K →
      Real.log ‖riemannZeta₁ z‖ - Real.log ‖riemannZeta₁ c‖ ≤ B := by
    intro M0 B hM0_nonneg hM_exp hB_nonneg h_le
    rcases eq_or_lt_of_le (norm_nonneg (riemannZeta₁ z)) with hz0 | hz_pos
    · rw [← hz0, Real.log_zero, zero_sub]
      linarith [Real.log_nonneg (show 1 ≤ ‖riemannZeta₁ c‖ by linarith)]
    · have hK_le : K ≤ 3 * ‖riemannZeta₁ c‖ := by linarith
      have h_le_c : ‖riemannZeta₁ z‖ ≤ (3 * M0) * ‖riemannZeta₁ c‖ := by
        calc
          ‖riemannZeta₁ z‖ ≤ M0 * K := h_le
          _ ≤ M0 * (3 * ‖riemannZeta₁ c‖) := mul_le_mul_of_nonneg_left hK_le hM0_nonneg
          _ = (3 * M0) * ‖riemannZeta₁ c‖ := by ring
      have hdiv : ‖riemannZeta₁ z‖ / ‖riemannZeta₁ c‖ ≤ Real.exp B :=
        (div_le_iff₀ hc_pos).mpr (h_le_c.trans (mul_le_mul_of_nonneg_right hM_exp hc_pos.le))
      have hlog := Real.log_le_log (div_pos hz_pos hc_pos) hdiv
      rw [Real.log_div hz_pos.ne' hc_pos.ne', Real.log_exp] at hlog
      exact hlog
  unfold circleMaj
  split_ifs with h0 h1 h2 h3 h4m h4 h5 h6 h7
  · -- Branch 0: `θ ≤ π / 2 + 1 / 10` (`z.re ≥ 3 / 2`)
    have hcos : -1 / 10 ≤ Real.cos θ := by
      have hs : Real.sin (θ - Real.pi / 2) ≤ 1 / 10 := by
        rcases le_or_gt (θ - Real.pi / 2) 0 with hneg | hpos
        · exact (Real.sin_nonpos_of_nonpos_of_neg_pi_le hneg
            (by linarith [Real.pi_gt_three])).trans (by norm_num)
        · exact (Real.sin_lt hpos).le.trans (by linarith)
      rw [cos_eq_neg_sin_sub_pi_div_two]
      linarith
    have hz_re : 3 / 2 ≤ z.re := by linarith
    have hz_ne1 : z ≠ 1 := fun h ↦ by have := congrArg Complex.re h; simp at this; linarith
    have hzeta1 : ‖riemannZeta₁ z‖ = ‖z - 1‖ * ‖riemannZeta z‖ := by
      have hs_ne : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne1
      rw [show riemannZeta₁ z = (z - 1) * riemannZeta z by
        rw [riemannZeta_eq_inv_sub_mul hz_ne1, ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul],
        norm_mul]
    have hzeta_b : ‖riemannZeta z‖ ≤ 4 := by
      have hb := norm_riemannZeta_le_of_one_lt_re (by linarith : 1 < z.re)
      have hdiv : 1 / (z.re - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    refine to_log_bound (13 / 2) 3 (by norm_num) ?_ (by norm_num) ?_
    · calc
        3 * (13 / 2 : ℝ) ≤ (65 / 24) ^ 3 := by norm_num
        _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) hexp1_fine 3
        _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
    · rw [hzeta1]
      calc
        ‖z - 1‖ * ‖riemannZeta z‖ ≤ ((13 / 8) * K) * 4 :=
          mul_le_mul hz_sub1 hzeta_b (norm_nonneg _) (by positivity)
        _ = (13 / 2) * K := by ring
  · -- Branch 1: `π / 2 + 1 / 10 < θ ≤ π / 2 + 4 / 25` (`z.re ≥ 6 / 5`)
    have hcos : -4 / 25 ≤ Real.cos θ := by
      have hs : Real.sin (θ - Real.pi / 2) ≤ 4 / 25 :=
        (Real.sin_lt (by linarith)).le.trans (by linarith)
      rw [cos_eq_neg_sin_sub_pi_div_two]
      linarith
    have hz_re : 6 / 5 ≤ z.re := by linarith
    have hz_ne1 : z ≠ 1 := fun h ↦ by have := congrArg Complex.re h; simp at this; linarith
    have hzeta1 : ‖riemannZeta₁ z‖ = ‖z - 1‖ * ‖riemannZeta z‖ := by
      have hs_ne : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne1
      rw [show riemannZeta₁ z = (z - 1) * riemannZeta z by
        rw [riemannZeta_eq_inv_sub_mul hz_ne1, ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul],
        norm_mul]
    have hzeta_b : ‖riemannZeta z‖ ≤ 7 := by
      have hb := norm_riemannZeta_le_of_one_lt_re (by linarith : 1 < z.re)
      have hdiv : 1 / (z.re - 1) ≤ 5 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    refine to_log_bound (91 / 8) 4 (by norm_num) ?_ (by norm_num) ?_
    · calc
        3 * (91 / 8 : ℝ) ≤ (8 / 3) ^ 4 := by norm_num
        _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) hexp1 4
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    · rw [hzeta1]
      calc
        ‖z - 1‖ * ‖riemannZeta z‖ ≤ ((13 / 8) * K) * 7 :=
          mul_le_mul hz_sub1 hzeta_b (norm_nonneg _) (by positivity)
        _ = (91 / 8) * K := by ring
  · -- Branch 2: `π / 2 + 4 / 25 < θ ≤ π / 2 + 31 / 100` (`z.re ≥ 9 / 20`)
    have hcos : -31 / 100 ≤ Real.cos θ := by
      have hs : Real.sin (θ - Real.pi / 2) ≤ 31 / 100 :=
        (Real.sin_lt (by linarith)).le.trans (by linarith)
      rw [cos_eq_neg_sin_sub_pi_div_two]
      linarith
    have hz_re : 9 / 20 ≤ z.re := by linarith
    have hb := norm_riemannZeta₁_le (by linarith : 0 < z.re)
    have hdiv : ‖z‖ / z.re ≤ (25 / 6) * |y| := by
      rw [div_le_iff₀ (by linarith)]
      have h1' : (25 / 6) * |y| * (9 / 20) ≤ (25 / 6) * |y| * z.re :=
        mul_le_mul_of_nonneg_left hz_re (by positivity)
      linarith
    refine to_log_bound ((175 / 24) * |y|) (Real.log |y| + 4) (by positivity) ?_
      (by linarith) ?_
    · rw [Real.exp_add, Real.exp_log (by linarith), mul_comm |y|]
      have h_mul : 3 * ((175 / 24) * |y|) = (175 / 8) * |y| := by ring
      rw [h_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg y)
      calc
        (175 / 8 : ℝ) ≤ (8 / 3) ^ 4 := by norm_num
        _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) hexp1 4
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    · have h_prod_b : ‖z - 1‖ * (1 + ‖z‖ / z.re) ≤ ((13 / 8) * K) * ((53 / 12) * |y|) :=
        mul_le_mul hz_sub1 (by linarith) (by positivity) (by positivity)
      nlinarith
  · -- Branch 3: `π / 2 + 31 / 100 < θ ≤ π / 2 + 11 / 25` (`-1 / 5 ≤ z.re ≤ 1 / 2`)
    have hz_re_up : z.re ≤ 1 / 2 := by
      have hs : 3 / 10 ≤ Real.sin (θ - Real.pi / 2) := by
        have hcube := Real.sin_gt_sub_cube (by linarith : 0 < θ - Real.pi / 2)
        have hmono : (31 / 100) - (31 / 100) ^ 3 / 6 ≤
            (θ - Real.pi / 2) - (θ - Real.pi / 2) ^ 3 / 6 := by
          have hd : 0 ≤ ((θ - Real.pi / 2) - 31 / 100) *
              (1 - ((θ - Real.pi / 2) ^ 2 + (θ - Real.pi / 2) * (31 / 100) +
                (31 / 100) ^ 2) / 6) :=
            mul_nonneg (by linarith) (by nlinarith)
          linarith
        linarith
      rw [hz_re_eq, cos_eq_neg_sin_sub_pi_div_two]
      linarith
    have hcos : -11 / 25 ≤ Real.cos θ := by
      have hs : Real.sin (θ - Real.pi / 2) ≤ 11 / 25 :=
        (Real.sin_lt (by linarith)).le.trans (by linarith)
      rw [cos_eq_neg_sin_sub_pi_div_two]
      linarith
    let w : ℂ := 1 - z
    have hw_re_lo : 1 / 2 ≤ w.re := by simp [w]; linarith
    have hw_re_hi : w.re ≤ 6 / 5 := by simp [w]; linarith
    have hw_im : |w.im| = |z.im| := by simp [w]
    have hchi := norm_chi_factor_le hy hw_re_lo (by linarith)
      (by rw [hw_im]; linarith) (by rw [hw_im]; exact hz_im_hi)
    have hchi_y : ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w) * Complex.cos (↑Real.pi * w / 2) *
        Complex.Gamma w‖ ≤ 2 * Real.exp ((7 / 10) * Real.log |y|) := by
      refine hchi.trans ?_
      have hexp_le : Real.exp ((w.re - 1 / 2) * (Real.log |y| - 3 / 10)) ≤
          Real.exp ((7 / 10) * Real.log |y|) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      linarith
    have hzeta_w : ‖riemannZeta w‖ ≤ (9 / 2) * |y| := by
      have hw_ne1 : w ≠ 1 := by
        intro h; have := congrArg Complex.im h; simp [w] at this
        rw [this] at hz_im_lo; norm_num at hz_im_lo; linarith
      have hb := norm_riemannZeta_le (by linarith) hw_ne1
      have hw1 : 3 ≤ ‖w - 1‖ := by
        have h1' : w - 1 = -z := by dsimp [w]; ring
        rw [h1', norm_neg]
        exact (by linarith : 3 ≤ |z.im|).trans (Complex.abs_im_le_norm z)
      have hd1 : 1 / ‖w - 1‖ ≤ 1 / 3 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hw1
      have hd2 : ‖w‖ / w.re ≤ 2 * ‖w‖ := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [norm_nonneg w]
      have hw_n : ‖w‖ ≤ 2 * |y| := by
        have h1' : ‖w‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le 1 z
        rw [norm_one] at h1'
        linarith
      linarith
    refine to_log_bound ((117 / 8) * |y| * Real.exp ((7 / 10) * Real.log |y|))
      ((17 / 10) * Real.log |y| + 4) (by positivity) ?_ (by linarith) ?_
    · have hexp_split : Real.exp ((17 / 10) * Real.log |y| + 4) =
          Real.exp 4 * (|y| * Real.exp ((7 / 10) * Real.log |y|)) := by
        rw [← Real.exp_log (by linarith : 0 < |y|), ← Real.exp_add, ← Real.exp_add,
          Real.log_exp]
        congr 1
        ring
      rw [hexp_split]
      have h_mul : 3 * ((117 / 8) * |y| * Real.exp ((7 / 10) * Real.log |y|)) =
          (351 / 8) * (|y| * Real.exp ((7 / 10) * Real.log |y|)) := by ring
      rw [h_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc
        (351 / 8 : ℝ) ≤ (8 / 3) ^ 4 := by norm_num
        _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) hexp1 4
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    · rw [norm_riemannZeta₁_eq_functional_of_re_le_half hy hz_mem (by linarith)]
      have hp1 : ‖z - 1‖ * ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w) *
          Complex.cos (↑Real.pi * w / 2) * Complex.Gamma w‖ ≤
          ((13 / 8) * K) * (2 * Real.exp ((7 / 10) * Real.log |y|)) :=
        mul_le_mul hz_sub1 hchi_y (norm_nonneg _) (by positivity)
      calc
        ‖z - 1‖ * ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w) *
            Complex.cos (↑Real.pi * w / 2) * Complex.Gamma w‖ * ‖riemannZeta w‖
          ≤ (((13 / 8) * K) * (2 * Real.exp ((7 / 10) * Real.log |y|))) * ((9 / 2) * |y|) :=
            mul_le_mul hp1 hzeta_w (norm_nonneg _) (by positivity)
        _ = ((117 / 8) * |y| * Real.exp ((7 / 10) * Real.log |y|)) * K := by ring
  · -- Branch 4a: `π / 2 + 11 / 25 < θ ≤ π / 2 + 13 / 25` (`z.re ≤ -1 / 20`, `w.re ≥ 21 / 20`)
    have hsin_ge : (41 / 100 : ℝ) ≤ Real.sin (θ - Real.pi / 2) := by
      have hcube := Real.sin_gt_sub_cube (by linarith : 0 < θ - Real.pi / 2)
      have hmono : (11 / 25) - (11 / 25) ^ 3 / 6 ≤
          (θ - Real.pi / 2) - (θ - Real.pi / 2) ^ 3 / 6 := by
        have hd : 0 ≤ ((θ - Real.pi / 2) - 11 / 25) *
            (1 - ((θ - Real.pi / 2) ^ 2 + (θ - Real.pi / 2) * (11 / 25) +
              (11 / 25) ^ 2) / 6) :=
          mul_nonneg (by linarith) (by nlinarith)
        linarith
      linarith
    have hz_re : z.re ≤ -1 / 20 := by
      rw [hz_re_eq, cos_eq_neg_sin_sub_pi_div_two]
      linarith
    let w : ℂ := 1 - z
    have hw_re_lo : 21 / 20 ≤ w.re := by simp [w]; linarith
    have hw_re_hi : w.re ≤ 4 := by simp [w]; linarith
    have hw_im : |w.im| = |z.im| := by simp [w]
    have hchi := norm_chi_factor_le hy (by linarith) hw_re_hi
      (by rw [hw_im]; linarith) (by rw [hw_im]; exact hz_im_hi)
    have hzeta_w : ‖riemannZeta w‖ ≤ 22 := by
      have hb := norm_riemannZeta_le_of_one_lt_re (by linarith : 1 < w.re)
      have hd : 1 / (w.re - 1) ≤ 20 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have hexp_eq : w.re - 1 / 2 = -3 / 2 - 5 * Real.cos θ := by
      simp [w, hz_re_eq]
      ring
    let E : ℝ := Real.exp ((w.re - 1 / 2) * (Real.log |y| - 3 / 10))
    refine to_log_bound ((143 / 2) * E)
      ((-3 / 2 - 5 * Real.cos θ) * (Real.log |y| - 3 / 10) + 6) (by positivity) ?_
      (by rw [← hexp_eq]; nlinarith) ?_
    · rw [← hexp_eq, Real.exp_add, mul_comm E]
      have h_mul : 3 * ((143 / 2) * E) = (429 / 2) * E := by ring
      rw [h_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      calc
        (429 / 2 : ℝ) ≤ (8 / 3) ^ 6 := by norm_num
        _ ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) hexp1 6
        _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
    · rw [norm_riemannZeta₁_eq_functional_of_re_le_half hy hz_mem (by linarith)]
      have hp1 : ‖z - 1‖ * ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w) *
          Complex.cos (↑Real.pi * w / 2) * Complex.Gamma w‖ ≤
          ((13 / 8) * K) * (2 * E) :=
        mul_le_mul hz_sub1 hchi (norm_nonneg _) (by positivity)
      calc
        ‖z - 1‖ * ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w) *
            Complex.cos (↑Real.pi * w / 2) * Complex.Gamma w‖ * ‖riemannZeta w‖
          ≤ (((13 / 8) * K) * (2 * E)) * 22 :=
            mul_le_mul hp1 hzeta_w (norm_nonneg _) (by positivity)
        _ = ((143 / 2) * E) * K := by ring
  · -- Branch 4b: `π / 2 + 13 / 25 < θ ≤ 3 * π / 2 - 13 / 25` (`z.re ≤ -2 / 5`, `w.re ≥ 7 / 5`)
    have hsin_ge : (12 / 25 : ℝ) ≤ Real.sin (θ - Real.pi / 2) := by
      by_cases h_mid : θ ≤ Real.pi
      · have hcube := Real.sin_gt_sub_cube (by linarith : 0 < θ - Real.pi / 2)
        have hmono : (13 / 25) - (13 / 25) ^ 3 / 6 ≤
            (θ - Real.pi / 2) - (θ - Real.pi / 2) ^ 3 / 6 := by
          have hd : 0 ≤ ((θ - Real.pi / 2) - 13 / 25) *
              (1 - ((θ - Real.pi / 2) ^ 2 + (θ - Real.pi / 2) * (13 / 25) +
                (13 / 25) ^ 2) / 6) :=
            mul_nonneg (by linarith) (by nlinarith [Real.pi_lt_four])
          linarith
        linarith
      · have h_sym : Real.sin (θ - Real.pi / 2) = Real.sin (3 * Real.pi / 2 - θ) := by
          rw [← Real.sin_pi_sub]
          ring_nf
        rw [h_sym]
        have hcube := Real.sin_gt_sub_cube (by linarith : 0 < 3 * Real.pi / 2 - θ)
        have hmono : (13 / 25) - (13 / 25) ^ 3 / 6 ≤
            (3 * Real.pi / 2 - θ) - (3 * Real.pi / 2 - θ) ^ 3 / 6 := by
          have hd : 0 ≤ ((3 * Real.pi / 2 - θ) - 13 / 25) *
              (1 - ((3 * Real.pi / 2 - θ) ^ 2 + (3 * Real.pi / 2 - θ) * (13 / 25) +
                (13 / 25) ^ 2) / 6) :=
            mul_nonneg (by linarith) (by nlinarith [Real.pi_lt_four])
          linarith
        linarith
    have hz_re : z.re ≤ -2 / 5 := by
      rw [hz_re_eq, cos_eq_neg_sin_sub_pi_div_two]
      linarith
    let w : ℂ := 1 - z
    have hw_re_lo : 7 / 5 ≤ w.re := by simp [w]; linarith
    have hw_re_hi : w.re ≤ 4 := by simp [w]; linarith
    have hw_im : |w.im| = |z.im| := by simp [w]
    have hchi := norm_chi_factor_le hy (by linarith) hw_re_hi
      (by rw [hw_im]; linarith) (by rw [hw_im]; exact hz_im_hi)
    have hzeta_w : ‖riemannZeta w‖ ≤ 9 / 2 := by
      have hb := norm_riemannZeta_le_of_one_lt_re (by linarith : 1 < w.re)
      have hd : 1 / (w.re - 1) ≤ 5 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have hexp_eq : w.re - 1 / 2 = -3 / 2 - 5 * Real.cos θ := by
      simp [w, hz_re_eq]
      ring
    let E : ℝ := Real.exp ((w.re - 1 / 2) * (Real.log |y| - 3 / 10))
    refine to_log_bound ((117 / 8) * E)
      ((-3 / 2 - 5 * Real.cos θ) * (Real.log |y| - 3 / 10) + 4) (by positivity) ?_
      (by rw [← hexp_eq]; nlinarith) ?_
    · rw [← hexp_eq, Real.exp_add, mul_comm E]
      have h_mul : 3 * ((117 / 8) * E) = (351 / 8) * E := by ring
      rw [h_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      calc
        (351 / 8 : ℝ) ≤ (8 / 3) ^ 4 := by norm_num
        _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) hexp1 4
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    · rw [norm_riemannZeta₁_eq_functional_of_re_le_half hy hz_mem (by linarith)]
      have hp1 : ‖z - 1‖ * ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w) *
          Complex.cos (↑Real.pi * w / 2) * Complex.Gamma w‖ ≤
          ((13 / 8) * K) * (2 * E) :=
        mul_le_mul hz_sub1 hchi (norm_nonneg _) (by positivity)
      calc
        ‖z - 1‖ * ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w) *
            Complex.cos (↑Real.pi * w / 2) * Complex.Gamma w‖ * ‖riemannZeta w‖
          ≤ (((13 / 8) * K) * (2 * E)) * (9 / 2) :=
            mul_le_mul hp1 hzeta_w (norm_nonneg _) (by positivity)
        _ = ((117 / 8) * E) * K := by ring
  · -- Branch 4c: `3 * π / 2 - 13 / 25 < θ ≤ 3 * π / 2 - 11 / 25`
    -- (`z.re ≤ -1 / 20`, `w.re ≥ 21 / 20`)
    have hsin_ge : (41 / 100 : ℝ) ≤ Real.sin (θ - Real.pi / 2) := by
      have h_sym : Real.sin (θ - Real.pi / 2) = Real.sin (3 * Real.pi / 2 - θ) := by
        rw [← Real.sin_pi_sub]
        ring_nf
      rw [h_sym]
      have hcube := Real.sin_gt_sub_cube (by linarith : 0 < 3 * Real.pi / 2 - θ)
      have hmono : (11 / 25) - (11 / 25) ^ 3 / 6 ≤
          (3 * Real.pi / 2 - θ) - (3 * Real.pi / 2 - θ) ^ 3 / 6 := by
        have hd : 0 ≤ ((3 * Real.pi / 2 - θ) - 11 / 25) *
            (1 - ((3 * Real.pi / 2 - θ) ^ 2 + (3 * Real.pi / 2 - θ) * (11 / 25) +
              (11 / 25) ^ 2) / 6) :=
          mul_nonneg (by linarith) (by nlinarith)
        linarith
      linarith
    have hz_re : z.re ≤ -1 / 20 := by
      rw [hz_re_eq, cos_eq_neg_sin_sub_pi_div_two]
      linarith
    let w : ℂ := 1 - z
    have hw_re_lo : 21 / 20 ≤ w.re := by simp [w]; linarith
    have hw_re_hi : w.re ≤ 4 := by simp [w]; linarith
    have hw_im : |w.im| = |z.im| := by simp [w]
    have hchi := norm_chi_factor_le hy (by linarith) hw_re_hi
      (by rw [hw_im]; linarith) (by rw [hw_im]; exact hz_im_hi)
    have hzeta_w : ‖riemannZeta w‖ ≤ 22 := by
      have hb := norm_riemannZeta_le_of_one_lt_re (by linarith : 1 < w.re)
      have hd : 1 / (w.re - 1) ≤ 20 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have hexp_eq : w.re - 1 / 2 = -3 / 2 - 5 * Real.cos θ := by
      simp [w, hz_re_eq]
      ring
    let E : ℝ := Real.exp ((w.re - 1 / 2) * (Real.log |y| - 3 / 10))
    refine to_log_bound ((143 / 2) * E)
      ((-3 / 2 - 5 * Real.cos θ) * (Real.log |y| - 3 / 10) + 6) (by positivity) ?_
      (by rw [← hexp_eq]; nlinarith) ?_
    · rw [← hexp_eq, Real.exp_add, mul_comm E]
      have h_mul : 3 * ((143 / 2) * E) = (429 / 2) * E := by ring
      rw [h_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      calc
        (429 / 2 : ℝ) ≤ (8 / 3) ^ 6 := by norm_num
        _ ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) hexp1 6
        _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
    · rw [norm_riemannZeta₁_eq_functional_of_re_le_half hy hz_mem (by linarith)]
      have hp1 : ‖z - 1‖ * ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w) *
          Complex.cos (↑Real.pi * w / 2) * Complex.Gamma w‖ ≤
          ((13 / 8) * K) * (2 * E) :=
        mul_le_mul hz_sub1 hchi (norm_nonneg _) (by positivity)
      calc
        ‖z - 1‖ * ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w) *
            Complex.cos (↑Real.pi * w / 2) * Complex.Gamma w‖ * ‖riemannZeta w‖
          ≤ (((13 / 8) * K) * (2 * E)) * 22 :=
            mul_le_mul hp1 hzeta_w (norm_nonneg _) (by positivity)
        _ = ((143 / 2) * E) * K := by ring
  · -- Branch 5: `3 * π / 2 - 11 / 25 < θ ≤ 3 * π / 2 - 31 / 100` (`-1 / 5 ≤ z.re ≤ 1 / 2`)
    have hz_re_up : z.re ≤ 1 / 2 := by
      have hs : 3 / 10 ≤ Real.sin (3 * Real.pi / 2 - θ) := by
        have hcube := Real.sin_gt_sub_cube (by linarith : 0 < 3 * Real.pi / 2 - θ)
        have hmono : (31 / 100) - (31 / 100) ^ 3 / 6 ≤
            (3 * Real.pi / 2 - θ) - (3 * Real.pi / 2 - θ) ^ 3 / 6 := by
          have hd : 0 ≤ ((3 * Real.pi / 2 - θ) - 31 / 100) *
              (1 - ((3 * Real.pi / 2 - θ) ^ 2 + (3 * Real.pi / 2 - θ) * (31 / 100) +
                (31 / 100) ^ 2) / 6) :=
            mul_nonneg (by linarith) (by nlinarith)
          linarith
        linarith
      have hsym : Real.sin (θ - Real.pi / 2) = Real.sin (3 * Real.pi / 2 - θ) := by
        rw [← Real.sin_pi_sub]
        ring_nf
      rw [hz_re_eq, cos_eq_neg_sin_sub_pi_div_two, hsym]
      linarith
    let w : ℂ := 1 - z
    have hw_re_lo : 1 / 2 ≤ w.re := by simp [w]; linarith
    have hw_re_hi : w.re ≤ 6 / 5 := by
      have hcos : -11 / 25 ≤ Real.cos θ := by
        have hsym : Real.sin (θ - Real.pi / 2) = Real.sin (3 * Real.pi / 2 - θ) := by
          rw [← Real.sin_pi_sub]; ring_nf
        have hs : Real.sin (3 * Real.pi / 2 - θ) ≤ 11 / 25 :=
          (Real.sin_lt (by linarith)).le.trans (by linarith)
        rw [cos_eq_neg_sin_sub_pi_div_two, hsym]
        linarith
      simp [w]
      linarith
    have hw_im : |w.im| = |z.im| := by simp [w]
    have hchi := norm_chi_factor_le hy hw_re_lo (by linarith)
      (by rw [hw_im]; linarith) (by rw [hw_im]; exact hz_im_hi)
    have hchi_y : ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w) * Complex.cos (↑Real.pi * w / 2) *
        Complex.Gamma w‖ ≤ 2 * Real.exp ((7 / 10) * Real.log |y|) := by
      refine hchi.trans ?_
      have hexp_le : Real.exp ((w.re - 1 / 2) * (Real.log |y| - 3 / 10)) ≤
          Real.exp ((7 / 10) * Real.log |y|) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      linarith
    have hzeta_w : ‖riemannZeta w‖ ≤ (9 / 2) * |y| := by
      have hw_ne1 : w ≠ 1 := by
        intro h; have := congrArg Complex.im h; simp [w] at this
        rw [this] at hz_im_lo; norm_num at hz_im_lo; linarith
      have hb := norm_riemannZeta_le (by linarith) hw_ne1
      have hw1 : 3 ≤ ‖w - 1‖ := by
        have h1' : w - 1 = -z := by dsimp [w]; ring
        rw [h1', norm_neg]
        exact (by linarith : 3 ≤ |z.im|).trans (Complex.abs_im_le_norm z)
      have hd1 : 1 / ‖w - 1‖ ≤ 1 / 3 :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hw1
      have hd2 : ‖w‖ / w.re ≤ 2 * ‖w‖ := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [norm_nonneg w]
      have hw_n : ‖w‖ ≤ 2 * |y| := by
        have h1' : ‖w‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le 1 z
        rw [norm_one] at h1'
        linarith
      linarith
    refine to_log_bound ((117 / 8) * |y| * Real.exp ((7 / 10) * Real.log |y|))
      ((17 / 10) * Real.log |y| + 4) (by positivity) ?_ (by linarith) ?_
    · have hexp_split : Real.exp ((17 / 10) * Real.log |y| + 4) =
          Real.exp 4 * (|y| * Real.exp ((7 / 10) * Real.log |y|)) := by
        rw [← Real.exp_log (by linarith : 0 < |y|), ← Real.exp_add, ← Real.exp_add,
          Real.log_exp]
        congr 1
        ring
      rw [hexp_split]
      have h_mul : 3 * ((117 / 8) * |y| * Real.exp ((7 / 10) * Real.log |y|)) =
          (351 / 8) * (|y| * Real.exp ((7 / 10) * Real.log |y|)) := by ring
      rw [h_mul]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc
        (351 / 8 : ℝ) ≤ (8 / 3) ^ 4 := by norm_num
        _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) hexp1 4
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    · rw [norm_riemannZeta₁_eq_functional_of_re_le_half hy hz_mem (by linarith)]
      have hp1 : ‖z - 1‖ * ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w) *
          Complex.cos (↑Real.pi * w / 2) * Complex.Gamma w‖ ≤
          ((13 / 8) * K) * (2 * Real.exp ((7 / 10) * Real.log |y|)) :=
        mul_le_mul hz_sub1 hchi_y (norm_nonneg _) (by positivity)
      calc
        ‖z - 1‖ * ‖(2 : ℂ) * (2 * ↑Real.pi) ^ (-w) *
            Complex.cos (↑Real.pi * w / 2) * Complex.Gamma w‖ * ‖riemannZeta w‖
          ≤ (((13 / 8) * K) * (2 * Real.exp ((7 / 10) * Real.log |y|))) * ((9 / 2) * |y|) :=
            mul_le_mul hp1 hzeta_w (norm_nonneg _) (by positivity)
        _ = ((117 / 8) * |y| * Real.exp ((7 / 10) * Real.log |y|)) * K := by ring
  · -- Branch 6: `3 * π / 2 - 31 / 100 < θ ≤ 3 * π / 2 - 4 / 25` (`z.re ≥ 9 / 20`)
    have hcos : -31 / 100 ≤ Real.cos θ := by
      have hsym : Real.sin (θ - Real.pi / 2) = Real.sin (3 * Real.pi / 2 - θ) := by
        rw [← Real.sin_pi_sub]; ring_nf
      have hs : Real.sin (3 * Real.pi / 2 - θ) ≤ 31 / 100 :=
        (Real.sin_lt (by linarith)).le.trans (by linarith)
      rw [cos_eq_neg_sin_sub_pi_div_two, hsym]
      linarith
    have hz_re : 9 / 20 ≤ z.re := by linarith
    have hb := norm_riemannZeta₁_le (by linarith : 0 < z.re)
    have hdiv : ‖z‖ / z.re ≤ (25 / 6) * |y| := by
      rw [div_le_iff₀ (by linarith)]
      have h1' : (25 / 6) * |y| * (9 / 20) ≤ (25 / 6) * |y| * z.re :=
        mul_le_mul_of_nonneg_left hz_re (by positivity)
      linarith
    refine to_log_bound ((175 / 24) * |y|) (Real.log |y| + 4) (by positivity) ?_
      (by linarith) ?_
    · rw [Real.exp_add, Real.exp_log (by linarith), mul_comm |y|]
      have h_mul : 3 * ((175 / 24) * |y|) = (175 / 8) * |y| := by ring
      rw [h_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg y)
      calc
        (175 / 8 : ℝ) ≤ (8 / 3) ^ 4 := by norm_num
        _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) hexp1 4
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    · have h_prod_b : ‖z - 1‖ * (1 + ‖z‖ / z.re) ≤ ((13 / 8) * K) * ((53 / 12) * |y|) :=
        mul_le_mul hz_sub1 (by linarith) (by positivity) (by positivity)
      nlinarith
  · -- Branch 7: `3 * π / 2 - 4 / 25 < θ ≤ 3 * π / 2 - 1 / 10` (`z.re ≥ 6 / 5`)
    have hcos : -4 / 25 ≤ Real.cos θ := by
      have hsym : Real.sin (θ - Real.pi / 2) = Real.sin (3 * Real.pi / 2 - θ) := by
        rw [← Real.sin_pi_sub]; ring_nf
      have hs : Real.sin (3 * Real.pi / 2 - θ) ≤ 4 / 25 :=
        (Real.sin_lt (by linarith)).le.trans (by linarith)
      rw [cos_eq_neg_sin_sub_pi_div_two, hsym]
      linarith
    have hz_re : 6 / 5 ≤ z.re := by linarith
    have hz_ne1 : z ≠ 1 := fun h ↦ by have := congrArg Complex.re h; simp at this; linarith
    have hzeta1 : ‖riemannZeta₁ z‖ = ‖z - 1‖ * ‖riemannZeta z‖ := by
      have hs_ne : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne1
      rw [show riemannZeta₁ z = (z - 1) * riemannZeta z by
        rw [riemannZeta_eq_inv_sub_mul hz_ne1, ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul],
        norm_mul]
    have hzeta_b : ‖riemannZeta z‖ ≤ 7 := by
      have hb := norm_riemannZeta_le_of_one_lt_re (by linarith : 1 < z.re)
      have hdiv : 1 / (z.re - 1) ≤ 5 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    refine to_log_bound (91 / 8) 4 (by norm_num) ?_ (by norm_num) ?_
    · calc
        3 * (91 / 8 : ℝ) ≤ (8 / 3) ^ 4 := by norm_num
        _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) hexp1 4
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    · rw [hzeta1]
      calc
        ‖z - 1‖ * ‖riemannZeta z‖ ≤ ((13 / 8) * K) * 7 :=
          mul_le_mul hz_sub1 hzeta_b (norm_nonneg _) (by positivity)
        _ = (91 / 8) * K := by ring
  · -- Branch 8: `θ > 3 * π / 2 - 1 / 10` (`z.re ≥ 3 / 2`)
    have hcos : -1 / 10 ≤ Real.cos θ := by
      have hsym : Real.sin (θ - Real.pi / 2) = Real.sin (3 * Real.pi / 2 - θ) := by
        rw [← Real.sin_pi_sub]; ring_nf
      have hs : Real.sin (3 * Real.pi / 2 - θ) ≤ 1 / 10 := by
        rcases le_or_gt (3 * Real.pi / 2 - θ) 0 with hneg | hpos
        · exact (Real.sin_nonpos_of_nonpos_of_neg_pi_le hneg
            (by linarith [Real.pi_gt_three])).trans (by norm_num)
        · exact (Real.sin_lt hpos).le.trans (by linarith)
      rw [cos_eq_neg_sin_sub_pi_div_two, hsym]
      linarith
    have hz_re : 3 / 2 ≤ z.re := by linarith
    have hz_ne1 : z ≠ 1 := fun h ↦ by have := congrArg Complex.re h; simp at this; linarith
    have hzeta1 : ‖riemannZeta₁ z‖ = ‖z - 1‖ * ‖riemannZeta z‖ := by
      have hs_ne : z - 1 ≠ 0 := sub_ne_zero.mpr hz_ne1
      rw [show riemannZeta₁ z = (z - 1) * riemannZeta z by
        rw [riemannZeta_eq_inv_sub_mul hz_ne1, ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul],
        norm_mul]
    have hzeta_b : ‖riemannZeta z‖ ≤ 4 := by
      have hb := norm_riemannZeta_le_of_one_lt_re (by linarith : 1 < z.re)
      have hdiv : 1 / (z.re - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    refine to_log_bound (13 / 2) 3 (by norm_num) ?_ (by norm_num) ?_
    · calc
        3 * (13 / 2 : ℝ) ≤ (65 / 24) ^ 3 := by norm_num
        _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) hexp1_fine 3
        _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
    · rw [hzeta1]
      calc
        ‖z - 1‖ * ‖riemannZeta z‖ ≤ ((13 / 8) * K) * 4 :=
          mul_le_mul hz_sub1 hzeta_b (norm_nonneg _) (by positivity)
        _ = (13 / 2) * K := by ring

/-!
## Section 4: Exact Integration of `circleMaj` & Sharp `3 / 4` Zero-Counting Bound
-/

/-- Interval integrability of the piecewise bounded measurable function `circleMaj y`. -/
lemma intervalIntegrable_circleMaj (y : ℝ) (a b : ℝ) :
    IntervalIntegrable (circleMaj y) volume a b := by
  let Labs : ℝ := abs (Real.log (abs y))
  have hm_cos : ∀ c : ℝ, Measurable (fun θ : ℝ ↦
      (-3 / 2 - 5 * Real.cos θ) * (Real.log |y| - 3 / 10) + c) :=
    fun c ↦ ((measurable_const.sub (Real.measurable_cos.const_mul 5)).mul_const
      (Real.log |y| - 3 / 10)).add measurable_const
  have hm : Measurable (circleMaj y) := by
    unfold circleMaj
    exact Measurable.ite measurableSet_Iic measurable_const
      (Measurable.ite measurableSet_Iic measurable_const
        (Measurable.ite measurableSet_Iic measurable_const
          (Measurable.ite measurableSet_Iic measurable_const
            (Measurable.ite measurableSet_Iic (hm_cos 6)
              (Measurable.ite measurableSet_Iic (hm_cos 4)
                (Measurable.ite measurableSet_Iic (hm_cos 6)
                  (Measurable.ite measurableSet_Iic measurable_const
                    (Measurable.ite measurableSet_Iic measurable_const
                      (Measurable.ite measurableSet_Iic measurable_const
                        measurable_const)))))))))
  have hnorm : ∀ θ : ℝ, ‖circleMaj y θ‖ ≤ 7 * Labs + 9 := by
    intro θ
    unfold circleMaj
    have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have hl : 0 ≤ Labs := abs_nonneg _
    have hl_le : Real.log |y| ≤ Labs := le_abs_self (Real.log |y|)
    have hl_neg : -Real.log |y| ≤ Labs := neg_le_abs (Real.log |y|)
    have h1 := (abs_le.mp hc).1
    have h2 := (abs_le.mp hc).2
    split_ifs <;> · rw [Real.norm_eq_abs, abs_le]; constructor <;> nlinarith
  exact (intervalIntegrable_const (c := 7 * Labs + 9)).mono_fun'
    hm.aestronglyMeasurable (ae_of_all _ hnorm)

/-- Rational bounds `903 / 1000 ≤ Real.cos (11 / 25) ≤ 9048 / 10000` proved by MVT. -/
lemma cos_eleven_twenty_fifths_bounds :
    (903 / 1000 : ℝ) ≤ Real.cos (11 / 25 : ℝ) ∧ Real.cos (11 / 25 : ℝ) ≤ 9048 / 10000 := by
  have hd_hi : ∀ t ∈ Icc (0 : ℝ) (11 / 25),
      HasDerivAt (fun x : ℝ ↦ Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24))
        (-(Real.sin t - (t - t ^ 3 / 6))) t := by
    intro t _
    have h1 := Real.hasDerivAt_cos t
    have h2 : HasDerivAt (fun x : ℝ ↦ 1 - x ^ 2 / 2 + x ^ 4 / 24) (-t + t ^ 3 / 6) t := by
      have p2 := (hasDerivAt_pow 2 t).div_const 2
      have p4 := (hasDerivAt_pow 4 t).div_const 24
      refine ((hasDerivAt_const t (1 : ℝ)).sub p2 |>.add p4).congr_deriv ?_
      ring
    exact (h1.sub h2).congr_deriv (by ring)
  have hd_lo : ∀ t ∈ Icc (0 : ℝ) (11 / 25),
      HasDerivAt (fun x : ℝ ↦ Real.cos x - (1 - x ^ 2 / 2)) (-(Real.sin t - t)) t := by
    intro t _
    have h1 := Real.hasDerivAt_cos t
    have h2 : HasDerivAt (fun x : ℝ ↦ 1 - x ^ 2 / 2) (-t) t :=
      ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).congr_deriv (by ring)
    exact (h1.sub h2).congr_deriv (by ring)
  obtain ⟨ξ1, hξ1_mem, hξ1_eq⟩ := exists_hasDerivAt_eq_slope
    (fun x : ℝ ↦ Real.cos x - (1 - x ^ 2 / 2)) (fun t ↦ -(Real.sin t - t))
    (by norm_num : (0 : ℝ) < 11 / 25)
    (fun t ht ↦ (hd_lo t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ hd_lo t (Ioo_subset_Icc_self ht))
  obtain ⟨ξ2, hξ2_mem, hξ2_eq⟩ := exists_hasDerivAt_eq_slope
    (fun x : ℝ ↦ Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24))
    (fun t ↦ -(Real.sin t - (t - t ^ 3 / 6))) (by norm_num : (0 : ℝ) < 11 / 25)
    (fun t ht ↦ (hd_hi t ht).continuousAt.continuousWithinAt)
    (fun t ht ↦ hd_hi t (Ioo_subset_Icc_self ht))
  have hsin_lt := Real.sin_lt hξ1_mem.1
  have hsin_gt := Real.sin_gt_sub_cube hξ2_mem.1
  rw [eq_div_iff (by norm_num : (11 / 25 : ℝ) - 0 ≠ 0)] at hξ1_eq hξ2_eq
  simp only [Real.cos_zero] at hξ1_eq hξ2_eq
  constructor <;> nlinarith

set_option maxHeartbeats 1200000 in
-- Explicit numerical interval and contour integral bounds.
/-- Integral upper bound for `circleMaj y` over `[0, 2 * π]`:
`∫ θ in 0..(2 * π), circleMaj y θ ≤ 2 * π * ((3 / 2 * Real.log 2) * Real.log |y| + 13 / 4)`. -/
lemma integral_circleMaj_le {y : ℝ} (hy : 8 ≤ |y|) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), circleMaj y θ) ≤
      2 * Real.pi * ((3 / 2 * Real.log 2) * Real.log |y| + 13 / 4) := by
  let t0 : ℝ := 0
  let s0 : ℝ := Real.pi / 2 + 1 / 10
  let t1 : ℝ := Real.pi / 2 + 4 / 25
  let t2 : ℝ := Real.pi / 2 + 31 / 100
  let t3 : ℝ := Real.pi / 2 + 11 / 25
  let m1 : ℝ := Real.pi / 2 + 13 / 25
  let m2 : ℝ := 3 * Real.pi / 2 - 13 / 25
  let t4 : ℝ := 3 * Real.pi / 2 - 11 / 25
  let t5 : ℝ := 3 * Real.pi / 2 - 31 / 100
  let t6 : ℝ := 3 * Real.pi / 2 - 4 / 25
  let s1 : ℝ := 3 * Real.pi / 2 - 1 / 10
  let t7 : ℝ := 2 * Real.pi
  have hpi_lo : (3141592 / 1000000 : ℝ) < Real.pi := by linarith [Real.pi_gt_d6]
  have hpi_hi : Real.pi < (3141593 / 1000000 : ℝ) := by linarith [Real.pi_lt_d6]
  have ht0s : t0 ≤ s0 := by dsimp [t0, s0]; linarith
  have hs01 : s0 ≤ t1 := by dsimp [s0, t1]; linarith
  have ht12 : t1 ≤ t2 := by dsimp [t1, t2]; linarith
  have ht23 : t2 ≤ t3 := by dsimp [t2, t3]; linarith
  have ht3m1 : t3 ≤ m1 := by dsimp [t3, m1]; linarith
  have hm12 : m1 ≤ m2 := by dsimp [m1, m2]; linarith
  have hm24 : m2 ≤ t4 := by dsimp [m2, t4]; linarith
  have ht45 : t4 ≤ t5 := by dsimp [t4, t5]; linarith
  have ht56 : t5 ≤ t6 := by dsimp [t5, t6]; linarith
  have ht6s : t6 ≤ s1 := by dsimp [t6, s1]; linarith
  have hs17 : s1 ≤ t7 := by dsimp [s1, t7]; linarith
  have hsplit : (∫ θ in t0..t7, circleMaj y θ) =
      (∫ θ in t0..s0, circleMaj y θ) + (∫ θ in s0..t1, circleMaj y θ) +
      (∫ θ in t1..t2, circleMaj y θ) + (∫ θ in t2..t3, circleMaj y θ) +
      ((∫ θ in t3..m1, circleMaj y θ) + (∫ θ in m1..m2, circleMaj y θ) +
        (∫ θ in m2..t4, circleMaj y θ)) +
      (∫ θ in t4..t5, circleMaj y θ) + (∫ θ in t5..t6, circleMaj y θ) +
      (∫ θ in t6..s1, circleMaj y θ) + (∫ θ in s1..t7, circleMaj y θ) := by
    have hi := intervalIntegrable_circleMaj y
    have add_adj := fun a b c ↦ intervalIntegral.integral_add_adjacent_intervals (hi a b) (hi b c)
    rw [add_adj t0 s0 t1, add_adj t0 t1 t2, add_adj t0 t2 t3,
      add_adj t3 m1 m2, add_adj t3 m2 t4, add_adj t0 t3 t4,
      add_adj t0 t4 t5, add_adj t0 t5 t6, add_adj t0 t6 s1, add_adj t0 s1 t7]
  have it_t : ∀ {c : Prop} [Decidable c] {x y : ℝ}, c → (if c then x else y) = x :=
    fun h ↦ by simp [h]
  have nle : ∀ {a b θ : ℝ}, a ≤ b → b < θ → ¬ θ ≤ a :=
    fun hab hlt ↦ not_le.mpr (lt_of_le_of_lt hab hlt)
  have it_f : ∀ {a b θ : ℝ} [Decidable (θ ≤ a)] {x y : ℝ},
      a ≤ b → b < θ → (if θ ≤ a then x else y) = y :=
    fun hab hlt ↦ by simp [nle hab hlt]
  have hi0 : (∫ θ in t0..s0, circleMaj y θ) = (s0 - t0) * 3 := by
    have hc : EqOn (circleMaj y) (fun _ ↦ (3 : ℝ)) (Ioc t0 s0) := by
      intro θ hθ; unfold circleMaj; rw [it_t hθ.2]
    rw [intervalIntegral.integral_of_le ht0s, setIntegral_congr_fun measurableSet_Ioc hc,
      ← intervalIntegral.integral_of_le ht0s, intervalIntegral.integral_const, smul_eq_mul]
  have hi1 : (∫ θ in s0..t1, circleMaj y θ) = (t1 - s0) * 4 := by
    have hc : EqOn (circleMaj y) (fun _ ↦ (4 : ℝ)) (Ioc s0 t1) := by
      intro θ hθ; unfold circleMaj
      rw [it_f le_rfl hθ.1, it_t hθ.2]
    rw [intervalIntegral.integral_of_le hs01, setIntegral_congr_fun measurableSet_Ioc hc,
      ← intervalIntegral.integral_of_le hs01, intervalIntegral.integral_const, smul_eq_mul]
  have hi2 : (∫ θ in t1..t2, circleMaj y θ) = (t2 - t1) * (Real.log |y| + 4) := by
    have hc : EqOn (circleMaj y) (fun _ ↦ Real.log |y| + 4) (Ioc t1 t2) := by
      intro θ hθ; unfold circleMaj
      rw [it_f hs01 hθ.1, it_f le_rfl hθ.1, it_t hθ.2]
    rw [intervalIntegral.integral_of_le ht12, setIntegral_congr_fun measurableSet_Ioc hc,
      ← intervalIntegral.integral_of_le ht12, intervalIntegral.integral_const, smul_eq_mul]
  have hi3 : (∫ θ in t2..t3, circleMaj y θ) = (t3 - t2) * ((17 / 10) * Real.log |y| + 4) := by
    have hc : EqOn (circleMaj y) (fun _ ↦ (17 / 10) * Real.log |y| + 4) (Ioc t2 t3) := by
      intro θ hθ; dsimp [t2] at hθ; unfold circleMaj
      rw [it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f le_rfl hθ.1, it_t hθ.2]
    rw [intervalIntegral.integral_of_le ht23, setIntegral_congr_fun measurableSet_Ioc hc,
      ← intervalIntegral.integral_of_le ht23, intervalIntegral.integral_const, smul_eq_mul]
  have hi4 :
      (∫ θ in t3..m1, circleMaj y θ) + (∫ θ in m1..m2, circleMaj y θ) +
          (∫ θ in m2..t4, circleMaj y θ) =
        ((-3 / 2) * (t4 - t3) + 10 * Real.cos (11 / 25)) * (Real.log |y| - 3 / 10) +
          6 * (m1 - t3) + 4 * (m2 - m1) + 6 * (t4 - m2) := by
    let fbase : ℝ → ℝ := fun θ ↦ (-3 / 2 - 5 * Real.cos θ) * (Real.log |y| - 3 / 10)
    have hf_ii : ∀ a b : ℝ, IntervalIntegrable fbase volume a b := fun a b ↦
      ((intervalIntegrable_const.sub
        (Real.continuous_cos.intervalIntegrable a b |>.const_mul 5)).mul_const _)
    have hm_a : (∫ θ in t3..m1, circleMaj y θ) = (∫ θ in t3..m1, fbase θ) + 6 * (m1 - t3) := by
      have hc : EqOn (circleMaj y) (fun θ ↦ fbase θ + 6) (Ioc t3 m1) := by
        intro θ hθ; dsimp [t3, fbase] at hθ ⊢; unfold circleMaj
        rw [it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
          it_f (by linarith) hθ.1, it_f le_rfl hθ.1, it_t hθ.2]
      rw [intervalIntegral.integral_of_le ht3m1, setIntegral_congr_fun measurableSet_Ioc hc,
        ← intervalIntegral.integral_of_le ht3m1,
        intervalIntegral.integral_add (hf_ii t3 m1) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    have hm_b : (∫ θ in m1..m2, circleMaj y θ) = (∫ θ in m1..m2, fbase θ) + 4 * (m2 - m1) := by
      have hc : EqOn (circleMaj y) (fun θ ↦ fbase θ + 4) (Ioc m1 m2) := by
        intro θ hθ; dsimp [m1, fbase] at hθ ⊢; unfold circleMaj
        rw [it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
          it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
          it_f le_rfl hθ.1, it_t hθ.2]
      rw [intervalIntegral.integral_of_le hm12, setIntegral_congr_fun measurableSet_Ioc hc,
        ← intervalIntegral.integral_of_le hm12,
        intervalIntegral.integral_add (hf_ii m1 m2) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    have hm_c : (∫ θ in m2..t4, circleMaj y θ) = (∫ θ in m2..t4, fbase θ) + 6 * (t4 - m2) := by
      have hc : EqOn (circleMaj y) (fun θ ↦ fbase θ + 6) (Ioc m2 t4) := by
        intro θ hθ; dsimp [m2, fbase] at hθ ⊢; unfold circleMaj
        rw [it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
          it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
          it_f (by linarith) hθ.1, it_f le_rfl hθ.1, it_t hθ.2]
      rw [intervalIntegral.integral_of_le hm24, setIntegral_congr_fun measurableSet_Ioc hc,
        ← intervalIntegral.integral_of_le hm24,
        intervalIntegral.integral_add (hf_ii m2 t4) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul, mul_comm]
    have hcos_int : (∫ θ in t3..t4, Real.cos θ) = -2 * Real.cos (11 / 25) := by
      rw [integral_cos]
      have hs1 : Real.sin t4 = -Real.cos (11 / 25) := by
        dsimp [t4]
        have h : 3 * Real.pi / 2 - 11 / 25 = 2 * Real.pi - (11 / 25 + Real.pi / 2) := by ring
        rw [h, Real.sin_two_pi_sub, Real.sin_add_pi_div_two]
      have hs2 : Real.sin t3 = Real.cos (11 / 25) := by
        dsimp [t3]
        rw [add_comm, Real.sin_add_pi_div_two]
      rw [hs1, hs2]
      ring
    have hf_tot : (∫ θ in t3..t4, fbase θ) =
        ((-3 / 2) * (t4 - t3) + 10 * Real.cos (11 / 25)) * (Real.log |y| - 3 / 10) := by
      have hexpand : fbase =
          fun θ : ℝ ↦ (-3 / 2) * (Real.log |y| - 3 / 10) +
            (-5 * (Real.log |y| - 3 / 10)) * Real.cos θ := by
        ext θ; dsimp [fbase]; ring
      have hcos_ii : IntervalIntegrable
          (fun θ : ℝ ↦ (-5 * (Real.log |y| - 3 / 10)) * Real.cos θ) volume t3 t4 :=
        Real.continuous_cos.intervalIntegrable t3 t4 |>.const_mul _
      rw [hexpand, intervalIntegral.integral_add intervalIntegrable_const hcos_ii,
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hcos_int,
        smul_eq_mul]
      ring
    have hf_sum :
        (∫ θ in t3..m1, fbase θ) + (∫ θ in m1..m2, fbase θ) + (∫ θ in m2..t4, fbase θ) =
          ∫ θ in t3..t4, fbase θ := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hf_ii t3 m1) (hf_ii m1 m2),
        intervalIntegral.integral_add_adjacent_intervals (hf_ii t3 m2) (hf_ii m2 t4)]
    rw [hm_a, hm_b, hm_c]
    linarith [hf_sum, hf_tot]
  have hi5 : (∫ θ in t4..t5, circleMaj y θ) = (t5 - t4) * ((17 / 10) * Real.log |y| + 4) := by
    have hc : EqOn (circleMaj y) (fun _ ↦ (17 / 10) * Real.log |y| + 4) (Ioc t4 t5) := by
      intro θ hθ; dsimp [t4] at hθ; unfold circleMaj
      rw [it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f le_rfl hθ.1, it_t hθ.2]
    rw [intervalIntegral.integral_of_le ht45, setIntegral_congr_fun measurableSet_Ioc hc,
      ← intervalIntegral.integral_of_le ht45, intervalIntegral.integral_const, smul_eq_mul]
  have hi6 : (∫ θ in t5..t6, circleMaj y θ) = (t6 - t5) * (Real.log |y| + 4) := by
    have hc : EqOn (circleMaj y) (fun _ ↦ Real.log |y| + 4) (Ioc t5 t6) := by
      intro θ hθ; dsimp [t5] at hθ; unfold circleMaj
      rw [it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f (by linarith) hθ.1, it_f le_rfl hθ.1, it_t hθ.2]
    rw [intervalIntegral.integral_of_le ht56, setIntegral_congr_fun measurableSet_Ioc hc,
      ← intervalIntegral.integral_of_le ht56, intervalIntegral.integral_const, smul_eq_mul]
  have hi7 : (∫ θ in t6..s1, circleMaj y θ) = (s1 - t6) * 4 := by
    have hc : EqOn (circleMaj y) (fun _ ↦ (4 : ℝ)) (Ioc t6 s1) := by
      intro θ hθ; dsimp [t6] at hθ; unfold circleMaj
      rw [it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f le_rfl hθ.1, it_t hθ.2]
    rw [intervalIntegral.integral_of_le ht6s, setIntegral_congr_fun measurableSet_Ioc hc,
      ← intervalIntegral.integral_of_le ht6s, intervalIntegral.integral_const, smul_eq_mul]
  have hi8 : (∫ θ in s1..t7, circleMaj y θ) = (t7 - s1) * 3 := by
    have hc : EqOn (circleMaj y) (fun _ ↦ (3 : ℝ)) (Ioc s1 t7) := by
      intro θ hθ; dsimp [s1] at hθ; unfold circleMaj
      rw [it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f (by linarith) hθ.1, it_f (by linarith) hθ.1,
        it_f (by linarith) hθ.1, it_f le_rfl hθ.1]
    rw [intervalIntegral.integral_of_le hs17, setIntegral_congr_fun measurableSet_Ioc hc,
      ← intervalIntegral.integral_of_le hs17, intervalIntegral.integral_const, smul_eq_mul]
  change (∫ θ in t0..t7, circleMaj y θ) ≤ _
  rw [hsplit, hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8]
  dsimp [t0, s0, t1, t2, t3, m1, m2, t4, t5, t6, s1, t7]
  obtain ⟨hcos_lo, hcos_hi⟩ := cos_eleven_twenty_fifths_bounds
  have hlog2 : (6931 / 10000 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog_y_nonneg : 0 ≤ Real.log |y| := Real.log_nonneg (by linarith)
  have h_coeff :
      (31 / 100 - 4 / 25) + (17 / 10) * (11 / 25 - 31 / 100) +
          ((-3 / 2) * (Real.pi - 22 / 25) + 10 * Real.cos (11 / 25)) +
          (17 / 10) * (11 / 25 - 31 / 100) + (31 / 100 - 4 / 25) ≤
        2 * Real.pi * (3 / 2 * Real.log 2) := by
    nlinarith
  have h_mul := mul_le_mul_of_nonneg_right h_coeff hlog_y_nonneg
  have h_const :
      (Real.pi / 2 + 1 / 10) * 3 + (4 / 25 - 1 / 10) * 4 + (31 / 100 - 4 / 25) * 4 +
          (11 / 25 - 31 / 100) * 4 +
          ((-3 / 2) * (Real.pi - 22 / 25) + 10 * Real.cos (11 / 25)) * (-3 / 10) +
          6 * (2 / 25) + 4 * (Real.pi - 26 / 25) + 6 * (2 / 25) +
          (11 / 25 - 31 / 100) * 4 + (31 / 100 - 4 / 25) * 4 + (4 / 25 - 1 / 10) * 4 +
          (Real.pi / 2 + 1 / 10) * 3 ≤
        2 * Real.pi * (13 / 4) := by
    linarith
  have h_id :
      (Real.pi / 2 + 1 / 10 - 0) * 3 +
          (Real.pi / 2 + 4 / 25 - (Real.pi / 2 + 1 / 10)) * 4 +
          (Real.pi / 2 + 31 / 100 - (Real.pi / 2 + 4 / 25)) * (Real.log |y| + 4) +
          (Real.pi / 2 + 11 / 25 - (Real.pi / 2 + 31 / 100)) * ((17 / 10) * Real.log |y| + 4) +
          (((-3 / 2) * (3 * Real.pi / 2 - 11 / 25 - (Real.pi / 2 + 11 / 25)) +
            10 * Real.cos (11 / 25)) * (Real.log |y| - 3 / 10) +
            6 * (Real.pi / 2 + 13 / 25 - (Real.pi / 2 + 11 / 25)) +
            4 * (3 * Real.pi / 2 - 13 / 25 - (Real.pi / 2 + 13 / 25)) +
            6 * (3 * Real.pi / 2 - 11 / 25 - (3 * Real.pi / 2 - 13 / 25))) +
          (3 * Real.pi / 2 - 31 / 100 - (3 * Real.pi / 2 - 11 / 25)) *
            ((17 / 10) * Real.log |y| + 4) +
          (3 * Real.pi / 2 - 4 / 25 - (3 * Real.pi / 2 - 31 / 100)) * (Real.log |y| + 4) +
          (3 * Real.pi / 2 - 1 / 10 - (3 * Real.pi / 2 - 4 / 25)) * 4 +
          (2 * Real.pi - (3 * Real.pi / 2 - 1 / 10)) * 3 =
        ((31 / 100 - 4 / 25) + (17 / 10) * (11 / 25 - 31 / 100) +
          ((-3 / 2) * (Real.pi - 22 / 25) + 10 * Real.cos (11 / 25)) +
          (17 / 10) * (11 / 25 - 31 / 100) + (31 / 100 - 4 / 25)) * Real.log |y| +
        ((Real.pi / 2 + 1 / 10) * 3 + (4 / 25 - 1 / 10) * 4 + (31 / 100 - 4 / 25) * 4 +
          (11 / 25 - 31 / 100) * 4 +
          ((-3 / 2) * (Real.pi - 22 / 25) + 10 * Real.cos (11 / 25)) * (-3 / 10) +
          6 * (2 / 25) + 4 * (Real.pi - 26 / 25) + 6 * (2 / 25) +
          (11 / 25 - 31 / 100) * 4 + (31 / 100 - 4 / 25) * 4 + (4 / 25 - 1 / 10) * 4 +
          (Real.pi / 2 + 1 / 10) * 3) := by
    ring
  rw [h_id, mul_add]
  linarith

/-- **Local Height-4 Window Multiplicity Bound (`r = 5 / 2`, `R = 5`, `|y| ≥ 8`)**:
Under `RiemannHypothesis`, for every `y : ℝ` with `8 ≤ |y|`,
`∑ ρ ∈ nontrivialZetaZerosInFourWindow y, analyticOrderNatAt riemannZeta ρ ≤
  (3 / 2) * Real.log |y| + 47 / 10`. -/
theorem sum_analyticOrderNatAt_fourWindow_le_three_halves
    (hRH : RiemannHypothesis) {y : ℝ} (hy : 8 ≤ |y|) :
    ((∑ ρ ∈ nontrivialZetaZerosInFourWindow y, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
      (3 / 2) * Real.log |y| + 47 / 10 := by
  let c : ℂ := 2 + (y : ℂ) * I
  have h_div :
      ((∑ ρ ∈ nontrivialZetaZerosInFourWindow y, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
        ((∑ᶠ u, divisor riemannZeta₁ (closedBall c |(5 / 2 : ℝ)|) u : ℤ) : ℝ) := by
    refine sum_analyticOrderNatAt_le_finsum_divisor_riemannZeta₁
      (nontrivialZetaZerosInFourWindow y) c (5 / 2) fun ρ hρ ↦ ?_
    exact ⟨mem_closedBall_two_add_mul_I_five_halves_of_riemannHypothesis hRH y hρ,
      (mem_nontrivialZetaZerosInFourWindow.mp hρ).1.2.2⟩
  have h_jensen := sum_divisor_le_circleAverage_sub_log_norm
    (analyticOnNhd_riemannZeta₁ (closedBall c |(5 : ℝ)|))
    (r := 5 / 2) (by norm_num) (by norm_num) (riemannZeta₁_two_add_mul_I_ne_zero y)
  have h_ratio : (5 : ℝ) / (5 / 2) = 2 := by norm_num
  rw [h_ratio] at h_jensen
  have h_int_f : IntervalIntegrable
      (fun θ ↦ Real.log ‖riemannZeta₁ (circleMap c 5 θ)‖) volume 0 (2 * Real.pi) :=
    ((analyticOnNhd_riemannZeta₁ (closedBall c |(5 : ℝ)|)).mono
      (by simpa using sphere_subset_closedBall)).meromorphicOn.circleIntegrable_log_norm
  have h_avg_sub : Real.circleAverage (fun x ↦ Real.log ‖riemannZeta₁ x‖) c 5 -
      Real.log ‖riemannZeta₁ c‖ =
      (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.log ‖riemannZeta₁ (circleMap c 5 θ)‖ - Real.log ‖riemannZeta₁ c‖) := by
    rw [Real.circleAverage_def, smul_eq_mul]
    rw [intervalIntegral.integral_sub h_int_f intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    field_simp [Real.pi_ne_zero]
    ring
  have h_int_le :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.log ‖riemannZeta₁ (circleMap c 5 θ)‖ - Real.log ‖riemannZeta₁ c‖) ≤
      ∫ θ in (0 : ℝ)..(2 * Real.pi), circleMaj y θ := by
    refine intervalIntegral.integral_mono_on (by positivity)
      (h_int_f.sub intervalIntegrable_const) (intervalIntegrable_circleMaj y 0 (2 * Real.pi)) ?_
    intro θ hθ
    exact log_norm_riemannZeta₁_sub_le_circleMaj hy hθ.1 hθ.2
  have h_maj := integral_circleMaj_le hy
  have h_rhs_le : Real.circleAverage (fun x ↦ Real.log ‖riemannZeta₁ x‖) c 5 -
      Real.log ‖riemannZeta₁ c‖ ≤ (3 / 2 * Real.log 2) * Real.log |y| + 13 / 4 := by
    rw [h_avg_sub]
    calc
      (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖riemannZeta₁ (circleMap c 5 θ)‖ - Real.log ‖riemannZeta₁ c‖)
        ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * ((3 / 2 * Real.log 2) * Real.log |y| + 13 / 4)) :=
          mul_le_mul_of_nonneg_left (h_int_le.trans h_maj) (by positivity)
      _ = (3 / 2 * Real.log 2) * Real.log |y| + 13 / 4 :=
          inv_mul_cancel_left₀ (by positivity) _
  have hlog2 : (6931 / 10000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h_step : ((∑ᶠ u, divisor riemannZeta₁ (closedBall c |(5 / 2 : ℝ)|) u : ℤ) : ℝ) *
      Real.log 2 ≤ ((3 / 2) * Real.log |y| + 47 / 10) * Real.log 2 := by
    nlinarith
  exact h_div.trans (le_of_mul_le_mul_right h_step (by linarith))

/-- Sharpened `13 / 5` linear-term Riemann–von Mangoldt bound
(`(weightedZeroCountingFunction t : ℝ) ≤ (3 / 4) * t * Real.log t + (13 / 5) * t`) for `6 ≤ t`. -/
theorem weightedZeroCountingFunction_le_thirteen_fifths
    (hRH : RiemannHypothesis) {t : ℝ} (ht : 6 ≤ t) :
    (weightedZeroCountingFunction t : ℝ) ≤ (3 / 4) * t * Real.log t + (13 / 5) * t := by
  classical
  let K : ℕ := ⌊(t - 6) / 4⌋₊ + 1
  let W : ℕ → Finset ℂ := fun k ↦
    nontrivialZetaZerosInFourWindow (8 + 4 * (k : ℝ)) ∪
      nontrivialZetaZerosInFourWindow (-(8 + 4 * (k : ℝ)))
  have h_sub : nontrivialZetaZerosUpTo t ⊆ (Finset.range K).biUnion W :=
    nontrivialZetaZerosUpTo_subset_biUnion_fourWindows hRH t
  have h_nat_le :
      weightedZeroCountingFunction t ≤
        ∑ k ∈ Finset.range K, ∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ := by
    unfold weightedZeroCountingFunction
    exact (Finset.sum_le_sum_of_subset h_sub).trans
      (sum_biUnion_range_le_nat K W (analyticOrderNatAt riemannZeta))
  have h_real_le :
      (weightedZeroCountingFunction t : ℝ) ≤
        ∑ k ∈ Finset.range K, ((∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) := by
    exact_mod_cast h_nat_le
  have ht_pos : 0 < t := by linarith
  have h_wk_bound : ∀ k ∈ Finset.range K,
      ((∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
        3 * Real.log t + 52 / 5 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hk_le : k ≤ ⌊(t - 6) / 4⌋₊ := Nat.le_of_lt_succ hk
    have hk_real : (k : ℝ) ≤ (t - 6) / 4 :=
      (Nat.cast_le.mpr hk_le).trans (Nat.floor_le (by linarith))
    have hk_nonneg : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h_u_nat := sum_union_le_nat
      (nontrivialZetaZerosInFourWindow (8 + 4 * (k : ℝ)))
      (nontrivialZetaZerosInFourWindow (-(8 + 4 * (k : ℝ))))
      (analyticOrderNatAt riemannZeta)
    have h_u_real :
        ((∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
          ((∑ ρ ∈ nontrivialZetaZerosInFourWindow (8 + 4 * (k : ℝ)),
            analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) +
          ((∑ ρ ∈ nontrivialZetaZerosInFourWindow (-(8 + 4 * (k : ℝ))),
            analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) := by
      dsimp only [W]
      exact_mod_cast h_u_nat
    have hy1 : 8 ≤ |8 + 4 * (k : ℝ)| := by
      rw [abs_of_nonneg (by positivity)]
      linarith
    have hy2 : 8 ≤ |-(8 + 4 * (k : ℝ))| := by
      rw [abs_neg]
      exact hy1
    have hb1 := sum_analyticOrderNatAt_fourWindow_le_three_halves hRH hy1
    have hb2 := sum_analyticOrderNatAt_fourWindow_le_three_halves hRH hy2
    rw [abs_neg] at hb2
    have h_abs_le : |8 + 4 * (k : ℝ)| ≤ (4 / 3) * t := by
      rw [abs_of_nonneg (by positivity)]
      linarith
    have h_log_le : Real.log |8 + 4 * (k : ℝ)| ≤ Real.log t + 1 / 3 := by
      have h1 : Real.log |8 + 4 * (k : ℝ)| ≤ Real.log ((4 / 3) * t) :=
        Real.log_le_log (by positivity) h_abs_le
      rw [Real.log_mul (by norm_num) ht_pos.ne'] at h1
      have h2 : Real.log (4 / 3) ≤ 1 / 3 :=
        (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
      linarith
    linarith
  have h_sum_le :
      (∑ k ∈ Finset.range K, ((∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ)) ≤
        (K : ℝ) * (3 * Real.log t + 52 / 5) := by
    calc
      (∑ k ∈ Finset.range K, ((∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ))
        ≤ ∑ _k ∈ Finset.range K, (3 * Real.log t + 52 / 5) := Finset.sum_le_sum h_wk_bound
      _ = (K : ℝ) * (3 * Real.log t + 52 / 5) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hK_le : (K : ℝ) ≤ t / 4 := by
    dsimp only [K]
    push_cast
    have hfl : (⌊(t - 6) / 4⌋₊ : ℝ) ≤ (t - 6) / 4 := Nat.floor_le (by linarith)
    linarith
  have h_log_t_pos : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have h_prod_le :
      (K : ℝ) * (3 * Real.log t + 52 / 5) ≤ (t / 4) * (3 * Real.log t + 52 / 5) :=
    mul_le_mul_of_nonneg_right hK_le (by positivity)
  nlinarith

/-- **Part 1 (Sharp Multiplicity-Weighted Riemann–von Mangoldt Upper Bound, `a_rvM = 3 / 4`)**:
Under `RiemannHypothesis`, for all `6 ≤ t`,
`(weightedZeroCountingFunction t : ℝ) ≤ (3 / 4) * t * Real.log t + 4 * t`. -/
theorem weightedZeroCountingFunction_le_three_fourths
    (hRH : RiemannHypothesis) {t : ℝ} (ht : 6 ≤ t) :
    (weightedZeroCountingFunction t : ℝ) ≤ (3 / 4) * t * Real.log t + 4 * t := by
  linarith [weightedZeroCountingFunction_le_thirteen_fifths hRH ht]

/-- Unweighted Riemann–von Mangoldt corollary with `a_rvM = 3 / 4`, `C_rvM = 4`. -/
theorem zeroCountingFunction_le_three_fourths
    (hRH : RiemannHypothesis) {t : ℝ} (ht : 6 ≤ t) :
    (zeroCountingFunction t : ℝ) ≤ (3 / 4) * t * Real.log t + 4 * t := by
  have h1 : (zeroCountingFunction t : ℝ) ≤ (weightedZeroCountingFunction t : ℝ) := by
    exact_mod_cast zeroCountingFunction_le_weightedZeroCountingFunction t
  exact h1.trans (weightedZeroCountingFunction_le_three_fourths hRH ht)

/-!
## Section 5: Large-`x` (`x ≥ 21846`) Explicit Formula & `quarterClock` Bound for `n - θ(n)`
-/

/-- Base-4 digit count (`quarterClock (n - 1)` is the 120-state machine's base-4 clock). -/
def quarterClock : ℕ → ℕ
  | 0 => 0
  | z + 1 => 1 + quarterClock (z / 4)

/-- Exact base-4 invariant for `quarterClock`: `3 * z + 4 ≤ 4 ^ (quarterClock z + 1)`. -/
lemma three_mul_add_four_le_four_pow_quarterClock_succ (z : ℕ) :
    3 * z + 4 ≤ 4 ^ (quarterClock z + 1) := by
  induction z using Nat.strongRecOn with
  | ind n ih =>
    rcases n with _ | m
    · simp [quarterClock]
    · simp only [quarterClock]
      have hlt : m / 4 < m + 1 := by omega
      have h := ih (m / 4) hlt
      calc
        3 * (m + 1) + 4 ≤ 4 * (3 * (m / 4) + 4) := by omega
        _ ≤ 4 * 4 ^ (quarterClock (m / 4) + 1) := Nat.mul_le_mul_left 4 h
        _ = 4 ^ (1 + quarterClock (m / 4) + 1) := by
            rw [← pow_succ', add_comm (quarterClock (m / 4)) 1]

/-- For `x ≥ 21846`, `(499 / 50 : ℝ) ≤ Real.log x`. -/
lemma log_ge_499_div_50 {x : ℝ} (hx : 21846 ≤ x) :
    (499 / 50 : ℝ) ≤ Real.log x := by
  have hpow : (2 : ℝ) ^ (72 : ℕ) ≤ x ^ (5 : ℕ) :=
    (by norm_num : (2 : ℝ) ^ (72 : ℕ) ≤ (21846 : ℝ) ^ (5 : ℕ)).trans
      (pow_le_pow_left₀ (by norm_num) hx 5)
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  linarith [Real.log_two_gt_d9]

/-- For `x ≥ 21846`, `(295 / 2 : ℝ) ≤ Real.sqrt x`. -/
lemma sqrt_ge_295_div_2 {x : ℝ} (hx : 21846 ≤ x) :
    (295 / 2 : ℝ) ≤ Real.sqrt x := by
  have hsq : (295 / 2 : ℝ) ^ 2 ≤ x := by norm_num; linarith
  have hs := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by norm_num)] at hs

/-- For `x ≥ 21846`, `(Real.log x) ^ 2 ≤ (4 / 5 : ℝ) * Real.sqrt x`. -/
lemma sq_log_le_four_fifths_sqrt {x : ℝ} (hx : 21846 ≤ x) :
    (Real.log x) ^ 2 ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  set v : ℝ := Real.log x / 4
  have hL : (499 / 50 : ℝ) ≤ Real.log x := log_ge_499_div_50 hx
  have hv : (499 / 200 : ℝ) ≤ v := by dsimp [v]; linarith
  have hv_nonneg : 0 ≤ v := by linarith
  have h_sum := Real.sum_le_exp_of_nonneg hv_nonneg 7
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial,
    Nat.cast_one, Nat.cast_mul, pow_zero, pow_one, zero_add] at h_sum
  norm_num at h_sum
  have h_v2 : (499 / 200 : ℝ) ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ (by norm_num) hv 2
  have h_v3 : (499 / 200 : ℝ) ^ 3 ≤ v ^ 3 := pow_le_pow_left₀ (by norm_num) hv 3
  have h_v4 : (499 / 200 : ℝ) ^ 4 ≤ v ^ 4 := pow_le_pow_left₀ (by norm_num) hv 4
  have h_v5 : (499 / 200 : ℝ) ^ 5 ≤ v ^ 5 := pow_le_pow_left₀ (by norm_num) hv 5
  have h_mono :
      (23 / 5 : ℝ) ≤ 2 + v / 4 + v ^ 2 / 6 + v ^ 3 / 24 + v ^ 4 / 120 + v ^ 5 / 720 := by
    linarith
  have h_id :
      1 + v + v ^ 2 / 2 + v ^ 3 / 6 + v ^ 4 / 24 + v ^ 5 / 120 + v ^ 6 / 720 =
        (v / 2 - 1) ^ 2 +
          v * (2 + v / 4 + v ^ 2 / 6 + v ^ 3 / 24 + v ^ 4 / 120 + v ^ 5 / 720) := by
    ring
  have hexp : (23 / 5 : ℝ) * v ≤ Real.exp v := by
    nlinarith [sq_nonneg (v / 2 - 1)]
  have h_exp_sq : (Real.exp v) ^ 2 = Real.sqrt x := by
    rw [sq, ← Real.exp_add]
    have h_half : v + v = Real.log (Real.sqrt x) := by
      dsimp [v]
      rw [Real.log_sqrt (by linarith)]
      ring
    rw [h_half, Real.exp_log (Real.sqrt_pos.mpr (by linarith))]
  have h_sq_le : ((23 / 5 : ℝ) * v) ^ 2 ≤ (Real.exp v) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hexp 2
  rw [h_exp_sq] at h_sq_le
  dsimp [v] at h_sq_le
  nlinarith

set_option maxHeartbeats 800000 in
-- Explicit numerical interval and contour integral bounds.
/-- Explicit upper bound `|ψ(x) - x| ≤ (571 / 1000) * √x * (log x) ^ 2` for `x ≥ 21846`
using `a_rvM = 3 / 4`, `C = 13 / 5`, `D = 0`, `A = 1`, `B = 85`,
`h = (9 / 50) * √x * (log x) ^ 2`, and `T = (37 / 2) * √x / log x`. -/
lemma abs_psi_sub_self_le_571_div_1000 (hRH : RiemannHypothesis) {x : ℝ} (hx : 21846 ≤ x) :
    |Chebyshev.psi x - x| ≤ (571 / 1000 : ℝ) * Real.sqrt x * (Real.log x) ^ 2 := by
  let lgx : ℝ := Real.log x
  let sqx : ℝ := Real.sqrt x
  let h : ℝ := (9 / 50 : ℝ) * sqx * lgx ^ 2
  let T : ℝ := (37 / 2 : ℝ) * sqx / lgx
  let a_rvM : ℝ := 3 / 4
  let C : ℝ := 13 / 5
  let D : ℝ := 0
  let A : ℝ := 1
  let B : ℝ := 85
  have hL : (499 / 50 : ℝ) ≤ lgx := log_ge_499_div_50 hx
  have hL_pos : 0 < lgx := by linarith
  have hL_sq : (99 : ℝ) ≤ lgx ^ 2 := by nlinarith
  have hS : (295 / 2 : ℝ) ≤ sqx := sqrt_ge_295_div_2 hx
  have hS_pos : 0 < sqx := by linarith
  have hS_sq : sqx ^ 2 = x := Real.sq_sqrt (by linarith)
  have hL2_le_S : lgx ^ 2 ≤ (4 / 5 : ℝ) * sqx := sq_log_le_four_fifths_sqrt hx
  have hh_pos : 0 < h := by dsimp [h]; positivity
  have hh_le_x : h ≤ (18 / 125 : ℝ) * x := by
    calc
      h = (9 / 50 : ℝ) * sqx * lgx ^ 2 := rfl
      _ ≤ (9 / 50 : ℝ) * sqx * ((4 / 5 : ℝ) * sqx) :=
        mul_le_mul_of_nonneg_left hL2_le_S (by positivity)
      _ = (18 / 125 : ℝ) * sqx ^ 2 := by ring
      _ = (18 / 125 : ℝ) * x := by rw [hS_sq]
  have hx_sub_h : 1 ≤ x - h := by linarith
  have h6_le_T : 6 ≤ T := by
    dsimp [T]
    rw [le_div_iff₀ hL_pos]
    nlinarith
  have hT_pos : 0 < T := by linarith
  have hx_add_h_le : x + h ≤ (143 / 125 : ℝ) * sqx ^ 2 := by linarith
  have h_sqrt_xh : Real.sqrt (x + h) ≤ (107 / 100 : ℝ) * sqx := by
    have h1 : x + h ≤ ((107 / 100 : ℝ) * sqx) ^ 2 := by nlinarith
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  have h_rpow_32 : (x + h) ^ (3 / 2 : ℝ) ≤ (49 / 40 : ℝ) * sqx ^ 3 := by
    have h_split : (x + h) ^ (3 / 2 : ℝ) = (x + h) * Real.sqrt (x + h) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith),
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    rw [h_split]
    calc
      (x + h) * Real.sqrt (x + h) ≤ ((143 / 125 : ℝ) * sqx ^ 2) * ((107 / 100 : ℝ) * sqx) :=
        mul_le_mul hx_add_h_le h_sqrt_xh (Real.sqrt_nonneg _) (by positivity)
      _ ≤ (49 / 40 : ℝ) * sqx ^ 3 := by nlinarith [pow_nonneg hS_pos.le 3]
  have h_rpow_34 : (x + h) ^ (3 / 4 : ℝ) ≤ (1 / 10 : ℝ) * sqx ^ 2 := by
    have h12 : (12 : ℝ) ^ (4 : ℝ) ≤ x + h := by norm_num; linarith
    have h12_le : (12 : ℝ) ≤ (x + h) ^ (1 / 4 : ℝ) := by
      have h1 := Real.rpow_le_rpow (by positivity) h12 (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rw [← Real.rpow_mul (by norm_num)] at h1
      norm_num at h1
      exact h1
    have h_prod : (x + h) ^ (3 / 4 : ℝ) * (x + h) ^ (1 / 4 : ℝ) = x + h := by
      rw [← Real.rpow_add (by linarith)]
      norm_num
    nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ x + h) (3 / 4 : ℝ)]
  have h_logT_le : Real.log T ≤ lgx / 2 + 3 / 4 := by
    have h_logL : (9 / 4 : ℝ) ≤ Real.log lgx := by
      have hp : (2 : ℝ) ^ (13 : ℕ) ≤ lgx ^ (4 : ℕ) :=
        (by norm_num : (2 : ℝ) ^ (13 : ℕ) ≤ (499 / 50 : ℝ) ^ (4 : ℕ)).trans
          (pow_le_pow_left₀ (by norm_num) hL 4)
      have hl := Real.log_le_log (by positivity) hp
      rw [Real.log_pow, Real.log_pow] at hl
      push_cast at hl
      linarith [Real.log_two_gt_d9]
    have h_log37 : Real.log (37 / 2 : ℝ) ≤ 3 := by
      have he3 : (37 / 2 : ℝ) ≤ Real.exp 3 := by
        calc
          (37 / 2 : ℝ) ≤ (8 / 3) ^ (3 : ℕ) := by norm_num
          _ ≤ (Real.exp 1) ^ (3 : ℕ) := pow_le_pow_left₀ (by norm_num) eight_thirds_le_exp_one 3
          _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
      have hl := Real.log_le_log (by norm_num) he3
      rwa [Real.log_exp] at hl
    have h_eq : Real.log T = Real.log (37 / 2 : ℝ) + Real.log sqx - Real.log lgx := by
      dsimp [T]
      rw [Real.log_div (by positivity) hL_pos.ne', Real.log_mul (by norm_num) hS_pos.ne']
    have h_logS : Real.log sqx = lgx / 2 := Real.log_sqrt (by linarith)
    linarith
  have h_logT_nonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have h_log6_ge : (89 / 50 : ℝ) ≤ Real.log 6 := by
    have hp : (2 : ℝ) ^ (18 : ℕ) ≤ (6 : ℝ) ^ (7 : ℕ) := by norm_num
    have hl := Real.log_le_log (by positivity) hp
    rw [Real.log_pow, Real.log_pow] at hl
    push_cast at hl
    linarith [Real.log_two_gt_d9]
  have h_bracket3 :
      a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / 6 -
        a_rvM / 2 * (Real.log 6) ^ 2 - C * Real.log 6 ≤
      (3 / 32 : ℝ) * lgx ^ 2 + (49 / 25 : ℝ) * lgx := by
    have hs1 : (Real.log T) ^ 2 ≤ (lgx / 2 + 3 / 4) ^ 2 := sq_le_sq' (by linarith) h_logT_le
    have hs2 : (89 / 50 : ℝ) ^ 2 ≤ (Real.log 6) ^ 2 := sq_le_sq' (by linarith) h_log6_ge
    dsimp [a_rvM, C, D]
    nlinarith
  have h_term3 :
      Real.sqrt (x + h) *
        (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / 6 -
          a_rvM / 2 * (Real.log 6) ^ 2 - C * Real.log 6) ≤
      (321 / 3200 : ℝ) * sqx * lgx ^ 2 + (21 / 10 : ℝ) * sqx * lgx := by
    calc
      Real.sqrt (x + h) *
          (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / 6 -
            a_rvM / 2 * (Real.log 6) ^ 2 - C * Real.log 6)
        ≤ Real.sqrt (x + h) * ((3 / 32 : ℝ) * lgx ^ 2 + (49 / 25 : ℝ) * lgx) :=
          mul_le_mul_of_nonneg_left h_bracket3 (Real.sqrt_nonneg (x + h))
      _ ≤ ((107 / 100 : ℝ) * sqx) * ((3 / 32 : ℝ) * lgx ^ 2 + (49 / 25 : ℝ) * lgx) :=
          mul_le_mul_of_nonneg_right h_sqrt_xh (by positivity)
      _ ≤ (321 / 3200 : ℝ) * sqx * lgx ^ 2 + (21 / 10 : ℝ) * sqx * lgx := by
          have : 0 ≤ sqx * lgx := mul_nonneg hS_pos.le hL_pos.le
          have : 0 ≤ sqx * lgx ^ 2 := mul_nonneg hS_pos.le (sq_nonneg lgx)
          linarith
  have h_term4 :
      (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
        ((2 * a_rvM * Real.log T + 2 * a_rvM + 2 * C) / T + 2 * D / T ^ 2) ≤
      (57 / 50 : ℝ) * sqx * lgx := by
    dsimp [a_rvM, C, D]
    rw [mul_zero, zero_div, add_zero, div_mul_div_comm, div_le_iff₀ (mul_pos hh_pos hT_pos)]
    have h_hT : h * T = (333 / 100 : ℝ) * sqx ^ 2 * lgx := by
      dsimp [h, T]
      field_simp [hL_pos.ne']
      ring
    rw [h_hT]
    have h_num1 : 2 * (x + h) ^ (3 / 2 : ℝ) ≤ (49 / 20 : ℝ) * sqx ^ 3 := by linarith
    have h_num2 :
        2 * (3 / 4 : ℝ) * Real.log T + 2 * (3 / 4 : ℝ) + 2 * (13 / 5 : ℝ) ≤
          (77 / 50 : ℝ) * lgx := by
      linarith
    calc
      (2 * (x + h) ^ (3 / 2 : ℝ)) *
          (2 * (3 / 4 : ℝ) * Real.log T + 2 * (3 / 4 : ℝ) + 2 * (13 / 5 : ℝ))
        ≤ ((49 / 20 : ℝ) * sqx ^ 3) * ((77 / 50 : ℝ) * lgx) :=
          mul_le_mul h_num1 h_num2 (by positivity) (by positivity)
      _ ≤ (57 / 50 : ℝ) * sqx * lgx * ((333 / 100 : ℝ) * sqx ^ 2 * lgx) := by
          have hc : (3773 / 1000 : ℝ) ≤ (57 / 50 : ℝ) * (333 / 100 : ℝ) := by norm_num
          have h_lg : lgx ≤ lgx ^ 2 := by nlinarith
          have hl2 : sqx ^ 3 * lgx ≤ sqx ^ 3 * lgx ^ 2 :=
            mul_le_mul_of_nonneg_left h_lg (pow_nonneg hS_pos.le 3)
          calc
            ((49 / 20 : ℝ) * sqx ^ 3) * ((77 / 50 : ℝ) * lgx)
              = (3773 / 1000 : ℝ) * (sqx ^ 3 * lgx) := by ring
            _ ≤ ((57 / 50 : ℝ) * (333 / 100 : ℝ)) * (sqx ^ 3 * lgx ^ 2) :=
                mul_le_mul hc hl2 (by positivity) (by positivity)
            _ = (57 / 50 : ℝ) * sqx * lgx * ((333 / 100 : ℝ) * sqx ^ 2 * lgx) := by ring
  have h_term5 :
      32 * (2 * A + B) / (Real.pi * h) * (x + h) ^ (3 / 4 : ℝ) ≤
        (53 / 1000 : ℝ) * sqx * lgx ^ 2 := by
    dsimp [A, B]
    rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos Real.pi_pos hh_pos)]
    have hpi_gt : (3 : ℝ) * h ≤ Real.pi * h :=
      mul_le_mul_of_nonneg_right Real.pi_gt_three.le hh_pos.le
    have h_num : 32 * (2 * (1 : ℝ) + 85) * (x + h) ^ (3 / 4 : ℝ) ≤
        (1392 / 5 : ℝ) * sqx ^ 2 := by linarith
    have h_den :
        (1392 / 5 : ℝ) * sqx ^ 2 ≤ (53 / 1000 : ℝ) * sqx * lgx ^ 2 * ((3 : ℝ) * h) := by
      dsimp [h]
      have h_id2 : (53 / 1000 : ℝ) * sqx * lgx ^ 2 *
          ((3 : ℝ) * ((9 / 50 : ℝ) * sqx * lgx ^ 2)) =
          (1431 / 50000 : ℝ) * sqx ^ 2 * (lgx ^ 2) ^ 2 := by ring
      rw [h_id2]
      have hL4 : (99 : ℝ) ^ 2 ≤ (lgx ^ 2) ^ 2 := pow_le_pow_left₀ (by norm_num) hL_sq 2
      nlinarith
    exact h_num.trans (h_den.trans (mul_le_mul_of_nonneg_left hpi_gt (by positivity)))
  have h_term2 : Real.log (2 * Real.pi) ≤ (1 / 500 : ℝ) * sqx * lgx ^ 2 := by
    have hpi : 2 * Real.pi ≤ 8 := by linarith [Real.pi_lt_four]
    have hl : Real.log (2 * Real.pi) ≤ 7 :=
      (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    nlinarith
  obtain ⟨C_h, hCh, h_heights_hb⟩ :=
    exists_zero_free_height_with_log_pow_five_bound hRH h6_le_T
  have hN_bound : ∀ t ≥ 6,
      (weightedZeroCountingFunction t : ℝ) ≤
        a_rvM * t * Real.log t + C * t + D := by
    intro t ht
    dsimp [a_rvM, C, D]
    rw [add_zero]
    exact weightedZeroCountingFunction_le_thirteen_fifths hRH ht
  have h_left_zeta : ∀ t : ℝ,
      ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * Real.log (|t| + 2) + B := by
    intro t
    have h_eq : (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        (-1 / 4 : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    rw [h_eq, neg_div, norm_neg, ← logDeriv_apply]
    dsimp [A, B]
    rw [one_mul]
    exact norm_logDeriv_riemannZeta_leftVertical_le_eighty_five t
  have h_explicit :=
    abs_psi_sub_self_le_weighted_riemannVonMangoldt_six_neg_one_fourth
      hRH hx_sub_h hh_pos h6_le_T (by norm_num) (by norm_num) (by norm_num) (by norm_num) hCh
      hN_bound h_left_zeta h_heights_hb
  have hSL_le : (81 / 25 : ℝ) * (sqx * lgx) ≤ (13 / 40 : ℝ) * (sqx * lgx ^ 2) := by
    have hl : (81 / 25 : ℝ) ≤ (13 / 40 : ℝ) * lgx := by linarith
    calc
      (81 / 25 : ℝ) * (sqx * lgx)
        ≤ ((13 / 40 : ℝ) * lgx) * (sqx * lgx) :=
          mul_le_mul_of_nonneg_right hl (mul_nonneg hS_pos.le hL_pos.le)
      _ = (13 / 40 : ℝ) * (sqx * lgx ^ 2) := by ring
  have h_rhs :
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / 6 -
            a_rvM / 2 * (Real.log 6) ^ 2 - C * Real.log 6) +
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          ((2 * a_rvM * Real.log T + 2 * a_rvM + 2 * C) / T + 2 * D / T ^ 2) +
        32 * (2 * A + B) / (Real.pi * h) * (x + h) ^ (3 / 4 : ℝ) ≤
      (571 / 1000 : ℝ) * sqx * lgx ^ 2 := by
    have hh2 : h / 2 = (9 / 100 : ℝ) * sqx * lgx ^ 2 := by dsimp [h]; ring
    have h_pos_s : 0 ≤ sqx * lgx ^ 2 := mul_nonneg hS_pos.le (sq_nonneg lgx)
    linarith
  exact h_explicit.trans h_rhs

/-- Costa–Pereira explicit bound `ψ(x) - θ(x) ≤ (9 / 200) * √x * (log x) ^ 2` for `x ≥ 21846`. -/
lemma psi_sub_theta_le_nine_two_hundredths {x : ℝ} (hx : 21846 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (9 / 200 : ℝ) * Real.sqrt x * (Real.log x) ^ 2 := by
  have hS : (295 / 2 : ℝ) ≤ Real.sqrt x := sqrt_ge_295_div_2 hx
  have hS_pos : 0 < Real.sqrt x := by linarith
  have hL : (499 / 50 : ℝ) ≤ Real.log x := log_ge_499_div_50 hx
  have hL_pos : 0 < Real.log x := by linarith
  have hlog4 : Real.log 4 ≤ (7 / 5 : ℝ) := by
    have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h4, Real.log_pow]
    push_cast
    linarith [Real.log_two_lt_d9]
  have hr2 : x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
    rw [← one_div, Real.sqrt_eq_rpow]
  have hr3 : x ^ (3 : ℝ)⁻¹ ≤ (1 / 5 : ℝ) * Real.sqrt x := by
    have hpow : (x ^ (3 : ℝ)⁻¹) ^ (3 : ℕ) = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    have h_rhs : x ≤ ((1 / 5 : ℝ) * Real.sqrt x) ^ (3 : ℕ) := by
      have hsq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
      have hs125 : (125 : ℝ) ≤ Real.sqrt x := by linarith
      calc
        x = (Real.sqrt x) ^ 2 * 1 := by rw [hsq, mul_one]
        _ ≤ (Real.sqrt x) ^ 2 * ((1 / 125 : ℝ) * Real.sqrt x) :=
            mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
        _ = ((1 / 5 : ℝ) * Real.sqrt x) ^ (3 : ℕ) := by ring
    exact le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) (hpow.le.trans h_rhs)
  have hr5 : x ^ (5 : ℝ)⁻¹ ≤ (1 / 5 : ℝ) * Real.sqrt x :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num : (5 : ℝ)⁻¹ ≤ 3⁻¹)).trans hr3
  have hp2 : Chebyshev.psi (x ^ (2 : ℝ)⁻¹) ≤
      (7 / 5 : ℝ) * Real.sqrt x + (1 / 12 : ℝ) * (Real.sqrt x * Real.log x) := by
    rw [hr2]
    have hb := Chebyshev.psi_le (x := Real.sqrt x) (by linarith)
    have h_ss : Real.sqrt (Real.sqrt x) ≤ (1 / 12 : ℝ) * Real.sqrt x := by
      have h1 : Real.sqrt x ≤ ((1 / 12 : ℝ) * Real.sqrt x) ^ 2 := by nlinarith
      have h2 := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq (by positivity)] at h2
    have h_ls : Real.log (Real.sqrt x) = Real.log x / 2 := Real.log_sqrt (by linarith)
    rw [h_ls] at hb
    nlinarith [mul_le_mul_of_nonneg_right h_ss hL_pos.le]
  have hp3 : Chebyshev.psi (x ^ (3 : ℝ)⁻¹) ≤ (27 / 25 : ℝ) * Real.sqrt x := by
    have hb := Chebyshev.psi_le_const_mul_self (x := x ^ (3 : ℝ)⁻¹) (by positivity)
    nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ x) (3 : ℝ)⁻¹]
  have hp5 : Chebyshev.psi (x ^ (5 : ℝ)⁻¹) ≤ (27 / 25 : ℝ) * Real.sqrt x := by
    have hb := Chebyshev.psi_le_const_mul_self (x := x ^ (5 : ℝ)⁻¹) (by positivity)
    nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ x) (5 : ℝ)⁻¹]
  have hcp := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h_sum : Chebyshev.psi x - Chebyshev.theta x ≤
      (89 / 25 : ℝ) * Real.sqrt x + (1 / 12 : ℝ) * (Real.sqrt x * Real.log x) := by
    linarith
  have hL_sq : (99 : ℝ) ≤ (Real.log x) ^ 2 := by nlinarith
  have ht1 : (89 / 25 : ℝ) * Real.sqrt x ≤
      (36 / 1000 : ℝ) * (Real.sqrt x * (Real.log x) ^ 2) := by
    have h1 : (89 / 25 : ℝ) ≤ (36 / 1000 : ℝ) * (Real.log x) ^ 2 := by linarith
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_right h1 hS_pos.le
  have ht2 : (1 / 12 : ℝ) * (Real.sqrt x * Real.log x) ≤
      (9 / 1000 : ℝ) * (Real.sqrt x * (Real.log x) ^ 2) := by
    have h1 : (1 / 12 : ℝ) ≤ (9 / 1000 : ℝ) * Real.log x := by linarith
    calc
      (1 / 12 : ℝ) * (Real.sqrt x * Real.log x)
        ≤ ((9 / 1000 : ℝ) * Real.log x) * (Real.sqrt x * Real.log x) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hS_pos.le hL_pos.le)
      _ = (9 / 1000 : ℝ) * (Real.sqrt x * (Real.log x) ^ 2) := by ring
  linarith

/-- **Part 2 (Large-`n` Chebyshev `θ` Bound for Shunia's 120-State Machine, `n ≥ 21846`)**:
Under `RiemannHypothesis`, for every `n : ℕ` with `21846 ≤ n`,
`(n : ℝ) - Chebyshev.theta n < ((quarterClock (n - 1) + 1) * 2 ^ quarterClock (n - 1) : ℝ) *
  Real.log n`. -/
theorem theta_sub_lt_quarterClock_of_ge_21846
    (hRH : RiemannHypothesis) (n : ℕ) (hn : 21846 ≤ n) :
    (n : ℝ) - Chebyshev.theta n <
      ((quarterClock (n - 1) + 1) * 2 ^ quarterClock (n - 1) : ℝ) * Real.log n := by
  have hx : (21846 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : (499 / 50 : ℝ) ≤ Real.log n := log_ge_499_div_50 hx
  have hL_pos : 0 < Real.log n := by linarith
  have hS_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
  have h_psi := abs_psi_sub_self_le_571_div_1000 hRH hx
  have h_diff := psi_sub_theta_le_nine_two_hundredths hx
  have h_n_sub_theta : (n : ℝ) - Chebyshev.theta n ≤
      (77 / 125 : ℝ) * Real.sqrt n * (Real.log n) ^ 2 := by
    have h_tri : (n : ℝ) - Chebyshev.theta n ≤
        |Chebyshev.psi n - n| + (Chebyshev.psi n - Chebyshev.theta n) := by
      have : (n : ℝ) - Chebyshev.psi n ≤ |Chebyshev.psi n - n| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      linarith
    linarith
  set q : ℕ := quarterClock (n - 1)
  have hq_nat : 3 * n + 1 ≤ 4 ^ (q + 1) := by
    have hb : 3 * (n - 1) + 4 ≤ 4 ^ (q + 1) :=
      three_mul_add_four_le_four_pow_quarterClock_succ (n - 1)
    omega
  have h3n_lt : 3 * (n : ℝ) < (4 : ℝ) ^ (q + 1) := by
    have hle : (3 * n + 1 : ℝ) ≤ (4 : ℝ) ^ (q + 1) := by exact_mod_cast hq_nat
    linarith
  have hn_lt : (n : ℝ) < (4 : ℝ) ^ (q + 1) := by linarith
  have h_sqrt_le : Real.sqrt n ≤ (1155 / 1000 : ℝ) * (2 : ℝ) ^ q := by
    have h1 : (n : ℝ) ≤ ((1155 / 1000 : ℝ) * (2 : ℝ) ^ q) ^ 2 := by
      have h4eq : (4 : ℝ) ^ (q + 1) = 4 * ((2 : ℝ) ^ q) ^ 2 := by
        rw [pow_succ', show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, mul_comm 2 q, pow_mul]
      rw [h4eq] at h3n_lt
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) q]
    have h2 := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (by positivity)] at h2
  have h_log_lt : Real.log n < (13863 / 10000 : ℝ) * ((q : ℝ) + 1) := by
    have hlog := Real.log_lt_log (by positivity) hn_lt
    rw [Real.log_pow] at hlog
    push_cast at hlog
    have hlog4 : Real.log 4 ≤ (13863 / 10000 : ℝ) := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      rw [h4, Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9]
    have hmul : ((q : ℝ) + 1) * Real.log 4 ≤ ((q : ℝ) + 1) * (13863 / 10000 : ℝ) :=
      mul_le_mul_of_nonneg_left hlog4 (by positivity)
    linarith
  have h_prod_lt :
      ((77 / 125 : ℝ) * Real.sqrt n) * Real.log n <
        ((q : ℝ) + 1) * (2 : ℝ) ^ q := by
    calc
      ((77 / 125 : ℝ) * Real.sqrt n) * Real.log n
        < ((77 / 125 : ℝ) * Real.sqrt n) * ((13863 / 10000 : ℝ) * ((q : ℝ) + 1)) :=
          mul_lt_mul_of_pos_left h_log_lt (by positivity)
      _ ≤ ((77 / 125 : ℝ) * ((1155 / 1000 : ℝ) * (2 : ℝ) ^ q)) *
            ((13863 / 10000 : ℝ) * ((q : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_sqrt_le (by norm_num))
            (by positivity)
      _ ≤ ((q : ℝ) + 1) * (2 : ℝ) ^ q := by
          have hq_pos : 0 ≤ ((q : ℝ) + 1) * (2 : ℝ) ^ q := by positivity
          linarith
  have h_rhs_gt :
      (77 / 125 : ℝ) * Real.sqrt n * (Real.log n) ^ 2 <
        (((q : ℝ) + 1) * (2 : ℝ) ^ q) * Real.log n := by
    have h1 := mul_lt_mul_of_pos_right h_prod_lt hL_pos
    simpa [sq, mul_assoc] using h1
  exact h_n_sub_theta.trans_lt (by simpa [q] using h_rhs_gt)

end ConjectureMachines.Riemann120.VonMangoldt

end

