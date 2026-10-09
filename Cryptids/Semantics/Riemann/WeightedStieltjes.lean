/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Riemann.VonMangoldtCount
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.Positivity
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Complex.Positivity
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.Floor

/-!
# Smoothed Perron Formula for $\psi_1(x)$, Vertical Tail Bound at $c = 2$, and Rectangle Contour
Shift

This standalone file proves (fully verified with **zero warnings**):

1. **Exact Smoothed Perron Representation of $\psi_1(x)$**:
   - Connects `psi1 x = ∫ t in 1..x, Chebyshev.psi t` via Abel summation
     (`psi1_eq_sum_Icc_sub_mul_vonMangoldt`) to `∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (x - n) * Λ n`.
   - Combines with the smoothed Perron formula (`smoothed_perron_vonMangoldt`) to prove that for all
     `x ≥ 1` and `c > 1` (`ofReal_psi1_eq_smoothedPerron_integral`, and at `c = 2`,
     `ofReal_psi1_eq_smoothedPerron_integral_two`):
     $$(\psi_1(x) : \mathbb{C}) = \frac{1}{2\pi} \int_{-\infty}^\infty
       \text{smoothedPerronIntegrand}(x, c + t I)\,dt.$$

2. **Explicit Bound on `‖-deriv riemannZeta (2 + t * I) / riemannZeta (2 + t * I)‖ ≤ 2` and
Vertical Tail at $c = 2$**:
   - Proves via the telescoping comparison
     $\frac{\Lambda(n)}{n^2} \le \frac{\log n}{n^2} \le \frac{2 + \log(n - 1)}{n - 1} - \frac{2 +
     \log n}{n}$
     for $n \ge 2$ (`norm_neg_deriv_riemannZeta_div_two_add_mul_I_le_two`) that for all $t \in
     \mathbb{R}$,
     $$\left\|-\frac{\zeta'(2 + t I)}{\zeta(2 + t I)}\right\| \le 2.$$
   - Deduces that for all `x > 0` and `t : ℝ` (`norm_smoothedPerronIntegrand_two_add_mul_I_le`),
     $$\|\text{smoothedPerronIntegrand}(x, 2 + t I)\| \le \frac{2 x^3}{t^2 + 4},$$
     and for all `x > 0` and `U > 0`
     (`norm_inv_two_pi_integral_sub_intervalIntegral_smoothedPerronIntegrand_two_le`),
     $$\left\|\frac{1}{2\pi} \int_{-\infty}^\infty \text{smoothedPerronIntegrand}(x, 2 + t I)\,dt
       - \frac{1}{2\pi} \int_{-U}^U \text{smoothedPerronIntegrand}(x, 2 + t I)\,dt\right\|
       \le \frac{2 x^3}{\pi U}.$$

3. **Contour Shift Decomposition & Triangle Inequality Error Reductions**:
   - Combines the removable-singularity regularization (`regularizedSmoothedPerron`) and the
     4-corner `log` + `arctan` rectangle residue theorem (`rectBoundaryIntegral_eq_sum_residues`) on
     `[a, 2] × [-U, U]` to express the truncated vertical integral at `c = 2` in terms of the left
     vertical integral at `Re(s) = a`, the top/bottom horizontal integrals at `Im(s) = ±U`, and the
     principal parts / residues at `s = 1`, `s = 0`, and `ρ ∈ nontrivialZetaZerosUpTo U`.
   - Proves the triangle inequality error reductions
     (`abs_psi1_sub_main_add_log_two_pi_sub_zeroSum_le_of_neg`,
     `abs_psi1_sub_main_sub_zeroSum_le_of_neg`, and `abs_psi1_sub_main_sub_zeroSum_le_of_pos`).
-/

@[expose] public section

namespace ConjectureMachines.Riemann543.Semantics.WeightedStieltjes

export ConjectureMachines.Riemann543.Semantics.VonMangoldtCount
  (IsNontrivialZetaZero isNontrivialZetaZero_ne_zero re_lt_one_of_isNontrivialZetaZero
   zero_lt_re_of_isNontrivialZetaZero mem_criticalStrip_of_isNontrivialZetaZero
   finite_nontrivialZetaZeros_le nontrivialZetaZerosUpTo mem_nontrivialZetaZerosUpTo
   nontrivialZetaZerosBetween mem_nontrivialZetaZerosBetween
   filter_not_lt_abs_im_nontrivialZetaZerosUpTo sub_floor_bounds quartic_floor_bounds
   quarticKernel norm_quarticKernel_le_one_sixteenth measurable_quarticKernel
   locallyIntegrableOn_quarticKernel isBigO_quarticKernel_atTop
   isBigO_quarticKernel_nhdsGT_zero mellinConvergent_quarticKernel
   differentiableAt_mellin_quarticKernel mellin_quarticKernel_neg_add_three_eq
   sum_Icc_const_mul_pow_bounds LSeries_const_mul_pow_add_nat_eq
   integrableOn_floor_poly_mul_cpow integral_floor_poly_mul_cpow_eq sum_Icc_pow_zero
   sum_Icc_two_mul_pow_one sum_Icc_six_mul_pow_two sum_Icc_four_mul_pow_three
   integral_Ioi_one_cpow_neg_add_one mellin_quarticKernel_neg_add_three_eq_of_one_lt_re
   isPreconnected_re_pos sub_one_mul_mellin_quarticKernel_eq_of_re_pos
   mellin_quarticKernel_eq_of_riemannZeta_eq_zero quarticIocAntideriv
   hasDerivAt_quarticIocAntideriv integral_Ioc_one_two_quartic_le
   integral_Ioi_two_quartic_tail_le norm_mellin_quarticKernel_le_of_re_eq_half
   two_hundred_forty_le_norm_prod_of_riemannZeta_eq_zero_of_re_eq_half
   thirty_seven_lt_im_sq_of_riemannZeta_eq_zero_of_re_eq_half
   six_lt_abs_im_of_riemannZeta_eq_zero_of_re_eq_half
   thirty_seven_lt_im_sq_of_riemannHypothesis six_lt_abs_im_of_riemannHypothesis
   nontrivialZetaZerosUpTo_eq_empty_of_le_six one_le_analyticOrderNatAt_of_isNontrivialZetaZero
   nontrivialZetaZerosUpTo_subset_of_le weightedZeroCountingFunction
   weightedZeroCountingFunction_eq_zero_of_le_six filter_abs_im_le_nontrivialZetaZerosBetween
   setIntegral_indicator_deriv_eq_sub integrableOn_indicator_of_continuousOn hasDerivAt_one_div
   intervalIntegral_riemannVonMangoldt_div_sq)

export RiemannSchmidt
  (analyticOrderAt_riemannZeta_ne_top)

open Complex Finset Filter MeasureTheory Set Asymptotics Topology
open scoped Real Topology Interval

/-- The integrated (smoothed) Chebyshev function $\psi_1(x) = \int_1^x \psi(t)\,dt$. -/
noncomputable def psi1 (x : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..x, Chebyshev.psi t

section PerronAndTail

open Real

/-!
# Section 1: 1D FTC Rectangle Identity & Vertical Integral Shift
-/

/-- For any `c t : ℝ`, the derivative of `x ↦ (x : ℂ) + (t : ℂ) * I` at `c` is `1`. -/
lemma hasDerivAt_ofReal_add_const_mul_I (c t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ (x : ℂ) + (t : ℂ) * I) 1 c := by
  simpa using (Complex.ofRealCLM.hasDerivAt (x := c)).add_const ((t : ℂ) * I)

/-- For any `c t : ℝ`, the derivative of `y ↦ (c : ℂ) + (y : ℂ) * I` at `t` is `I`. -/
lemma hasDerivAt_const_add_ofReal_mul_I (c t : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (c : ℂ) + (y : ℂ) * I) I t := by
  have h1 : HasDerivAt (fun y : ℝ ↦ (y : ℂ) * I) (1 * I) t :=
    (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I
  simpa using h1.const_add (c : ℂ)

/-- **1D FTC Rectangle Identity for Holomorphic Functions**:
If `F : ℂ → ℂ` is complex differentiable on an open set `U` containing the closed rectangle
`uIcc c₁ c₂ ×ℂ uIcc a b`, then the difference of the vertical integrals of `F` along `Re(s) = c₂`
and `Re(s) = c₁` from `t = a` to `t = b` equals `-I` times the horizontal integral of
`F(c + b * I) - F(c + a * I)` from `c = c₁` to `c = c₂`. -/
theorem vertical_integral_sub_eq_horizontal_integral {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {c₁ c₂ a b : ℝ}
    (h_mem : ∀ c ∈ uIcc c₁ c₂, ∀ t ∈ uIcc a b, (c : ℂ) + (t : ℂ) * I ∈ U) :
    (∫ t in a..b, F ((c₂ : ℂ) + (t : ℂ) * I)) - (∫ t in a..b, F ((c₁ : ℂ) + (t : ℂ) * I)) =
      -I * ∫ c in c₁..c₂, (F ((c : ℂ) + (b : ℂ) * I) - F ((c : ℂ) + (a : ℂ) * I)) := by
  have hF'_diff : DifferentiableOn ℂ (deriv F) U := hF.deriv hU
  have hF'_cont : ContinuousOn (deriv F) U := hF'_diff.continuousOn
  have h_map_cont : Continuous (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + (p.2 : ℂ) * I) := by fun_prop
  have h_rect_cont : ContinuousOn (fun p : ℝ × ℝ ↦ deriv F ((p.1 : ℂ) + (p.2 : ℂ) * I))
      (uIcc c₁ c₂ ×ˢ uIcc a b) := by
    refine hF'_cont.comp h_map_cont.continuousOn ?_
    rintro ⟨c, t⟩ ⟨hc, ht⟩
    exact h_mem c hc t ht
  have h_rect_int : IntegrableOn (fun p : ℝ × ℝ ↦ deriv F ((p.1 : ℂ) + (p.2 : ℂ) * I))
      (uIoc c₁ c₂ ×ˢ uIoc a b) := by
    refine (h_rect_cont.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set ?_
    exact prod_mono uIoc_subset_uIcc uIoc_subset_uIcc
  have h_vert_int (c : ℝ) (hc : c ∈ uIcc c₁ c₂) :
      IntervalIntegrable (fun t : ℝ ↦ F ((c : ℂ) + (t : ℂ) * I)) volume a b := by
    refine (ContinuousOn.intervalIntegrable ?_)
    refine hF.continuousOn.comp (by fun_prop : Continuous fun t : ℝ ↦ (c : ℂ) +
      (t : ℂ) * I).continuousOn ?_
    intro t ht
    exact h_mem c hc t ht
  have h_ftc_c (t : ℝ) (ht : t ∈ uIcc a b) :
      ∫ c in c₁..c₂, deriv F ((c : ℂ) + (t : ℂ) * I) =
        F ((c₂ : ℂ) + (t : ℂ) * I) - F ((c₁ : ℂ) + (t : ℂ) * I) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro c hc
      have h_at : HasDerivAt F (deriv F ((c : ℂ) + (t : ℂ) * I)) ((c : ℂ) + (t : ℂ) * I) :=
        (hF.differentiableAt (hU.mem_nhds (h_mem c hc t ht))).hasDerivAt
      simpa [Function.comp_def] using h_at.scomp c (hasDerivAt_ofReal_add_const_mul_I c t)
    · refine ContinuousOn.intervalIntegrable ?_
      refine hF'_cont.comp (by fun_prop : Continuous fun c : ℝ ↦ (c : ℂ) +
        (t : ℂ) * I).continuousOn ?_
      intro c hc
      exact h_mem c hc t ht
  have h_ftc_t (c : ℝ) (hc : c ∈ uIcc c₁ c₂) :
      ∫ t in a..b, deriv F ((c : ℂ) + (t : ℂ) * I) =
        -I * (F ((c : ℂ) + (b : ℂ) * I) - F ((c : ℂ) + (a : ℂ) * I)) := by
    have h1 : ∫ t in a..b, I * deriv F ((c : ℂ) + (t : ℂ) * I) =
        F ((c : ℂ) + (b : ℂ) * I) - F ((c : ℂ) + (a : ℂ) * I) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        have h_at : HasDerivAt F (deriv F ((c : ℂ) + (t : ℂ) * I)) ((c : ℂ) + (t : ℂ) * I) :=
          (hF.differentiableAt (hU.mem_nhds (h_mem c hc t ht))).hasDerivAt
        simpa [Function.comp_def, mul_comm] using
          h_at.scomp t (hasDerivAt_const_add_ofReal_mul_I c t)
      · refine ContinuousOn.intervalIntegrable ?_
        refine continuousOn_const.mul (hF'_cont.comp
          (by fun_prop : Continuous fun t : ℝ ↦ (c : ℂ) + (t : ℂ) * I).continuousOn ?_)
        intro t ht
        exact h_mem c hc t ht
    rw [intervalIntegral.integral_const_mul] at h1
    calc ∫ t in a..b, deriv F ((c : ℂ) + (t : ℂ) * I)
        = (-I * I) * ∫ t in a..b, deriv F ((c : ℂ) + (t : ℂ) * I) := by simp
      _ = -I * (I * ∫ t in a..b, deriv F ((c : ℂ) + (t : ℂ) * I)) := by ring
      _ = -I * (F ((c : ℂ) + (b : ℂ) * I) - F ((c : ℂ) + (a : ℂ) * I)) := by rw [h1]
  calc (∫ t in a..b, F ((c₂ : ℂ) + (t : ℂ) * I)) - (∫ t in a..b, F ((c₁ : ℂ) + (t : ℂ) * I))
      = ∫ t in a..b, (F ((c₂ : ℂ) + (t : ℂ) * I) - F ((c₁ : ℂ) + (t : ℂ) * I)) := by
        rw [intervalIntegral.integral_sub (h_vert_int c₂ right_mem_uIcc)
          (h_vert_int c₁ left_mem_uIcc)]
    _ = ∫ t in a..b, ∫ c in c₁..c₂, deriv F ((c : ℂ) + (t : ℂ) * I) := by
        refine intervalIntegral.integral_congr fun t ht ↦ (h_ftc_c t ht).symm
    _ = ∫ c in c₁..c₂, ∫ t in a..b, deriv F ((c : ℂ) + (t : ℂ) * I) := by
        exact (intervalIntegral_intervalIntegral_swap
          (F := fun c t : ℝ ↦ deriv F ((c : ℂ) + (t : ℂ) * I)) h_rect_int).symm
    _ = ∫ c in c₁..c₂, -I * (F ((c : ℂ) + (b : ℂ) * I) - F ((c : ℂ) + (a : ℂ) * I)) := by
        refine intervalIntegral.integral_congr fun c hc ↦ h_ftc_t c hc
    _ = -I * ∫ c in c₁..c₂, (F ((c : ℂ) + (b : ℂ) * I) - F ((c : ℂ) + (a : ℂ) * I)) := by
        rw [intervalIntegral.integral_const_mul]

/-- Bound on the difference of truncated vertical integrals in terms of horizontal segment bounds.
-/
theorem norm_vertical_integral_sub_le {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {c₁ c₂ a b M_a M_b : ℝ}
    (h_mem : ∀ c ∈ uIcc c₁ c₂, ∀ t ∈ uIcc a b, (c : ℂ) + (t : ℂ) * I ∈ U)
    (hMa : ∀ c ∈ uIcc c₁ c₂, ‖F ((c : ℂ) + (a : ℂ) * I)‖ ≤ M_a)
    (hMb : ∀ c ∈ uIcc c₁ c₂, ‖F ((c : ℂ) + (b : ℂ) * I)‖ ≤ M_b) :
    ‖(∫ t in a..b, F ((c₂ : ℂ) + (t : ℂ) * I)) - (∫ t in a..b, F ((c₁ : ℂ) + (t : ℂ) * I))‖ ≤
      (M_b + M_a) * |c₂ - c₁| := by
  rw [vertical_integral_sub_eq_horizontal_integral hU hF h_mem, norm_mul, norm_neg,
    Complex.norm_I, one_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun c hc ↦ ?_
  have hc' : c ∈ uIcc c₁ c₂ := uIoc_subset_uIcc hc
  calc ‖F ((c : ℂ) + (b : ℂ) * I) - F ((c : ℂ) + (a : ℂ) * I)‖
      ≤ ‖F ((c : ℂ) + (b : ℂ) * I)‖ + ‖F ((c : ℂ) + (a : ℂ) * I)‖ := norm_sub_le _ _
    _ ≤ M_b + M_a := add_le_add (hMb c hc') (hMa c hc')

/-- **Improper Vertical Integral Shift Theorem**:
If `F : ℂ → ℂ` is complex differentiable on an open set `U` containing the closed strip
`{s : ℂ | s.re ∈ uIcc c₁ c₂}`, is integrable along both vertical lines `Re(s) = c₁` and
`Re(s) = c₂`, and `sup_{c ∈ uIcc c₁ c₂} ‖F(c ± T*I)‖ → 0` as `T → ∞`, then the improper vertical
integrals along `Re(s) = c₁` and `Re(s) = c₂` are equal. -/
theorem integral_vertical_eq_of_differentiableOn_strip {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {c₁ c₂ : ℝ}
    (h_mem : ∀ c ∈ uIcc c₁ c₂, ∀ t : ℝ, (c : ℂ) + (t : ℂ) * I ∈ U)
    (h_int₁ : Integrable (fun t : ℝ ↦ F ((c₁ : ℂ) + (t : ℂ) * I)))
    (h_int₂ : Integrable (fun t : ℝ ↦ F ((c₂ : ℂ) + (t : ℂ) * I)))
    {B : ℝ → ℝ} (hB_tendsto : Tendsto B atTop (𝓝 0))
    (hB_top : ∀ᶠ T : ℝ in atTop, ∀ c ∈ uIcc c₁ c₂, ‖F ((c : ℂ) + (T : ℂ) * I)‖ ≤ B T)
    (hB_bot : ∀ᶠ T : ℝ in atTop, ∀ c ∈ uIcc c₁ c₂, ‖F ((c : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ B T) :
    (∫ t : ℝ, F ((c₂ : ℂ) + (t : ℂ) * I)) = ∫ t : ℝ, F ((c₁ : ℂ) + (t : ℂ) * I) := by
  have h_lim₁ : Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, F ((c₁ : ℂ) + (t : ℂ) * I))
      atTop (𝓝 (∫ t : ℝ, F ((c₁ : ℂ) + (t : ℂ) * I))) :=
    intervalIntegral_tendsto_integral h_int₁ tendsto_neg_atTop_atBot tendsto_id
  have h_lim₂ : Tendsto (fun T : ℝ ↦ ∫ t in (-T)..T, F ((c₂ : ℂ) + (t : ℂ) * I))
      atTop (𝓝 (∫ t : ℝ, F ((c₂ : ℂ) + (t : ℂ) * I))) :=
    intervalIntegral_tendsto_integral h_int₂ tendsto_neg_atTop_atBot tendsto_id
  have h_diff_lim : Tendsto (fun T : ℝ ↦
      (∫ t in (-T)..T, F ((c₂ : ℂ) + (t : ℂ) * I)) -
      (∫ t in (-T)..T, F ((c₁ : ℂ) + (t : ℂ) * I)))
      atTop (𝓝 ((∫ t : ℝ, F ((c₂ : ℂ) + (t : ℂ) * I)) - ∫ t : ℝ, F ((c₁ : ℂ) + (t : ℂ) * I))) :=
    h_lim₂.sub h_lim₁
  have h_diff_zero : Tendsto (fun T : ℝ ↦
      (∫ t in (-T)..T, F ((c₂ : ℂ) + (t : ℂ) * I)) -
      (∫ t in (-T)..T, F ((c₁ : ℂ) + (t : ℂ) * I))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using (hB_tendsto.add hB_tendsto).mul_const |c₂ - c₁|)
    filter_upwards [hB_top, hB_bot] with T hT_top hT_bot
    exact norm_vertical_integral_sub_le hU hF (fun c hc t _ ↦ h_mem c hc t) hT_bot hT_top
  exact sub_eq_zero.mp (tendsto_nhds_unique h_diff_lim h_diff_zero)

/-!
# Section 2A: Basic Norm Bounds, Pole-Pair Integral, and the `0 < y ≤ 1` Case
-/

lemma re_ofReal_add_ofReal_mul_I (c t : ℝ) : ((c : ℂ) + (t : ℂ) * I).re = c := by
  simp

lemma im_ofReal_add_ofReal_mul_I (c t : ℝ) : ((c : ℂ) + (t : ℂ) * I).im = t := by
  simp

lemma norm_sq_ofReal_add_ofReal_mul_I (c t : ℝ) :
    ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2 = c ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [sq]

lemma norm_ofReal_add_ofReal_mul_I_ge_abs_re (c t : ℝ) :
    |c| ≤ ‖(c : ℂ) + (t : ℂ) * I‖ := by
  simpa using Complex.abs_re_le_norm ((c : ℂ) + (t : ℂ) * I)

lemma norm_ofReal_add_ofReal_mul_I_ge_abs_im (c t : ℝ) :
    |t| ≤ ‖(c : ℂ) + (t : ℂ) * I‖ := by
  simpa using Complex.abs_im_le_norm ((c : ℂ) + (t : ℂ) * I)

lemma ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero {c t : ℝ} (hc : c ≠ 0) :
    (c : ℂ) + (t : ℂ) * I ≠ 0 := by
  intro h
  have hre := congr_arg Complex.re h
  exact hc (by simpa using hre)

lemma ofReal_add_ofReal_mul_I_ne_zero_of_im_ne_zero {c t : ℝ} (ht : t ≠ 0) :
    (c : ℂ) + (t : ℂ) * I ≠ 0 := by
  intro h
  have him := congr_arg Complex.im h
  exact ht (by simpa using him)

/-- For any `c ≠ 0`, `t ↦ (c ^ 2 + t ^ 2)⁻¹` is integrable on `ℝ`. -/
lemma integrable_inv_sq_add_sq {c : ℝ} (hc : c ≠ 0) :
    Integrable (fun t : ℝ ↦ (c ^ 2 + t ^ 2)⁻¹) := by
  have h_eq : (fun t : ℝ ↦ (c ^ 2 + t ^ 2)⁻¹) =
      fun t : ℝ ↦ (c ^ 2)⁻¹ * (1 + (c⁻¹ * t) ^ 2)⁻¹ := by
    ext t
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
    field_simp
  rw [h_eq]
  exact (integrable_inv_one_add_mul_sq (inv_ne_zero hc)).const_mul (c ^ 2)⁻¹

/-- For any `c ≠ 0`, `∫ t : ℝ, (c ^ 2 + t ^ 2)⁻¹ = π / |c|`. -/
lemma integral_inv_sq_add_sq {c : ℝ} (hc : c ≠ 0) :
    (∫ t : ℝ, (c ^ 2 + t ^ 2)⁻¹) = π / |c| := by
  have h_eq : (fun t : ℝ ↦ (c ^ 2 + t ^ 2)⁻¹) =
      fun t : ℝ ↦ (c ^ 2)⁻¹ * (1 + (c⁻¹ * t) ^ 2)⁻¹ := by
    ext t
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
    field_simp
  rw [h_eq, integral_const_mul, integral_univ_inv_one_add_mul_sq, abs_inv, div_inv_eq_mul]
  have h_abs : c ^ 2 = |c| ^ 2 := (sq_abs c).symm
  have h_abs_ne : |c| ≠ 0 := abs_ne_zero.mpr hc
  rw [h_abs]
  field_simp

/-- Algebraic decomposition of `((a : ℂ) + t * I)⁻¹` into real and imaginary parts. -/
lemma inv_ofReal_add_ofReal_mul_I_eq {a t : ℝ} (ha : a ≠ 0) :
    ((a : ℂ) + (t : ℂ) * I)⁻¹ =
      ((a / (a ^ 2 + t ^ 2) : ℝ) : ℂ) - ((t / (a ^ 2 + t ^ 2) : ℝ) : ℂ) * I := by
  have h_ne : (a : ℂ) + (t : ℂ) * I ≠ 0 := ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero ha
  have h_sq_pos : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg t)
  have h_sq_ne : (a : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
    exact_mod_cast h_sq_pos.ne'
  apply mul_left_cancel₀ h_ne
  rw [mul_inv_cancel₀ h_ne]
  symm
  push_cast
  have hI : I ^ 2 = -1 := I_sq
  calc ((a : ℂ) + (t : ℂ) * I) *
        ((a : ℂ) / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) - (t : ℂ) / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) * I)
      = ((a : ℂ) ^ 2 - (t : ℂ) ^ 2 * I ^ 2) / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) := by ring
    _ = ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) / ((a : ℂ) ^ 2 + (t : ℂ) ^ 2) := by rw [hI]; ring
    _ = 1 := div_self h_sq_ne

/-- Integrability of the odd imaginary part `t ↦ t / (a^2 + t^2) - t / (b^2 + t^2)` for `a, b ≠ 0`.
-/
lemma integrable_im_pole_pair {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (fun t : ℝ ↦ t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2)) := by
  refine ((integrable_inv_sq_add_sq hb).const_mul (|b ^ 2 - a ^ 2| / (2 * |a|))).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have ha_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 := fun t ↦
      (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg t)).ne'
    have hb_ne : ∀ t : ℝ, b ^ 2 + t ^ 2 ≠ 0 := fun t ↦
      (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hb) (sq_nonneg t)).ne'
    fun_prop (disch := assumption)
  · filter_upwards with t
    have ha_pos : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg t)
    have hb_pos : 0 < b ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hb) (sq_nonneg t)
    have h_diff : t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2) =
        (b ^ 2 - a ^ 2) * t / ((a ^ 2 + t ^ 2) * (b ^ 2 + t ^ 2)) := by
      field_simp
      ring
    rw [h_diff, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (mul_pos ha_pos hb_pos)]
    have h_amgm : 2 * |a| * |t| ≤ a ^ 2 + t ^ 2 := by
      have hsq : 0 ≤ (|a| - |t|) ^ 2 := sq_nonneg _
      linarith [sq_abs a, sq_abs t]
    have h_t_le : |t| / (a ^ 2 + t ^ 2) ≤ 1 / (2 * |a|) := by
      rw [div_le_div_iff₀ ha_pos (by positivity)]
      linarith
    calc |b ^ 2 - a ^ 2| * |t| / ((a ^ 2 + t ^ 2) * (b ^ 2 + t ^ 2))
        = |b ^ 2 - a ^ 2| * (|t| / (a ^ 2 + t ^ 2)) * (b ^ 2 + t ^ 2)⁻¹ := by
          field_simp
      _ ≤ |b ^ 2 - a ^ 2| * (1 / (2 * |a|)) * (b ^ 2 + t ^ 2)⁻¹ := by
          gcongr
      _ = |b ^ 2 - a ^ 2| / (2 * |a|) * (b ^ 2 + t ^ 2)⁻¹ := by ring

/-- The integral of the odd imaginary part `t ↦ t / (a^2 + t^2) - t / (b^2 + t^2)` is `0`. -/
lemma integral_im_pole_pair {a b : ℝ} :
    (∫ t : ℝ, (t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2))) = 0 := by
  let f : ℝ → ℝ := fun t ↦ t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2)
  have h_odd : ∀ t : ℝ, f (-t) = -f t := by
    intro t
    dsimp [f]
    ring
  have h_emb : MeasurableEmbedding (fun x : ℝ ↦ -x) :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have h_comp_neg : (∫ t : ℝ, f (-t)) = ∫ t : ℝ, f t := by
    have h1 := h_emb.integral_map (μ := volume) f
    rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at h1
    exact h1.symm
  have h_int : (∫ t : ℝ, f t) = -(∫ t : ℝ, f t) := by
    calc (∫ t : ℝ, f t) = ∫ t : ℝ, f (-t) := h_comp_neg.symm
      _ = ∫ t : ℝ, -f t := by simp_rw [h_odd]
      _ = -(∫ t : ℝ, f t) := integral_neg f
  linarith

/-- For `a ≠ 0` and `b ≠ 0`, `t ↦ ((a : ℂ) + t * I)⁻¹ - ((b : ℂ) + t * I)⁻¹` is integrable on `ℝ`.
-/
lemma integrable_inv_sub_inv_ofReal_add_ofReal_mul_I {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Integrable (fun t : ℝ ↦ ((a : ℂ) + (t : ℂ) * I)⁻¹ - ((b : ℂ) + (t : ℂ) * I)⁻¹) := by
  have h_eq : (fun t : ℝ ↦ ((a : ℂ) + (t : ℂ) * I)⁻¹ - ((b : ℂ) + (t : ℂ) * I)⁻¹) =
      fun t : ℝ ↦ (((a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2) : ℝ) : ℂ) -
        ((t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2) : ℝ) : ℂ) * I) := by
    ext t
    rw [inv_ofReal_add_ofReal_mul_I_eq ha, inv_ofReal_add_ofReal_mul_I_eq hb]
    push_cast
    ring
  rw [h_eq]
  have h_re : Integrable (fun t : ℝ ↦ a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2)) := by
    simp_rw [div_eq_mul_inv]
    exact Integrable.sub ((integrable_inv_sq_add_sq ha).const_mul a)
      ((integrable_inv_sq_add_sq hb).const_mul b)
  exact Integrable.sub h_re.ofReal ((integrable_im_pole_pair ha hb).ofReal.mul_const I)

/-- **Pole-Pair Integral Formula**:
For `b < 0 < a`, `∫ t : ℝ, (((a : ℂ) + t * I)⁻¹ - ((b : ℂ) + t * I)⁻¹) = 2 * π`. -/
theorem integral_inv_sub_inv_ofReal_add_ofReal_mul_I {a b : ℝ} (ha : 0 < a) (hb : b < 0) :
    (∫ t : ℝ, (((a : ℂ) + (t : ℂ) * I)⁻¹ - ((b : ℂ) + (t : ℂ) * I)⁻¹)) = 2 * π := by
  have h_eq : (fun t : ℝ ↦ ((a : ℂ) + (t : ℂ) * I)⁻¹ - ((b : ℂ) + (t : ℂ) * I)⁻¹) =
      fun t : ℝ ↦ (((a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2) : ℝ) : ℂ) -
        ((t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2) : ℝ) : ℂ) * I) := by
    ext t
    rw [inv_ofReal_add_ofReal_mul_I_eq ha.ne', inv_ofReal_add_ofReal_mul_I_eq hb.ne]
    push_cast
    ring
  have h_re_int : Integrable (fun t : ℝ ↦ a * (a ^ 2 + t ^ 2)⁻¹) :=
    (integrable_inv_sq_add_sq ha.ne').const_mul a
  have h_re_int' : Integrable (fun t : ℝ ↦ b * (b ^ 2 + t ^ 2)⁻¹) :=
    (integrable_inv_sq_add_sq hb.ne).const_mul b
  have h_re_diff : Integrable (fun t : ℝ ↦ a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2)) := by
    simp_rw [div_eq_mul_inv]
    exact Integrable.sub h_re_int h_re_int'
  have h_re_c : Integrable (fun t : ℝ ↦ ((a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2) : ℝ) : ℂ)) :=
    h_re_diff.ofReal
  have h_im_c : Integrable (fun t : ℝ ↦
      ((t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2) : ℝ) : ℂ) * I) :=
    (integrable_im_pole_pair ha.ne' hb.ne).ofReal.mul_const I
  have h_re_ofReal : (∫ t : ℝ, ((a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((∫ t : ℝ, (a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2)) : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm h_re_diff
  have h_im_ofReal : (∫ t : ℝ, ((t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((∫ t : ℝ, (t / (a ^ 2 + t ^ 2) - t / (b ^ 2 + t ^ 2)) : ℝ) : ℂ) :=
    Complex.ofRealCLM.integral_comp_comm (integrable_im_pole_pair ha.ne' hb.ne)
  rw [h_eq, integral_sub h_re_c h_im_c]
  rw [integral_mul_const, h_im_ofReal, integral_im_pole_pair, Complex.ofReal_zero,
    zero_mul, sub_zero, h_re_ofReal]
  have h_re_eval : (∫ t : ℝ, (a / (a ^ 2 + t ^ 2) - b / (b ^ 2 + t ^ 2))) = 2 * π := by
    simp_rw [div_eq_mul_inv]
    rw [integral_sub h_re_int h_re_int', integral_const_mul, integral_const_mul,
      integral_inv_sq_add_sq ha.ne', integral_inv_sq_add_sq hb.ne,
      abs_of_pos ha, abs_of_neg hb]
    have ha_ne : a ≠ 0 := ha.ne'
    have hb_ne : b ≠ 0 := hb.ne
    field_simp
    ring
  rw [h_re_eval]
  push_cast
  ring

/-- The smoothed Perron integrand `s ↦ y ^ (s + 1) / (s * (s + 1))`. -/
noncomputable def smoothedPerronKernel (y : ℝ) (s : ℂ) : ℂ :=
  (y : ℂ) ^ (s + 1) / (s * (s + 1))

/-- For `0 < y`, `z ↦ (y : ℂ) ^ (z + 1)` is differentiable on all of `ℂ`. -/
lemma differentiable_ofReal_cpow_add_one {y : ℝ} (hy : 0 < y) :
    Differentiable ℂ (fun z : ℂ ↦ (y : ℂ) ^ (z + 1)) := by
  intro z
  exact (differentiableAt_id.add_const 1).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))

/-- For `0 < y`, `smoothedPerronKernel y` is differentiable on `{s : ℂ | s ≠ 0 ∧ s + 1 ≠ 0}`. -/
lemma differentiableOn_smoothedPerronKernel {y : ℝ} (hy : 0 < y) :
    DifferentiableOn ℂ (smoothedPerronKernel y) {s : ℂ | s ≠ 0 ∧ s + 1 ≠ 0} := by
  intro s hs
  refine ((differentiable_ofReal_cpow_add_one hy s).div
    (differentiableAt_id.mul (differentiableAt_id.add_const 1))
    (mul_ne_zero hs.1 hs.2)).differentiableWithinAt

/-- Pointwise norm bound on `smoothedPerronKernel y (c + t * I)` for `0 < y` and `0 < c`. -/
lemma norm_smoothedPerronKernel_le {y c : ℝ} (hy : 0 < y) (hc : 0 < c) (t : ℝ) :
    ‖smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)‖ ≤
      y ^ (c + 1) * (c ^ 2 + t ^ 2)⁻¹ := by
  dsimp [smoothedPerronKernel]
  rw [norm_div, norm_mul]
  have h_num : ‖(y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + 1)‖ = y ^ (c + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy]
    simp
  rw [h_num]
  have h_den : c ^ 2 + t ^ 2 ≤
      ‖(c : ℂ) + (t : ℂ) * I‖ * ‖(c : ℂ) + (t : ℂ) * I + 1‖ := by
    have h1 : c ^ 2 + t ^ 2 = ‖(c : ℂ) + (t : ℂ) * I‖ ^ 2 :=
      (norm_sq_ofReal_add_ofReal_mul_I c t).symm
    have h2 : ‖(c : ℂ) + (t : ℂ) * I‖ ≤ ‖(c : ℂ) + (t : ℂ) * I + 1‖ := by
      have h_eq : (c : ℂ) + (t : ℂ) * I + 1 = ((c + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
        push_cast; ring
      rw [h_eq, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
        norm_sq_ofReal_add_ofReal_mul_I, norm_sq_ofReal_add_ofReal_mul_I]
      nlinarith
    rw [h1, sq]
    exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have hc_pos : 0 < c ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hc_pos h_den) (rpow_nonneg hy.le _)

/-- For `0 < y` and `0 < c`, `t ↦ smoothedPerronKernel y (c + t * I)` is integrable on `ℝ`. -/
theorem integrable_smoothedPerronKernel {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    Integrable (fun t : ℝ ↦ smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)) := by
  refine ((integrable_inv_sq_add_sq hc.ne').const_mul (y ^ (c + 1))).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have h_cont : Continuous (fun t : ℝ ↦ (c : ℂ) + (t : ℂ) * I) := by fun_prop
    refine (differentiableOn_smoothedPerronKernel hy).continuousOn.comp_continuous h_cont
      fun t ↦ ⟨ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero hc.ne', ?_⟩
    have h_eq : (c : ℂ) + (t : ℂ) * I + 1 = ((c + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
      push_cast; ring
    rw [h_eq]
    exact ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero (by linarith)
  · filter_upwards with t
    exact norm_smoothedPerronKernel_le hy hc t

/-- Helper bound for `y ^ (c + 1)` when `c ∈ uIcc c₁ c₂`. -/
lemma rpow_add_one_le_max_of_mem_uIcc {y c₁ c₂ c : ℝ} (hy : 0 < y) (hc : c ∈ uIcc c₁ c₂) :
    y ^ (c + 1) ≤ max (y ^ (c₁ + 1)) (y ^ (c₂ + 1)) := by
  have hc_min : min c₁ c₂ ≤ c := hc.1
  have hc_max : c ≤ max c₁ c₂ := hc.2
  rcases le_or_gt y 1 with hy1 | hy1
  · have h1 : y ^ (c + 1) ≤ y ^ (min c₁ c₂ + 1) :=
      Real.rpow_le_rpow_of_exponent_ge hy hy1 (by linarith)
    refine h1.trans ?_
    rcases min_cases c₁ c₂ with ⟨hmin, _⟩ | ⟨hmin, _⟩ <;> rw [hmin]
    · exact le_max_left _ _
    · exact le_max_right _ _
  · have h1 : y ^ (c + 1) ≤ y ^ (max c₁ c₂ + 1) :=
      Real.rpow_le_rpow_of_exponent_le hy1.le (by linarith)
    refine h1.trans ?_
    rcases max_cases c₁ c₂ with ⟨hmax, _⟩ | ⟨hmax, _⟩ <;> rw [hmax]
    · exact le_max_left _ _
    · exact le_max_right _ _

/-- Shifting the vertical line `Re(s) = c` for `smoothedPerronKernel y` when `c₁, c₂ > 0`. -/
theorem integral_smoothedPerronKernel_eq_of_pos {y c₁ c₂ : ℝ} (hy : 0 < y)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    (∫ t : ℝ, smoothedPerronKernel y ((c₂ : ℂ) + (t : ℂ) * I)) =
      ∫ t : ℝ, smoothedPerronKernel y ((c₁ : ℂ) + (t : ℂ) * I) := by
  let U : Set ℂ := {s : ℂ | 0 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hF : DifferentiableOn ℂ (smoothedPerronKernel y) U := by
    refine (differentiableOn_smoothedPerronKernel hy).mono fun s hs ↦ ⟨?_, ?_⟩
    · intro h0
      have hs_pos : 0 < s.re := hs
      rw [h0, Complex.zero_re] at hs_pos
      exact lt_irrefl 0 hs_pos
    · intro h1
      have hre : (s + 1).re = 0 := by rw [h1, Complex.zero_re]
      simp only [Complex.add_re, Complex.one_re] at hre
      have hs_pos : 0 < s.re := hs
      linarith
  let M : ℝ := max (y ^ (c₁ + 1)) (y ^ (c₂ + 1))
  refine integral_vertical_eq_of_differentiableOn_strip hU hF
    (fun c hc t ↦ ?_) (integrable_smoothedPerronKernel hy hc₁)
    (integrable_smoothedPerronKernel hy hc₂)
    (B := fun T : ℝ ↦ M * (T ^ 2)⁻¹) ?_ ?_ ?_
  · change 0 < ((c : ℂ) + (t : ℂ) * I).re
    rw [re_ofReal_add_ofReal_mul_I]
    exact lt_of_lt_of_le (lt_min hc₁ hc₂) hc.1
  · have h_tendsto : Tendsto (fun T : ℝ ↦ (T ^ 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
    simpa using h_tendsto.const_mul M
  · filter_upwards [eventually_gt_atTop 0] with T hT c hc
    have hc_pos : 0 < c := lt_of_lt_of_le (lt_min hc₁ hc₂) hc.1
    have h_le := norm_smoothedPerronKernel_le hy hc_pos T
    have h_yc : y ^ (c + 1) ≤ M := rpow_add_one_le_max_of_mem_uIcc hy hc
    have h_inv : (c ^ 2 + T ^ 2)⁻¹ ≤ (T ^ 2)⁻¹ :=
      inv_anti₀ (sq_pos_of_pos hT) (by nlinarith)
    exact h_le.trans (mul_le_mul h_yc h_inv (by positivity) (by positivity))
  · filter_upwards [eventually_gt_atTop 0] with T hT c hc
    have hc_pos : 0 < c := lt_of_lt_of_le (lt_min hc₁ hc₂) hc.1
    have h_le := norm_smoothedPerronKernel_le hy hc_pos (-T)
    rw [neg_sq] at h_le
    have h_yc : y ^ (c + 1) ≤ M := rpow_add_one_le_max_of_mem_uIcc hy hc
    have h_inv : (c ^ 2 + T ^ 2)⁻¹ ≤ (T ^ 2)⁻¹ :=
      inv_anti₀ (sq_pos_of_pos hT) (by nlinarith)
    exact h_le.trans (mul_le_mul h_yc h_inv (by positivity) (by positivity))

/-- **Smoothed Perron Formula for `0 < y ≤ 1`**:
When `0 < y ≤ 1` and `0 < c`, the vertical integral of `smoothedPerronKernel y` vanishes. -/
theorem integral_smoothedPerronKernel_eq_zero_of_le_one {y c : ℝ} (hy : 0 < y) (hy1 : y ≤ 1)
    (hc : 0 < c) :
    (∫ t : ℝ, smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)) = 0 := by
  have h_bound : ∀ C : ℝ, 0 < C →
      ‖∫ t : ℝ, smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)‖ ≤ π / C := by
    intro C hC
    rw [← integral_smoothedPerronKernel_eq_of_pos hy hc hC]
    calc ‖∫ t : ℝ, smoothedPerronKernel y ((C : ℂ) + (t : ℂ) * I)‖
        ≤ ∫ t : ℝ, ‖smoothedPerronKernel y ((C : ℂ) + (t : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, y ^ (C + 1) * (C ^ 2 + t ^ 2)⁻¹ := by
          refine integral_mono (integrable_smoothedPerronKernel hy hC).norm
            ((integrable_inv_sq_add_sq hC.ne').const_mul _) (norm_smoothedPerronKernel_le hy hC)
      _ = y ^ (C + 1) * (π / |C|) := by
          rw [integral_const_mul, integral_inv_sq_add_sq hC.ne']
      _ ≤ 1 * (π / C) := by
          rw [abs_of_pos hC]
          gcongr
          exact Real.rpow_le_one hy.le hy1 (by linarith)
      _ = π / C := one_mul _
  have h_tendsto : Tendsto (fun C : ℝ ↦ π / C) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul π
  have h_norm_le : ‖∫ t : ℝ, smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)‖ ≤ 0 := by
    refine ge_of_tendsto h_tendsto ?_
    filter_upwards [eventually_gt_atTop 0] with C hC
    exact h_bound C hC
  exact norm_le_zero_iff.mp h_norm_le

/-!
# Section 2B: Removable-Singularity Pole Subtraction and the `y ≥ 1` Case
-/

/-- The pole-subtracted auxiliary function for `y > 0`, defined globally via `dslope` at `0` and
`-1`
so that its removable singularities at `s = 0` and `s = -1` are automatically resolved. -/
noncomputable def perronAux (y : ℝ) (s : ℂ) : ℂ :=
  dslope (fun z : ℂ ↦ (y : ℂ) ^ (z + 1)) 0 s -
  dslope (fun z : ℂ ↦ (y : ℂ) ^ (z + 1)) (-1) s +
  ((y : ℂ) - 1) / (s - 1)

/-- For `0 < y`, `perronAux y` is complex differentiable on the entire half-plane `{s : ℂ | s.re <
1}`. -/
lemma differentiableOn_perronAux {y : ℝ} (hy : 0 < y) :
    DifferentiableOn ℂ (perronAux y) {s : ℂ | s.re < 1} := by
  have h_ent : DifferentiableOn ℂ (fun z : ℂ ↦ (y : ℂ) ^ (z + 1)) univ :=
    (differentiable_ofReal_cpow_add_one hy).differentiableOn
  have hd0 : DifferentiableOn ℂ (dslope (fun z : ℂ ↦ (y : ℂ) ^ (z + 1)) 0) univ :=
    (Complex.differentiableOn_dslope univ_mem).mpr h_ent
  have hd1 : DifferentiableOn ℂ (dslope (fun z : ℂ ↦ (y : ℂ) ^ (z + 1)) (-1)) univ :=
    (Complex.differentiableOn_dslope univ_mem).mpr h_ent
  have h_div : DifferentiableOn ℂ (fun s : ℂ ↦ ((y : ℂ) - 1) / (s - 1)) {s : ℂ | s.re < 1} := by
    intro s hs
    refine ((differentiableAt_const _).div (differentiableAt_id.sub_const 1)
      ?_).differentiableWithinAt
    intro h_eq
    have hre : (s - 1).re = 0 := by rw [h_eq, Complex.zero_re]
    simp only [Complex.sub_re, Complex.one_re] at hre
    have hs_lt : s.re < 1 := hs
    linarith
  exact ((hd0.mono (subset_univ _)).sub (hd1.mono (subset_univ _))).add h_div

/-- **Form A of `perronAux`**: Away from `s = 0` and `s = -1`, `perronAux y s` is the smoothed
Perron
integrand minus the pole pairs at `(0, 1)` and `(-1, 1)`. -/
lemma perronAux_eq_pole_sub {y : ℝ} {s : ℂ} (hs0 : s ≠ 0) (hs_add1 : s + 1 ≠ 0) :
    perronAux y s =
      smoothedPerronKernel y s - (y : ℂ) * (s⁻¹ - (s - 1)⁻¹) + ((s + 1)⁻¹ - (s - 1)⁻¹) := by
  have hs_neg1 : s ≠ -1 := fun h ↦ hs_add1 (by rw [h]; ring)
  unfold perronAux smoothedPerronKernel
  rw [dslope_of_ne _ hs0, dslope_of_ne _ hs_neg1, slope_def_field, slope_def_field]
  simp only [zero_add, Complex.cpow_one, neg_add_cancel, Complex.cpow_zero, sub_zero,
    sub_neg_eq_add]
  field_simp [hs0, hs_add1]
  ring

/-- **Form B of `perronAux`**: Away from `s = 0, -1, 1`, `perronAux y s` is a sum of three terms
each
decaying quadratically as `|s| → ∞`. -/
lemma perronAux_eq_quad_decay {y : ℝ} {s : ℂ} (hs0 : s ≠ 0) (hs_add1 : s + 1 ≠ 0)
    (hs_sub1 : s - 1 ≠ 0) :
    perronAux y s =
      smoothedPerronKernel y s + (y : ℂ) / (s * (s - 1)) - 2 / ((s + 1) * (s - 1)) := by
  rw [perronAux_eq_pole_sub hs0 hs_add1]
  field_simp [hs0, hs_add1, hs_sub1]
  ring

/-- Horizontal segment bound for `perronAux y (c + T * I)` when `T ≠ 0`. -/
lemma norm_perronAux_horizontal_le {y c T : ℝ} (hy : 0 < y) (hT : T ≠ 0) :
    ‖perronAux y ((c : ℂ) + (T : ℂ) * I)‖ ≤ (y ^ (c + 1) + y + 2) * (T ^ 2)⁻¹ := by
  let s : ℂ := (c : ℂ) + (T : ℂ) * I
  have hs_add1_eq : s + 1 = ((c + 1 : ℝ) : ℂ) + (T : ℂ) * I := by dsimp [s]; push_cast; ring
  have hs_sub1_eq : s - 1 = ((c - 1 : ℝ) : ℂ) + (T : ℂ) * I := by dsimp [s]; push_cast; ring
  have hs0 : s ≠ 0 := ofReal_add_ofReal_mul_I_ne_zero_of_im_ne_zero hT
  have hs_add1 : s + 1 ≠ 0 := by
    rw [hs_add1_eq]; exact ofReal_add_ofReal_mul_I_ne_zero_of_im_ne_zero hT
  have hs_sub1 : s - 1 ≠ 0 := by
    rw [hs_sub1_eq]; exact ofReal_add_ofReal_mul_I_ne_zero_of_im_ne_zero hT
  have h_norm_s : |T| ≤ ‖s‖ := norm_ofReal_add_ofReal_mul_I_ge_abs_im c T
  have h_norm_add1 : |T| ≤ ‖s + 1‖ := by
    rw [hs_add1_eq]; exact norm_ofReal_add_ofReal_mul_I_ge_abs_im (c + 1) T
  have h_norm_sub1 : |T| ≤ ‖s - 1‖ := by
    rw [hs_sub1_eq]; exact norm_ofReal_add_ofReal_mul_I_ge_abs_im (c - 1) T
  have hT2_pos : 0 < T ^ 2 := sq_pos_of_ne_zero hT
  have h_prod1 : T ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    rw [← sq_abs T, sq]; exact mul_le_mul h_norm_s h_norm_add1 (abs_nonneg T) (norm_nonneg _)
  have h_prod2 : T ^ 2 ≤ ‖s‖ * ‖s - 1‖ := by
    rw [← sq_abs T, sq]; exact mul_le_mul h_norm_s h_norm_sub1 (abs_nonneg T) (norm_nonneg _)
  have h_prod3 : T ^ 2 ≤ ‖s + 1‖ * ‖s - 1‖ := by
    rw [← sq_abs T, sq]; exact mul_le_mul h_norm_add1 h_norm_sub1 (abs_nonneg T) (norm_nonneg _)
  have h_term1 : ‖smoothedPerronKernel y s‖ ≤ y ^ (c + 1) * (T ^ 2)⁻¹ := by
    dsimp [smoothedPerronKernel]
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hre : (s + 1).re = c + 1 := by rw [hs_add1_eq]; simp
    rw [hre, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hT2_pos h_prod1) (rpow_nonneg hy.le _)
  have h_term2 : ‖(y : ℂ) / (s * (s - 1))‖ ≤ y * (T ^ 2)⁻¹ := by
    rw [norm_div, norm_mul, Complex.norm_of_nonneg hy.le, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hT2_pos h_prod2) hy.le
  have h_term3 : ‖(2 : ℂ) / ((s + 1) * (s - 1))‖ ≤ 2 * (T ^ 2)⁻¹ := by
    rw [norm_div, norm_mul, Complex.norm_ofNat, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hT2_pos h_prod3) (by positivity)
  change ‖perronAux y s‖ ≤ _
  rw [perronAux_eq_quad_decay hs0 hs_add1 hs_sub1]
  calc ‖smoothedPerronKernel y s + (y : ℂ) / (s * (s - 1)) - 2 / ((s + 1) * (s - 1))‖
      ≤ ‖smoothedPerronKernel y s + (y : ℂ) / (s * (s - 1))‖ +
          ‖(2 : ℂ) / ((s + 1) * (s - 1))‖ := norm_sub_le _ _
    _ ≤ ‖smoothedPerronKernel y s‖ + ‖(y : ℂ) / (s * (s - 1))‖ +
          ‖(2 : ℂ) / ((s + 1) * (s - 1))‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ y ^ (c + 1) * (T ^ 2)⁻¹ + y * (T ^ 2)⁻¹ + 2 * (T ^ 2)⁻¹ :=
          add_le_add (add_le_add h_term1 h_term2) h_term3
    _ = (y ^ (c + 1) + y + 2) * (T ^ 2)⁻¹ := by ring

/-- Vertical line bound for `perronAux y (C + t * I)` when `1 ≤ y` and `C < -1`. -/
lemma norm_perronAux_vertical_le_of_lt_neg_one {y C : ℝ} (hy1 : 1 ≤ y) (hC : C < -1) (t : ℝ) :
    ‖perronAux y ((C : ℂ) + (t : ℂ) * I)‖ ≤ (y + 3) * ((C + 1) ^ 2 + t ^ 2)⁻¹ := by
  have hy : 0 < y := zero_lt_one.trans_le hy1
  let s : ℂ := (C : ℂ) + (t : ℂ) * I
  have hs_add1_eq : s + 1 = ((C + 1 : ℝ) : ℂ) + (t : ℂ) * I := by dsimp [s]; push_cast; ring
  have hs_sub1_eq : s - 1 = ((C - 1 : ℝ) : ℂ) + (t : ℂ) * I := by dsimp [s]; push_cast; ring
  have hs0 : s ≠ 0 := ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero (by linarith)
  have hs_add1 : s + 1 ≠ 0 := by
    rw [hs_add1_eq]; exact ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero (by linarith)
  have hs_sub1 : s - 1 ≠ 0 := by
    rw [hs_sub1_eq]; exact ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero (by linarith)
  have h_sq_pos : 0 < (C + 1) ^ 2 + t ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (by linarith)) (sq_nonneg t)
  have h_norm_add1_sq : ‖s + 1‖ ^ 2 = (C + 1) ^ 2 + t ^ 2 := by
    rw [hs_add1_eq, norm_sq_ofReal_add_ofReal_mul_I]
  have h_le_s : ‖s + 1‖ ≤ ‖s‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), h_norm_add1_sq,
      norm_sq_ofReal_add_ofReal_mul_I]
    nlinarith
  have h_le_sub1 : ‖s + 1‖ ≤ ‖s - 1‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), h_norm_add1_sq, hs_sub1_eq,
      norm_sq_ofReal_add_ofReal_mul_I]
    nlinarith
  have h_prod1 : (C + 1) ^ 2 + t ^ 2 ≤ ‖s‖ * ‖s + 1‖ := by
    rw [← h_norm_add1_sq, sq]
    exact mul_le_mul_of_nonneg_right h_le_s (norm_nonneg _)
  have h_prod2 : (C + 1) ^ 2 + t ^ 2 ≤ ‖s‖ * ‖s - 1‖ := by
    rw [← h_norm_add1_sq, sq]
    exact mul_le_mul h_le_s h_le_sub1 (norm_nonneg _) (norm_nonneg _)
  have h_prod3 : (C + 1) ^ 2 + t ^ 2 ≤ ‖s + 1‖ * ‖s - 1‖ := by
    rw [← h_norm_add1_sq, sq]
    exact mul_le_mul_of_nonneg_left h_le_sub1 (norm_nonneg _)
  have h_yC : y ^ (C + 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
  have h_term1 : ‖smoothedPerronKernel y s‖ ≤ 1 * ((C + 1) ^ 2 + t ^ 2)⁻¹ := by
    dsimp [smoothedPerronKernel]
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    have hre : (s + 1).re = C + 1 := by rw [hs_add1_eq]; simp
    rw [hre, div_eq_mul_inv]
    exact mul_le_mul h_yC (inv_anti₀ h_sq_pos h_prod1) (by positivity) zero_le_one
  have h_term2 : ‖(y : ℂ) / (s * (s - 1))‖ ≤ y * ((C + 1) ^ 2 + t ^ 2)⁻¹ := by
    rw [norm_div, norm_mul, Complex.norm_of_nonneg hy.le, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ h_sq_pos h_prod2) hy.le
  have h_term3 : ‖(2 : ℂ) / ((s + 1) * (s - 1))‖ ≤ 2 * ((C + 1) ^ 2 + t ^ 2)⁻¹ := by
    rw [norm_div, norm_mul, Complex.norm_ofNat, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ h_sq_pos h_prod3) (by positivity)
  change ‖perronAux y s‖ ≤ _
  rw [perronAux_eq_quad_decay hs0 hs_add1 hs_sub1]
  calc ‖smoothedPerronKernel y s + (y : ℂ) / (s * (s - 1)) - 2 / ((s + 1) * (s - 1))‖
      ≤ ‖smoothedPerronKernel y s + (y : ℂ) / (s * (s - 1))‖ +
          ‖(2 : ℂ) / ((s + 1) * (s - 1))‖ := norm_sub_le _ _
    _ ≤ ‖smoothedPerronKernel y s‖ + ‖(y : ℂ) / (s * (s - 1))‖ +
          ‖(2 : ℂ) / ((s + 1) * (s - 1))‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 1 * ((C + 1) ^ 2 + t ^ 2)⁻¹ + y * ((C + 1) ^ 2 + t ^ 2)⁻¹ +
          2 * ((C + 1) ^ 2 + t ^ 2)⁻¹ :=
          add_le_add (add_le_add h_term1 h_term2) h_term3
    _ = (y + 3) * ((C + 1) ^ 2 + t ^ 2)⁻¹ := by ring

/-- Integrability of `t ↦ perronAux y (C + t * I)` for `1 ≤ y` and `C < -1`. -/
lemma integrable_perronAux_of_lt_neg_one {y C : ℝ} (hy1 : 1 ≤ y) (hC : C < -1) :
    Integrable (fun t : ℝ ↦ perronAux y ((C : ℂ) + (t : ℂ) * I)) := by
  have hy : 0 < y := zero_lt_one.trans_le hy1
  have hC1 : C + 1 ≠ 0 := by linarith
  refine ((integrable_inv_sq_add_sq hC1).const_mul (y + 3)).mono' ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    have h_cont : Continuous (fun t : ℝ ↦ (C : ℂ) + (t : ℂ) * I) := by fun_prop
    refine (differentiableOn_perronAux hy).continuousOn.comp_continuous h_cont fun t ↦ ?_
    change ((C : ℂ) + (t : ℂ) * I).re < 1
    rw [re_ofReal_add_ofReal_mul_I]
    linarith
  · filter_upwards with t
    exact norm_perronAux_vertical_le_of_lt_neg_one hy1 hC t

/-- For `0 < y` and `c ∈ (0, 1)`, `t ↦ perronAux y (c + t * I)` is integrable and its integral is
`(∫ t, smoothedPerronKernel y (c + t * I)) - 2 * π * (y - 1)`. -/
lemma integrable_and_integral_perronAux_of_mem_Ioo {y c : ℝ} (hy : 0 < y) (hc0 : 0 < c)
    (hc1 : c < 1) :
    Integrable (fun t : ℝ ↦ perronAux y ((c : ℂ) + (t : ℂ) * I)) ∧
      (∫ t : ℝ, perronAux y ((c : ℂ) + (t : ℂ) * I)) =
        (∫ t : ℝ, smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)) -
          2 * π * ((y : ℂ) - 1) := by
  have h_eq : (fun t : ℝ ↦ perronAux y ((c : ℂ) + (t : ℂ) * I)) =
      fun t : ℝ ↦ smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I) -
        (y : ℂ) * (((c : ℂ) + (t : ℂ) * I)⁻¹ - (((c - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) +
        ((((c + 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹ - (((c - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) := by
    ext t
    have hs0 : (c : ℂ) + (t : ℂ) * I ≠ 0 := ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero hc0.ne'
    have h_add1 : (c : ℂ) + (t : ℂ) * I + 1 = ((c + 1 : ℝ) : ℂ) + (t : ℂ) * I := by
      push_cast; ring
    have h_sub1 : (c : ℂ) + (t : ℂ) * I - 1 = ((c - 1 : ℝ) : ℂ) + (t : ℂ) * I := by
      push_cast; ring
    have hs_add1 : (c : ℂ) + (t : ℂ) * I + 1 ≠ 0 := by
      rw [h_add1]; exact ofReal_add_ofReal_mul_I_ne_zero_of_re_ne_zero (by linarith)
    rw [perronAux_eq_pole_sub hs0 hs_add1, h_add1, h_sub1]
  have h_int1 : Integrable (fun t : ℝ ↦ smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)) :=
    integrable_smoothedPerronKernel hy hc0
  have h_int2 : Integrable (fun t : ℝ ↦
      ((c : ℂ) + (t : ℂ) * I)⁻¹ - (((c - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) :=
    integrable_inv_sub_inv_ofReal_add_ofReal_mul_I hc0.ne' (by linarith)
  have h_int2_y : Integrable (fun t : ℝ ↦
      (y : ℂ) * (((c : ℂ) + (t : ℂ) * I)⁻¹ - (((c - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹)) :=
    h_int2.const_mul (y : ℂ)
  have h_int12 : Integrable (fun t : ℝ ↦
      smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I) -
        (y : ℂ) * (((c : ℂ) + (t : ℂ) * I)⁻¹ - (((c - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹)) :=
    Integrable.sub h_int1 h_int2_y
  have h_int3 : Integrable (fun t : ℝ ↦
      (((c + 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹ - (((c - 1 : ℝ) : ℂ) + (t : ℂ) * I)⁻¹) :=
    integrable_inv_sub_inv_ofReal_add_ofReal_mul_I (by linarith) (by linarith)
  refine ⟨?_, ?_⟩
  · rw [h_eq]
    exact Integrable.add h_int12 h_int3
  · rw [h_eq, integral_add h_int12 h_int3, integral_sub h_int1 h_int2_y, integral_const_mul,
      integral_inv_sub_inv_ofReal_add_ofReal_mul_I hc0 (by linarith),
      integral_inv_sub_inv_ofReal_add_ofReal_mul_I (by linarith) (by linarith)]
    ring

/-- **Smoothed Perron Formula for `y ≥ 1`**:
When `1 ≤ y` and `0 < c`, the vertical integral of `smoothedPerronKernel y` equals `2 * π * (y -
1)`. -/
theorem integral_smoothedPerronKernel_eq_of_ge_one {y c : ℝ} (hy1 : 1 ≤ y) (hc : 0 < c) :
    (∫ t : ℝ, smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)) = 2 * π * ((y : ℂ) - 1) := by
  have hy : 0 < y := zero_lt_one.trans_le hy1
  have hc0_pos : (0 : ℝ) < 1 / 2 := by norm_num
  have hc0_lt1 : (1 / 2 : ℝ) < 1 := by norm_num
  rw [integral_smoothedPerronKernel_eq_of_pos hy hc0_pos hc]
  obtain ⟨h_int_c0, h_eval_c0⟩ := integrable_and_integral_perronAux_of_mem_Ioo hy hc0_pos hc0_lt1
  suffices h_zero : (∫ t : ℝ, perronAux y (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) = 0 by
    linear_combination -h_eval_c0 + h_zero
  have h_shift : ∀ C : ℝ, C < -1 →
      (∫ t : ℝ, perronAux y (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ, perronAux y ((C : ℂ) + (t : ℂ) * I) := by
    intro C hC
    let U : Set ℂ := {s : ℂ | s.re < 1}
    have hU : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
    have hF : DifferentiableOn ℂ (perronAux y) U := differentiableOn_perronAux hy
    let M : ℝ := max (y ^ (C + 1)) (y ^ ((1 / 2 : ℝ) + 1))
    refine integral_vertical_eq_of_differentiableOn_strip hU hF
      (fun σ hσ t ↦ ?_) (integrable_perronAux_of_lt_neg_one hy1 hC) h_int_c0
      (B := fun T : ℝ ↦ (M + y + 2) * (T ^ 2)⁻¹) ?_ ?_ ?_
    · change ((σ : ℂ) + (t : ℂ) * I).re < 1
      rw [re_ofReal_add_ofReal_mul_I]
      have h_max : max C (1 / 2) < 1 := max_lt (by linarith) hc0_lt1
      exact lt_of_le_of_lt hσ.2 h_max
    · have h_tendsto : Tendsto (fun T : ℝ ↦ (T ^ 2)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
      simpa using h_tendsto.const_mul (M + y + 2)
    · filter_upwards [eventually_gt_atTop 0] with T hT σ hσ
      have h_le := norm_perronAux_horizontal_le hy (c := σ) hT.ne'
      have h_yσ : y ^ (σ + 1) ≤ M := rpow_add_one_le_max_of_mem_uIcc hy hσ
      exact h_le.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    · filter_upwards [eventually_gt_atTop 0] with T hT σ hσ
      have h_le := norm_perronAux_horizontal_le hy (c := σ) (neg_ne_zero.mpr hT.ne')
      rw [neg_sq] at h_le
      have h_yσ : y ^ (σ + 1) ≤ M := rpow_add_one_le_max_of_mem_uIcc hy hσ
      exact h_le.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have h_bound : ∀ u : ℝ, 0 < u →
      ‖∫ t : ℝ, perronAux y (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ (y + 3) * (π / u) := by
    intro u hu
    have hC : -(u + 1) < -1 := by linarith
    rw [h_shift (-(u + 1)) hC]
    have hC1 : -(u + 1) + 1 = -u := by ring
    have h_neg_u_ne : -(u + 1) + 1 ≠ 0 := by linarith
    calc ‖∫ t : ℝ, perronAux y (((-(u + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖
        ≤ ∫ t : ℝ, ‖perronAux y (((-(u + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (y + 3) * ((-(u + 1) + 1) ^ 2 + t ^ 2)⁻¹ := by
          refine integral_mono (integrable_perronAux_of_lt_neg_one hy1 hC).norm
            ((integrable_inv_sq_add_sq h_neg_u_ne).const_mul (y + 3))
            (norm_perronAux_vertical_le_of_lt_neg_one hy1 hC)
      _ = (y + 3) * (π / |-(u + 1) + 1|) := by
          rw [integral_const_mul, integral_inv_sq_add_sq h_neg_u_ne]
      _ = (y + 3) * (π / u) := by
          rw [hC1, abs_neg, abs_of_pos hu]
  have h_tendsto : Tendsto (fun u : ℝ ↦ (y + 3) * (π / u)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_inv_atTop_zero.const_mul π).const_mul (y + 3)
  have h_norm_le : ‖∫ t : ℝ, perronAux y (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ 0 := by
    refine ge_of_tendsto h_tendsto ?_
    filter_upwards [eventually_gt_atTop 0] with u hu
    exact h_bound u hu
  exact norm_le_zero_iff.mp h_norm_le

/-- **Combined Smoothed Perron Kernel Formula**:
For all `0 < y` and `0 < c`,
`((2 * π : ℂ)⁻¹) * ∫ t : ℝ, y ^ (c + 1 + t * I) / ((c + t * I) * (c + 1 + t * I)) = max (y - 1) 0`.
-/
theorem smoothed_perron_kernel_eval {y c : ℝ} (hy : 0 < y) (hc : 0 < c) :
    (2 * (π : ℂ))⁻¹ * (∫ t : ℝ, smoothedPerronKernel y ((c : ℂ) + (t : ℂ) * I)) =
      ((max (y - 1) 0 : ℝ) : ℂ) := by
  have hpi : (2 * (π : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rcases le_or_gt y 1 with hy1 | hy1
  · rw [integral_smoothedPerronKernel_eq_zero_of_le_one hy hy1 hc, mul_zero,
      max_eq_right (by linarith : y - 1 ≤ 0), Complex.ofReal_zero]
  · rw [integral_smoothedPerronKernel_eq_of_ge_one hy1.le hc,
      max_eq_left (by linarith : 0 ≤ y - 1), Complex.ofReal_sub, Complex.ofReal_one]
    field_simp [hpi]

/-!
# Section 3: Smoothed Perron Formula for `ψ₁(x) = ∑_{n ≤ x} Λ(n) * (x - n)`
-/

open scoped ArithmeticFunction.vonMangoldt LSeries.notation

/-- For `0 < x`, `n ≠ 0`, and any `s : ℂ`, multiplying `LSeries.term f s n` by
`smoothedPerronKernel x s` rescales the argument of `smoothedPerronKernel` to `x / n`. -/
lemma term_mul_smoothedPerronKernel_of_ne_zero {f : ℕ → ℂ} {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    LSeries.term f s n * smoothedPerronKernel x s =
      (f n * (n : ℂ)) * smoothedPerronKernel (x / n) s := by
  have hn_c : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h_div : (((x / n : ℝ) : ℂ)) ^ (s + 1) = (x : ℂ) ^ (s + 1) / ((n : ℂ) ^ s * (n : ℂ)) := by
    rw [Complex.ofReal_div, Complex.ofReal_natCast,
      ← Complex.ofReal_natCast n,
      Complex.div_cpow_ofReal_nonneg hx.le (Nat.cast_nonneg n) (s + 1),
      Complex.ofReal_natCast, Complex.cpow_add _ _ hn_c, Complex.cpow_one]
  unfold smoothedPerronKernel
  rw [LSeries.term_of_ne_zero hn, h_div]
  calc (f n / (n : ℂ) ^ s) * ((x : ℂ) ^ (s + 1) / (s * (s + 1)))
      = (f n * (n : ℂ) / (n : ℂ)) * ((x : ℂ) ^ (s + 1) / (n : ℂ) ^ s / (s * (s + 1))) := by
        rw [mul_div_cancel_right₀ _ hn_c]
        ring
    _ = (f n * (n : ℂ)) * ((x : ℂ) ^ (s + 1) / ((n : ℂ) ^ s * (n : ℂ)) / (s * (s + 1))) := by
        ring

/-- For each `n : ℕ`, `0 < x`, and `0 < c`, the `n`-th term of the Dirichlet-Perron series is
integrable along `Re(s) = c`. -/
lemma integrable_term_mul_smoothedPerronKernel (f : ℕ → ℂ) {x c : ℝ} (hx : 0 < x)
    (hc : 0 < c) (n : ℕ) :
    Integrable (fun t : ℝ ↦
      LSeries.term f ((c : ℂ) + (t : ℂ) * I) n *
        smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · have h_eq : (fun t : ℝ ↦
        LSeries.term f ((c : ℂ) + (t : ℂ) * I) n *
          smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)) =
        fun t : ℝ ↦ (f n * (n : ℂ)) *
          smoothedPerronKernel (x / n) ((c : ℂ) + (t : ℂ) * I) := by
      ext t
      exact term_mul_smoothedPerronKernel_of_ne_zero hx hn _
    rw [h_eq]
    have hxn : 0 < x / n := div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    exact (integrable_smoothedPerronKernel hxn hc).const_mul _

/-- Norm of `LSeries.term f (c + t * I) n` is independent of `t`. -/
lemma norm_term_ofReal_add_ofReal_mul_I (f : ℕ → ℂ) (c t : ℝ) (n : ℕ) :
    ‖LSeries.term f ((c : ℂ) + (t : ℂ) * I) n‖ = ‖LSeries.term f (c : ℂ) n‖ := by
  simp [LSeries.norm_term_eq]

/-- If `LSeriesSummable f c`, then the `L¹` norms of the Dirichlet-Perron terms along `Re(s) = c`
are summable over `n : ℕ`. -/
lemma summable_integral_norm_term_mul_smoothedPerronKernel {f : ℕ → ℂ} {x c : ℝ}
    (h_sum : LSeriesSummable f (c : ℂ)) :
    Summable (fun n : ℕ ↦ ∫ t : ℝ,
      ‖LSeries.term f ((c : ℂ) + (t : ℂ) * I) n *
        smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)‖) := by
  have h_eq : (fun n : ℕ ↦ ∫ t : ℝ,
      ‖LSeries.term f ((c : ℂ) + (t : ℂ) * I) n *
        smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)‖) =
      fun n : ℕ ↦ ‖LSeries.term f (c : ℂ) n‖ *
        ∫ t : ℝ, ‖smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)‖ := by
    ext n
    simp_rw [norm_mul, norm_term_ofReal_add_ofReal_mul_I, integral_const_mul]
  rw [h_eq]
  exact h_sum.norm.mul_right _

/-- Evaluation of the `n`-th term integral in the smoothed Perron series. -/
lemma integral_term_mul_smoothedPerronKernel (f : ℕ → ℂ) {x c : ℝ} (hx : 0 < x)
    (hc : 0 < c) (n : ℕ) :
    (2 * (π : ℂ))⁻¹ * (∫ t : ℝ,
      LSeries.term f ((c : ℂ) + (t : ℂ) * I) n *
        smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)) =
      if n = 0 then 0 else f n * ((max (x - n) 0 : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · simp only [hn, ↓reduceIte]
    have h_eq : (fun t : ℝ ↦
        LSeries.term f ((c : ℂ) + (t : ℂ) * I) n *
          smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I)) =
        fun t : ℝ ↦ (f n * (n : ℂ)) *
          smoothedPerronKernel (x / n) ((c : ℂ) + (t : ℂ) * I) := by
      ext t
      exact term_mul_smoothedPerronKernel_of_ne_zero hx hn _
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hxn : 0 < x / n := div_pos hx hn_pos
    rw [h_eq, integral_const_mul, ← mul_assoc, mul_comm (2 * (π : ℂ))⁻¹, mul_assoc,
      smoothed_perron_kernel_eval hxn hc, mul_assoc]
    congr 1
    have h_max : (n : ℝ) * max (x / n - 1) 0 = max (x - n) 0 := by
      rw [mul_max_of_nonneg _ _ hn_pos.le, mul_zero, mul_sub, mul_div_cancel₀ _ hn_pos.ne', mul_one]
    exact_mod_cast congr_arg ((↑) : ℝ → ℂ) h_max

/-- Reduction of the `tsum` of `if n = 0 then 0 else f n * max (x - n) 0` to `Finset.Icc 1 ⌊x⌋₊`. -/
lemma tsum_ite_mul_max_sub_eq_sum_Icc (f : ℕ → ℂ) {x : ℝ} (hx : 0 ≤ x) :
    (∑' n : ℕ, if n = 0 then (0 : ℂ) else f n * ((max (x - n) 0 : ℝ) : ℂ)) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * ((x : ℂ) - (n : ℂ)) := by
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊)]
  · refine Finset.sum_congr rfl fun n hn ↦ ?_
    rw [Finset.mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff hx).mp hn.2
    simp only [hn0, ↓reduceIte, max_eq_left (sub_nonneg.mpr hnx),
      Complex.ofReal_sub, Complex.ofReal_natCast]
  · intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn0 | hnx
    · have h0 : n = 0 := by omega
      simp [h0]
    · rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · have h_gt : x < (n : ℝ) := (Nat.floor_lt hx).mp hnx
        simp [hn0, max_eq_right (by linarith : x - (n : ℝ) ≤ 0)]

/-- **Smoothed Perron Formula for General L-Series**:
If `LSeriesSummable f c` with `0 < c` and `0 < x`, then
`∑ n ∈ Icc 1 ⌊x⌋₊, f n * (x - n) = (2 * π)⁻¹ * ∫ t : ℝ, LSeries f (c + t * I) * x^(c + 1 + t * I) /
((c + t * I)*(c + 1 + t * I))`. -/
theorem smoothed_perron_LSeries {f : ℕ → ℂ} {x c : ℝ} (hx : 0 < x) (hc : 0 < c)
    (h_sum : LSeriesSummable f (c : ℂ)) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, f n * ((x : ℂ) - (n : ℂ))) =
      (2 * (π : ℂ))⁻¹ * ∫ t : ℝ,
        LSeries f ((c : ℂ) + (t : ℂ) * I) *
          smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I) := by
  have h_pointwise (t : ℝ) :
      LSeries f ((c : ℂ) + (t : ℂ) * I) * smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I) =
        ∑' n : ℕ, LSeries.term f ((c : ℂ) + (t : ℂ) * I) n *
          smoothedPerronKernel x ((c : ℂ) + (t : ℂ) * I) := by
    rw [LSeries, tsum_mul_right]
  simp_rw [h_pointwise]
  rw [← integral_tsum_of_summable_integral_norm
    (integrable_term_mul_smoothedPerronKernel f hx hc)
    (summable_integral_norm_term_mul_smoothedPerronKernel h_sum)]
  rw [← tsum_mul_left]
  simp_rw [integral_term_mul_smoothedPerronKernel f hx hc]
  exact (tsum_ite_mul_max_sub_eq_sum_Icc f hx.le).symm

/-- **Smoothed Perron Formula for Chebyshev's `ψ₁(x) = ∑_{1 ≤ n ≤ x} Λ(n) * (x - n)`**:
For any `x > 0` and `c > 1`,
`∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * (x - n) = (2 * π)⁻¹ * ∫ t : ℝ, (-deriv riemannZeta (c + t *
I) / riemannZeta (c + t * I)) * (x ^ (c + 1 + t * I) / ((c + t * I) * (c + 1 + t * I)))`. -/
theorem smoothed_perron_vonMangoldt {x c : ℝ} (hx : 0 < x) (hc : 1 < c) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℂ) * ((x : ℂ) - (n : ℂ))) =
      (2 * (π : ℂ))⁻¹ * ∫ t : ℝ,
        (-deriv riemannZeta ((c : ℂ) + (t : ℂ) * I) / riemannZeta ((c : ℂ) + (t : ℂ) * I)) *
          ((x : ℂ) ^ ((c : ℂ) + (t : ℂ) * I + 1) /
            (((c : ℂ) + (t : ℂ) * I) * ((c : ℂ) + (t : ℂ) * I + 1))) := by
  have hc_re : 1 < (c : ℂ).re := by simpa using hc
  have h_sum : LSeriesSummable ↗Λ (c : ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hc_re
  rw [smoothed_perron_LSeries hx (zero_lt_one.trans hc) h_sum]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  dsimp only
  have h_re_t : 1 < ((c : ℂ) + (t : ℂ) * I).re := by simpa using hc
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h_re_t]
  rfl


/-!
## Section 1B: Connecting `psi1 x` to the Smoothed Perron Integral
-/

/-- The smoothed Perron integrand
$M(x, s) = \left(-\frac{\zeta'(s)}{\zeta(s)}\right) \frac{x^{s+1}}{s(s+1)}$. -/
noncomputable def smoothedPerronIntegrand (x : ℝ) (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s) * smoothedPerronKernel x s

theorem sum_Icc_vonMangoldt_eq_psi (t : ℝ) :
    ∑ k ∈ Icc 1 ⌊t⌋₊, (Λ k : ℝ) = Chebyshev.psi t := by
  rw [Chebyshev.psi, ← Icc_add_one_left_eq_Ioc, zero_add]

theorem sum_Icc_mul_vonMangoldt_eq_mul_psi_sub_psi1 {t : ℝ} (ht : 1 ≤ t) :
    ∑ k ∈ Icc 1 ⌊t⌋₊, (k : ℝ) * Λ k = t * Chebyshev.psi t - psi1 t := by
  have h := sum_mul_eq_sub_integral_mul₀ (c := fun k : ℕ ↦ (Λ k : ℝ)) (f := id)
    ArithmeticFunction.map_zero t (fun x _ ↦ differentiableAt_id) (by simp)
  have hsum0 : ∀ n : ℕ, ∑ k ∈ Icc 0 n, (k : ℝ) * Λ k = ∑ k ∈ Icc 1 n, (k : ℝ) * Λ k := by
    intro n
    rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by simp)]
    simp
  have hsum_psi : ∀ x : ℝ, ∑ k ∈ Icc 0 ⌊x⌋₊, (Λ k : ℝ) = Chebyshev.psi x := by
    intro x
    rw [← insert_Icc_add_one_left_eq_Icc (Nat.zero_le _), sum_insert (by simp),
      ArithmeticFunction.map_zero, zero_add, zero_add, sum_Icc_vonMangoldt_eq_psi]
  simp only [id_eq, deriv_id, one_mul, hsum0, hsum_psi] at h
  rw [h]
  unfold psi1
  rw [intervalIntegral.integral_of_le ht]

theorem psi1_eq_mul_psi_sub_sum_Icc {t : ℝ} (ht : 1 ≤ t) :
    psi1 t = t * Chebyshev.psi t - ∑ k ∈ Icc 1 ⌊t⌋₊, (k : ℝ) * Λ k := by
  linarith [sum_Icc_mul_vonMangoldt_eq_mul_psi_sub_psi1 ht]

/-- For `1 ≤ x`, `psi1 x = ∑ n ∈ Icc 1 ⌊x⌋₊, (x - n) * Λ n`. -/
theorem psi1_eq_sum_Icc_sub_mul_vonMangoldt {x : ℝ} (hx : 1 ≤ x) :
    psi1 x = ∑ n ∈ Icc 1 ⌊x⌋₊, (x - n) * Λ n := by
  have h1 := sum_Icc_mul_vonMangoldt_eq_mul_psi_sub_psi1 hx
  have h2 := sum_Icc_vonMangoldt_eq_psi x
  have h3 : ∑ n ∈ Icc 1 ⌊x⌋₊, (x - n) * Λ n =
      x * (∑ n ∈ Icc 1 ⌊x⌋₊, (Λ n : ℝ)) - ∑ n ∈ Icc 1 ⌊x⌋₊, (n : ℝ) * Λ n := by
    simp only [sub_mul, sum_sub_distrib, ← mul_sum]
  rw [h2] at h3
  linarith

theorem ofReal_psi1_eq_sum_Icc_vonMangoldt {x : ℝ} (hx : 1 ≤ x) :
    (psi1 x : ℂ) = ∑ n ∈ Icc 1 ⌊x⌋₊, (Λ n : ℂ) * ((x : ℂ) - (n : ℂ)) := by
  rw [psi1_eq_sum_Icc_sub_mul_vonMangoldt hx]
  push_cast
  refine sum_congr rfl fun n _ ↦ ?_
  ring

/-- **Smoothed Perron Representation of `psi1 x`**:
For all `x ≥ 1` and `c > 1`,
$$(\psi_1(x) : \mathbb{C}) = \frac{1}{2\pi} \int_{-\infty}^\infty
  \text{smoothedPerronIntegrand}(x, c + t I)\,dt.$$ -/
theorem ofReal_psi1_eq_smoothedPerron_integral {x c : ℝ} (hx : 1 ≤ x) (hc : 1 < c) :
    (psi1 x : ℂ) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, smoothedPerronIntegrand x ((c : ℂ) + (t : ℂ) * I) := by
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  rw [ofReal_psi1_eq_sum_Icc_vonMangoldt hx, smoothed_perron_vonMangoldt hx_pos hc]
  rfl

/-- **Smoothed Perron Representation of `psi1 x` at `c = 2`**:
For all `x ≥ 1`,
$$(\psi_1(x) : \mathbb{C}) = \frac{1}{2\pi} \int_{-\infty}^\infty
  \text{smoothedPerronIntegrand}(x, 2 + t I)\,dt.$$ -/
theorem ofReal_psi1_eq_smoothedPerron_integral_two {x : ℝ} (hx : 1 ≤ x) :
    (psi1 x : ℂ) =
      (2 * (Real.pi : ℂ))⁻¹ * ∫ t : ℝ, smoothedPerronIntegrand x (2 + (t : ℂ) * I) := by
  simpa using ofReal_psi1_eq_smoothedPerron_integral hx (by norm_num : (1 : ℝ) < 2)

/-!
## Section 2: Explicit Bound on `‖-deriv riemannZeta (2 + t * I) / riemannZeta (2 + t * I)‖ ≤ 2`
and Vertical Tail at $c = 2$
-/

/-- Telescoping majorant `(2 + log n) / n` for `log n / n^2`. -/
noncomputable def logTelescope (n : ℕ) : ℝ :=
  if n = 0 then 0 else (2 + Real.log n) / n

theorem logTelescope_zero : logTelescope 0 = 0 := rfl

theorem logTelescope_one : logTelescope 1 = 2 := by
  simp [logTelescope]

theorem logTelescope_nonneg (n : ℕ) : 0 ≤ logTelescope n := by
  unfold logTelescope
  split_ifs with hn
  · exact le_rfl
  · have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    positivity

/-- For every `n ≥ 2`, `Real.log n / n ^ 2 ≤ logTelescope (n - 1) - logTelescope n`. -/
theorem log_nat_div_sq_le_logTelescope_sub {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n : ℝ) / (n : ℝ) ^ 2 ≤ logTelescope (n - 1) - logTelescope n := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n - 1 ≠ 0 := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by positivity
  have hn1_cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hdiv_pos : 0 < (n : ℝ) / ((n - 1 : ℕ) : ℝ) := div_pos hn_pos hn1_pos
  have hlog_div : Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤
      (n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hdiv_pos
  rw [Real.log_div hn_pos.ne' hn1_pos.ne'] at hlog_div
  have hmul1 : ((n - 1 : ℕ) : ℝ) * (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hlog_div hn1_pos.le
    have hrhs : ((n - 1 : ℕ) : ℝ) * ((n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1) = 1 := by
      rw [hn1_cast]
      have : (n : ℝ) - 1 ≠ 0 := by rw [← hn1_cast]; exact hn1_pos.ne'
      field_simp
      ring
    linarith
  have hlog_mono : 0 ≤ Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) := by
    refine sub_nonneg.mpr (Real.log_le_log hn1_pos ?_)
    exact_mod_cast Nat.sub_le n 1
  have hn_le_two : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
    rw [hn1_cast]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hmul2 : (n : ℝ) * (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) ≤ 2 := by
    calc
      (n : ℝ) * (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ))
        ≤ (2 * ((n - 1 : ℕ) : ℝ)) * (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hn_le_two hlog_mono
      _ = 2 * (((n - 1 : ℕ) : ℝ) * (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ))) := by ring
      _ ≤ 2 * 1 := by linarith
      _ = 2 := by ring
  have hnum : Real.log (n : ℝ) ≤
      (n : ℝ) * (2 + Real.log ((n - 1 : ℕ) : ℝ)) - ((n - 1 : ℕ) : ℝ) * (2 + Real.log (n : ℝ)) := by
    rw [hn1_cast] at hmul2 ⊢
    linarith
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hden_le : (n : ℝ) * ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [hn1_cast]
    nlinarith
  calc
    Real.log (n : ℝ) / (n : ℝ) ^ 2
      ≤ Real.log (n : ℝ) / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_left hlog_nonneg (mul_pos hn_pos hn1_pos) hden_le
    _ ≤ ((n : ℝ) * (2 + Real.log ((n - 1 : ℕ) : ℝ)) -
          ((n - 1 : ℕ) : ℝ) * (2 + Real.log (n : ℝ))) / ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hnum (mul_pos hn_pos hn1_pos).le
    _ = logTelescope (n - 1) - logTelescope n := by
        simp only [logTelescope, hn0, hn1, ↓reduceIte]
        have h1 : (n : ℝ) ≠ 0 := hn_pos.ne'
        have h2 : ((n - 1 : ℕ) : ℝ) ≠ 0 := hn1_pos.ne'
        field_simp

theorem norm_term_vonMangoldt_two_add_mul_I_le (t : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    ‖LSeries.term (↗Λ) (2 + (t : ℂ) * I) n‖ ≤ logTelescope (n - 1) - logTelescope n := by
  rw [LSeries.norm_term_eq]
  have hn0 : n ≠ 0 := by omega
  simp only [hn0, ↓reduceIte, Complex.norm_real]
  rw [Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hre : ((2 : ℂ) + (t : ℂ) * I).re = 2 := by simp
  rw [hre, Real.rpow_two]
  refine (div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (sq_nonneg _)).trans ?_
  exact log_nat_div_sq_le_logTelescope_sub hn

theorem sum_range_norm_term_vonMangoldt_le_two_sub (t : ℝ) :
    ∀ N : ℕ, 2 ≤ N →
      ∑ n ∈ Finset.range N, ‖LSeries.term (↗Λ) (2 + (t : ℂ) * I) n‖ ≤
        2 - logTelescope (N - 1) := by
  intro N hN
  induction N with
  | zero => omega
  | succ m ihm =>
    rcases lt_or_ge m 2 with hm_lt | hm_ge
    · have hm1 : m = 1 := by omega
      subst hm1
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp [LSeries.term, logTelescope_one]
    · rw [Finset.sum_range_succ]
      have ih := ihm hm_ge
      have hterm := norm_term_vonMangoldt_two_add_mul_I_le t hm_ge
      have hsub : m + 1 - 1 = m := Nat.add_sub_cancel m 1
      rw [hsub]
      linarith

theorem sum_range_norm_term_vonMangoldt_le_two (t : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖LSeries.term (↗Λ) (2 + (t : ℂ) * I) n‖ ≤ 2 := by
  rcases lt_or_ge N 2 with hlt | hge
  · interval_cases N
    · simp
    · simp [LSeries.term]
  · have h := sum_range_norm_term_vonMangoldt_le_two_sub t N hge
    linarith [logTelescope_nonneg (N - 1)]

theorem tsum_norm_term_vonMangoldt_le_two (t : ℝ) :
    ∑' n : ℕ, ‖LSeries.term (↗Λ) (2 + (t : ℂ) * I) n‖ ≤ 2 := by
  have hs : 1 < ((2 : ℂ) + (t : ℂ) * I).re := by simp
  have hsum : Summable (fun n : ℕ ↦ ‖LSeries.term (↗Λ) (2 + (t : ℂ) * I) n‖) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm
  exact hsum.tsum_le_of_sum_range_le (sum_range_norm_term_vonMangoldt_le_two t)

/-- **Explicit Upper Bound on `-ζ'(2 + t I) / ζ(2 + t I)`**:
For all `t : ℝ`,
$$\left\|-\frac{\zeta'(2 + t I)}{\zeta(2 + t I)}\right\| \le 2.$$ -/
theorem norm_neg_deriv_riemannZeta_div_two_add_mul_I_le_two (t : ℝ) :
    ‖-deriv riemannZeta (2 + (t : ℂ) * I) / riemannZeta (2 + (t : ℂ) * I)‖ ≤ 2 := by
  have hs : 1 < ((2 : ℂ) + (t : ℂ) * I).re := by simp
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  unfold LSeries
  exact (norm_tsum_le_tsum_norm (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).norm).trans
    (tsum_norm_term_vonMangoldt_le_two t)

theorem norm_two_add_mul_I_sq (t : ℝ) :
    ‖(2 : ℂ) + (t : ℂ) * I‖ ^ 2 = t ^ 2 + 4 := by
  have h : (2 : ℂ) + (t : ℂ) * I = ⟨2, t⟩ := by
    apply Complex.ext <;> simp
  rw [h, Complex.sq_norm, Complex.normSq_mk]
  ring

theorem norm_three_add_mul_I_sq (t : ℝ) :
    ‖(2 : ℂ) + (t : ℂ) * I + 1‖ ^ 2 = t ^ 2 + 9 := by
  have h : (2 : ℂ) + (t : ℂ) * I + 1 = ⟨3, t⟩ := by
    apply Complex.ext
    · simp; norm_num
    · simp
  rw [h, Complex.sq_norm, Complex.normSq_mk]
  ring

theorem sq_add_four_le_norm_mul_two_add_mul_I (t : ℝ) :
    t ^ 2 + 4 ≤ ‖((2 : ℂ) + (t : ℂ) * I) * ((2 : ℂ) + (t : ℂ) * I + 1)‖ := by
  rw [norm_mul, ← norm_two_add_mul_I_sq t, sq]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [← abs_of_nonneg (norm_nonneg ((2 : ℂ) + (t : ℂ) * I)),
    ← abs_of_nonneg (norm_nonneg ((2 : ℂ) + (t : ℂ) * I + 1)), ← sq_le_sq,
    norm_two_add_mul_I_sq, norm_three_add_mul_I_sq]
  linarith

theorem norm_smoothedPerronKernel_two_add_mul_I_le {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖smoothedPerronKernel x (2 + (t : ℂ) * I)‖ ≤ x ^ (3 : ℝ) / (t ^ 2 + 4) := by
  unfold smoothedPerronKernel
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : ((2 : ℂ) + (t : ℂ) * I + 1).re = 3 := by simp; norm_num
  rw [hre]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le 3) (by positivity)
    (sq_add_four_le_norm_mul_two_add_mul_I t)

/-- **Pointwise Quadratic Decay Bound for `smoothedPerronIntegrand` at $c = 2$**:
For all `x > 0` and `t : ℝ`,
$$\|\text{smoothedPerronIntegrand}(x, 2 + t I)\| \le \frac{2 x^3}{t^2 + 4}.$$ -/
theorem norm_smoothedPerronIntegrand_two_add_mul_I_le {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖smoothedPerronIntegrand x (2 + (t : ℂ) * I)‖ ≤ 2 * x ^ (3 : ℝ) / (t ^ 2 + 4) := by
  unfold smoothedPerronIntegrand
  rw [norm_mul, mul_div_assoc]
  exact mul_le_mul (norm_neg_deriv_riemannZeta_div_two_add_mul_I_le_two t)
    (norm_smoothedPerronKernel_two_add_mul_I_le hx t)
    (norm_nonneg _) (by norm_num)

theorem integrable_smoothedPerronIntegrand_two {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ ↦ smoothedPerronIntegrand x (2 + (t : ℂ) * I)) := by
  have hcont : Continuous (fun t : ℝ ↦ smoothedPerronIntegrand x (2 + (t : ℂ) * I)) := by
    unfold smoothedPerronIntegrand smoothedPerronKernel
    refine Continuous.mul ?_ ?_
    · refine Continuous.div ?_ ?_ ?_
      · refine Continuous.neg ?_
        have hdiff : DifferentiableOn ℂ (deriv riemannZeta) {1}ᶜ :=
          (differentiableOn_riemannZeta.analyticOnNhd isOpen_compl_singleton).deriv.differentiableOn
        refine hdiff.continuousOn.comp_continuous (by fun_prop) fun t ↦ ?_
        intro h
        have hre := congrArg Complex.re h
        simp at hre
      · refine differentiableOn_riemannZeta.continuousOn.comp_continuous (by fun_prop) fun t ↦ ?_
        intro h
        have hre := congrArg Complex.re h
        simp at hre
      · intro t
        exact riemannZeta_ne_zero_of_one_lt_re (by simp)
    · refine Continuous.div ?_ (by fun_prop) ?_
      · have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
        refine Continuous.const_cpow (by fun_prop) (Or.inl hx0)
      · intro t
        have hpos : 0 < t ^ 2 + 4 := by positivity
        have hle := sq_add_four_le_norm_mul_two_add_mul_I t
        exact norm_ne_zero_iff.mp (hpos.trans_le hle).ne'
  have hdom : Integrable (fun t : ℝ ↦ (2 * x ^ (3 : ℝ)) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (2 * x ^ (3 : ℝ))
  refine hdom.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t ↦ ?_)
  refine (norm_smoothedPerronIntegrand_two_add_mul_I_le hx t).trans ?_
  rw [div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact inv_anti₀ (by positivity) (by linarith)

theorem integral_Ioi_inv_sq_eq {U : ℝ} (hU : 0 < U) :
    ∫ t in Ioi U, (t ^ 2)⁻¹ = U⁻¹ := by
  have hcongr : EqOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (fun t : ℝ ↦ t ^ (-2 : ℝ)) (Ioi U) := by
    intro t ht
    dsimp only
    have ht_pos : 0 < t := hU.trans ht
    rw [Real.rpow_neg ht_pos.le, ← Real.rpow_natCast t 2]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_Ioi_rpow_of_lt (by norm_num) hU]
  have h1 : (-2 : ℝ) + 1 = -1 := by norm_num
  rw [h1, div_neg, div_one, neg_neg, Real.rpow_neg_one]

theorem integrableOn_Ioi_inv_sq {U : ℝ} (hU : 0 < U) :
    IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Ioi U) := by
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hU).congr_fun ?_
    measurableSet_Ioi
  intro t ht
  dsimp only
  have ht_pos : 0 < t := hU.trans ht
  rw [Real.rpow_neg ht_pos.le, ← Real.rpow_natCast t 2]
  norm_num

theorem norm_setIntegral_Ioi_smoothedPerronIntegrand_two_le {x U : ℝ} (hx : 0 < x) (hU : 0 < U) :
    ‖∫ t in Ioi U, smoothedPerronIntegrand x (2 + (t : ℂ) * I)‖ ≤ 2 * x ^ (3 : ℝ) / U := by
  calc
    ‖∫ t in Ioi U, smoothedPerronIntegrand x (2 + (t : ℂ) * I)‖
      ≤ ∫ t in Ioi U, ‖smoothedPerronIntegrand x (2 + (t : ℂ) * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi U, (2 * x ^ (3 : ℝ)) * (t ^ 2)⁻¹ := by
        refine setIntegral_mono_on (integrable_smoothedPerronIntegrand_two hx).norm.integrableOn
          ((integrableOn_Ioi_inv_sq hU).const_mul (2 * x ^ (3 : ℝ))) measurableSet_Ioi fun t ht ↦ ?_
        have ht_pos : 0 < t := hU.trans ht
        refine (norm_smoothedPerronIntegrand_two_add_mul_I_le hx t).trans ?_
        rw [div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact inv_anti₀ (sq_pos_of_pos ht_pos) (by linarith)
    _ = 2 * x ^ (3 : ℝ) / U := by
        rw [integral_const_mul, integral_Ioi_inv_sq_eq hU, div_eq_mul_inv]

theorem norm_setIntegral_Iic_smoothedPerronIntegrand_two_le {x U : ℝ} (hx : 0 < x) (hU : 0 < U) :
    ‖∫ t in Iic (-U), smoothedPerronIntegrand x (2 + (t : ℂ) * I)‖ ≤ 2 * x ^ (3 : ℝ) / U := by
  have hsub : (∫ t in Iic (-U), smoothedPerronIntegrand x (2 + (t : ℂ) * I)) =
      ∫ t in Ioi U, smoothedPerronIntegrand x (2 + ((-t : ℝ) : ℂ) * I) := by
    rw [← integral_comp_neg_Ioi]
  rw [hsub]
  calc
    ‖∫ t in Ioi U, smoothedPerronIntegrand x (2 + ((-t : ℝ) : ℂ) * I)‖
      ≤ ∫ t in Ioi U, ‖smoothedPerronIntegrand x (2 + ((-t : ℝ) : ℂ) * I)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi U, (2 * x ^ (3 : ℝ)) * (t ^ 2)⁻¹ := by
        refine setIntegral_mono_on
          (((integrable_smoothedPerronIntegrand_two hx).comp_neg).norm.integrableOn)
          ((integrableOn_Ioi_inv_sq hU).const_mul (2 * x ^ (3 : ℝ))) measurableSet_Ioi fun t ht ↦ ?_
        have ht_pos : 0 < t := hU.trans ht
        have hb := norm_smoothedPerronIntegrand_two_add_mul_I_le hx (-t)
        rw [neg_sq] at hb
        refine hb.trans ?_
        rw [div_eq_mul_inv]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact inv_anti₀ (sq_pos_of_pos ht_pos) (by linarith)
    _ = 2 * x ^ (3 : ℝ) / U := by
        rw [integral_const_mul, integral_Ioi_inv_sq_eq hU, div_eq_mul_inv]

theorem norm_integral_sub_intervalIntegral_smoothedPerronIntegrand_two_le
    {x U : ℝ} (hx : 0 < x) (hU : 0 < U) :
    ‖(∫ t : ℝ, smoothedPerronIntegrand x (2 + (t : ℂ) * I)) -
      (∫ t in (-U)..U, smoothedPerronIntegrand x (2 + (t : ℂ) * I))‖ ≤
        4 * x ^ (3 : ℝ) / U := by
  have hint := integrable_smoothedPerronIntegrand_two hx
  have hle : -U ≤ U := by linarith
  rw [intervalIntegral.integral_of_le hle]
  have hcompl := integral_add_compl (s := Ioc (-U) U) measurableSet_Ioc hint
  have hsub : (∫ t : ℝ, smoothedPerronIntegrand x (2 + (t : ℂ) * I)) -
      (∫ t in Ioc (-U) U, smoothedPerronIntegrand x (2 + (t : ℂ) * I)) =
        ∫ t in (Ioc (-U) U)ᶜ, smoothedPerronIntegrand x (2 + (t : ℂ) * I) := by
    linear_combination -hcompl
  have hset : (Ioc (-U) U)ᶜ = Iic (-U) ∪ Ioi U := compl_Ioc
  have hdisj : Disjoint (Iic (-U)) (Ioi U) := by
    rw [Set.disjoint_iff]
    intro t ⟨ht1, ht2⟩
    rw [Set.mem_Iic] at ht1
    rw [Set.mem_Ioi] at ht2
    linarith
  rw [hsub, hset, setIntegral_union hdisj measurableSet_Ioi hint.integrableOn hint.integrableOn]
  calc
    ‖(∫ t in Iic (-U), smoothedPerronIntegrand x (2 + (t : ℂ) * I)) +
        (∫ t in Ioi U, smoothedPerronIntegrand x (2 + (t : ℂ) * I))‖
      ≤ ‖∫ t in Iic (-U), smoothedPerronIntegrand x (2 + (t : ℂ) * I)‖ +
          ‖∫ t in Ioi U, smoothedPerronIntegrand x (2 + (t : ℂ) * I)‖ := norm_add_le _ _
    _ ≤ 2 * x ^ (3 : ℝ) / U + 2 * x ^ (3 : ℝ) / U :=
        add_le_add (norm_setIntegral_Iic_smoothedPerronIntegrand_two_le hx hU)
          (norm_setIntegral_Ioi_smoothedPerronIntegrand_two_le hx hU)
    _ = 4 * x ^ (3 : ℝ) / U := by ring

/-- **Vertical Tail Bound at $c = 2$**:
For all `x > 0` and `U > 0`,
$$\left\|\frac{1}{2\pi} \int_{-\infty}^\infty \text{smoothedPerronIntegrand}(x, 2 + t I)\,dt
  - \frac{1}{2\pi} \int_{-U}^U \text{smoothedPerronIntegrand}(x, 2 + t I)\,dt\right\|
  \le \frac{2 x^3}{\pi U}.$$ -/
theorem norm_inv_two_pi_integral_sub_intervalIntegral_smoothedPerronIntegrand_two_le
    {x U : ℝ} (hx : 0 < x) (hU : 0 < U) :
    ‖(2 * (Real.pi : ℂ))⁻¹ * (∫ t : ℝ, smoothedPerronIntegrand x (2 + (t : ℂ) * I)) -
      (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, smoothedPerronIntegrand x (2 + (t : ℂ) * I))‖ ≤
        2 * x ^ (3 : ℝ) / (Real.pi * U) := by
  have h2pi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [← ofReal_ofNat, ← ofReal_mul, Complex.norm_real, Real.norm_of_nonneg Real.two_pi_pos.le]
  rw [← mul_sub, norm_mul, norm_inv, h2pi]
  calc
    (2 * Real.pi)⁻¹ *
        ‖(∫ t : ℝ, smoothedPerronIntegrand x (2 + (t : ℂ) * I)) -
          (∫ t in (-U)..U, smoothedPerronIntegrand x (2 + (t : ℂ) * I))‖
      ≤ (2 * Real.pi)⁻¹ * (4 * x ^ (3 : ℝ) / U) :=
        mul_le_mul_of_nonneg_left
          (norm_integral_sub_intervalIntegral_smoothedPerronIntegrand_two_le hx hU)
          (by positivity)
    _ = 2 * x ^ (3 : ℝ) / (Real.pi * U) := by
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        have hU0 : U ≠ 0 := hU.ne'
        field_simp
        ring

/-- **Truncated Smoothed Perron Approximation to `psi1 x` at $c = 2$**:
For all `x ≥ 1` and `U > 0`,
$$\left\|(\psi_1(x) : \mathbb{C})
  - \frac{1}{2\pi} \int_{-U}^U \text{smoothedPerronIntegrand}(x, 2 + t I)\,dt\right\|
  \le \frac{2 x^3}{\pi U}.$$ -/
theorem norm_psi1_sub_truncated_smoothedPerron_two_le {x U : ℝ} (hx : 1 ≤ x) (hU : 0 < U) :
    ‖(psi1 x : ℂ) -
      (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, smoothedPerronIntegrand x (2 + (t : ℂ) * I))‖ ≤
        2 * x ^ (3 : ℝ) / (Real.pi * U) := by
  rw [ofReal_psi1_eq_smoothedPerron_integral_two hx]
  exact norm_inv_two_pi_integral_sub_intervalIntegral_smoothedPerronIntegrand_two_le
    (zero_lt_one.trans_le hx) hU

end PerronAndTail

/-!
## Section 1: General Removable-Pole Lemmas & Finite Multi-Pole Removal
-/

/-- If `g : ℂ → ℂ` is differentiable at `p`, then `(g s - g p) / (s - p)` tends to `deriv g p`
on the punctured neighborhood `𝓝[≠] p`. -/
theorem tendsto_sub_div_sub_of_differentiableAt {g : ℂ → ℂ} {p : ℂ}
    (hg : DifferentiableAt ℂ g p) :
    Tendsto (fun s ↦ (g s - g p) / (s - p)) (𝓝[≠] p) (𝓝 (deriv g p)) := by
  have hc : ContinuousAt (dslope g p) p := continuousAt_dslope_same.mpr hg
  have ht : Tendsto (dslope g p) (𝓝[≠] p) (𝓝 (deriv g p)) := by
    rw [← dslope_same]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [dslope_of_ne _ hs, slope_def_field]

/-- **General Single-Pole Removable Singularity Lemma (`AnalyticAt`)**:
If `f : ℂ → ℂ` is complex-differentiable on a punctured neighborhood of `p` and
`f s - r / (s - p) → L` as `s → p` (`s ≠ p`), then updating `s ↦ f s - r / (s - p)` at `p`
with `L` yields a function that is analytic at `p`. -/
theorem analyticAt_update_sub_inv_sub_of_tendsto {f : ℂ → ℂ} {p r L : ℂ}
    (hf : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ f z)
    (hL : Tendsto (fun s ↦ f s - r / (s - p)) (𝓝[≠] p) (𝓝 L)) :
    AnalyticAt ℂ (Function.update (fun s ↦ f s - r / (s - p)) p L) p := by
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  · filter_upwards [hf, self_mem_nhdsWithin] with z hfz hzp
    have hsub : z - p ≠ 0 := sub_ne_zero.mpr hzp
    have hd : DifferentiableAt ℂ (fun s ↦ f s - r / (s - p)) z :=
      hfz.sub (differentiableAt_const r |>.div (differentiableAt_id.sub_const p) hsub)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hzp] with w hw
    simp [Function.update_of_ne hw]
  · exact continuousAt_update_same.mpr hL

/-- **General Single-Pole Removable Singularity Lemma (`DifferentiableAt`)**:
If `f : ℂ → ℂ` is complex-differentiable on a punctured neighborhood of `p` and
`f s - r / (s - p) → L` as `s → p` (`s ≠ p`), then updating `s ↦ f s - r / (s - p)` at `p`
with `L` yields a function that is complex-differentiable at `p`. -/
theorem differentiableAt_update_sub_inv_sub_of_tendsto {f : ℂ → ℂ} {p r L : ℂ}
    (hf : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ f z)
    (hL : Tendsto (fun s ↦ f s - r / (s - p)) (𝓝[≠] p) (𝓝 L)) :
    DifferentiableAt ℂ (Function.update (fun s ↦ f s - r / (s - p)) p L) p :=
  (analyticAt_update_sub_inv_sub_of_tendsto hf hL).differentiableAt

/-- Removing a finite set of simple poles `S : Finset ℂ` from `f : ℂ → ℂ`, where each pole `q ∈ S`
has residue `res q` and punctured-neighborhood limit `limVal q = lim_{s → q} (f s - res q / (s -
q))`.
Away from `S`, `removePoles f S res limVal s = f s - ∑ q ∈ S, res q / (s - q)`. -/
noncomputable def removePoles (f : ℂ → ℂ) (S : Finset ℂ) (res limVal : ℂ → ℂ) (s : ℂ) : ℂ :=
  open Classical in
  if s ∈ S then
    limVal s - ∑ q ∈ S.erase s, res q / (s - q)
  else
    f s - ∑ q ∈ S, res q / (s - q)

/-- For `s ∉ S`, `removePoles f S res limVal s = f s - ∑ q ∈ S, res q / (s - q)`. -/
theorem removePoles_of_notMem (f : ℂ → ℂ) (S : Finset ℂ) (res limVal : ℂ → ℂ) {s : ℂ}
    (hs : s ∉ S) :
    removePoles f S res limVal s = f s - ∑ q ∈ S, res q / (s - q) := by
  simp [removePoles, hs]

/-- For `p ∈ S`, `removePoles f S res limVal p = limVal p - ∑ q ∈ S.erase p, res q / (p - q)`. -/
theorem removePoles_of_mem (f : ℂ → ℂ) (S : Finset ℂ) (res limVal : ℂ → ℂ) {p : ℂ}
    (hp : p ∈ S) :
    removePoles f S res limVal p = limVal p - ∑ q ∈ S.erase p, res q / (p - q) := by
  simp [removePoles, hp]

/-- Near any `p ∈ S`, `removePoles f S res limVal` agrees on a neighborhood of `p` with
`Function.update (fun s ↦ f s - res p / (s - p)) p (limVal p) s - ∑ q ∈ S.erase p, res q / (s -
q)`. -/
theorem removePoles_eventuallyEq_near_pole (f : ℂ → ℂ) (S : Finset ℂ) (res limVal : ℂ → ℂ)
    {p : ℂ} (hp : p ∈ S) :
    removePoles f S res limVal =ᶠ[𝓝 p] fun s ↦
      Function.update (fun z ↦ f z - res p / (z - p)) p (limVal p) s -
        ∑ q ∈ S.erase p, res q / (s - q) := by
  classical
  have hclosed : IsClosed ((S.erase p : Finset ℂ) : Set ℂ) := (S.erase p).finite_toSet.isClosed
  have hp_notMem : p ∉ ((S.erase p : Finset ℂ) : Set ℂ) := by simp
  filter_upwards [hclosed.isOpen_compl.mem_nhds hp_notMem] with s hs
  rcases eq_or_ne s p with rfl | hsp
  · rw [removePoles_of_mem f S res limVal hp, Function.update_self]
  · have hs_notMem_S : s ∉ S := by
      intro hsS
      exact hs (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hsp, hsS⟩))
    rw [removePoles_of_notMem f S res limVal hs_notMem_S,
      Function.update_of_ne hsp, ← Finset.add_sum_erase S (fun q ↦ res q / (s - q)) hp]
    ring

/-- **Analyticity of `removePoles` at a Pole `p ∈ S`**:
If `f` is complex-differentiable on `𝓝[≠] p` and `f s - res p / (s - p) → limVal p` on `𝓝[≠] p`,
then `removePoles f S res limVal` is analytic at `p`. -/
theorem analyticAt_removePoles_of_mem {f : ℂ → ℂ} {S : Finset ℂ} {res limVal : ℂ → ℂ} {p : ℂ}
    (hp : p ∈ S)
    (hf : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ f z)
    (hL : Tendsto (fun s ↦ f s - res p / (s - p)) (𝓝[≠] p) (𝓝 (limVal p))) :
    AnalyticAt ℂ (removePoles f S res limVal) p := by
  refine AnalyticAt.congr ?_ (removePoles_eventuallyEq_near_pole f S res limVal hp).symm
  refine (analyticAt_update_sub_inv_sub_of_tendsto hf hL).sub ?_
  have hdiff : DifferentiableOn ℂ (fun s ↦ ∑ q ∈ S.erase p, res q / (s - q))
      (((S.erase p : Finset ℂ) : Set ℂ)ᶜ) := by
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.fun_sum fun q hq ↦ ?_
    have hsq : s - q ≠ 0 := by
      refine sub_ne_zero.mpr fun h ↦ hs ?_
      subst h
      exact Finset.mem_coe.mpr hq
    exact (differentiableAt_const (res q)).div (differentiableAt_id.sub_const q) hsq
  have hopen : IsOpen (((S.erase p : Finset ℂ) : Set ℂ)ᶜ) :=
    (S.erase p).finite_toSet.isClosed.isOpen_compl
  exact (hdiff.analyticOnNhd hopen) p (by simp)

/-- **Differentiability of `removePoles` at a Pole `p ∈ S`**. -/
theorem differentiableAt_removePoles_of_mem {f : ℂ → ℂ} {S : Finset ℂ} {res limVal : ℂ → ℂ} {p : ℂ}
    (hp : p ∈ S)
    (hf : ∀ᶠ z in 𝓝[≠] p, DifferentiableAt ℂ f z)
    (hL : Tendsto (fun s ↦ f s - res p / (s - p)) (𝓝[≠] p) (𝓝 (limVal p))) :
    DifferentiableAt ℂ (removePoles f S res limVal) p :=
  (analyticAt_removePoles_of_mem hp hf hL).differentiableAt

/-- **Differentiability of `removePoles` Away from `S`**:
If `s ∉ S` and `DifferentiableAt ℂ f s`, then `DifferentiableAt ℂ (removePoles f S res limVal) s`.
-/
theorem differentiableAt_removePoles_of_notMem {f : ℂ → ℂ} {S : Finset ℂ} {res limVal : ℂ → ℂ}
    {s : ℂ} (hs : s ∉ S) (hf : DifferentiableAt ℂ f s) :
    DifferentiableAt ℂ (removePoles f S res limVal) s := by
  have hd : DifferentiableAt ℂ (fun z ↦ f z - ∑ q ∈ S, res q / (z - q)) s := by
    refine hf.sub (DifferentiableAt.fun_sum fun q hq ↦ ?_)
    have hsq : s - q ≠ 0 := sub_ne_zero.mpr (fun h ↦ hs (h ▸ hq))
    exact (differentiableAt_const (res q)).div (differentiableAt_id.sub_const q) hsq
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [S.finite_toSet.isClosed.isOpen_compl.mem_nhds hs] with z hz
  exact removePoles_of_notMem f S res limVal hz

/-- **Analyticity of `removePoles` Away from `S`**:
If `s ∉ S` and `AnalyticAt ℂ f s`, then `AnalyticAt ℂ (removePoles f S res limVal) s`. -/
theorem analyticAt_removePoles_of_notMem {f : ℂ → ℂ} {S : Finset ℂ} {res limVal : ℂ → ℂ}
    {s : ℂ} (hs : s ∉ S) (hf : AnalyticAt ℂ f s) :
    AnalyticAt ℂ (removePoles f S res limVal) s := by
  refine Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds hf.eventually_analyticAt,
      nhdsWithin_le_nhds (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hs)] with z hfz hzs
    exact differentiableAt_removePoles_of_notMem hzs hfz.differentiableAt
  · exact (differentiableAt_removePoles_of_notMem hs hf.differentiableAt).continuousAt

/-!
## Section 2: Principal-Part Limit Theorems for the Smoothed Perron Integrand
-/

/-- For `0 < x`, `s ↦ (x : ℂ) ^ (s + 1)` is complex-differentiable at every `s : ℂ`. -/
theorem differentiableAt_ofReal_cpow_add_one {x : ℝ} (hx : 0 < x) (s : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ ↦ (x : ℂ) ^ (z + 1)) s :=
  (differentiable_ofReal_cpow_add_one hx).differentiableAt

/-- For `0 < x`, `smoothedPerronKernel x` is complex-differentiable at every `s ≠ 0, -1`. -/
theorem differentiableAt_smoothedPerronKernel {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs0 : s ≠ 0) (hs_neg1 : s ≠ -1) :
    DifferentiableAt ℂ (smoothedPerronKernel x) s := by
  unfold smoothedPerronKernel
  have hs1 : s + 1 ≠ 0 := add_eq_zero_iff_eq_neg.not.mpr hs_neg1
  exact (differentiableAt_ofReal_cpow_add_one hx s).div
    (differentiableAt_id.mul (differentiableAt_id.add_const 1)) (mul_ne_zero hs0 hs1)

/-- For `0 < x`, `smoothedPerronKernel x` is analytic at every `s ≠ 0, -1`. -/
theorem analyticAt_smoothedPerronKernel {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs0 : s ≠ 0) (hs_neg1 : s ≠ -1) :
    AnalyticAt ℂ (smoothedPerronKernel x) s := by
  have hopen : IsOpen ({0, -1}ᶜ : Set ℂ) :=
    (isClosed_singleton.union isClosed_singleton).isOpen_compl
  have hdiff : DifferentiableOn ℂ (smoothedPerronKernel x) ({0, -1}ᶜ : Set ℂ) := by
    intro z hz
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
    exact (differentiableAt_smoothedPerronKernel hx hz.1 hz.2).differentiableWithinAt
  exact (hdiff.analyticOnNhd hopen) s (by simp [hs0, hs_neg1])

/-- At `s = 1`, `smoothedPerronKernel x 1 = (x : ℂ) ^ 2 / 2`. -/
theorem smoothedPerronKernel_one (x : ℝ) :
    smoothedPerronKernel x 1 = (x : ℂ) ^ 2 / 2 := by
  unfold smoothedPerronKernel
  have h1 : (1 : ℂ) + 1 = (2 : ℕ) := by norm_num
  rw [h1, cpow_natCast]
  ring

/-- `riemannZeta` is analytic at every `s ≠ 1`. -/
theorem analyticAt_riemannZeta {s : ℂ} (hs1 : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s :=
  analyticOn_riemannZeta s hs1

/-- `deriv riemannZeta` is analytic at every `s ≠ 1`. -/
theorem analyticAt_deriv_riemannZeta {s : ℂ} (hs1 : s ≠ 1) :
    AnalyticAt ℂ (deriv riemannZeta) s :=
  (analyticAt_riemannZeta hs1).deriv

/-- `deriv riemannZeta` is complex-differentiable at every `s ≠ 1`. -/
theorem differentiableAt_deriv_riemannZeta {s : ℂ} (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (deriv riemannZeta) s :=
  (analyticAt_deriv_riemannZeta hs1).differentiableAt

/-- For `0 < x`, `smoothedPerronIntegrand x` is complex-differentiable at every `s` where
`s ≠ 1`, `s ≠ 0`, `s ≠ -1`, and `riemannZeta s ≠ 0`. -/
theorem differentiableAt_smoothedPerronIntegrand {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs1 : s ≠ 1) (hs0 : s ≠ 0) (hs_neg1 : s ≠ -1) (hζ : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ (smoothedPerronIntegrand x) s := by
  unfold smoothedPerronIntegrand
  exact ((differentiableAt_deriv_riemannZeta hs1).neg.div
    (differentiableAt_riemannZeta hs1) hζ).mul (differentiableAt_smoothedPerronKernel hx hs0
      hs_neg1)

/-- For `0 < x`, `smoothedPerronIntegrand x` is analytic at every `s` where
`s ≠ 1`, `s ≠ 0`, `s ≠ -1`, and `riemannZeta s ≠ 0`. -/
theorem analyticAt_smoothedPerronIntegrand {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs1 : s ≠ 1) (hs0 : s ≠ 0) (hs_neg1 : s ≠ -1) (hζ : riemannZeta s ≠ 0) :
    AnalyticAt ℂ (smoothedPerronIntegrand x) s := by
  unfold smoothedPerronIntegrand
  exact ((analyticAt_deriv_riemannZeta hs1).neg.div
    (analyticAt_riemannZeta hs1) hζ).mul (analyticAt_smoothedPerronKernel hx hs0 hs_neg1)

/-!
### Subsection 2.1: Principal Part at $s = 1$
-/

/-- The residue of `smoothedPerronIntegrand x` at `s = 1` is `x ^ 2 / 2`. -/
noncomputable def resOne (x : ℝ) : ℂ :=
  (x : ℂ) ^ 2 / 2

/-- The limit value of `smoothedPerronIntegrand x s - resOne x / (s - 1)` as `s → 1`. -/
noncomputable def limOne (x : ℝ) : ℂ :=
  deriv (smoothedPerronKernel x) 1 -
    (deriv riemannZeta₁ 1 / riemannZeta₁ 1) * smoothedPerronKernel x 1

/-- **Principal-Part Limit Theorem at $s = 1$**:
For `0 < x`, `smoothedPerronIntegrand x s - ((x : ℂ) ^ 2 / 2) / (s - 1) → limOne x`
as `s → 1` in `𝓝[≠] 1`. -/
theorem tendsto_smoothedPerronIntegrand_sub_resOne {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s ↦ smoothedPerronIntegrand x s - resOne x / (s - 1))
      (𝓝[≠] 1) (𝓝 (limOne x)) := by
  have hg_diff : DifferentiableAt ℂ (smoothedPerronKernel x) 1 :=
    differentiableAt_smoothedPerronKernel hx one_ne_zero (by norm_num)
  have ht1 : Tendsto (fun s ↦ (smoothedPerronKernel x s - smoothedPerronKernel x 1) / (s - 1))
      (𝓝[≠] 1) (𝓝 (deriv (smoothedPerronKernel x) 1)) :=
    tendsto_sub_div_sub_of_differentiableAt hg_diff
  have hζ₁_an : AnalyticAt ℂ riemannZeta₁ 1 :=
    (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ) 1 (mem_univ 1)
  have hζ₁_ne : riemannZeta₁ 1 ≠ 0 := by rw [riemannZeta₁_one]; exact one_ne_zero
  have hc2 : ContinuousAt
      (fun s ↦ (deriv riemannZeta₁ s / riemannZeta₁ s) * smoothedPerronKernel x s) 1 := by
    refine ContinuousAt.mul ?_ hg_diff.continuousAt
    exact hζ₁_an.deriv.continuousAt.div differentiable_riemannZeta₁.continuous.continuousAt hζ₁_ne
  have ht2 : Tendsto
      (fun s ↦ (deriv riemannZeta₁ s / riemannZeta₁ s) * smoothedPerronKernel x s)
      (𝓝[≠] 1) (𝓝 ((deriv riemannZeta₁ 1 / riemannZeta₁ 1) * smoothedPerronKernel x 1)) :=
    hc2.tendsto.mono_left nhdsWithin_le_nhds
  refine (ht1.sub ht2).congr' ?_
  filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add] with s hs
  unfold smoothedPerronIntegrand resOne
  rw [← smoothedPerronKernel_one x, neg_div, hs]
  ring

/-- `smoothedPerronIntegrand x` is complex-differentiable on a punctured neighborhood of `1`. -/
theorem eventually_differentiableAt_smoothedPerronIntegrand_nhdsNE_one {x : ℝ} (hx : 0 < x) :
    ∀ᶠ z in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ (smoothedPerronIntegrand x) z := by
  have hopen : IsOpen {z : ℂ | (1 / 2 : ℝ) < z.re} := isOpen_lt continuous_const continuous_re
  have hmem : {z : ℂ | (1 / 2 : ℝ) < z.re} ∈ 𝓝[≠] (1 : ℂ) :=
    nhdsWithin_le_nhds (hopen.mem_nhds (by norm_num))
  have hζ₁_ne : ∀ᶠ z in 𝓝[≠] (1 : ℂ), riemannZeta₁ z ≠ 0 := by
    refine nhdsWithin_le_nhds ?_
    refine differentiable_riemannZeta₁.continuous.continuousAt.eventually_ne ?_
    rw [riemannZeta₁_one]
    exact one_ne_zero
  filter_upwards [self_mem_nhdsWithin, hmem, hζ₁_ne] with z hz1 hz_re hz_ζ₁
  have hz0 : z ≠ 0 := by
    intro h; subst h; simp at hz_re; linarith
  have hz_neg1 : z ≠ -1 := by
    intro h; subst h; simp at hz_re; linarith
  have hζ_ne : riemannZeta z ≠ 0 := by
    rw [riemannZeta_eq_inv_sub_mul hz1]
    exact mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hz1)) hz_ζ₁
  exact differentiableAt_smoothedPerronIntegrand hx hz1 hz0 hz_neg1 hζ_ne

/-!
### Subsection 2.2: Principal Part at $s = 0$
-/

/-- The auxiliary function $h_x(s) = \left(-\frac{\zeta'(s)}{\zeta(s)}\right) \frac{x^{s+1}}{s+1}$,
so that `smoothedPerronIntegrand x s = auxZero x s / s`. -/
noncomputable def auxZero (x : ℝ) (s : ℂ) : ℂ :=
  (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ (s + 1) / (s + 1))

/-- The residue of `smoothedPerronIntegrand x` at `s = 0`:
`resZero x = (-deriv riemannZeta 0 / riemannZeta 0) * (x : ℂ)`. -/
noncomputable def resZero (x : ℝ) : ℂ :=
  (-deriv riemannZeta 0 / riemannZeta 0) * (x : ℂ)

/-- The limit value of `smoothedPerronIntegrand x s - resZero x / (s - 0)` as `s → 0`. -/
noncomputable def limZero (x : ℝ) : ℂ :=
  deriv (auxZero x) 0

/-- At `s = 0`, `auxZero x 0 = resZero x`. -/
theorem auxZero_zero (x : ℝ) : auxZero x 0 = resZero x := by
  unfold auxZero resZero
  simp

/-- For all `s : ℂ`, `smoothedPerronIntegrand x s = auxZero x s / (s - 0)`. -/
theorem smoothedPerronIntegrand_eq_auxZero_div (x : ℝ) (s : ℂ) :
    smoothedPerronIntegrand x s = auxZero x s / (s - 0) := by
  unfold smoothedPerronIntegrand smoothedPerronKernel auxZero
  rw [sub_zero, div_mul_eq_div_div_swap, mul_div_assoc]

/-- For `0 < x`, `auxZero x` is complex-differentiable at `s = 0`. -/
theorem differentiableAt_auxZero_zero {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℂ (auxZero x) 0 := by
  unfold auxZero
  have h01 : (0 : ℂ) ≠ 1 := zero_ne_one
  have hζ0 : riemannZeta 0 ≠ 0 := by rw [riemannZeta_zero]; norm_num
  refine ((differentiableAt_deriv_riemannZeta h01).neg.div
    (differentiableAt_riemannZeta h01) hζ0).mul ?_
  exact (differentiableAt_ofReal_cpow_add_one hx 0).div
    (differentiableAt_id.add_const 1) (by norm_num)

/-- **Principal-Part Limit Theorem at $s = 0$**:
For `0 < x`, `smoothedPerronIntegrand x s - resZero x / (s - 0) → limZero x`
as `s → 0` in `𝓝[≠] 0`. -/
theorem tendsto_smoothedPerronIntegrand_sub_resZero {x : ℝ} (hx : 0 < x) :
    Tendsto (fun s ↦ smoothedPerronIntegrand x s - resZero x / (s - 0))
      (𝓝[≠] 0) (𝓝 (limZero x)) := by
  have ht := tendsto_sub_div_sub_of_differentiableAt (differentiableAt_auxZero_zero hx)
  unfold limZero
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s _
  rw [smoothedPerronIntegrand_eq_auxZero_div, ← auxZero_zero, sub_div]

/-- `smoothedPerronIntegrand x` is complex-differentiable on a punctured neighborhood of `0`. -/
theorem eventually_differentiableAt_smoothedPerronIntegrand_nhdsNE_zero {x : ℝ} (hx : 0 < x) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (smoothedPerronIntegrand x) z := by
  have h1 : ({1, -1}ᶜ : Set ℂ) ∈ 𝓝[≠] (0 : ℂ) := by
    refine nhdsWithin_le_nhds ?_
    exact (isClosed_singleton.union isClosed_singleton).isOpen_compl.mem_nhds (by simp)
  have hζ : ∀ᶠ z in 𝓝[≠] (0 : ℂ), riemannZeta z ≠ 0 := by
    refine nhdsWithin_le_nhds ?_
    refine (differentiableAt_riemannZeta zero_ne_one).continuousAt.eventually_ne ?_
    rw [riemannZeta_zero]
    norm_num
  filter_upwards [self_mem_nhdsWithin, h1, hζ] with z hz0 hz1 hz_ζ
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz1
  exact differentiableAt_smoothedPerronIntegrand hx hz1.1 hz0 hz1.2 hz_ζ

/-!
### Subsection 2.3: Principal Part at Any Zero $\rho \ne 0, 1, -1$ of `riemannZeta`
-/

/-- If `riemannZeta ρ = 0` and `ρ ≠ 1`, then `analyticOrderNatAt riemannZeta ρ ≠ 0`. -/
theorem analyticOrderNatAt_riemannZeta_ne_zero {ρ : ℂ} (hζ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) :
    analyticOrderNatAt riemannZeta ρ ≠ 0 := by
  have hne_top := analyticOrderAt_riemannZeta_ne_top hρ1
  have hne_zero : analyticOrderAt riemannZeta ρ ≠ 0 := by
    intro h0
    exact ((analyticAt_riemannZeta hρ1).analyticOrderAt_eq_zero.mp h0) hζ
  intro hnat0
  apply hne_zero
  rw [← Nat.cast_analyticOrderNatAt hne_top, hnat0, Nat.cast_zero]

/-- If `u` is analytic at `ρ` with `u ρ ≠ 0` and `riemannZeta =ᶠ[𝓝 ρ] fun z ↦ (z - ρ) ^ m • u z`
with `m ≠ 0`, then on `𝓝[≠] ρ`:
`deriv riemannZeta z / riemannZeta z = (m : ℂ) / (z - ρ) + deriv u z / u z`. -/
theorem eventually_logDeriv_riemannZeta_eq_near_zero {ρ : ℂ} {m : ℕ} {u : ℂ → ℂ}
    (hm : m ≠ 0) (hu_an : AnalyticAt ℂ u ρ) (hu_ne : u ρ ≠ 0)
    (heq : riemannZeta =ᶠ[𝓝 ρ] fun z ↦ (z - ρ) ^ m • u z) :
    ∀ᶠ z in 𝓝[≠] ρ,
      deriv riemannZeta z / riemannZeta z = (m : ℂ) / (z - ρ) + deriv u z / u z := by
  have heq_mul : riemannZeta =ᶠ[𝓝 ρ] fun z ↦ (z - ρ) ^ m * u z := by
    simpa only [smul_eq_mul] using heq
  have hderiv_eq : deriv riemannZeta =ᶠ[𝓝 ρ] deriv (fun z ↦ (z - ρ) ^ m * u z) :=
    heq_mul.deriv
  have hu_diff : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ u z :=
    hu_an.eventually_analyticAt.mono fun _ hz ↦ hz.differentiableAt
  have hu_ne_nhds : ∀ᶠ z in 𝓝 ρ, u z ≠ 0 :=
    hu_an.continuousAt.eventually_ne hu_ne
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds heq_mul,
    nhdsWithin_le_nhds hderiv_eq,
    nhdsWithin_le_nhds hu_diff,
    nhdsWithin_le_nhds hu_ne_nhds] with z hzρ hζ_z hdζ_z hu_z hu_z_ne
  have hpow_deriv : HasDerivAt (fun w : ℂ ↦ (w - ρ) ^ m)
      ((m : ℂ) * (z - ρ) ^ (m - 1)) z := by
    have h1 := ((hasDerivAt_id z).sub_const ρ).pow m
    rw [mul_one] at h1
    exact h1
  have hmul_deriv : deriv (fun w : ℂ ↦ (w - ρ) ^ m * u w) z =
      (m : ℂ) * (z - ρ) ^ (m - 1) * u z + (z - ρ) ^ m * deriv u z :=
    (hpow_deriv.mul hu_z.hasDerivAt).deriv
  rw [hdζ_z, hmul_deriv, hζ_z]
  have hsub_ne : z - ρ ≠ 0 := sub_ne_zero.mpr hzρ
  have hpow_split : (z - ρ) ^ m = (z - ρ) ^ (m - 1) * (z - ρ) := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)]
  have hpow_ne : (z - ρ) ^ (m - 1) ≠ 0 := pow_ne_zero (m - 1) hsub_ne
  rw [hpow_split]
  field_simp

/-- The residue of `smoothedPerronIntegrand x` at a zero `ρ` of `riemannZeta` (`ρ ≠ 0, 1, -1`):
`resZeroRho x ρ = -(analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedPerronKernel x ρ`. -/
noncomputable def resZeroRho (x : ℝ) (ρ : ℂ) : ℂ :=
  -(analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedPerronKernel x ρ

/-- **Existence of the Principal-Part Limit at Any Zero $\rho \ne 0, 1, -1$ of `riemannZeta`**:
If `0 < x`, `riemannZeta ρ = 0`, `ρ ≠ 1`, `ρ ≠ 0`, and `ρ ≠ -1`, then there exists `L : ℂ`
such that `smoothedPerronIntegrand x s - resZeroRho x ρ / (s - ρ) → L` on `𝓝[≠] ρ`. -/
theorem exists_tendsto_smoothedPerronIntegrand_sub_resZeroRho {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0) (hρ_neg1 : ρ ≠ -1) :
    ∃ L : ℂ, Tendsto (fun s ↦ smoothedPerronIntegrand x s - resZeroRho x ρ / (s - ρ))
      (𝓝[≠] ρ) (𝓝 L) := by
  have hne_top := analyticOrderAt_riemannZeta_ne_top hρ1
  obtain ⟨u, hu_an, hu_ne, heq⟩ :=
    (analyticAt_riemannZeta hρ1).analyticOrderAt_ne_top.mp hne_top
  set m := analyticOrderNatAt riemannZeta ρ
  have hm : m ≠ 0 := analyticOrderNatAt_riemannZeta_ne_zero hζ hρ1
  have hlog := eventually_logDeriv_riemannZeta_eq_near_zero hm hu_an hu_ne heq
  have hg_diff : DifferentiableAt ℂ (smoothedPerronKernel x) ρ :=
    differentiableAt_smoothedPerronKernel hx hρ0 hρ_neg1
  refine ⟨-(m : ℂ) * deriv (smoothedPerronKernel x) ρ -
    (deriv u ρ / u ρ) * smoothedPerronKernel x ρ, ?_⟩
  have ht1 : Tendsto
      (fun s ↦ -(m : ℂ) * ((smoothedPerronKernel x s - smoothedPerronKernel x ρ) / (s - ρ)))
      (𝓝[≠] ρ) (𝓝 (-(m : ℂ) * deriv (smoothedPerronKernel x) ρ)) :=
    (tendsto_sub_div_sub_of_differentiableAt hg_diff).const_mul (-(m : ℂ))
  have hc2 : ContinuousAt (fun s ↦ (deriv u s / u s) * smoothedPerronKernel x s) ρ :=
    (hu_an.deriv.continuousAt.div hu_an.continuousAt hu_ne).mul hg_diff.continuousAt
  have ht2 : Tendsto (fun s ↦ (deriv u s / u s) * smoothedPerronKernel x s)
      (𝓝[≠] ρ) (𝓝 ((deriv u ρ / u ρ) * smoothedPerronKernel x ρ)) :=
    hc2.tendsto.mono_left nhdsWithin_le_nhds
  refine (ht1.sub ht2).congr' ?_
  filter_upwards [hlog] with s hs
  unfold smoothedPerronIntegrand resZeroRho
  rw [neg_div, hs]
  ring

/-- The limit value of `smoothedPerronIntegrand x s - resZeroRho x ρ / (s - ρ)` as `s → ρ`. -/
noncomputable def limZeroRho (x : ℝ) (ρ : ℂ) : ℂ :=
  limUnder (𝓝[≠] ρ) (fun s ↦ smoothedPerronIntegrand x s - resZeroRho x ρ / (s - ρ))

/-- **Principal-Part Limit Theorem at Any Zero $\rho \ne 0, 1, -1$ of `riemannZeta`**:
If `0 < x`, `riemannZeta ρ = 0`, `ρ ≠ 1`, `ρ ≠ 0`, and `ρ ≠ -1`, then
`smoothedPerronIntegrand x s - resZeroRho x ρ / (s - ρ) → limZeroRho x ρ` on `𝓝[≠] ρ`. -/
theorem tendsto_smoothedPerronIntegrand_sub_resZeroRho {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hζ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0) (hρ_neg1 : ρ ≠ -1) :
    Tendsto (fun s ↦ smoothedPerronIntegrand x s - resZeroRho x ρ / (s - ρ))
      (𝓝[≠] ρ) (𝓝 (limZeroRho x ρ)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_smoothedPerronIntegrand_sub_resZeroRho hx hζ hρ1 hρ0 hρ_neg1
  unfold limZeroRho
  rwa [hL.limUnder_eq]

/-- If `0 < x`, `ρ ≠ 1`, `ρ ≠ 0`, and `ρ ≠ -1`, then `smoothedPerronIntegrand x` is
complex-differentiable on a punctured neighborhood `𝓝[≠] ρ`. -/
theorem eventually_differentiableAt_smoothedPerronIntegrand_nhdsNE_of_ne {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hρ1 : ρ ≠ 1) (hρ0 : ρ ≠ 0) (hρ_neg1 : ρ ≠ -1) :
    ∀ᶠ z in 𝓝[≠] ρ, DifferentiableAt ℂ (smoothedPerronIntegrand x) z := by
  have hne_top := analyticOrderAt_riemannZeta_ne_top hρ1
  obtain ⟨u, hu_an, hu_ne, heq⟩ :=
    (analyticAt_riemannZeta hρ1).analyticOrderAt_ne_top.mp hne_top
  have hζ_ne : ∀ᶠ z in 𝓝[≠] ρ, riemannZeta z ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds heq,
      nhdsWithin_le_nhds (hu_an.continuousAt.eventually_ne hu_ne)] with z hzρ hζ_z hu_z
    rw [hζ_z, smul_eq_mul]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzρ)) hu_z
  have h_avoid : ({1, 0, -1}ᶜ : Set ℂ) ∈ 𝓝[≠] ρ := by
    refine nhdsWithin_le_nhds ?_
    refine (isClosed_singleton.union (isClosed_singleton.union
      isClosed_singleton)).isOpen_compl.mem_nhds ?_
    simp [hρ1, hρ0, hρ_neg1]
  filter_upwards [h_avoid, hζ_ne] with z hz hζ_z
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hz
  exact differentiableAt_smoothedPerronIntegrand hx hz.1 hz.2.1 hz.2.2 hζ_z

/-!
## Section 3: Zero Classification in $\{s \in \mathbb{C} \mid -1/2 < s.\text{re} \wedge
|s.\text{im}| \le T\}$
-/

/-- Every zero `s` of `riemannZeta` with `-1 / 2 < s.re` is a nontrivial zero
(since every trivial zero `-2 * (n + 1)` has real part `≤ -2 < -1 / 2`, and `riemannZeta 1 ≠ 0`). -/
theorem isNontrivialZetaZero_of_re_gt_neg_half {s : ℂ}
    (hζ : riemannZeta s = 0) (hre : -1 / 2 < s.re) :
    IsNontrivialZetaZero s := by
  refine ⟨hζ, ?_, ?_⟩
  · rintro ⟨n, rfl⟩
    have hre_le : (-2 * ((n : ℂ) + 1)).re ≤ -2 := by simp
    linarith
  · rintro rfl
    exact riemannZeta_one_ne_zero hζ

theorem isNontrivialZetaZero_ne_neg_one {s : ℂ} (hs : IsNontrivialZetaZero s) : s ≠ -1 := by
  rintro rfl
  have h := zero_lt_re_of_isNontrivialZetaZero hs
  norm_num at h

/-- **Zero Classification in `{s : ℂ | -1 / 2 < s.re ∧ |s.im| ≤ T}`**:
Every zero `s` of `riemannZeta` in the half-strip `-1 / 2 < s.re` with `|s.im| ≤ T`
belongs to `nontrivialZetaZerosUpTo T`. -/
theorem mem_nontrivialZetaZerosUpTo_of_re_gt_neg_half {T : ℝ} {s : ℂ}
    (hζ : riemannZeta s = 0) (hre : -1 / 2 < s.re) (him : |s.im| ≤ T) :
    s ∈ nontrivialZetaZerosUpTo T :=
  mem_nontrivialZetaZerosUpTo.mpr ⟨isNontrivialZetaZero_of_re_gt_neg_half hζ hre, him⟩

theorem one_notMem_nontrivialZetaZerosUpTo (T : ℝ) :
    (1 : ℂ) ∉ nontrivialZetaZerosUpTo T := by
  intro h
  exact (mem_nontrivialZetaZerosUpTo.mp h).1.2.2 rfl

theorem zero_notMem_nontrivialZetaZerosUpTo (T : ℝ) :
    (0 : ℂ) ∉ nontrivialZetaZerosUpTo T := by
  intro h
  exact isNontrivialZetaZero_ne_zero (mem_nontrivialZetaZerosUpTo.mp h).1 rfl

/-!
## Section 4: Regularized Smoothed Perron Integrand & Rectangle Holomorphicity
-/

/-- The finite set of poles of `smoothedPerronIntegrand x` in the region
`-1 / 2 < s.re ∧ |s.im| ≤ T`, namely `{1, 0} ∪ nontrivialZetaZerosUpTo T`. -/
noncomputable def perronPolesUpTo (T : ℝ) : Finset ℂ :=
  insert (1 : ℂ) (insert (0 : ℂ) (nontrivialZetaZerosUpTo T))

@[simp]
theorem mem_perronPolesUpTo {T : ℝ} {s : ℂ} :
    s ∈ perronPolesUpTo T ↔ s = 1 ∨ s = 0 ∨ s ∈ nontrivialZetaZerosUpTo T := by
  simp [perronPolesUpTo]

/-- The residue of `smoothedPerronIntegrand x` at a pole `p ∈ perronPolesUpTo T`. -/
noncomputable def perronResidue (x : ℝ) (p : ℂ) : ℂ :=
  if p = 1 then resOne x
  else if p = 0 then resZero x
  else resZeroRho x p

/-- The punctured-neighborhood limit of `smoothedPerronIntegrand x s - perronResidue x p / (s - p)`
at a pole `p ∈ perronPolesUpTo T`. -/
noncomputable def perronLimVal (x : ℝ) (p : ℂ) : ℂ :=
  if p = 1 then limOne x
  else if p = 0 then limZero x
  else limZeroRho x p

@[simp]
theorem perronResidue_one (x : ℝ) : perronResidue x 1 = resOne x := by
  simp [perronResidue]

@[simp]
theorem perronResidue_zero (x : ℝ) : perronResidue x 0 = resZero x := by
  simp [perronResidue]

theorem perronResidue_of_mem_nontrivialZetaZerosUpTo (x : ℝ) {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ nontrivialZetaZerosUpTo T) :
    perronResidue x ρ = resZeroRho x ρ := by
  have hζ := (mem_nontrivialZetaZerosUpTo.mp hρ).1
  have h1 : ρ ≠ 1 := hζ.2.2
  have h0 : ρ ≠ 0 := isNontrivialZetaZero_ne_zero hζ
  simp [perronResidue, h1, h0]

/-- **The Regularized Smoothed Perron Integrand (`regularizedSmoothedPerron`)**:
Obtained from `smoothedPerronIntegrand x` by subtracting the principal parts at `1`, `0`,
and all `ρ ∈ nontrivialZetaZerosUpTo T` and filling in their removable singularities. -/
noncomputable def regularizedSmoothedPerron (x T : ℝ) (s : ℂ) : ℂ :=
  removePoles (smoothedPerronIntegrand x) (perronPolesUpTo T) (perronResidue x) (perronLimVal x) s

/-- **Explicit Formula for `regularizedSmoothedPerron x T s` Away from the Poles**:
For every `s ∉ perronPolesUpTo T` (i.e., `s ≠ 1`, `s ≠ 0`, and `s ∉ nontrivialZetaZerosUpTo T`),
$$
\text{regularizedSmoothedPerron } x\, T\, s =
  \text{smoothedPerronIntegrand } x\, s
  - \frac{\text{resOne } x}{s - 1}
  - \frac{\text{resZero } x}{s}
  - \sum_{\rho \in \text{nontrivialZetaZerosUpTo } T} \frac{\text{resZeroRho } x\, \rho}{s - \rho}.
$$ -/
theorem regularizedSmoothedPerron_eq_of_notMem (x T : ℝ) {s : ℂ}
    (hs : s ∉ perronPolesUpTo T) :
    regularizedSmoothedPerron x T s =
      smoothedPerronIntegrand x s -
        resOne x / (s - 1) -
        resZero x / s -
        ∑ ρ ∈ nontrivialZetaZerosUpTo T, resZeroRho x ρ / (s - ρ) := by
  unfold regularizedSmoothedPerron
  rw [removePoles_of_notMem _ _ _ _ hs]
  unfold perronPolesUpTo
  have h1_notMem : (1 : ℂ) ∉ insert (0 : ℂ) (nontrivialZetaZerosUpTo T) := by
    rw [Finset.mem_insert, not_or]
    exact ⟨one_ne_zero, one_notMem_nontrivialZetaZerosUpTo T⟩
  have h0_notMem : (0 : ℂ) ∉ nontrivialZetaZerosUpTo T :=
    zero_notMem_nontrivialZetaZerosUpTo T
  rw [Finset.sum_insert h1_notMem, Finset.sum_insert h0_notMem,
    perronResidue_one, perronResidue_zero, sub_zero]
  have hsum : ∑ ρ ∈ nontrivialZetaZerosUpTo T, perronResidue x ρ / (s - ρ) =
      ∑ ρ ∈ nontrivialZetaZerosUpTo T, resZeroRho x ρ / (s - ρ) := by
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    rw [perronResidue_of_mem_nontrivialZetaZerosUpTo x hρ]
  rw [hsum]
  ring

/-- For `0 < x` and every pole `p ∈ perronPolesUpTo T`, `regularizedSmoothedPerron x T` is
analytic at `p`. -/
theorem analyticAt_regularizedSmoothedPerron_of_mem_poles {x T : ℝ} (hx : 0 < x) {p : ℂ}
    (hp : p ∈ perronPolesUpTo T) :
    AnalyticAt ℂ (regularizedSmoothedPerron x T) p := by
  unfold regularizedSmoothedPerron
  rcases mem_perronPolesUpTo.mp hp with rfl | rfl | hρ
  · refine analyticAt_removePoles_of_mem hp
      (eventually_differentiableAt_smoothedPerronIntegrand_nhdsNE_one hx) ?_
    simpa [perronResidue, perronLimVal] using tendsto_smoothedPerronIntegrand_sub_resOne hx
  · refine analyticAt_removePoles_of_mem hp
      (eventually_differentiableAt_smoothedPerronIntegrand_nhdsNE_zero hx) ?_
    simpa [perronResidue, perronLimVal] using tendsto_smoothedPerronIntegrand_sub_resZero hx
  · have hζ := (mem_nontrivialZetaZerosUpTo.mp hρ).1
    have h1 : p ≠ 1 := hζ.2.2
    have h0 : p ≠ 0 := isNontrivialZetaZero_ne_zero hζ
    have h_neg1 : p ≠ -1 := isNontrivialZetaZero_ne_neg_one hζ
    refine analyticAt_removePoles_of_mem hp
      (eventually_differentiableAt_smoothedPerronIntegrand_nhdsNE_of_ne hx h1 h0 h_neg1) ?_
    simpa [perronResidue, perronLimVal, h1, h0] using
      tendsto_smoothedPerronIntegrand_sub_resZeroRho hx hζ.1 h1 h0 h_neg1

/-- **Analyticity of `regularizedSmoothedPerron x T` on `{s : ℂ | -1 / 2 < s.re ∧ |s.im| ≤ T}`**:
For `0 < x`, `regularizedSmoothedPerron x T` is analytic at every `s : ℂ` satisfying
`-1 / 2 < s.re` and `|s.im| ≤ T`. -/
theorem analyticAt_regularizedSmoothedPerron {x T : ℝ} (hx : 0 < x) {s : ℂ}
    (hre : -1 / 2 < s.re) (him : |s.im| ≤ T) :
    AnalyticAt ℂ (regularizedSmoothedPerron x T) s := by
  by_cases hs : s ∈ perronPolesUpTo T
  · exact analyticAt_regularizedSmoothedPerron_of_mem_poles hx hs
  · unfold regularizedSmoothedPerron
    refine analyticAt_removePoles_of_notMem hs ?_
    have hs1 : s ≠ 1 := fun h ↦ hs (mem_perronPolesUpTo.mpr (Or.inl h))
    have hs0 : s ≠ 0 := fun h ↦ hs (mem_perronPolesUpTo.mpr (Or.inr (Or.inl h)))
    have hs_neg1 : s ≠ -1 := by
      rintro rfl
      norm_num at hre
    have hζ : riemannZeta s ≠ 0 := by
      intro hζ0
      exact hs (mem_perronPolesUpTo.mpr
        (Or.inr (Or.inr (mem_nontrivialZetaZerosUpTo_of_re_gt_neg_half hζ0 hre him))))
    exact analyticAt_smoothedPerronIntegrand hx hs1 hs0 hs_neg1 hζ

/-- **Differentiability of `regularizedSmoothedPerron x T` on `{s : ℂ | -1 / 2 < s.re ∧ |s.im| ≤
T}`**:
For `0 < x`, `regularizedSmoothedPerron x T` is complex-differentiable at every `s : ℂ`
satisfying `-1 / 2 < s.re` and `|s.im| ≤ T`. -/
theorem differentiableAt_regularizedSmoothedPerron {x T : ℝ} (hx : 0 < x) {s : ℂ}
    (hre : -1 / 2 < s.re) (him : |s.im| ≤ T) :
    DifferentiableAt ℂ (regularizedSmoothedPerron x T) s :=
  (analyticAt_regularizedSmoothedPerron hx hre him).differentiableAt

/-- **Cauchy Rectangle Theorem for `regularizedSmoothedPerron x T`**:
For `0 < x`, `0 ≤ T`, and `-1 / 2 < a ≤ b`, `regularizedSmoothedPerron x T` is differentiable
on the closed rectangle `[a, b] ×ℂ [-T, T]`, and its boundary rectangle integral vanishes:
$$
\left(\int_a^b \text{regularizedSmoothedPerron } x\, T\, (\sigma - i T)\, d\sigma
  - \int_a^b \text{regularizedSmoothedPerron } x\, T\, (\sigma + i T)\, d\sigma\right)
+ i \left(\int_{-T}^T \text{regularizedSmoothedPerron } x\, T\, (b + i y)\, dy
  - \int_{-T}^T \text{regularizedSmoothedPerron } x\, T\, (a + i y)\, dy\right) = 0.
$$ -/
theorem integral_boundary_rect_regularizedSmoothedPerron_eq_zero
    {x T a b : ℝ} (hx : 0 < x) (hT : 0 ≤ T) (ha : -1 / 2 < a) (hab : a ≤ b) :
    ((∫ σ : ℝ in a..b, regularizedSmoothedPerron x T (σ + (-T : ℝ) * I)) -
      ∫ σ : ℝ in a..b, regularizedSmoothedPerron x T (σ + (T : ℝ) * I)) +
    I * ((∫ y : ℝ in (-T)..T, regularizedSmoothedPerron x T (b + (y : ℝ) * I)) -
      ∫ y : ℝ in (-T)..T, regularizedSmoothedPerron x T (a + (y : ℝ) * I)) = 0 := by
  have hdiff : DifferentiableOn ℂ (regularizedSmoothedPerron x T)
      (Set.uIcc ((a : ℂ) + (-T : ℝ) * I).re ((b : ℂ) + (T : ℝ) * I).re ×ℂ
        Set.uIcc ((a : ℂ) + (-T : ℝ) * I).im ((b : ℂ) + (T : ℝ) * I).im) := by
    intro s hs
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hs
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le (by linarith), mem_reProdIm, Set.mem_Icc,
      Set.mem_Icc] at hs
    refine (differentiableAt_regularizedSmoothedPerron hx ?_ ?_).differentiableWithinAt
    · linarith [hs.1.1]
    · exact abs_le.mpr hs.2
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (regularizedSmoothedPerron x T) (a + (-T : ℝ) * I) (b + (T : ℝ) * I) hdiff
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at hrect
  linear_combination hrect
/-!
## Section 1: Definition of `rectBoundaryIntegral` and Exact 1D `log` + `arctan` Antiderivatives
-/

/-- The counterclockwise boundary integral of `f : ℂ → ℂ` around the rectangle
`[c₁, c₂] × [-T, T]`, defined purely in terms of four 1D `intervalIntegral`s:
- Right vertical edge `c₂ + t * I` (`t` from `-T` to `T`),
- Left vertical edge `c₁ + t * I` (`t` from `-T` to `T`, negated),
- Top horizontal edge `σ + T * I` (`σ` from `c₁` to `c₂`, negated),
- Bottom horizontal edge `σ - T * I` (`σ` from `c₁` to `c₂`). -/
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) (c₁ c₂ T : ℝ) : ℂ :=
  (I * ∫ t in (-T)..T, f (c₂ + t * I))
  - (I * ∫ t in (-T)..T, f (c₁ + t * I))
  - (∫ σ in c₁..c₂, f (σ + T * I))
  + (∫ σ in c₁..c₂, f (σ - T * I))

/-- Scaling linearity of `rectBoundaryIntegral`: pulling out a constant `r : ℂ`. -/
theorem rectBoundaryIntegral_const_mul (r : ℂ) (f : ℂ → ℂ) (c₁ c₂ T : ℝ) :
    rectBoundaryIntegral (fun s ↦ r * f s) c₁ c₂ T =
      r * rectBoundaryIntegral f c₁ c₂ T := by
  unfold rectBoundaryIntegral
  simp only [intervalIntegral.integral_const_mul]
  ring

/-- For `a ≠ 0` and any `x : ℝ`, `0 < a ^ 2 + x ^ 2`. -/
theorem add_sq_pos_of_ne_zero {a x : ℝ} (ha : a ≠ 0) : 0 < a ^ 2 + x ^ 2 :=
  add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero ha) (sq_nonneg x)

/-- Real derivative of `u ↦ 1 / 2 * Real.log (a ^ 2 + (u - y₀) ^ 2)` for `a ≠ 0`. -/
theorem hasDerivAt_half_log_add_sq {a y₀ t : ℝ} (ha : a ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ 1 / 2 * Real.log (a ^ 2 + (u - y₀) ^ 2))
      ((t - y₀) / (a ^ 2 + (t - y₀) ^ 2)) t := by
  have hpos : a ^ 2 + (t - y₀) ^ 2 ≠ 0 := (add_sq_pos_of_ne_zero ha).ne'
  have hd_inner : HasDerivAt (fun u : ℝ ↦ a ^ 2 + (u - y₀) ^ 2) (2 * (t - y₀)) t := by
    have hd1 : HasDerivAt (fun u : ℝ ↦ (u - y₀) ^ 2) (2 * (t - y₀) ^ (2 - 1) * 1) t :=
      ((hasDerivAt_id t).sub_const y₀).pow 2
    simpa [Pi.pow_def] using hd1.const_add (a ^ 2)
  have hd := ((Real.hasDerivAt_log hpos).comp t hd_inner).const_mul (1 / 2)
  refine hd.congr_deriv ?_
  ring

/-- Real derivative of `u ↦ Real.arctan ((u - y₀) / a)` for `a ≠ 0`. -/
theorem hasDerivAt_arctan_sub_div {a y₀ t : ℝ} (ha : a ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ Real.arctan ((u - y₀) / a))
      (a / (a ^ 2 + (t - y₀) ^ 2)) t := by
  have hpos : a ^ 2 + (t - y₀) ^ 2 ≠ 0 := (add_sq_pos_of_ne_zero ha).ne'
  have hd_inner : HasDerivAt (fun u : ℝ ↦ (u - y₀) / a) (1 / a) t :=
    ((hasDerivAt_id t).sub_const y₀).div_const a
  have hd := hd_inner.arctan
  refine hd.congr_deriv ?_
  field_simp [ha, hpos]

/-- If `a ≠ 0`, then `(a : ℂ) + (b : ℂ) * I ≠ 0`. -/
theorem complex_add_mul_I_ne_zero_of_left {a b : ℝ} (ha : a ≠ 0) :
    (a : ℂ) + (b : ℂ) * I ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  exact ha (by simpa using hre)

/-- If `b ≠ 0`, then `(a : ℂ) + (b : ℂ) * I ≠ 0`. -/
theorem complex_add_mul_I_ne_zero_of_right {a b : ℝ} (hb : b ≠ 0) :
    (a : ℂ) + (b : ℂ) * I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  exact hb (by simpa using him)

/-- **Vertical 1D Antiderivative**:
For `a ≠ 0` (`a = c - p.re`) and `y₀ = p.im`, the complex antiderivative of
`t ↦ I / (a + (t - y₀) * I)` along the vertical line `s = c + t * I`. -/
noncomputable def vertPoleAntideriv (a y₀ u : ℝ) : ℂ :=
  ((1 / 2 * Real.log (a ^ 2 + (u - y₀) ^ 2) : ℝ) : ℂ) +
    I * ((Real.arctan ((u - y₀) / a) : ℝ) : ℂ)

/-- **Horizontal 1D Antiderivative**:
For `b ≠ 0` (`b = y - p.im`) and `x₀ = p.re`, the complex antiderivative of
`σ ↦ 1 / ((σ - x₀) + b * I)` along the horizontal line `s = σ + y * I`. -/
noncomputable def horizPoleAntideriv (b x₀ u : ℝ) : ℂ :=
  ((1 / 2 * Real.log ((u - x₀) ^ 2 + b ^ 2) : ℝ) : ℂ) -
    I * ((Real.arctan ((u - x₀) / b) : ℝ) : ℂ)

/-- Exact 1D `HasDerivAt` for `vertPoleAntideriv a y₀` when `a ≠ 0`. -/
theorem hasDerivAt_vertPoleAntideriv {a y₀ t : ℝ} (ha : a ≠ 0) :
    HasDerivAt (vertPoleAntideriv a y₀)
      (I / ((a : ℂ) + ((t - y₀ : ℝ) : ℂ) * I)) t := by
  unfold vertPoleAntideriv
  have hd1 := (hasDerivAt_half_log_add_sq ha (y₀ := y₀) (t := t)).ofReal_comp
  have hd2 := ((hasDerivAt_arctan_sub_div ha (y₀ := y₀) (t := t)).ofReal_comp).const_mul I
  refine (hd1.add hd2).congr_deriv ?_
  have hpos : (a : ℂ) ^ 2 + ((t : ℂ) - y₀) ^ 2 ≠ 0 := by
    exact_mod_cast (add_sq_pos_of_ne_zero ha (x := t - y₀)).ne'
  have hden : (a : ℂ) + ((t - y₀ : ℝ) : ℂ) * I ≠ 0 :=
    complex_add_mul_I_ne_zero_of_left ha
  push_cast at hden ⊢
  rw [← mul_div_assoc, ← add_div, div_eq_div_iff hpos hden]
  linear_combination (a : ℂ) * ((t : ℂ) - y₀) * Complex.I_sq

/-- Exact 1D `HasDerivAt` for `horizPoleAntideriv b x₀` when `b ≠ 0`. -/
theorem hasDerivAt_horizPoleAntideriv {b x₀ σ : ℝ} (hb : b ≠ 0) :
    HasDerivAt (horizPoleAntideriv b x₀)
      (1 / (((σ - x₀ : ℝ) : ℂ) + (b : ℂ) * I)) σ := by
  have h_eq : horizPoleAntideriv b x₀ = fun u : ℝ ↦
      ((1 / 2 * Real.log (b ^ 2 + (u - x₀) ^ 2) : ℝ) : ℂ) -
        I * ((Real.arctan ((u - x₀) / b) : ℝ) : ℂ) := by
    ext u
    simp only [horizPoleAntideriv, add_comm ((u - x₀) ^ 2) (b ^ 2)]
  rw [h_eq]
  have hd1 := (hasDerivAt_half_log_add_sq hb (y₀ := x₀) (t := σ)).ofReal_comp
  have hd2 := ((hasDerivAt_arctan_sub_div hb (y₀ := x₀) (t := σ)).ofReal_comp).const_mul I
  refine (hd1.sub hd2).congr_deriv ?_
  have hpos : (b : ℂ) ^ 2 + ((σ : ℂ) - x₀) ^ 2 ≠ 0 := by
    exact_mod_cast (add_sq_pos_of_ne_zero hb (x := σ - x₀)).ne'
  have hden : ((σ - x₀ : ℝ) : ℂ) + (b : ℂ) * I ≠ 0 :=
    complex_add_mul_I_ne_zero_of_right hb
  push_cast at hden ⊢
  rw [← mul_div_assoc, ← sub_div, div_eq_div_iff hpos hden]
  linear_combination -(b : ℂ) ^ 2 * Complex.I_sq

/-- Decomposition of `(c : ℂ) + (t : ℂ) * I - p` into real and imaginary offsets. -/
theorem vertical_sub_eq (c t : ℝ) (p : ℂ) :
    (c : ℂ) + (t : ℂ) * I - p =
      ((c - p.re : ℝ) : ℂ) + ((t - p.im : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

/-- Decomposition of `(σ : ℂ) + (y : ℂ) * I - p` into real and imaginary offsets. -/
theorem horizontal_sub_eq (σ y : ℝ) (p : ℂ) :
    (σ : ℂ) + (y : ℂ) * I - p =
      ((σ - p.re : ℝ) : ℂ) + ((y - p.im : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp

/-- **Closed-Form 1D Vertical Integral of `I / (a + (t - y₀) * I)`**:
For `a ≠ 0` and any `y₀, t₁, t₂ : ℝ`,
$$\int_{t_1}^{t_2} \frac{i}{a + (t - y_0) i} \, dt
  = \Phi_{\text{vert}}(a, y_0, t_2) - \Phi_{\text{vert}}(a, y_0, t_1).$$ -/
theorem intervalIntegral_I_div_add_mul_I {a y₀ : ℝ} (ha : a ≠ 0) (t₁ t₂ : ℝ) :
    (∫ t : ℝ in t₁..t₂, I / ((a : ℂ) + ((t - y₀ : ℝ) : ℂ) * I)) =
      vertPoleAntideriv a y₀ t₂ - vertPoleAntideriv a y₀ t₁ := by
  have hderiv : ∀ t ∈ Set.uIcc t₁ t₂,
      HasDerivAt (vertPoleAntideriv a y₀)
        (I / ((a : ℂ) + ((t - y₀ : ℝ) : ℂ) * I)) t :=
    fun t _ ↦ hasDerivAt_vertPoleAntideriv ha
  have hcont : Continuous (fun t : ℝ ↦ I / ((a : ℂ) + ((t - y₀ : ℝ) : ℂ) * I)) := by
    refine continuous_const.div ?_ (fun t ↦ complex_add_mul_I_ne_zero_of_left ha)
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable t₁ t₂)

/-- **Closed-Form 1D Horizontal Integral of `1 / ((σ - x₀) + b * I)`**:
For `b ≠ 0` and any `x₀, c₁, c₂ : ℝ`,
$$\int_{c_1}^{c_2} \frac{1}{(\sigma - x_0) + b i} \, d\sigma
  = \Phi_{\text{horiz}}(b, x_0, c_2) - \Phi_{\text{horiz}}(b, x_0, c_1).$$ -/
theorem intervalIntegral_one_div_add_mul_I {b x₀ : ℝ} (hb : b ≠ 0) (c₁ c₂ : ℝ) :
    (∫ σ : ℝ in c₁..c₂, 1 / (((σ - x₀ : ℝ) : ℂ) + (b : ℂ) * I)) =
      horizPoleAntideriv b x₀ c₂ - horizPoleAntideriv b x₀ c₁ := by
  have hderiv : ∀ σ ∈ Set.uIcc c₁ c₂,
      HasDerivAt (horizPoleAntideriv b x₀)
        (1 / (((σ - x₀ : ℝ) : ℂ) + (b : ℂ) * I)) σ :=
    fun σ _ ↦ hasDerivAt_horizPoleAntideriv hb
  have hcont : Continuous (fun σ : ℝ ↦ 1 / (((σ - x₀ : ℝ) : ℂ) + (b : ℂ) * I)) := by
    refine continuous_const.div ?_ (fun σ ↦ complex_add_mul_I_ne_zero_of_right hb)
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable c₁ c₂)

/-- Vertical line integral of `1 / (c + t * I - p)` multiplied by `I` when `c ≠ p.re`. -/
theorem mul_I_vertical_integral_inv_sub_eq {c : ℝ} {p : ℂ} (hc : c ≠ p.re) (T : ℝ) :
    I * (∫ t : ℝ in (-T)..T, 1 / ((c : ℂ) + (t : ℂ) * I - p)) =
      vertPoleAntideriv (c - p.re) p.im T - vertPoleAntideriv (c - p.re) p.im (-T) := by
  rw [← intervalIntegral.integral_const_mul]
  have h_fn :
      (fun t : ℝ ↦ I * (1 / ((c : ℂ) + (t : ℂ) * I - p))) =
        fun t : ℝ ↦ I / (((c - p.re : ℝ) : ℂ) + ((t - p.im : ℝ) : ℂ) * I) := by
    ext t
    rw [vertical_sub_eq, mul_one_div]
  rw [h_fn]
  exact intervalIntegral_I_div_add_mul_I (sub_ne_zero.mpr hc) (-T) T

/-- Horizontal line integral of `1 / (σ + y * I - p)` when `y ≠ p.im`. -/
theorem horizontal_integral_inv_sub_eq {y : ℝ} {p : ℂ} (hy : y ≠ p.im) (c₁ c₂ : ℝ) :
    (∫ σ : ℝ in c₁..c₂, 1 / ((σ : ℂ) + (y : ℂ) * I - p)) =
      horizPoleAntideriv (y - p.im) p.re c₂ - horizPoleAntideriv (y - p.im) p.re c₁ := by
  have h_fn :
      (fun σ : ℝ ↦ 1 / ((σ : ℂ) + (y : ℂ) * I - p)) =
        fun σ : ℝ ↦ 1 / (((σ - p.re : ℝ) : ℂ) + ((y - p.im : ℝ) : ℂ) * I) := by
    ext σ
    rw [horizontal_sub_eq]
  rw [h_fn]
  exact intervalIntegral_one_div_add_mul_I (sub_ne_zero.mpr hy) c₁ c₂

/-!
## Section 2: The 4-Corner `log` + `arctan` Cancellation (`rectBoundaryIntegral = 2πi`)
-/

/-- Complementary arctangent identity: for `0 < x` and `0 < y`,
$$\arctan\left(\frac{y}{x}\right) + \arctan\left(\frac{x}{y}\right) = \frac{\pi}{2}.$$ -/
theorem arctan_div_add_arctan_div_eq_pi_div_two {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.arctan (y / x) + Real.arctan (x / y) = Real.pi / 2 := by
  have h_inv : x / y = (y / x)⁻¹ := (inv_div y x).symm
  rw [h_inv, Real.arctan_inv_of_pos (div_pos hy hx)]
  ring

/-- **The 4-Corner `log` + `arctan` Rectangle Integral Identity**:
For any point `p ∈ ℂ` strictly inside the rectangle `[c₁, c₂] × [-T, T]`
(`c₁ < p.re < c₂` and `-T < p.im < T`),
$$\operatorname{rectBoundaryIntegral}\left(s \mapsto \frac{1}{s - p}\right) c_1\, c_2\, T = 2\pi
i.$$ -/
theorem rectBoundaryIntegral_inv_sub_eq_two_pi_I {c₁ c₂ T : ℝ} {p : ℂ}
    (hre₁ : c₁ < p.re) (hre₂ : p.re < c₂) (him₁ : -T < p.im) (him₂ : p.im < T) :
    rectBoundaryIntegral (fun s ↦ 1 / (s - p)) c₁ c₂ T = 2 * π * I := by
  unfold rectBoundaryIntegral
  have h_bot_fn :
      (fun σ : ℝ ↦ 1 / ((σ : ℂ) - (T : ℂ) * I - p)) =
        fun σ : ℝ ↦ 1 / ((σ : ℂ) + ((-T : ℝ) : ℂ) * I - p) := by
    ext σ
    push_cast
    ring_nf
  rw [h_bot_fn,
    mul_I_vertical_integral_inv_sub_eq hre₂.ne' T,
    mul_I_vertical_integral_inv_sub_eq hre₁.ne T,
    horizontal_integral_inv_sub_eq him₂.ne' c₁ c₂,
    horizontal_integral_inv_sub_eq him₁.ne c₁ c₂]
  simp only [vertPoleAntideriv, horizPoleAntideriv]
  set A : ℝ := c₂ - p.re
  set B : ℝ := p.re - c₁
  set C : ℝ := T - p.im
  set D : ℝ := T + p.im
  have hA : 0 < A := sub_pos.mpr hre₂
  have hB : 0 < B := sub_pos.mpr hre₁
  have hC : 0 < C := sub_pos.mpr him₂
  have hD : 0 < D := by dsimp [D]; linarith
  have hc₁_sub : c₁ - p.re = -B := by dsimp [B]; ring
  have hnegT_sub : -T - p.im = -D := by dsimp [D]; ring
  rw [hc₁_sub, hnegT_sub]
  have h_sq_B : (-B) ^ 2 = B ^ 2 := neg_sq B
  have h_sq_D : (-D) ^ 2 = D ^ 2 := neg_sq D
  have h_div1 : (-D) / A = -(D / A) := neg_div A D
  have h_div2 : C / (-B) = -(C / B) := div_neg C
  have h_div3 : (-D) / (-B) = D / B := neg_div_neg_eq D B
  have h_div4 : (-B) / C = -(B / C) := neg_div C B
  have h_div5 : A / (-D) = -(A / D) := div_neg A
  have h_div6 : (-B) / (-D) = B / D := neg_div_neg_eq B D
  rw [h_sq_B, h_sq_D, h_div1, h_div2, h_div3, h_div4, h_div5, h_div6]
  simp only [Real.arctan_neg, Complex.ofReal_neg]
  have h_pair1 := arctan_div_add_arctan_div_eq_pi_div_two hA hC
  have h_pair2 := arctan_div_add_arctan_div_eq_pi_div_two hA hD
  have h_pair3 := arctan_div_add_arctan_div_eq_pi_div_two hB hC
  have h_pair4 := arctan_div_add_arctan_div_eq_pi_div_two hB hD
  have h_sum_arctan :
      ((Real.arctan (C / A) : ℂ) + (Real.arctan (A / C) : ℂ)) +
        ((Real.arctan (D / A) : ℂ) + (Real.arctan (A / D) : ℂ)) +
        ((Real.arctan (C / B) : ℂ) + (Real.arctan (B / C) : ℂ)) +
        ((Real.arctan (D / B) : ℂ) + (Real.arctan (B / D) : ℂ)) = 2 * π := by
    norm_cast
    linarith
  linear_combination I * h_sum_arctan

/-- Corollary for a general residue `r : ℂ` at an interior pole `p`:
$$\operatorname{rectBoundaryIntegral}\left(s \mapsto \frac{r}{s - p}\right) c_1\, c_2\, T = 2\pi i
r.$$ -/
theorem rectBoundaryIntegral_div_sub_eq_two_pi_I_mul {c₁ c₂ T : ℝ} {p : ℂ} (r : ℂ)
    (hre₁ : c₁ < p.re) (hre₂ : p.re < c₂) (him₁ : -T < p.im) (him₂ : p.im < T) :
    rectBoundaryIntegral (fun s ↦ r / (s - p)) c₁ c₂ T = 2 * π * I * r := by
  have h_eq : (fun s : ℂ ↦ r / (s - p)) = fun s : ℂ ↦ r * (1 / (s - p)) := by
    ext s; ring
  rw [h_eq, rectBoundaryIntegral_const_mul,
    rectBoundaryIntegral_inv_sub_eq_two_pi_I hre₁ hre₂ him₁ him₂]
  ring

/-!
## Section 3: Rectangle Vanishing for Holomorphic Functions (`rectBoundaryIntegral = 0`)
-/

/-- The closed rectangle `[c₁, c₂] ×ℂ [-T, T]` in `ℂ`. -/
def closedRect (c₁ c₂ T : ℝ) : Set ℂ :=
  Set.Icc c₁ c₂ ×ℂ Set.Icc (-T) T

/-- The open rectangle `(c₁, c₂) ×ℂ (-T, T)` in `ℂ`. -/
def openRect (c₁ c₂ T : ℝ) : Set ℂ :=
  Set.Ioo c₁ c₂ ×ℂ Set.Ioo (-T) T

@[simp]
theorem mem_closedRect {c₁ c₂ T : ℝ} {s : ℂ} :
    s ∈ closedRect c₁ c₂ T ↔ (c₁ ≤ s.re ∧ s.re ≤ c₂) ∧ (-T ≤ s.im ∧ s.im ≤ T) :=
  Iff.rfl

@[simp]
theorem mem_openRect {c₁ c₂ T : ℝ} {s : ℂ} :
    s ∈ openRect c₁ c₂ T ↔ (c₁ < s.re ∧ s.re < c₂) ∧ (-T < s.im ∧ s.im < T) :=
  Iff.rfl

/-- Connection between `rectBoundaryIntegral F c₁ c₂ T` and the expression in
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` with corners
`z = c₁ - T * I` and `w = c₂ + T * I`. -/
theorem rectBoundaryIntegral_eq_cauchy_boundary (F : ℂ → ℂ) (c₁ c₂ T : ℝ) :
    rectBoundaryIntegral F c₁ c₂ T =
      (∫ x : ℝ in ((c₁ : ℂ) - (T : ℂ) * I).re..((c₂ : ℂ) + (T : ℂ) * I).re,
          F (x + ((c₁ : ℂ) - (T : ℂ) * I).im * I)) -
        (∫ x : ℝ in ((c₁ : ℂ) - (T : ℂ) * I).re..((c₂ : ℂ) + (T : ℂ) * I).re,
          F (x + ((c₂ : ℂ) + (T : ℂ) * I).im * I)) +
        I • (∫ y : ℝ in ((c₁ : ℂ) - (T : ℂ) * I).im..((c₂ : ℂ) + (T : ℂ) * I).im,
          F (((c₂ : ℂ) + (T : ℂ) * I).re + y * I)) -
        I • (∫ y : ℝ in ((c₁ : ℂ) - (T : ℂ) * I).im..((c₂ : ℂ) + (T : ℂ) * I).im,
          F (((c₁ : ℂ) - (T : ℂ) * I).re + y * I)) := by
  unfold rectBoundaryIntegral
  simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    sub_zero, add_re, add_zero, sub_im, mul_im, zero_add, zero_sub, ofReal_neg, neg_mul,
    add_im, smul_eq_mul]
  have h_bot :
      (fun x : ℝ ↦ F ((x : ℂ) + -((T : ℂ) * I))) =
        fun x : ℝ ↦ F ((x : ℂ) - (T : ℂ) * I) := by
    ext x; ring_nf
  rw [h_bot]
  ring

/-- **Rectangle Vanishing off a Countable Set**:
If `F : ℂ → ℂ` is continuous on `closedRect c₁ c₂ T` (`c₁ ≤ c₂`, `0 ≤ T`) and complex-differentiable
on `openRect c₁ c₂ T \ s` for a countable set `s : Set ℂ`, then
$$\operatorname{rectBoundaryIntegral} F\, c_1\, c_2\, T = 0.$$ -/
theorem rectBoundaryIntegral_eq_zero_of_differentiable_on_off_countable {c₁ c₂ T : ℝ}
    (hc : c₁ ≤ c₂) (hT : 0 ≤ T) {F : ℂ → ℂ} {s : Set ℂ} (hs : s.Countable)
    (hcont : ContinuousOn F (closedRect c₁ c₂ T))
    (hdiff : ∀ z ∈ openRect c₁ c₂ T \ s, DifferentiableAt ℂ F z) :
    rectBoundaryIntegral F c₁ c₂ T = 0 := by
  rw [rectBoundaryIntegral_eq_cauchy_boundary]
  set z : ℂ := (c₁ : ℂ) - (T : ℂ) * I
  set w : ℂ := (c₂ : ℂ) + (T : ℂ) * I
  have hz_re : z.re = c₁ := by simp [z]
  have hw_re : w.re = c₂ := by simp [w]
  have hz_im : z.im = -T := by simp [z]
  have hw_im : w.im = T := by simp [w]
  have h_negT_le : -T ≤ T := by linarith
  have h_closed : [[z.re, w.re]] ×ℂ [[z.im, w.im]] = closedRect c₁ c₂ T := by
    rw [hz_re, hw_re, hz_im, hw_im, uIcc_of_le hc, uIcc_of_le h_negT_le, closedRect]
  have h_open :
      Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) =
        openRect c₁ c₂ T := by
    rw [hz_re, hw_re, hz_im, hw_im, min_eq_left hc, max_eq_right hc,
      min_eq_left h_negT_le, max_eq_right h_negT_le, openRect]
  exact Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable F z w s hs
    (by rwa [h_closed]) (by rwa [h_open])

/-- **Rectangle Vanishing for Holomorphic Functions on an Open Set Containing the Rectangle**:
If `F : ℂ → ℂ` is complex-differentiable on a set `U` containing `closedRect c₁ c₂ T`
(`c₁ ≤ c₂`, `0 ≤ T`), then
$$\operatorname{rectBoundaryIntegral} F\, c_1\, c_2\, T = 0.$$ -/
theorem rectBoundaryIntegral_eq_zero_of_differentiableOn {c₁ c₂ T : ℝ}
    (hc : c₁ ≤ c₂) (hT : 0 ≤ T) {F : ℂ → ℂ} {U : Set ℂ}
    (hU : closedRect c₁ c₂ T ⊆ U) (hF : DifferentiableOn ℂ F U) :
    rectBoundaryIntegral F c₁ c₂ T = 0 := by
  have hF_rect : DifferentiableOn ℂ F (closedRect c₁ c₂ T) := hF.mono hU
  refine rectBoundaryIntegral_eq_zero_of_differentiable_on_off_countable hc hT countable_empty
    hF_rect.continuousOn fun z hz ↦ ?_
  have h_sub : openRect c₁ c₂ T ⊆ closedRect c₁ c₂ T :=
    inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)
  exact (hF_rect.mono h_sub).differentiableAt
    ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hz.1)

/-!
## Section 4: General Rectangle Residue Theorem (`rectBoundaryIntegral = 2πi ∑ r(p)`)
-/

/-- No point on the right or left vertical boundary lines `c + t * I` (`c = c₁` or `c = c₂`)
lies in `openRect c₁ c₂ T`. -/
theorem vertical_not_mem_openRect_left (c₁ c₂ T t : ℝ) :
    ((c₁ : ℂ) + (t : ℂ) * I) ∉ openRect c₁ c₂ T := by
  rw [mem_openRect]
  simp

theorem vertical_not_mem_openRect_right (c₁ c₂ T t : ℝ) :
    ((c₂ : ℂ) + (t : ℂ) * I) ∉ openRect c₁ c₂ T := by
  rw [mem_openRect]
  simp

/-- No point on the top or bottom horizontal boundary lines `σ ± T * I` lies in
`openRect c₁ c₂ T`. -/
theorem horizontal_not_mem_openRect_top (c₁ c₂ T σ : ℝ) :
    ((σ : ℂ) + (T : ℂ) * I) ∉ openRect c₁ c₂ T := by
  rw [mem_openRect]
  simp

theorem horizontal_not_mem_openRect_bot (c₁ c₂ T σ : ℝ) :
    ((σ : ℂ) - (T : ℂ) * I) ∉ openRect c₁ c₂ T := by
  rw [mem_openRect]
  simp

/-- Every point on the four boundary segments of `[c₁, c₂] × [-T, T]` (`c₁ ≤ c₂`, `0 ≤ T`)
belongs to `closedRect c₁ c₂ T`. -/
theorem vertical_mem_closedRect_left {c₁ c₂ T t : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    (ht : t ∈ Set.uIcc (-T) T) :
    ((c₁ : ℂ) + (t : ℂ) * I) ∈ closedRect c₁ c₂ T := by
  rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at ht
  rw [mem_closedRect]
  simp [hc, ht.1, ht.2]

theorem vertical_mem_closedRect_right {c₁ c₂ T t : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    (ht : t ∈ Set.uIcc (-T) T) :
    ((c₂ : ℂ) + (t : ℂ) * I) ∈ closedRect c₁ c₂ T := by
  rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at ht
  rw [mem_closedRect]
  simp [hc, ht.1, ht.2]

theorem horizontal_mem_closedRect_top {c₁ c₂ T σ : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    (hσ : σ ∈ Set.uIcc c₁ c₂) :
    ((σ : ℂ) + (T : ℂ) * I) ∈ closedRect c₁ c₂ T := by
  rw [Set.uIcc_of_le hc] at hσ
  have h_negT : -T ≤ T := by linarith
  rw [mem_closedRect]
  simp [hσ.1, hσ.2, h_negT]

theorem horizontal_mem_closedRect_bot {c₁ c₂ T σ : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    (hσ : σ ∈ Set.uIcc c₁ c₂) :
    ((σ : ℂ) - (T : ℂ) * I) ∈ closedRect c₁ c₂ T := by
  rw [Set.uIcc_of_le hc] at hσ
  have h_negT : -T ≤ T := by linarith
  rw [mem_closedRect]
  simp [hσ.1, hσ.2, h_negT]

/-- If `M₁` and `M₂` agree on `closedRect c₁ c₂ T \ P` where `P ⊆ openRect c₁ c₂ T` (`c₁ ≤ c₂`,
`0 ≤ T`), then `rectBoundaryIntegral M₁ c₁ c₂ T = rectBoundaryIntegral M₂ c₁ c₂ T`. -/
theorem rectBoundaryIntegral_congr_of_eqOn_sdiff {c₁ c₂ T : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {M₁ M₂ : ℂ → ℂ} {P : Set ℂ} (hP : P ⊆ openRect c₁ c₂ T)
    (heq : Set.EqOn M₁ M₂ (closedRect c₁ c₂ T \ P)) :
    rectBoundaryIntegral M₁ c₁ c₂ T = rectBoundaryIntegral M₂ c₁ c₂ T := by
  unfold rectBoundaryIntegral
  have h1 :
      (∫ t in (-T)..T, M₁ ((c₂ : ℂ) + (t : ℂ) * I)) =
        ∫ t in (-T)..T, M₂ ((c₂ : ℂ) + (t : ℂ) * I) :=
    intervalIntegral.integral_congr fun t ht ↦
      heq ⟨vertical_mem_closedRect_right hc hT ht,
        fun hp ↦ vertical_not_mem_openRect_right c₁ c₂ T t (hP hp)⟩
  have h2 :
      (∫ t in (-T)..T, M₁ ((c₁ : ℂ) + (t : ℂ) * I)) =
        ∫ t in (-T)..T, M₂ ((c₁ : ℂ) + (t : ℂ) * I) :=
    intervalIntegral.integral_congr fun t ht ↦
      heq ⟨vertical_mem_closedRect_left hc hT ht,
        fun hp ↦ vertical_not_mem_openRect_left c₁ c₂ T t (hP hp)⟩
  have h3 :
      (∫ σ in c₁..c₂, M₁ ((σ : ℂ) + (T : ℂ) * I)) =
        ∫ σ in c₁..c₂, M₂ ((σ : ℂ) + (T : ℂ) * I) :=
    intervalIntegral.integral_congr fun σ hσ ↦
      heq ⟨horizontal_mem_closedRect_top hc hT hσ,
        fun hp ↦ horizontal_not_mem_openRect_top c₁ c₂ T σ (hP hp)⟩
  have h4 :
      (∫ σ in c₁..c₂, M₁ ((σ : ℂ) - (T : ℂ) * I)) =
        ∫ σ in c₁..c₂, M₂ ((σ : ℂ) - (T : ℂ) * I) :=
    intervalIntegral.integral_congr fun σ hσ ↦
      heq ⟨horizontal_mem_closedRect_bot hc hT hσ,
        fun hp ↦ horizontal_not_mem_openRect_bot c₁ c₂ T σ (hP hp)⟩
  rw [h1, h2, h3, h4]

/-- For any pole `p ∈ openRect c₁ c₂ T` and residue `r : ℂ`, `s ↦ r / (s - p)` is continuous on
each of the four boundary lines of `[c₁, c₂] × [-T, T]`, hence `IntervalIntegrable`. -/
theorem intervalIntegrable_pole_right {c₁ c₂ T : ℝ} {p : ℂ} (r : ℂ) (hp : p ∈ openRect c₁ c₂ T) :
    IntervalIntegrable (fun t : ℝ ↦ r / ((c₂ : ℂ) + (t : ℂ) * I - p)) volume (-T) T := by
  refine (continuous_const.div ?_ fun t ↦ ?_).intervalIntegrable (-T) T
  · fun_prop
  · rw [vertical_sub_eq]
    exact complex_add_mul_I_ne_zero_of_left (sub_ne_zero.mpr hp.1.2.ne')

theorem intervalIntegrable_pole_left {c₁ c₂ T : ℝ} {p : ℂ} (r : ℂ) (hp : p ∈ openRect c₁ c₂ T) :
    IntervalIntegrable (fun t : ℝ ↦ r / ((c₁ : ℂ) + (t : ℂ) * I - p)) volume (-T) T := by
  refine (continuous_const.div ?_ fun t ↦ ?_).intervalIntegrable (-T) T
  · fun_prop
  · rw [vertical_sub_eq]
    exact complex_add_mul_I_ne_zero_of_left (sub_ne_zero.mpr hp.1.1.ne)

theorem intervalIntegrable_pole_top {c₁ c₂ T : ℝ} {p : ℂ} (r : ℂ) (hp : p ∈ openRect c₁ c₂ T) :
    IntervalIntegrable (fun σ : ℝ ↦ r / ((σ : ℂ) + (T : ℂ) * I - p)) volume c₁ c₂ := by
  refine (continuous_const.div ?_ fun σ ↦ ?_).intervalIntegrable c₁ c₂
  · fun_prop
  · rw [horizontal_sub_eq]
    exact complex_add_mul_I_ne_zero_of_right (sub_ne_zero.mpr hp.2.2.ne')

theorem intervalIntegrable_pole_bot {c₁ c₂ T : ℝ} {p : ℂ} (r : ℂ) (hp : p ∈ openRect c₁ c₂ T) :
    IntervalIntegrable (fun σ : ℝ ↦ r / ((σ : ℂ) - (T : ℂ) * I - p)) volume c₁ c₂ := by
  refine (continuous_const.div ?_ fun σ ↦ ?_).intervalIntegrable c₁ c₂
  · fun_prop
  · have h_eq : (σ : ℂ) - (T : ℂ) * I - p = (σ : ℂ) + ((-T : ℝ) : ℂ) * I - p := by
      push_cast; ring
    rw [h_eq, horizontal_sub_eq]
    exact complex_add_mul_I_ne_zero_of_right (sub_ne_zero.mpr hp.2.1.ne)

/-- If `F : ℂ → ℂ` is continuous on `closedRect c₁ c₂ T` (`c₁ ≤ c₂`, `0 ≤ T`), then `F` is
`IntervalIntegrable` along all four boundary segments of `[c₁, c₂] × [-T, T]`. -/
theorem intervalIntegrable_right_of_continuousOn {c₁ c₂ T : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {F : ℂ → ℂ} (hcont : ContinuousOn F (closedRect c₁ c₂ T)) :
    IntervalIntegrable (fun t : ℝ ↦ F ((c₂ : ℂ) + (t : ℂ) * I)) volume (-T) T := by
  refine (hcont.comp (by fun_prop) ?_).intervalIntegrable
  intro t ht
  exact vertical_mem_closedRect_right hc hT ht

theorem intervalIntegrable_left_of_continuousOn {c₁ c₂ T : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {F : ℂ → ℂ} (hcont : ContinuousOn F (closedRect c₁ c₂ T)) :
    IntervalIntegrable (fun t : ℝ ↦ F ((c₁ : ℂ) + (t : ℂ) * I)) volume (-T) T := by
  refine (hcont.comp (by fun_prop) ?_).intervalIntegrable
  intro t ht
  exact vertical_mem_closedRect_left hc hT ht

theorem intervalIntegrable_top_of_continuousOn {c₁ c₂ T : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {F : ℂ → ℂ} (hcont : ContinuousOn F (closedRect c₁ c₂ T)) :
    IntervalIntegrable (fun σ : ℝ ↦ F ((σ : ℂ) + (T : ℂ) * I)) volume c₁ c₂ := by
  refine (hcont.comp (by fun_prop) ?_).intervalIntegrable
  intro σ hσ
  exact horizontal_mem_closedRect_top hc hT hσ

theorem intervalIntegrable_bot_of_continuousOn {c₁ c₂ T : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {F : ℂ → ℂ} (hcont : ContinuousOn F (closedRect c₁ c₂ T)) :
    IntervalIntegrable (fun σ : ℝ ↦ F ((σ : ℂ) - (T : ℂ) * I)) volume c₁ c₂ := by
  refine (hcont.comp (by fun_prop) ?_).intervalIntegrable
  intro σ hσ
  exact horizontal_mem_closedRect_bot hc hT hσ

/-- Additivity of `rectBoundaryIntegral` for `F` continuous on `closedRect c₁ c₂ T` plus a finite
sum of interior poles `∑ p ∈ P, r p / (s - p)`. -/
theorem rectBoundaryIntegral_add_sum_poles {c₁ c₂ T : ℝ} (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {F : ℂ → ℂ} (hcont : ContinuousOn F (closedRect c₁ c₂ T))
    (P : Finset ℂ) (r : ℂ → ℂ) (hP : ∀ p ∈ P, p ∈ openRect c₁ c₂ T) :
    rectBoundaryIntegral (fun s ↦ F s + ∑ p ∈ P, r p / (s - p)) c₁ c₂ T =
      rectBoundaryIntegral F c₁ c₂ T +
        ∑ p ∈ P, rectBoundaryIntegral (fun s ↦ r p / (s - p)) c₁ c₂ T := by
  unfold rectBoundaryIntegral
  have h_sum_right :
      IntervalIntegrable (fun t : ℝ ↦ ∑ p ∈ P,
        r p / ((c₂ : ℂ) + (t : ℂ) * I - p)) volume (-T) T := by
    rw [← Finset.sum_fn]
    exact IntervalIntegrable.sum P fun p hp ↦ intervalIntegrable_pole_right (r p) (hP p hp)
  have h_sum_left :
      IntervalIntegrable (fun t : ℝ ↦ ∑ p ∈ P,
        r p / ((c₁ : ℂ) + (t : ℂ) * I - p)) volume (-T) T := by
    rw [← Finset.sum_fn]
    exact IntervalIntegrable.sum P fun p hp ↦ intervalIntegrable_pole_left (r p) (hP p hp)
  have h_sum_top :
      IntervalIntegrable (fun σ : ℝ ↦ ∑ p ∈ P, r p / ((σ : ℂ) + (T : ℂ) * I - p)) volume c₁ c₂ := by
    rw [← Finset.sum_fn]
    exact IntervalIntegrable.sum P fun p hp ↦ intervalIntegrable_pole_top (r p) (hP p hp)
  have h_sum_bot :
      IntervalIntegrable (fun σ : ℝ ↦ ∑ p ∈ P, r p / ((σ : ℂ) - (T : ℂ) * I - p)) volume c₁ c₂ := by
    rw [← Finset.sum_fn]
    exact IntervalIntegrable.sum P fun p hp ↦ intervalIntegrable_pole_bot (r p) (hP p hp)
  rw [intervalIntegral.integral_add (intervalIntegrable_right_of_continuousOn hc hT hcont)
    h_sum_right,
    intervalIntegral.integral_add (intervalIntegrable_left_of_continuousOn hc hT hcont) h_sum_left,
    intervalIntegral.integral_add (intervalIntegrable_top_of_continuousOn hc hT hcont) h_sum_top,
    intervalIntegral.integral_add (intervalIntegrable_bot_of_continuousOn hc hT hcont) h_sum_bot,
    intervalIntegral.integral_finsetSum fun p hp ↦ intervalIntegrable_pole_right (r p) (hP p hp),
    intervalIntegral.integral_finsetSum fun p hp ↦ intervalIntegrable_pole_left (r p) (hP p hp),
    intervalIntegral.integral_finsetSum fun p hp ↦ intervalIntegrable_pole_top (r p) (hP p hp),
    intervalIntegral.integral_finsetSum fun p hp ↦ intervalIntegrable_pole_bot (r p) (hP p hp)]
  simp only [mul_add, mul_sum, sum_add_distrib, sum_sub_distrib]
  ring

/-- **General Rectangle Residue Theorem (Holomorphic Remainder Form)**:
Let `P : Finset ℂ` be a finite set of poles strictly inside the rectangle `[c₁, c₂] × [-T, T]`
(`c₁ ≤ c₂`, `0 ≤ T`, `∀ p ∈ P, p ∈ openRect c₁ c₂ T`).
If `F : ℂ → ℂ` is continuous on `closedRect c₁ c₂ T`, complex-differentiable on
`openRect c₁ c₂ T \ s` for a countable set `s : Set ℂ`, and
`∀ z ∈ closedRect c₁ c₂ T \ P, M z = F z + ∑ p ∈ P, r p / (z - p)`, then
$$\operatorname{rectBoundaryIntegral} M\, c_1\, c_2\, T = 2\pi i \sum_{p \in P} r(p).$$ -/
theorem rectBoundaryIntegral_eq_sum_residues_off_countable {c₁ c₂ T : ℝ}
    (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {M F : ℂ → ℂ} {P : Finset ℂ} {r : ℂ → ℂ} {s : Set ℂ} (hs : s.Countable)
    (hP : ∀ p ∈ P, p ∈ openRect c₁ c₂ T)
    (hcont : ContinuousOn F (closedRect c₁ c₂ T))
    (hdiff : ∀ z ∈ openRect c₁ c₂ T \ s, DifferentiableAt ℂ F z)
    (hM : ∀ z ∈ closedRect c₁ c₂ T \ (P : Set ℂ), M z = F z + ∑ p ∈ P, r p / (z - p)) :
    rectBoundaryIntegral M c₁ c₂ T = 2 * π * I * ∑ p ∈ P, r p := by
  have hP_sub : (P : Set ℂ) ⊆ openRect c₁ c₂ T := fun p hp ↦ hP p (mem_coe.mp hp)
  have h_congr :
      rectBoundaryIntegral M c₁ c₂ T =
        rectBoundaryIntegral (fun z ↦ F z + ∑ p ∈ P, r p / (z - p)) c₁ c₂ T :=
    rectBoundaryIntegral_congr_of_eqOn_sdiff hc hT hP_sub hM
  rw [h_congr, rectBoundaryIntegral_add_sum_poles hc hT hcont P r hP,
    rectBoundaryIntegral_eq_zero_of_differentiable_on_off_countable hc hT hs hcont hdiff,
    zero_add, mul_sum]
  refine sum_congr rfl fun p hp ↦ ?_
  obtain ⟨⟨hre₁, hre₂⟩, ⟨him₁, him₂⟩⟩ := hP p hp
  exact rectBoundaryIntegral_div_sub_eq_two_pi_I_mul (r p) hre₁ hre₂ him₁ him₂

/-- **General Rectangle Residue Theorem (Open Neighborhood Form)**:
Let `P : Finset ℂ` be a finite set of poles strictly inside `[c₁, c₂] × [-T, T]`
(`c₁ ≤ c₂`, `0 ≤ T`, `∀ p ∈ P, (c₁ < p.re ∧ p.re < c₂) ∧ (-T < p.im ∧ p.im < T)`).
If `F : ℂ → ℂ` is complex-differentiable on a set `U` containing `closedRect c₁ c₂ T` and
`∀ z ∈ closedRect c₁ c₂ T \ P, M z = F z + ∑ p ∈ P, r p / (z - p)`, then
$$\operatorname{rectBoundaryIntegral} M\, c_1\, c_2\, T = 2\pi i \sum_{p \in P} r(p).$$ -/
theorem rectBoundaryIntegral_eq_sum_residues {c₁ c₂ T : ℝ}
    (hc : c₁ ≤ c₂) (hT : 0 ≤ T)
    {M F : ℂ → ℂ} {P : Finset ℂ} {r : ℂ → ℂ} {U : Set ℂ}
    (hP : ∀ p ∈ P, (c₁ < p.re ∧ p.re < c₂) ∧ (-T < p.im ∧ p.im < T))
    (hU : closedRect c₁ c₂ T ⊆ U)
    (hF : DifferentiableOn ℂ F U)
    (hM : ∀ z ∈ closedRect c₁ c₂ T \ (P : Set ℂ), M z = F z + ∑ p ∈ P, r p / (z - p)) :
    rectBoundaryIntegral M c₁ c₂ T = 2 * π * I * ∑ p ∈ P, r p := by
  have hF_rect : DifferentiableOn ℂ F (closedRect c₁ c₂ T) := hF.mono hU
  have h_sub : openRect c₁ c₂ T ⊆ closedRect c₁ c₂ T :=
    inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)
  refine rectBoundaryIntegral_eq_sum_residues_off_countable hc hT countable_empty hP
    hF_rect.continuousOn (fun z hz ↦ ?_) hM
  exact (hF_rect.mono h_sub).differentiableAt
    ((isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hz.1)

/-!
## Section 3C: Contour Shift Decomposition & Triangle Inequality Error Reductions
-/

theorem inv_two_pi_I_mul_I_mul (z : ℂ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * (I * z) = (2 * (Real.pi : ℂ))⁻¹ * z := by
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  rw [mul_inv, mul_assoc, inv_mul_cancel_left₀ hI]

theorem inv_two_pi_I_mul_two_pi_I_mul (z : ℂ) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * (2 * (Real.pi : ℂ) * I * z) = z := by
  have hne : 2 * (Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  exact inv_mul_cancel_left₀ hne z

theorem right_vertical_integral_eq_rectBoundaryIntegral_add (f : ℂ → ℂ) (c₁ c₂ U : ℝ) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (c₂ + t * I)) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * rectBoundaryIntegral f c₁ c₂ U +
        (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (c₁ + t * I)) +
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in c₁..c₂, f (σ + U * I)) -
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in c₁..c₂, f (σ - U * I)) := by
  have hrect : I * (∫ t in (-U)..U, f (c₂ + t * I)) =
      rectBoundaryIntegral f c₁ c₂ U +
        I * (∫ t in (-U)..U, f (c₁ + t * I)) +
        (∫ σ in c₁..c₂, f (σ + U * I)) -
        (∫ σ in c₁..c₂, f (σ - U * I)) := by
    unfold rectBoundaryIntegral
    ring
  have hmul := congrArg ((2 * (Real.pi : ℂ) * I)⁻¹ * ·) hrect
  rw [inv_two_pi_I_mul_I_mul] at hmul
  rw [hmul]
  simp only [mul_add, mul_sub, inv_two_pi_I_mul_I_mul]

theorem right_vertical_integral_two_eq_rectBoundaryIntegral_add (f : ℂ → ℂ) (a U : ℝ) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (2 + (t : ℂ) * I)) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * rectBoundaryIntegral f a 2 U +
        (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (a + (t : ℂ) * I)) +
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2, f (σ + (U : ℂ) * I)) -
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2, f (σ - (U : ℂ) * I)) := by
  simpa using right_vertical_integral_eq_rectBoundaryIntegral_add f a 2 U

theorem norm_inv_two_pi_I_mul (z : ℂ) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ * z‖ = (2 * Real.pi)⁻¹ * ‖z‖ := by
  have h2pi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [← ofReal_ofNat, ← ofReal_mul, Complex.norm_real, Real.norm_of_nonneg Real.two_pi_pos.le]
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_I, mul_one, h2pi]

theorem norm_inv_two_pi_mul (z : ℂ) :
    ‖(2 * (Real.pi : ℂ))⁻¹ * z‖ = (2 * Real.pi)⁻¹ * ‖z‖ := by
  have h2pi : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [← ofReal_ofNat, ← ofReal_mul, Complex.norm_real, Real.norm_of_nonneg Real.two_pi_pos.le]
  rw [norm_mul, norm_inv, h2pi]

theorem norm_contour_shift_remainder_le (f : ℂ → ℂ) (a c₂ U : ℝ) :
    ‖(2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (a + t * I)) +
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ + U * I)) -
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ - U * I))‖ ≤
      (2 * Real.pi)⁻¹ * ‖∫ t in (-U)..U, f (a + t * I)‖ +
        (2 * Real.pi)⁻¹ * ‖∫ σ in a..c₂, f (σ + U * I)‖ +
        (2 * Real.pi)⁻¹ * ‖∫ σ in a..c₂, f (σ - U * I)‖ := by
  calc
    ‖(2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (a + t * I)) +
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ + U * I)) -
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ - U * I))‖
      ≤ ‖(2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (a + t * I)) +
          (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ + U * I))‖ +
          ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ - U * I))‖ := norm_sub_le _ _
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, f (a + t * I))‖ +
          ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ + U * I))‖ +
          ‖(2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..c₂, f (σ - U * I))‖ := by
        gcongr
        exact norm_add_le _ _
    _ = (2 * Real.pi)⁻¹ * ‖∫ t in (-U)..U, f (a + t * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ σ in a..c₂, f (σ + U * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ σ in a..c₂, f (σ - U * I)‖ := by
        rw [norm_inv_two_pi_mul, norm_inv_two_pi_I_mul, norm_inv_two_pi_I_mul]

/-- `rectBoundaryIntegral` of `regularizedSmoothedPerron x U` vanishes on `[a, b] × [-U, U]`
for `-1 / 2 < a ≤ b` and `0 ≤ U`. -/
theorem rectBoundaryIntegral_regularizedSmoothedPerron_eq_zero
    {x U a b : ℝ} (hx : 0 < x) (hU : 0 ≤ U) (ha : -1 / 2 < a) (hab : a ≤ b) :
    rectBoundaryIntegral (regularizedSmoothedPerron x U) a b U = 0 := by
  have h := integral_boundary_rect_regularizedSmoothedPerron_eq_zero hx hU ha hab
  unfold rectBoundaryIntegral
  have hbot : (fun σ : ℝ ↦ regularizedSmoothedPerron x U ((σ : ℂ) - (U : ℂ) * I)) =
      fun σ : ℝ ↦ regularizedSmoothedPerron x U ((σ : ℂ) + ((-U : ℝ) : ℂ) * I) := by
    ext σ; push_cast; ring_nf
  rw [hbot]
  linear_combination h

/-- The sum of all principal parts of `smoothedPerronIntegrand x` in `{s | -1 / 2 < s.re ∧ |s.im| ≤
U}`. -/
noncomputable def perronPrincipalPartSum (x U : ℝ) (s : ℂ) : ℂ :=
  ∑ p ∈ perronPolesUpTo U, perronResidue x p / (s - p)

theorem perronPrincipalPartSum_eq (x U : ℝ) (s : ℂ) :
    perronPrincipalPartSum x U s =
      resOne x / (s - 1) + resZero x / s +
        ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ / (s - ρ) := by
  unfold perronPrincipalPartSum perronPolesUpTo
  have h1_notMem : (1 : ℂ) ∉ insert (0 : ℂ) (nontrivialZetaZerosUpTo U) := by
    rw [Finset.mem_insert, not_or]
    exact ⟨one_ne_zero, one_notMem_nontrivialZetaZerosUpTo U⟩
  have h0_notMem : (0 : ℂ) ∉ nontrivialZetaZerosUpTo U :=
    zero_notMem_nontrivialZetaZerosUpTo U
  rw [Finset.sum_insert h1_notMem, Finset.sum_insert h0_notMem,
    perronResidue_one, perronResidue_zero, sub_zero]
  have hsum : ∑ ρ ∈ nontrivialZetaZerosUpTo U, perronResidue x ρ / (s - ρ) =
      ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ / (s - ρ) := by
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    rw [perronResidue_of_mem_nontrivialZetaZerosUpTo x hρ]
  rw [hsum]
  ring

theorem smoothedPerronIntegrand_eq_regularized_add_principalParts (x U : ℝ) {s : ℂ}
    (hs : s ∉ perronPolesUpTo U) :
    smoothedPerronIntegrand x s =
      regularizedSmoothedPerron x U s + perronPrincipalPartSum x U s := by
  rw [regularizedSmoothedPerron_eq_of_notMem x U hs, perronPrincipalPartSum_eq]
  ring

theorem continuousOn_regularizedSmoothedPerron_closedRect
    {x U a b : ℝ} (hx : 0 < x) (ha : -1 / 2 < a) :
    ContinuousOn (regularizedSmoothedPerron x U) (closedRect a b U) := by
  intro s hs
  rw [mem_closedRect] at hs
  exact (differentiableAt_regularizedSmoothedPerron hx (by linarith [hs.1.1])
    (abs_le.mpr hs.2)).continuousAt.continuousWithinAt

/-- **Rectangle Boundary Integral Decomposition into Principal Parts**:
If `-1 / 2 < a ≤ b`, `0 ≤ U`, and every pole `p ∈ perronPolesUpTo U` lies strictly inside
`openRect a b U`, then `rectBoundaryIntegral (smoothedPerronIntegrand x) a b U` equals
`rectBoundaryIntegral (perronPrincipalPartSum x U) a b U`. -/
theorem rectBoundaryIntegral_smoothedPerronIntegrand_eq_principalParts
    {x U a b : ℝ} (hx : 0 < x) (hU : 0 ≤ U) (ha : -1 / 2 < a) (hab : a ≤ b)
    (hP : ∀ p ∈ perronPolesUpTo U, p ∈ openRect a b U) :
    rectBoundaryIntegral (smoothedPerronIntegrand x) a b U =
      rectBoundaryIntegral (perronPrincipalPartSum x U) a b U := by
  have hP_sub : ((perronPolesUpTo U : Finset ℂ) : Set ℂ) ⊆ openRect a b U :=
    fun p hp ↦ hP p (mem_coe.mp hp)
  have hcongr : rectBoundaryIntegral (smoothedPerronIntegrand x) a b U =
      rectBoundaryIntegral
        (fun s ↦ regularizedSmoothedPerron x U s + perronPrincipalPartSum x U s) a b U := by
    refine rectBoundaryIntegral_congr_of_eqOn_sdiff hab hU hP_sub ?_
    intro s hs
    exact smoothedPerronIntegrand_eq_regularized_add_principalParts x U hs.2
  rw [hcongr]
  unfold perronPrincipalPartSum
  have hadd := rectBoundaryIntegral_add_sum_poles hab hU
    (continuousOn_regularizedSmoothedPerron_closedRect hx ha)
    (perronPolesUpTo U) (perronResidue x) hP
  have hzero : rectBoundaryIntegral (fun s ↦ (0 : ℂ) + ∑ p ∈ perronPolesUpTo U,
    perronResidue x p / (s - p)) a b U =
      rectBoundaryIntegral (0 : ℂ → ℂ) a b U +
        ∑ p ∈ perronPolesUpTo U, rectBoundaryIntegral (fun s ↦ perronResidue x p / (s - p)) a b U :=
    rectBoundaryIntegral_add_sum_poles hab hU continuousOn_const
      (perronPolesUpTo U) (perronResidue x) hP
  have h0_rect : rectBoundaryIntegral (0 : ℂ → ℂ) a b U = 0 := by
    unfold rectBoundaryIntegral
    simp
  simp only [zero_add, h0_rect] at hzero
  rw [hadd, rectBoundaryIntegral_regularizedSmoothedPerron_eq_zero hx hU ha hab, zero_add, ← hzero]

/-- **Contour Shift Identity via Principal-Part Boundary Integral**:
Expresses the truncated vertical integral at `c = 2` in terms of the left vertical integral at `a`,
the top and bottom horizontal integrals at `±U`, and the rectangle boundary integral of the sum of
principal parts. -/
theorem truncated_smoothedPerron_two_eq_principalParts_add_boundary
    {x U a : ℝ} (hx : 0 < x) (hU : 0 ≤ U) (ha : -1 / 2 < a) (ha2 : a ≤ 2)
    (hP : ∀ p ∈ perronPolesUpTo U, p ∈ openRect a 2 U) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, smoothedPerronIntegrand x (2 + (t : ℂ) * I)) =
      (2 * (Real.pi : ℂ) * I)⁻¹ * rectBoundaryIntegral (perronPrincipalPartSum x U) a 2 U +
        (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, smoothedPerronIntegrand x (a + (t : ℂ) * I)) +
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2, smoothedPerronIntegrand x (σ + (U : ℂ) * I)) -
        (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2, smoothedPerronIntegrand x (σ - (U : ℂ) * I)) := by
  rw [right_vertical_integral_two_eq_rectBoundaryIntegral_add (smoothedPerronIntegrand x) a U,
    rectBoundaryIntegral_smoothedPerronIntegrand_eq_principalParts hx hU ha ha2 hP]

/-- When `-1 / 2 < a < 0`, `0 < U`, and no zero in `nontrivialZetaZerosUpTo U` has `|ρ.im| = U`,
every pole in `perronPolesUpTo U` lies strictly inside `openRect a 2 U`. -/
theorem perronPolesUpTo_mem_openRect_of_neg
    {U a : ℝ} (hU : 0 < U) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    ∀ p ∈ perronPolesUpTo U, p ∈ openRect a 2 U := by
  intro p hp
  rw [mem_openRect]
  rcases mem_perronPolesUpTo.mp hp with rfl | rfl | hρ
  · simp only [one_re, one_im]
    exact ⟨⟨by linarith, by norm_num⟩, ⟨by linarith, by linarith⟩⟩
  · simp only [zero_re, zero_im]
    exact ⟨⟨ha_neg, by norm_num⟩, ⟨by linarith, by linarith⟩⟩
  · have hstrip := mem_criticalStrip_of_isNontrivialZetaZero (mem_nontrivialZetaZerosUpTo.mp hρ).1
    have him := abs_lt.mp (h_no_horiz p hρ)
    exact ⟨⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩, him⟩

theorem sum_perronPolesUpTo_perronResidue (x U : ℝ) :
    ∑ p ∈ perronPolesUpTo U, perronResidue x p =
      resOne x + resZero x + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ := by
  unfold perronPolesUpTo
  have h1_notMem : (1 : ℂ) ∉ insert (0 : ℂ) (nontrivialZetaZerosUpTo U) := by
    rw [Finset.mem_insert, not_or]
    exact ⟨one_ne_zero, one_notMem_nontrivialZetaZerosUpTo U⟩
  have h0_notMem : (0 : ℂ) ∉ nontrivialZetaZerosUpTo U :=
    zero_notMem_nontrivialZetaZerosUpTo U
  rw [Finset.sum_insert h1_notMem, Finset.sum_insert h0_notMem,
    perronResidue_one, perronResidue_zero]
  have hsum : ∑ ρ ∈ nontrivialZetaZerosUpTo U, perronResidue x ρ =
      ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ :=
    Finset.sum_congr rfl fun ρ hρ ↦ perronResidue_of_mem_nontrivialZetaZerosUpTo x hρ
  rw [hsum, add_assoc]

/-- **Exact Rectangle Residue Theorem for `smoothedPerronIntegrand` (`-1 / 2 < a < 0`)**:
For `0 < x`, `0 < U`, `-1 / 2 < a < 0`, and `∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U`,
$$\operatorname{rectBoundaryIntegral}(\text{smoothedPerronIntegrand } x)\, a\, 2\, U
  = 2\pi i \left(\text{resOne } x + \text{resZero } x + \sum_{\rho \in
  \text{nontrivialZetaZerosUpTo } U} \text{resZeroRho } x\, \rho\right).$$ -/
theorem rectBoundaryIntegral_smoothedPerronIntegrand_eq_residues_of_neg
    {x U a : ℝ} (hx : 0 < x) (hU : 0 < U) (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    rectBoundaryIntegral (smoothedPerronIntegrand x) a 2 U =
      2 * (Real.pi : ℂ) * I *
        (resOne x + resZero x + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ) := by
  have ha2 : a ≤ 2 := by linarith
  have hP := perronPolesUpTo_mem_openRect_of_neg hU ha_neg h_no_horiz
  have hres := rectBoundaryIntegral_eq_sum_residues_off_countable (c₁ := a) (c₂ := 2) (T := U)
    ha2 hU.le (M := smoothedPerronIntegrand x) (F := regularizedSmoothedPerron x U)
    (P := perronPolesUpTo U) (r := perronResidue x) countable_empty hP
    (continuousOn_regularizedSmoothedPerron_closedRect hx ha)
    (fun z hz ↦ differentiableAt_regularizedSmoothedPerron hx
      (by linarith [hz.1.1.1]) (abs_le.mpr ⟨hz.1.2.1.le, hz.1.2.2.le⟩))
    (fun z hz ↦ smoothedPerronIntegrand_eq_regularized_add_principalParts x U hz.2)
  rw [hres, sum_perronPolesUpTo_perronResidue]

/-- **Exact Contour Shift Identity for `-1 / 2 < a < 0`**:
For `0 < x`, `0 < U`, `-1 / 2 < a < 0`, and `∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U`:
$$(2\pi)^{-1} \int_{-U}^U \text{smoothedPerronIntegrand } x\, (2 + t I)\,dt
  = \text{resOne } x + \text{resZero } x + \sum_{\rho \in \text{nontrivialZetaZerosUpTo } U}
  \text{resZeroRho } x\, \rho
    + (2\pi)^{-1} \int_{-U}^U \text{smoothedPerronIntegrand } x\, (a + t I)\,dt
    + (2\pi i)^{-1} \left(\int_a^2 \text{smoothedPerronIntegrand } x\, (\sigma + U I)\,d\sigma
      - \int_a^2 \text{smoothedPerronIntegrand } x\, (\sigma - U I)\,d\sigma\right).$$ -/
theorem truncated_smoothedPerron_two_eq_residues_add_boundary_of_neg
    {x U a : ℝ} (hx : 0 < x) (hU : 0 < U) (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, smoothedPerronIntegrand x (2 + (t : ℂ) * I)) =
      (resOne x + resZero x + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ) +
        ((2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, smoothedPerronIntegrand x (a + (t : ℂ) * I)) +
          (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2, smoothedPerronIntegrand x (σ + (U : ℂ) * I)) -
          (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2,
            smoothedPerronIntegrand x (σ - (U : ℂ) * I))) := by
  rw [right_vertical_integral_two_eq_rectBoundaryIntegral_add (smoothedPerronIntegrand x) a U,
    rectBoundaryIntegral_smoothedPerronIntegrand_eq_residues_of_neg hx hU ha ha_neg h_no_horiz,
    inv_two_pi_I_mul_two_pi_I_mul]
  ring

/-- **Exact Rectangle Residue Theorem for `smoothedPerronIntegrand` (`0 < a < 1`)**:
When `0 < a < 1`, `0 < U`, and every `ρ ∈ nontrivialZetaZerosUpTo U` satisfies `a < ρ.re` and
`|ρ.im| < U`, the pole `s = 0` lies outside `closedRect a 2 U`, so the interior poles are
`insert 1 (nontrivialZetaZerosUpTo U)` with residue sum
`resOne x + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ`. -/
theorem rectBoundaryIntegral_smoothedPerronIntegrand_eq_residues_of_pos
    {x U a : ℝ} (hx : 0 < x) (hU : 0 < U) (ha_pos : 0 < a) (ha_lt_one : a < 1)
    (h_zeros : ∀ ρ ∈ nontrivialZetaZerosUpTo U, a < ρ.re ∧ |ρ.im| < U) :
    rectBoundaryIntegral (smoothedPerronIntegrand x) a 2 U =
      2 * (Real.pi : ℂ) * I *
        (resOne x + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ) := by
  have ha : -1 / 2 < a := by linarith
  have ha2 : a ≤ 2 := by linarith
  let P_pos : Finset ℂ := insert (1 : ℂ) (nontrivialZetaZerosUpTo U)
  let F_pos : ℂ → ℂ := fun s ↦ regularizedSmoothedPerron x U s + resZero x / s
  have hP_pos : ∀ p ∈ P_pos, p ∈ openRect a 2 U := by
    intro p hp
    rw [mem_openRect]
    rcases Finset.mem_insert.mp hp with rfl | hρ
    · simp only [one_re, one_im]
      exact ⟨⟨ha_lt_one, by norm_num⟩, ⟨by linarith, by linarith⟩⟩
    · have hstrip := mem_criticalStrip_of_isNontrivialZetaZero (mem_nontrivialZetaZerosUpTo.mp hρ).1
      obtain ⟨hre_a, him⟩ := h_zeros p hρ
      exact ⟨⟨hre_a, by linarith [hstrip.2]⟩, abs_lt.mp him⟩
  have hF_diff : ∀ z ∈ closedRect a 2 U, DifferentiableAt ℂ F_pos z := by
    intro z hz
    rw [mem_closedRect] at hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp only [zero_re] at hz
      linarith [hz.1.1]
    exact (differentiableAt_regularizedSmoothedPerron hx (by linarith [hz.1.1])
      (abs_le.mpr hz.2)).add ((differentiableAt_const (resZero x)).div differentiableAt_id hz0)
  have hF_cont : ContinuousOn F_pos (closedRect a 2 U) :=
    fun z hz ↦ (hF_diff z hz).continuousAt.continuousWithinAt
  have h_open_sub : openRect a 2 U ⊆ closedRect a 2 U :=
    inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)
  have hM : ∀ z ∈ closedRect a 2 U \ (P_pos : Set ℂ),
      smoothedPerronIntegrand x z = F_pos z + ∑ p ∈ P_pos, perronResidue x p / (z - p) := by
    intro z ⟨hz_rect, hz_not_P⟩
    rw [mem_closedRect] at hz_rect
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp only [zero_re] at hz_rect
      linarith [hz_rect.1.1]
    have hz_not_poles : z ∉ perronPolesUpTo U := by
      intro hz_poles
      rcases mem_perronPolesUpTo.mp hz_poles with rfl | rfl | hρ
      · exact hz_not_P (Finset.mem_coe.mpr (Finset.mem_insert_self 1 _))
      · exact hz0 rfl
      · exact hz_not_P (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hρ))
    have h1_notMem : (1 : ℂ) ∉ nontrivialZetaZerosUpTo U := one_notMem_nontrivialZetaZerosUpTo U
    have hsum_P : ∑ p ∈ P_pos, perronResidue x p / (z - p) =
        resOne x / (z - 1) + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ / (z - ρ) := by
      dsimp [P_pos]
      rw [Finset.sum_insert h1_notMem, perronResidue_one]
      congr 1
      refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
      rw [perronResidue_of_mem_nontrivialZetaZerosUpTo x hρ]
    dsimp [F_pos]
    rw [regularizedSmoothedPerron_eq_of_notMem x U hz_not_poles, hsum_P]
    ring
  have hres := rectBoundaryIntegral_eq_sum_residues_off_countable (c₁ := a) (c₂ := 2) (T := U)
    ha2 hU.le (M := smoothedPerronIntegrand x) (F := F_pos)
    (P := P_pos) (r := perronResidue x) countable_empty hP_pos hF_cont
    (fun z hz ↦ hF_diff z (h_open_sub hz.1)) hM
  rw [hres]
  congr 1
  dsimp [P_pos]
  rw [Finset.sum_insert (one_notMem_nontrivialZetaZerosUpTo U), perronResidue_one]
  congr 1
  exact Finset.sum_congr rfl fun ρ hρ ↦ perronResidue_of_mem_nontrivialZetaZerosUpTo x hρ

/-- **Exact Contour Shift Identity for `0 < a < 1`**:
For `0 < x`, `0 < U`, `0 < a < 1`, and `∀ ρ ∈ nontrivialZetaZerosUpTo U, a < ρ.re ∧ |ρ.im| < U`:
$$(2\pi)^{-1} \int_{-U}^U \text{smoothedPerronIntegrand } x\, (2 + t I)\,dt
  = \text{resOne } x + \sum_{\rho \in \text{nontrivialZetaZerosUpTo } U} \text{resZeroRho } x\, \rho
    + (2\pi)^{-1} \int_{-U}^U \text{smoothedPerronIntegrand } x\, (a + t I)\,dt
    + (2\pi i)^{-1} \left(\int_a^2 \text{smoothedPerronIntegrand } x\, (\sigma + U I)\,d\sigma
      - \int_a^2 \text{smoothedPerronIntegrand } x\, (\sigma - U I)\,d\sigma\right).$$ -/
theorem truncated_smoothedPerron_two_eq_residues_add_boundary_of_pos
    {x U a : ℝ} (hx : 0 < x) (hU : 0 < U) (ha_pos : 0 < a) (ha_lt_one : a < 1)
    (h_zeros : ∀ ρ ∈ nontrivialZetaZerosUpTo U, a < ρ.re ∧ |ρ.im| < U) :
    (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, smoothedPerronIntegrand x (2 + (t : ℂ) * I)) =
      (resOne x + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ) +
        ((2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, smoothedPerronIntegrand x (a + (t : ℂ) * I)) +
          (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2, smoothedPerronIntegrand x (σ + (U : ℂ) * I)) -
          (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2,
            smoothedPerronIntegrand x (σ - (U : ℂ) * I))) := by
  rw [right_vertical_integral_two_eq_rectBoundaryIntegral_add (smoothedPerronIntegrand x) a U,
    rectBoundaryIntegral_smoothedPerronIntegrand_eq_residues_of_pos hx hU ha_pos ha_lt_one h_zeros,
    inv_two_pi_I_mul_two_pi_I_mul]
  ring

theorem resOne_re (x : ℝ) : (resOne x).re = x ^ 2 / 2 := by
  unfold resOne
  have h : (x : ℂ) ^ 2 / 2 = ((x ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h, ofReal_re]

theorem neg_deriv_riemannZeta_div_zero :
    -deriv riemannZeta 0 / riemannZeta 0 = -((Real.log (2 * Real.pi) : ℝ) : ℂ) := by
  rw [deriv_riemannZeta_zero, riemannZeta_zero]
  have hlog : Complex.log (2 * (Real.pi : ℂ)) = ((Real.log (2 * Real.pi) : ℝ) : ℂ) := by
    rw [← ofReal_ofNat, ← ofReal_mul, Complex.ofReal_log Real.two_pi_pos.le]
  rw [hlog]
  ring

theorem resZero_eq (x : ℝ) :
    resZero x = -((x * Real.log (2 * Real.pi) : ℝ) : ℂ) := by
  unfold resZero
  rw [neg_deriv_riemannZeta_div_zero]
  push_cast
  ring

theorem resZero_re (x : ℝ) :
    (resZero x).re = -(x * Real.log (2 * Real.pi)) := by
  rw [resZero_eq, neg_re, ofReal_re]

theorem norm_resZero {x : ℝ} (hx : 0 ≤ x) :
    ‖resZero x‖ = x * Real.log (2 * Real.pi) := by
  have hpi : 1 ≤ Real.pi := Real.two_le_pi.trans' one_le_two
  have hlog : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  rw [resZero_eq, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg hx hlog)]

theorem sum_resZeroRho_eq (x : ℝ) (S : Finset ℂ) :
    ∑ ρ ∈ S, resZeroRho x ρ =
      -(∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)))) := by
  unfold resZeroRho smoothedPerronKernel
  simp only [neg_mul, sum_neg_distrib]

theorem abs_re_sub_le_norm (z w : ℂ) :
    |z.re - w.re| ≤ ‖z - w‖ := by
  rw [← sub_re]
  exact Complex.abs_re_le_norm (z - w)

theorem abs_psi1_sub_re_le_of_trunc_decomp {x tailBound : ℝ} {truncInt mainResidues
  contourRemainder : ℂ}
    (htail : ‖(psi1 x : ℂ) - truncInt‖ ≤ tailBound)
    (hdecomp : truncInt = mainResidues + contourRemainder) :
    |psi1 x - mainResidues.re| ≤ tailBound + ‖contourRemainder‖ := by
  calc
    |psi1 x - mainResidues.re|
      = |(psi1 x : ℂ).re - mainResidues.re| := by rw [ofReal_re]
    _ ≤ ‖(psi1 x : ℂ) - mainResidues‖ := abs_re_sub_le_norm _ _
    _ = ‖((psi1 x : ℂ) - truncInt) + contourRemainder‖ := by
        rw [hdecomp]
        ring_nf
    _ ≤ ‖(psi1 x : ℂ) - truncInt‖ + ‖contourRemainder‖ := norm_add_le _ _
    _ ≤ tailBound + ‖contourRemainder‖ := add_le_add_left htail _

/-- **Triangle Inequality Error Reduction for `-1 / 2 < a < 0` (including the $s = 0$ residue $-x
\log(2\pi)$)**:
For `1 ≤ x`, `0 < U`, `-1 / 2 < a < 0`, and `∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U`:
$$\left|\psi_1(x) - \frac{x^2}{2} + x \log(2\pi)
  - \left(-\sum_{\rho \in \text{nontrivialZetaZerosUpTo } U}
      \frac{(m_\rho : \mathbb{C}) (x : \mathbb{C})^{\rho + 1}}{\rho(\rho +
      1)}\right).\text{re}\right|$$
$$\le \frac{2 x^3}{\pi U}
  + \frac{1}{2\pi} \left\|\int_{-U}^U \text{smoothedPerronIntegrand}(x, a + t I)\,dt\right\|
  + \frac{1}{2\pi} \left\|\int_a^2 \text{smoothedPerronIntegrand}(x, \sigma + U I)\,d\sigma\right\|
  + \frac{1}{2\pi} \left\|\int_a^2 \text{smoothedPerronIntegrand}(x, \sigma - U
  I)\,d\sigma\right\|.$$ -/
theorem abs_psi1_sub_main_add_log_two_pi_sub_zeroSum_le_of_neg
    {x U a : ℝ} (hx : 1 ≤ x) (hU : 0 < U) (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    |psi1 x - x ^ 2 / 2 + x * Real.log (2 * Real.pi) -
      (-(∑ ρ ∈ nontrivialZetaZerosUpTo U,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))))).re| ≤
      2 * x ^ (3 : ℝ) / (Real.pi * U) +
        ((2 * Real.pi)⁻¹ * ‖∫ t in (-U)..U, smoothedPerronIntegrand x (a + (t : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand x (σ + (U : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand x (σ - (U : ℂ) * I)‖) := by
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  have htail := norm_psi1_sub_truncated_smoothedPerron_two_le hx hU
  have hdecomp :=
    truncated_smoothedPerron_two_eq_residues_add_boundary_of_neg hx_pos hU ha ha_neg h_no_horiz
  have hbound := abs_psi1_sub_re_le_of_trunc_decomp htail hdecomp
  have hre : (resOne x + resZero x + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ).re =
      x ^ 2 / 2 - x * Real.log (2 * Real.pi) +
        (-(∑ ρ ∈ nontrivialZetaZerosUpTo U,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))))).re := by
    rw [add_re, add_re, resOne_re, resZero_re, sum_resZeroRho_eq]
    ring
  have h_lhs : psi1 x - (resOne x + resZero x + ∑ ρ ∈ nontrivialZetaZerosUpTo U,
    resZeroRho x ρ).re =
      psi1 x - x ^ 2 / 2 + x * Real.log (2 * Real.pi) -
        (-(∑ ρ ∈ nontrivialZetaZerosUpTo U,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))))).re := by
    rw [hre]
    ring
  rw [← h_lhs]
  exact hbound.trans (add_le_add_right
    (norm_contour_shift_remainder_le (smoothedPerronIntegrand x) a 2 U) _)

/-- **Triangle Inequality Error Reduction for `-1 / 2 < a < 0` (absorbing $x \log(2\pi)$ into the
bound)**:
For `1 ≤ x`, `0 < U`, `-1 / 2 < a < 0`, and `∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U`:
$$\left|\psi_1(x) - \frac{x^2}{2}
  - \left(-\sum_{\rho \in \text{nontrivialZetaZerosUpTo } U}
      \frac{(m_\rho : \mathbb{C}) (x : \mathbb{C})^{\rho + 1}}{\rho(\rho +
      1)}\right).\text{re}\right|$$
$$\le x \log(2\pi) + \frac{2 x^3}{\pi U}
  + \frac{1}{2\pi} \left\|\int_{-U}^U \text{smoothedPerronIntegrand}(x, a + t I)\,dt\right\|
  + \frac{1}{2\pi} \left\|\int_a^2 \text{smoothedPerronIntegrand}(x, \sigma + U I)\,d\sigma\right\|
  + \frac{1}{2\pi} \left\|\int_a^2 \text{smoothedPerronIntegrand}(x, \sigma - U
  I)\,d\sigma\right\|.$$ -/
theorem abs_psi1_sub_main_sub_zeroSum_le_of_neg
    {x U a : ℝ} (hx : 1 ≤ x) (hU : 0 < U) (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    |psi1 x - x ^ 2 / 2 -
      (-(∑ ρ ∈ nontrivialZetaZerosUpTo U,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))))).re| ≤
      x * Real.log (2 * Real.pi) + 2 * x ^ (3 : ℝ) / (Real.pi * U) +
        ((2 * Real.pi)⁻¹ * ‖∫ t in (-U)..U, smoothedPerronIntegrand x (a + (t : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand x (σ + (U : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand x (σ - (U : ℂ) * I)‖) := by
  have hmain := abs_psi1_sub_main_add_log_two_pi_sub_zeroSum_le_of_neg hx hU ha ha_neg h_no_horiz
  have hpi : 1 ≤ Real.pi := Real.two_le_pi.trans' one_le_two
  have hlog : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  have hxlog : 0 ≤ x * Real.log (2 * Real.pi) := mul_nonneg (zero_le_one.trans hx) hlog
  set Z := (-(∑ ρ ∈ nontrivialZetaZerosUpTo U,
    (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))))).re
  have htri : |psi1 x - x ^ 2 / 2 - Z| ≤
      |psi1 x - x ^ 2 / 2 + x * Real.log (2 * Real.pi) - Z| + |x * Real.log (2 * Real.pi)| := by
    have : psi1 x - x ^ 2 / 2 - Z =
        (psi1 x - x ^ 2 / 2 + x * Real.log (2 * Real.pi) - Z) - x * Real.log (2 * Real.pi) :=
          by ring
    rw [this]
    exact abs_sub _ _
  rw [abs_of_nonneg hxlog] at htri
  linarith

/-- **Triangle Inequality Error Reduction for `0 < a < 1`**:
For `1 ≤ x`, `0 < U`, `0 < a < 1`, and `∀ ρ ∈ nontrivialZetaZerosUpTo U, a < ρ.re ∧ |ρ.im| < U`:
$$\left|\psi_1(x) - \frac{x^2}{2}
  - \left(-\sum_{\rho \in \text{nontrivialZetaZerosUpTo } U}
      \frac{(m_\rho : \mathbb{C}) (x : \mathbb{C})^{\rho + 1}}{\rho(\rho +
      1)}\right).\text{re}\right|$$
$$\le \frac{2 x^3}{\pi U}
  + \frac{1}{2\pi} \left\|\int_{-U}^U \text{smoothedPerronIntegrand}(x, a + t I)\,dt\right\|
  + \frac{1}{2\pi} \left\|\int_a^2 \text{smoothedPerronIntegrand}(x, \sigma + U I)\,d\sigma\right\|
  + \frac{1}{2\pi} \left\|\int_a^2 \text{smoothedPerronIntegrand}(x, \sigma - U
  I)\,d\sigma\right\|.$$ -/
theorem abs_psi1_sub_main_sub_zeroSum_le_of_pos
    {x U a : ℝ} (hx : 1 ≤ x) (hU : 0 < U) (ha_pos : 0 < a) (ha_lt_one : a < 1)
    (h_zeros : ∀ ρ ∈ nontrivialZetaZerosUpTo U, a < ρ.re ∧ |ρ.im| < U) :
    |psi1 x - x ^ 2 / 2 -
      (-(∑ ρ ∈ nontrivialZetaZerosUpTo U,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))))).re| ≤
      2 * x ^ (3 : ℝ) / (Real.pi * U) +
        ((2 * Real.pi)⁻¹ * ‖∫ t in (-U)..U, smoothedPerronIntegrand x (a + (t : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand x (σ + (U : ℂ) * I)‖ +
          (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand x (σ - (U : ℂ) * I)‖) := by
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  have htail := norm_psi1_sub_truncated_smoothedPerron_two_le hx hU
  have hdecomp :=
    truncated_smoothedPerron_two_eq_residues_add_boundary_of_pos hx_pos hU ha_pos ha_lt_one h_zeros
  have hbound := abs_psi1_sub_re_le_of_trunc_decomp htail hdecomp
  have hre : (resOne x + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ).re =
      x ^ 2 / 2 +
        (-(∑ ρ ∈ nontrivialZetaZerosUpTo U,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))))).re := by
    rw [add_re, resOne_re, sum_resZeroRho_eq]
  have h_lhs : psi1 x - (resOne x + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x ρ).re =
      psi1 x - x ^ 2 / 2 -
        (-(∑ ρ ∈ nontrivialZetaZerosUpTo U,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * ((x : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1))))).re := by
    rw [hre]
    ring
  rw [← h_lhs]
  exact hbound.trans (add_le_add_right
    (norm_contour_shift_remainder_le (smoothedPerronIntegrand x) a 2 U) _)

/-!
## Section 4: Difference Quotient Contour Shift & Low/High Frequency Split Theorem

Taking the difference quotient `(psi1 (x₁ + h) - psi1 x₁) / h` (`1 ≤ x₁`, `0 < h`) **before**
taking norms cancels the `1 / h` against `h` in the `s = 0` pole residue:
$$\frac{\text{resZero}(x_1 + h) - \text{resZero}(x_1)}{h} = -\log(2\pi),$$
turns the `s = 1` main term into
$$\frac{\text{resOne}(x_1 + h) - \text{resOne}(x_1)}{h} = x_1 + \frac{h}{2},$$
and turns each nontrivial zero residue into
$$\frac{\text{resZeroRho}(x_1 + h, \rho) - \text{resZeroRho}(x_1, \rho)}{h}
  = -(m_\rho : \mathbb{C}) \cdot \text{smoothedZeroTerm}(x_1, h, \rho).$$
Splitting `nontrivialZetaZerosUpTo U` at cutoff `T` (`0 < T ≤ U`) into `nontrivialZetaZerosUpTo T`
and `nontrivialZetaZerosBetween T U` and combining the forward (`[x, x + h]`) and backward
(`[x - h, x]`) difference quotients yields `abs_psi_sub_self_le_smoothed_contour_shift`.
-/

/-- `Chebyshev.psi` is measurable, since it factors through `Nat.floor : ℝ → ℕ`. -/
theorem measurable_psi : Measurable Chebyshev.psi := by
  have heq : Chebyshev.psi =
    (fun n : ℕ ↦ ∑ k ∈ Ioc 0 n, ArithmeticFunction.vonMangoldt k) ∘ Nat.floor := rfl
  rw [heq]
  exact measurable_from_nat.comp Nat.measurable_floor

/-- `Chebyshev.psi` is `IntervalIntegrable` on `[a, b]` for all `a b : ℝ`. -/
theorem intervalIntegrable_psi (a b : ℝ) :
    IntervalIntegrable Chebyshev.psi volume a b := by
  refine (intervalIntegrable_const (c := Chebyshev.psi (max a b))).mono_fun'
    measurable_psi.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [Real.norm_of_nonneg (Chebyshev.psi_nonneg t)]
  have hle : t ≤ max a b := (uIoc_subset_uIcc ht).2
  exact Chebyshev.psi_mono hle

/-- For all `a b : ℝ`, `psi1 b - psi1 a = ∫ t in a..b, Chebyshev.psi t`. -/
theorem psi1_sub_psi1 (a b : ℝ) :
    psi1 b - psi1 a = ∫ t in a..b, Chebyshev.psi t := by
  unfold psi1
  have h := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_psi 1 a) (intervalIntegrable_psi a b)
  linarith

/-- If `a ≤ b`, then `(b - a) * Chebyshev.psi a ≤ psi1 b - psi1 a` and
`psi1 b - psi1 a ≤ (b - a) * Chebyshev.psi b`. -/
theorem mul_psi_le_psi1_sub_and_le {a b : ℝ} (hab : a ≤ b) :
    (b - a) * Chebyshev.psi a ≤ psi1 b - psi1 a ∧
      psi1 b - psi1 a ≤ (b - a) * Chebyshev.psi b := by
  rw [psi1_sub_psi1]
  constructor
  · calc
      (b - a) * Chebyshev.psi a = ∫ _ in a..b, Chebyshev.psi a := by
        simp [intervalIntegral.integral_const]
      _ ≤ ∫ t in a..b, Chebyshev.psi t :=
        intervalIntegral.integral_mono_on hab intervalIntegrable_const
          (intervalIntegrable_psi a b) fun t ht ↦ Chebyshev.psi_mono ht.1
  · calc
      (∫ t in a..b, Chebyshev.psi t) ≤ ∫ _ in a..b, Chebyshev.psi b :=
        intervalIntegral.integral_mono_on hab (intervalIntegrable_psi a b)
          intervalIntegrable_const fun t ht ↦ Chebyshev.psi_mono ht.2
      _ = (b - a) * Chebyshev.psi b := by
        simp [intervalIntegral.integral_const]

/-- **Upper Monotonicity Sandwich Lemma**:
For any `x : ℝ` and `0 < h`,
$$\psi(x) \le \frac{\psi_1(x + h) - \psi_1(x)}{h}.$$ -/
theorem psi_le_psi1_add_sub_div (x : ℝ) {h : ℝ} (hh : 0 < h) :
    Chebyshev.psi x ≤ (psi1 (x + h) - psi1 x) / h := by
  rw [le_div_iff₀ hh]
  have h1 := (mul_psi_le_psi1_sub_and_le (a := x) (b := x + h) (by linarith)).1
  linarith

/-- **Lower Monotonicity Sandwich Lemma**:
For any `x : ℝ` and `0 < h`,
$$\frac{\psi_1(x) - \psi_1(x - h)}{h} \le \psi(x).$$ -/
theorem psi1_sub_psi1_sub_div_le_psi (x : ℝ) {h : ℝ} (hh : 0 < h) :
    (psi1 x - psi1 (x - h)) / h ≤ Chebyshev.psi x := by
  rw [div_le_iff₀ hh]
  have h2 := (mul_psi_le_psi1_sub_and_le (a := x - h) (b := x) (by linarith)).2
  linarith

/-- The smoothed zero-sum term corresponding to the forward difference quotient of
`t ^ (ρ + 1) / (ρ * (ρ + 1))` over `[x, x + h]`:
$$\text{smoothedZeroTerm}(x, h, \rho)
  = \frac{(x + h)^{\rho + 1} - x^{\rho + 1}}{h \rho (\rho + 1)}.$$ -/
noncomputable def smoothedZeroTerm (x h : ℝ) (ρ : ℂ) : ℂ :=
  (((x + h : ℝ) : ℂ) ^ (ρ + 1) - (x : ℂ) ^ (ρ + 1)) / ((h : ℂ) * ρ * (ρ + 1))

/-- The backward difference quotient of `t ^ (ρ + 1) / (ρ * (ρ + 1))` over `[x - h, x]`. -/
noncomputable def smoothedZeroTermBackward (x h : ℝ) (ρ : ℂ) : ℂ :=
  ((x : ℂ) ^ (ρ + 1) - ((x - h : ℝ) : ℂ) ^ (ρ + 1)) / ((h : ℂ) * ρ * (ρ + 1))

/-- **Fundamental Theorem of Calculus for `∫_a^b t ^ ρ dt`**:
For any `a b : ℝ` and `ρ : ℂ` with `0 < ρ.re`,
$$\int_a^b t^\rho \, dt = \frac{b^{\rho + 1} - a^{\rho + 1}}{\rho + 1}.$$ -/
theorem integral_cpow_of_re_pos (a b : ℝ) {ρ : ℂ} (hρ : 0 < ρ.re) :
    (∫ t : ℝ in a..b, (t : ℂ) ^ ρ) = ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ + 1) :=
  integral_cpow (Or.inl (by linarith))

/-- For `0 < ρ.re`, `smoothedZeroTerm x h ρ` equals `(∫ t in x..(x + h), (t : ℂ) ^ ρ) / (h * ρ)`. -/
theorem smoothedZeroTerm_eq_integral_div (x h : ℝ) {ρ : ℂ} (hρ : 0 < ρ.re) :
    smoothedZeroTerm x h ρ = (∫ t : ℝ in x..(x + h), (t : ℂ) ^ ρ) / ((h : ℂ) * ρ) := by
  unfold smoothedZeroTerm
  rw [integral_cpow_of_re_pos x (x + h) hρ, div_div, mul_comm (ρ + 1)]

/-- For `0 < ρ.re`, `smoothedZeroTermBackward x h ρ` equals
`(∫ t in (x - h)..x, (t : ℂ) ^ ρ) / (h * ρ)`. -/
theorem smoothedZeroTermBackward_eq_integral_div (x h : ℝ) {ρ : ℂ} (hρ : 0 < ρ.re) :
    smoothedZeroTermBackward x h ρ = (∫ t : ℝ in (x - h)..x, (t : ℂ) ^ ρ) / ((h : ℂ) * ρ) := by
  unfold smoothedZeroTermBackward
  rw [integral_cpow_of_re_pos (x - h) x hρ, div_div, mul_comm (ρ + 1)]

/-- **Low-Frequency Norm Bound for `smoothedZeroTerm` (`ρ.re = 1 / 2`)**:
If `0 < x`, `0 < h`, and `ρ.re = 1 / 2`, then
$$\|\text{smoothedZeroTerm}(x, h, \rho)\| \le \frac{\sqrt{x + h}}{\|\rho\|}.$$ -/
theorem norm_smoothedZeroTerm_le_sqrt_div_norm {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖smoothedZeroTerm x h ρ‖ ≤ Real.sqrt (x + h) / ‖ρ‖ := by
  have hρ_pos : 0 < ρ.re := by linarith
  rw [smoothedZeroTerm_eq_integral_div x h hρ_pos, norm_div, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hh.le]
  have hint_le : ‖∫ t : ℝ in x..(x + h), (t : ℂ) ^ ρ‖ ≤ Real.sqrt (x + h) * |x + h - x| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
    rw [uIoc_of_le (by linarith)] at ht
    have ht_pos : 0 < t := hx.trans ht.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos, hre, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt ht.2
  have habs : |x + h - x| = h := by
    rw [add_sub_cancel_left, abs_of_pos hh]
  rw [habs] at hint_le
  calc
    ‖∫ t : ℝ in x..(x + h), (t : ℂ) ^ ρ‖ / (h * ‖ρ‖)
      ≤ (Real.sqrt (x + h) * h) / (h * ‖ρ‖) :=
        div_le_div_of_nonneg_right hint_le (mul_nonneg hh.le (norm_nonneg ρ))
    _ = Real.sqrt (x + h) / ‖ρ‖ := by
        rw [mul_comm (Real.sqrt (x + h)) h, mul_div_mul_left _ _ hh.ne']

/-- **Low-Frequency Norm Bound for `smoothedZeroTermBackward` (`ρ.re = 1 / 2`)**:
If `0 < x - h`, `0 < h`, and `ρ.re = 1 / 2`, then
$$\|\text{smoothedZeroTermBackward}(x, h, \rho)\| \le \frac{\sqrt{x}}{\|\rho\|}.$$ -/
theorem norm_smoothedZeroTermBackward_le_sqrt_div_norm {x h : ℝ} (hxh : 0 < x - h) (hh : 0 < h)
    {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖smoothedZeroTermBackward x h ρ‖ ≤ Real.sqrt x / ‖ρ‖ := by
  have hρ_pos : 0 < ρ.re := by linarith
  rw [smoothedZeroTermBackward_eq_integral_div x h hρ_pos, norm_div, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hh.le]
  have hint_le : ‖∫ t : ℝ in (x - h)..x, (t : ℂ) ^ ρ‖ ≤ Real.sqrt x * |x - (x - h)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht ↦ ?_
    rw [uIoc_of_le (by linarith)] at ht
    have ht_pos : 0 < t := hxh.trans ht.1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht_pos, hre, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt ht.2
  have habs : |x - (x - h)| = h := by
    rw [sub_sub_cancel, abs_of_pos hh]
  rw [habs] at hint_le
  calc
    ‖∫ t : ℝ in (x - h)..x, (t : ℂ) ^ ρ‖ / (h * ‖ρ‖)
      ≤ (Real.sqrt x * h) / (h * ‖ρ‖) :=
        div_le_div_of_nonneg_right hint_le (mul_nonneg hh.le (norm_nonneg ρ))
    _ = Real.sqrt x / ‖ρ‖ := by
        rw [mul_comm (Real.sqrt x) h, mul_div_mul_left _ _ hh.ne']

/-- For any complex number `ρ`, `|ρ.im| ^ 2 ≤ ‖ρ * (ρ + 1)‖`. -/
theorem sq_abs_im_le_norm_mul_add_one (ρ : ℂ) :
    |ρ.im| ^ 2 ≤ ‖ρ * (ρ + 1)‖ := by
  rw [sq, norm_mul]
  have h1 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have h2 : |ρ.im| ≤ ‖ρ + 1‖ := by
    simpa using Complex.abs_im_le_norm (ρ + 1)
  exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)

/-- **High-Frequency Norm Bound for `smoothedZeroTerm` (`ρ.re = 1 / 2`)**:
If `0 < x`, `0 < h`, `ρ.re = 1 / 2`, and `ρ.im ≠ 0`, then
$$\|\text{smoothedZeroTerm}(x, h, \rho)\| \le \frac{2 (x + h)^{3/2}}{h |\rho.\text{im}|^2}.$$ -/
theorem norm_smoothedZeroTerm_le_two_mul_rpow_div_sq_im {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    {ρ : ℂ} (hre : ρ.re = 1 / 2) (him : ρ.im ≠ 0) :
    ‖smoothedZeroTerm x h ρ‖ ≤ 2 * (x + h) ^ (3 / 2 : ℝ) / (h * |ρ.im| ^ 2) := by
  unfold smoothedZeroTerm
  rw [norm_div, mul_assoc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hh.le]
  have hre1 : (ρ + 1).re = 3 / 2 := by
    simp [hre]
    norm_num
  have hxh_pos : 0 < x + h := by linarith
  have hnum : ‖((x + h : ℝ) : ℂ) ^ (ρ + 1) - (x : ℂ) ^ (ρ + 1)‖ ≤ 2 * (x + h) ^ (3 / 2 : ℝ) := by
    calc
      ‖((x + h : ℝ) : ℂ) ^ (ρ + 1) - (x : ℂ) ^ (ρ + 1)‖
        ≤ ‖((x + h : ℝ) : ℂ) ^ (ρ + 1)‖ + ‖(x : ℂ) ^ (ρ + 1)‖ := norm_sub_le _ _
      _ = (x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxh_pos,
          Complex.norm_cpow_eq_rpow_re_of_pos hx, hre1]
      _ ≤ (x + h) ^ (3 / 2 : ℝ) + (x + h) ^ (3 / 2 : ℝ) := by
        gcongr
        linarith
      _ = 2 * (x + h) ^ (3 / 2 : ℝ) := by ring
  have hden : h * |ρ.im| ^ 2 ≤ h * ‖ρ * (ρ + 1)‖ :=
    mul_le_mul_of_nonneg_left (sq_abs_im_le_norm_mul_add_one ρ) hh.le
  have hden_pos : 0 < h * |ρ.im| ^ 2 := by
    have : 0 < |ρ.im| := abs_pos.mpr him
    positivity
  calc
    ‖((x + h : ℝ) : ℂ) ^ (ρ + 1) - (x : ℂ) ^ (ρ + 1)‖ / (h * ‖ρ * (ρ + 1)‖)
      ≤ (2 * (x + h) ^ (3 / 2 : ℝ)) / (h * ‖ρ * (ρ + 1)‖) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (2 * (x + h) ^ (3 / 2 : ℝ)) / (h * |ρ.im| ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) hden_pos hden

/-- Under `RiemannHypothesis`, for every nontrivial zero `ρ`, `0 < x`, and `0 < h`:
1. `‖smoothedZeroTerm x h ρ‖ ≤ Real.sqrt (x + h) / ‖ρ‖`, and
2. if `ρ.im ≠ 0`, `‖smoothedZeroTerm x h ρ‖ ≤ 2 * (x + h) ^ (3 / 2 : ℝ) / (h * |ρ.im| ^ 2)`. -/
theorem norm_smoothedZeroTerm_bounds_of_riemannHypothesis (hRH : RiemannHypothesis)
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) (him : ρ.im ≠ 0) :
    ‖smoothedZeroTerm x h ρ‖ ≤ Real.sqrt (x + h) / ‖ρ‖ ∧
      ‖smoothedZeroTerm x h ρ‖ ≤ 2 * (x + h) ^ (3 / 2 : ℝ) / (h * |ρ.im| ^ 2) := by
  have hre : ρ.re = 1 / 2 := hRH ρ hρ.1 hρ.2.1 hρ.2.2
  exact ⟨norm_smoothedZeroTerm_le_sqrt_div_norm hx hh hre,
    norm_smoothedZeroTerm_le_two_mul_rpow_div_sq_im hx hh hre him⟩

/-- **Exact Difference Quotient of the `s = 1` Residue**:
For `h ≠ 0`, `(resOne (x₁ + h) - resOne x₁) / (h : ℂ) = ((x₁ + h / 2 : ℝ) : ℂ)`. -/
theorem resOne_add_sub_div {x₁ h : ℝ} (hh : h ≠ 0) :
    (resOne (x₁ + h) - resOne x₁) / (h : ℂ) = ((x₁ + h / 2 : ℝ) : ℂ) := by
  unfold resOne
  have hh_c : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh
  push_cast
  field_simp [hh_c]
  ring

/-- **Exact Difference Quotient of the `s = 0` Residue (`1 / h` Cancellation)**:
For `h ≠ 0`, `(resZero (x₁ + h) - resZero x₁) / (h : ℂ) = -((Real.log (2 * Real.pi) : ℝ) : ℂ)`. -/
theorem resZero_add_sub_div {x₁ h : ℝ} (hh : h ≠ 0) :
    (resZero (x₁ + h) - resZero x₁) / (h : ℂ) = -((Real.log (2 * Real.pi) : ℝ) : ℂ) := by
  rw [resZero_eq, resZero_eq]
  have hh_c : (h : ℂ) ≠ 0 := ofReal_ne_zero.mpr hh
  push_cast
  field_simp [hh_c]
  ring

/-- **Exact Difference Quotient of a Nontrivial Zero Residue `resZeroRho`**:
`(resZeroRho (x₁ + h) ρ - resZeroRho x₁ ρ) / (h : ℂ) = -(analyticOrderNatAt riemannZeta ρ : ℂ) *
smoothedZeroTerm x₁ h ρ`. -/
theorem resZeroRho_add_sub_div (x₁ h : ℝ) (ρ : ℂ) :
    (resZeroRho (x₁ + h) ρ - resZeroRho x₁ ρ) / (h : ℂ) =
      -(analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ := by
  unfold resZeroRho smoothedPerronKernel smoothedZeroTerm
  rw [← mul_sub, mul_div_assoc, ← sub_div, div_div,
    show ρ * (ρ + 1) * (h : ℂ) = (h : ℂ) * ρ * (ρ + 1) by ring]

/-- **Exact Difference Quotient of the Finite Zero-Residue Sum**:
For any `S : Finset ℂ`,
`(∑ ρ ∈ S, resZeroRho (x₁ + h) ρ - ∑ ρ ∈ S, resZeroRho x₁ ρ) / (h : ℂ) = -(∑ ρ ∈ S,
(analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ)`. -/
theorem sum_resZeroRho_add_sub_div (x₁ h : ℝ) (S : Finset ℂ) :
    (∑ ρ ∈ S, resZeroRho (x₁ + h) ρ - ∑ ρ ∈ S, resZeroRho x₁ ρ) / (h : ℂ) =
      -(∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ) := by
  rw [← sum_sub_distrib, sum_div, ← sum_neg_distrib]
  refine sum_congr rfl fun ρ _ ↦ ?_
  rw [resZeroRho_add_sub_div, neg_mul]

/-- Real-part version of `sum_resZeroRho_add_sub_div`. -/
theorem re_sum_resZeroRho_add_sub_div (x₁ h : ℝ) (S : Finset ℂ) :
    ((∑ ρ ∈ S, resZeroRho (x₁ + h) ρ).re - (∑ ρ ∈ S, resZeroRho x₁ ρ).re) / h =
      (-(∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ)).re := by
  rw [← sub_re, ← Complex.div_ofReal_re, sum_resZeroRho_add_sub_div]

/-- **Complex Difference Quotient of the Truncated Smoothed Perron Contour Shift (`-1 / 2 < a <
0`)**:
Subtracting `truncated_smoothedPerron_two_eq_residues_add_boundary_of_neg` at `x₁` from that at
`x₁ + h` and dividing by `h` yields `x₁ + h / 2 - log(2π) - ∑ ρ, m_ρ * smoothedZeroTerm x₁ h ρ`
plus the difference quotient of the contour boundary integrals. -/
theorem truncated_smoothedPerron_two_add_sub_div_eq_of_neg
    {x₁ h U a : ℝ} (hx₁ : 0 < x₁) (hh : 0 < h) (hU : 0 < U)
    (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    (((2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, smoothedPerronIntegrand (x₁ + h) (2 + (t : ℂ) * I)) -
      (2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U,
        smoothedPerronIntegrand x₁ (2 + (t : ℂ) * I))) / (h : ℂ)) =
      (((x₁ + h / 2 : ℝ) : ℂ) - ((Real.log (2 * Real.pi) : ℝ) : ℂ) -
        ∑ ρ ∈ nontrivialZetaZerosUpTo U,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ) +
      ((((2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U,
        smoothedPerronIntegrand (x₁ + h) (a + (t : ℂ) * I)) +
          (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2,
            smoothedPerronIntegrand (x₁ + h) (σ + (U : ℂ) * I)) -
          (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2,
            smoothedPerronIntegrand (x₁ + h) (σ - (U : ℂ) * I))) -
        ((2 * (Real.pi : ℂ))⁻¹ * (∫ t in (-U)..U, smoothedPerronIntegrand x₁ (a + (t : ℂ) * I)) +
          (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2, smoothedPerronIntegrand x₁ (σ + (U : ℂ) * I)) -
          (2 * (Real.pi : ℂ) * I)⁻¹ * (∫ σ in a..2,
            smoothedPerronIntegrand x₁ (σ - (U : ℂ) * I)))) / (h : ℂ)) := by
  have hx₂ : 0 < x₁ + h := by linarith
  rw [truncated_smoothedPerron_two_eq_residues_add_boundary_of_neg hx₂ hU ha ha_neg h_no_horiz,
    truncated_smoothedPerron_two_eq_residues_add_boundary_of_neg hx₁ hU ha ha_neg h_no_horiz]
  have h_res :
      ((resOne (x₁ + h) + resZero (x₁ + h) + ∑ ρ ∈ nontrivialZetaZerosUpTo U,
        resZeroRho (x₁ + h) ρ) -
        (resOne x₁ + resZero x₁ + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x₁ ρ)) / (h : ℂ) =
      ((x₁ + h / 2 : ℝ) : ℂ) - ((Real.log (2 * Real.pi) : ℝ) : ℂ) -
        ∑ ρ ∈ nontrivialZetaZerosUpTo U,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ := by
    calc
      ((resOne (x₁ + h) + resZero (x₁ + h) + ∑ ρ ∈ nontrivialZetaZerosUpTo U,
        resZeroRho (x₁ + h) ρ) -
          (resOne x₁ + resZero x₁ + ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x₁ ρ)) / (h : ℂ)
        = (resOne (x₁ + h) - resOne x₁) / (h : ℂ) +
            (resZero (x₁ + h) - resZero x₁) / (h : ℂ) +
            (∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho (x₁ + h) ρ -
              ∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho x₁ ρ) / (h : ℂ) := by ring
      _ = ((x₁ + h / 2 : ℝ) : ℂ) - ((Real.log (2 * Real.pi) : ℝ) : ℂ) -
            ∑ ρ ∈ nontrivialZetaZerosUpTo U,
              (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ := by
          rw [resOne_add_sub_div hh.ne', resZero_add_sub_div hh.ne', sum_resZeroRho_add_sub_div]
          ring
  rw [← h_res]
  ring

/-- **Low/High Frequency Partition of `nontrivialZetaZerosUpTo U`**:
For `T ≤ U` and any function `f`, the sum over `nontrivialZetaZerosUpTo U` splits into the sum
over `nontrivialZetaZerosUpTo T` plus the sum over `nontrivialZetaZerosBetween T U`. -/
theorem sum_nontrivialZetaZerosUpTo_eq_add_between {α : Type*} [AddCommMonoid α]
    {T U : ℝ} (hTU : T ≤ U) (f : ℂ → α) :
    ∑ ρ ∈ nontrivialZetaZerosUpTo U, f ρ =
      (∑ ρ ∈ nontrivialZetaZerosUpTo T, f ρ) +
        ∑ ρ ∈ nontrivialZetaZerosBetween T U, f ρ := by
  rw [← filter_not_lt_abs_im_nontrivialZetaZerosUpTo hTU, nontrivialZetaZerosBetween,
    add_comm, sum_filter_add_sum_filter_not]

/-- **Low-Frequency Zero-Sum Bound (`|ρ.im| ≤ T`) under `RiemannHypothesis`**:
For `0 < x₁` and `0 < h`,
$$\left\|\sum_{\rho \in \mathcal{Z}(T)} (m_\rho : \mathbb{C}) \cdot \text{smoothedZeroTerm}(x_1, h,
\rho)\right\|
  \le \sqrt{x_1 + h} \sum_{\rho \in \mathcal{Z}(T)} \frac{m_\rho}{\|\rho\|}.$$ -/
theorem norm_sum_smoothedZeroTerm_upTo_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) {x₁ h T : ℝ} (hx₁ : 0 < x₁) (hh : 0 < h) :
    ‖∑ ρ ∈ nontrivialZetaZerosUpTo T,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ‖ ≤
      Real.sqrt (x₁ + h) *
        ∑ ρ ∈ nontrivialZetaZerosUpTo T, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun ρ hρ ↦ ?_)
  have hρ_zero : IsNontrivialZetaZero ρ := (mem_nontrivialZetaZerosUpTo.mp hρ).1
  have hre : ρ.re = 1 / 2 := hRH ρ hρ_zero.1 hρ_zero.2.1 hρ_zero.2.2
  rw [norm_mul, Complex.norm_natCast]
  calc
    (analyticOrderNatAt riemannZeta ρ : ℝ) * ‖smoothedZeroTerm x₁ h ρ‖
      ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * (Real.sqrt (x₁ + h) / ‖ρ‖) :=
        mul_le_mul_of_nonneg_left (norm_smoothedZeroTerm_le_sqrt_div_norm hx₁ hh hre)
          (Nat.cast_nonneg _)
    _ = Real.sqrt (x₁ + h) * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) := by ring

/-- **High-Frequency Zero-Sum Bound (`T < |ρ.im| ≤ U`) under `RiemannHypothesis`**:
For `0 < x₁`, `0 < h`, and `0 < T`,
$$\left\|\sum_{\rho \in \mathcal{Z}(T, U)} (m_\rho : \mathbb{C}) \cdot \text{smoothedZeroTerm}(x_1,
h, \rho)\right\|
  \le \frac{2 (x_1 + h)^{3/2}}{h} \sum_{\rho \in \mathcal{Z}(T, U)}
  \frac{m_\rho}{|\rho.\text{im}|^2}.$$ -/
theorem norm_sum_smoothedZeroTerm_between_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) {x₁ h T U : ℝ} (hx₁ : 0 < x₁) (hh : 0 < h) (hT : 0 < T) :
    ‖∑ ρ ∈ nontrivialZetaZerosBetween T U,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ‖ ≤
      (2 * (x₁ + h) ^ (3 / 2 : ℝ) / h) *
        ∑ ρ ∈ nontrivialZetaZerosBetween T U,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2 := by
  rw [mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun ρ hρ ↦ ?_)
  obtain ⟨hρ_zero, _, hρ_gt⟩ := mem_nontrivialZetaZerosBetween.mp hρ
  have hre : ρ.re = 1 / 2 := hRH ρ hρ_zero.1 hρ_zero.2.1 hρ_zero.2.2
  have him : ρ.im ≠ 0 := abs_pos.mp (hT.trans hρ_gt)
  rw [norm_mul, Complex.norm_natCast]
  calc
    (analyticOrderNatAt riemannZeta ρ : ℝ) * ‖smoothedZeroTerm x₁ h ρ‖
      ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) *
          (2 * (x₁ + h) ^ (3 / 2 : ℝ) / (h * |ρ.im| ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (norm_smoothedZeroTerm_le_two_mul_rpow_div_sq_im hx₁ hh hre him) (Nat.cast_nonneg _)
    _ = (2 * (x₁ + h) ^ (3 / 2 : ℝ) / h) *
          ((analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) := by ring

/-- **Combined Low/High Frequency Zero-Sum Bound up to `U` under `RiemannHypothesis`**:
For `0 < x₁`, `0 < h`, `0 < T`, and `T ≤ U`, splitting at `T` bounds the full zero sum up to `U`. -/
theorem norm_sum_smoothedZeroTerm_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) {x₁ h T U : ℝ}
    (hx₁ : 0 < x₁) (hh : 0 < h) (hT : 0 < T) (hTU : T ≤ U) :
    ‖∑ ρ ∈ nontrivialZetaZerosUpTo U,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ‖ ≤
      Real.sqrt (x₁ + h) *
        (∑ ρ ∈ nontrivialZetaZerosUpTo T,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) +
      (2 * (x₁ + h) ^ (3 / 2 : ℝ) / h) *
        (∑ ρ ∈ nontrivialZetaZerosBetween T U,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) := by
  rw [sum_nontrivialZetaZerosUpTo_eq_add_between hTU]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_sum_smoothedZeroTerm_upTo_le_of_riemannHypothesis hRH hx₁ hh)
    (norm_sum_smoothedZeroTerm_between_le_of_riemannHypothesis hRH hx₁ hh hT))

/-- The contour-shift boundary integral error at `y` along the shifted vertical line `Re s = a`
and the top/bottom horizontal segments `[a, 2] ± i U`. -/
noncomputable def contourBoundaryError (y a U : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ‖∫ t in (-U)..U, smoothedPerronIntegrand y (a + (t : ℂ) * I)‖ +
    (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand y (σ + (U : ℂ) * I)‖ +
    (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand y (σ - (U : ℂ) * I)‖

theorem contourBoundaryError_nonneg (y a U : ℝ) :
    0 ≤ contourBoundaryError y a U := by
  unfold contourBoundaryError
  positivity

/-- The combined difference-quotient contour and vertical-tail error for `|ψ(x) - x|` over
`[x - h, x]` and `[x, x + h]`, bounding the vertical tail by `4 * (x + h) ^ 3 / (Real.pi * h * U)`
and the horizontal-segment and left-vertical-line terms at `x - h, x, x + h`. -/
noncomputable def contourDiffError (x h a U : ℝ) : ℝ :=
  4 * (x + h) ^ (3 : ℝ) / (Real.pi * h * U) +
    max ((contourBoundaryError (x + h) a U + contourBoundaryError x a U) / h)
      ((contourBoundaryError x a U + contourBoundaryError (x - h) a U) / h)

/-- `contourDiffError x h a U` is bounded above by the symmetric sum of the boundary errors at
`x - h`, `x`, and `x + h`. -/
theorem contourDiffError_le_sum {x h a U : ℝ} (hh : 0 < h) :
    contourDiffError x h a U ≤
      4 * (x + h) ^ (3 : ℝ) / (Real.pi * h * U) +
        (contourBoundaryError (x - h) a U + 2 * contourBoundaryError x a U +
          contourBoundaryError (x + h) a U) / h := by
  unfold contourDiffError
  gcongr
  have h_minus : 0 ≤ contourBoundaryError (x - h) a U := contourBoundaryError_nonneg _ _ _
  have h_x : 0 ≤ contourBoundaryError x a U := contourBoundaryError_nonneg _ _ _
  have h_plus : 0 ≤ contourBoundaryError (x + h) a U := contourBoundaryError_nonneg _ _ _
  refine max_le ?_ ?_
  ·exact div_le_div_of_nonneg_right (by linarith) hh.le
  · exact div_le_div_of_nonneg_right (by linarith) hh.le

/-- Exact contour remainder at `y` before taking norms of the main term, `s = 0` pole, or zeros. -/
noncomputable def psi1ContourRemainder (y U : ℝ) : ℝ :=
  psi1 y - y ^ 2 / 2 + y * Real.log (2 * Real.pi) -
    (∑ ρ ∈ nontrivialZetaZerosUpTo U, resZeroRho y ρ).re

/-- Bound on `|psi1ContourRemainder y U|` for `1 ≤ y`, `0 < U`, `-1 / 2 < a < 0`. -/
theorem abs_psi1ContourRemainder_le_of_neg
    {y U a : ℝ} (hy : 1 ≤ y) (hU : 0 < U) (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    |psi1ContourRemainder y U| ≤
      2 * y ^ (3 : ℝ) / (Real.pi * U) + contourBoundaryError y a U := by
  unfold psi1ContourRemainder contourBoundaryError
  rw [sum_resZeroRho_eq]
  exact abs_psi1_sub_main_add_log_two_pi_sub_zeroSum_le_of_neg hy hU ha ha_neg h_no_horiz

/-- **Exact Difference Quotient Decomposition of `(psi1 (x₁ + h) - psi1 x₁) / h`**:
For `h ≠ 0`,
$$\frac{\psi_1(x_1 + h) - \psi_1(x_1)}{h} - \left(x_1 + \frac{h}{2}\right)
  = -\log(2\pi)
    + \left(-\sum_{\rho \in \mathcal{Z}(U)} (m_\rho : \mathbb{C}) \cdot
    \text{smoothedZeroTerm}(x_1, h, \rho)\right).\text{re}
    + \frac{\text{psi1ContourRemainder}(x_1 + h, U) - \text{psi1ContourRemainder}(x_1, U)}{h}.$$ -/
theorem psi1_add_sub_div_sub_linear_eq {x₁ h U : ℝ} (hh : h ≠ 0) :
    (psi1 (x₁ + h) - psi1 x₁) / h - (x₁ + h / 2) =
      -Real.log (2 * Real.pi) +
        (-(∑ ρ ∈ nontrivialZetaZerosUpTo U,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ)).re +
        (psi1ContourRemainder (x₁ + h) U - psi1ContourRemainder x₁ U) / h := by
  have h_zero := re_sum_resZeroRho_add_sub_div x₁ h (nontrivialZetaZerosUpTo U)
  unfold psi1ContourRemainder
  rw [← h_zero]
  field_simp [hh]
  ring

/-- **Difference Quotient Error Bound on `[x₁, x₁ + h]` (`1 ≤ x₁`, `0 < h`) under
`RiemannHypothesis`**:
Taking the difference quotient before taking norms bounds
`|(psi1 (x₁ + h) - psi1 x₁) / h - (x₁ + h / 2)|` by `Real.log (2 * Real.pi)` plus the low/high
frequency zero sums and the contour difference error. -/
theorem abs_psi1_add_sub_div_sub_linear_le_of_neg
    (hRH : RiemannHypothesis) {x₁ h T U a : ℝ}
    (hx₁ : 1 ≤ x₁) (hh : 0 < h) (hT : 0 < T) (hTU : T ≤ U)
    (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    |(psi1 (x₁ + h) - psi1 x₁) / h - (x₁ + h / 2)| ≤
      Real.log (2 * Real.pi) +
        Real.sqrt (x₁ + h) *
          (∑ ρ ∈ nontrivialZetaZerosUpTo T,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) +
        (2 * (x₁ + h) ^ (3 / 2 : ℝ) / h) *
          (∑ ρ ∈ nontrivialZetaZerosBetween T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) +
        (4 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * h * U) +
          (contourBoundaryError (x₁ + h) a U + contourBoundaryError x₁ a U) / h) := by
  have hU : 0 < U := hT.trans_le hTU
  have hx₁_pos : 0 < x₁ := zero_lt_one.trans_le hx₁
  have hx₂ : 1 ≤ x₁ + h := by linarith
  rw [psi1_add_sub_div_sub_linear_eq hh.ne']
  set Z : ℂ := ∑ ρ ∈ nontrivialZetaZerosUpTo U,
    (analyticOrderNatAt riemannZeta ρ : ℂ) * smoothedZeroTerm x₁ h ρ
  set R_diff : ℝ := (psi1ContourRemainder (x₁ + h) U - psi1ContourRemainder x₁ U) / h
  have htri : |-Real.log (2 * Real.pi) + (-Z).re + R_diff| ≤
      |-Real.log (2 * Real.pi)| + |(-Z).re| + |R_diff| := by
    exact (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
  have hpi : 1 ≤ Real.pi := Real.two_le_pi.trans' one_le_two
  have hlog_pos : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith)
  have h1 : |-Real.log (2 * Real.pi)| = Real.log (2 * Real.pi) := by
    rw [abs_neg, abs_of_nonneg hlog_pos]
  have h2 : |(-Z).re| ≤
      Real.sqrt (x₁ + h) *
        (∑ ρ ∈ nontrivialZetaZerosUpTo T,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) +
      (2 * (x₁ + h) ^ (3 / 2 : ℝ) / h) *
        (∑ ρ ∈ nontrivialZetaZerosBetween T U,
          (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) := by
    calc
      |(-Z).re| ≤ ‖-Z‖ := Complex.abs_re_le_norm (-Z)
      _ = ‖Z‖ := norm_neg Z
      _ ≤ _ := norm_sum_smoothedZeroTerm_le_of_riemannHypothesis hRH hx₁_pos hh hT hTU
  have hR₁ := abs_psi1ContourRemainder_le_of_neg hx₁ hU ha ha_neg h_no_horiz
  have hR₂ := abs_psi1ContourRemainder_le_of_neg hx₂ hU ha ha_neg h_no_horiz
  have hrpow_le : x₁ ^ (3 : ℝ) ≤ (x₁ + h) ^ (3 : ℝ) :=
    Real.rpow_le_rpow hx₁_pos.le (by linarith) (by norm_num)
  have htail_le : 2 * x₁ ^ (3 : ℝ) / (Real.pi * U) ≤ 2 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * U) := by
    gcongr
  have h3 : |R_diff| ≤
      4 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * h * U) +
        (contourBoundaryError (x₁ + h) a U + contourBoundaryError x₁ a U) / h := by
    dsimp [R_diff]
    rw [abs_div, abs_of_pos hh]
    have hsub : |psi1ContourRemainder (x₁ + h) U - psi1ContourRemainder x₁ U| ≤
        |psi1ContourRemainder (x₁ + h) U| + |psi1ContourRemainder x₁ U| := abs_sub _ _
    have h4 : 2 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * U) + 2 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * U) =
        4 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * U) := by ring
    have hsum : |psi1ContourRemainder (x₁ + h) U| + |psi1ContourRemainder x₁ U| ≤
        4 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * U) +
          (contourBoundaryError (x₁ + h) a U + contourBoundaryError x₁ a U) := by
      linarith
    calc
      |psi1ContourRemainder (x₁ + h) U - psi1ContourRemainder x₁ U| / h
        ≤ (4 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * U) +
            (contourBoundaryError (x₁ + h) a U + contourBoundaryError x₁ a U)) / h :=
          div_le_div_of_nonneg_right (hsub.trans hsum) hh.le
      _ = 4 * (x₁ + h) ^ (3 : ℝ) / (Real.pi * h * U) +
            (contourBoundaryError (x₁ + h) a U + contourBoundaryError x₁ a U) / h := by
          rw [add_div, div_div]
          ring
  linarith

/-- **Difference Quotient Contour Shift & Low/High Frequency Split Theorem**:
Combining the forward difference quotient on `[x, x + h]` and the backward difference quotient on
`[x - h, x]` (`1 ≤ x - h`, `0 < h`) with the monotonicity sandwich for `ψ` and the low/high
frequency zero split at cutoff `T` (`0 < T ≤ U`) proves:
$$|\psi(x) - x| \le \frac{h}{2} + \log(2\pi)
  + \sqrt{x + h} \sum_{\rho \in \mathcal{Z}(T)} \frac{m_\rho}{\|\rho\|}
  + \frac{2 (x + h)^{3/2}}{h} \sum_{\rho \in \mathcal{Z}(T, U)} \frac{m_\rho}{|\rho.\text{im}|^2}
  + \text{contourDiffError}(x, h, a, U).$$ -/
theorem abs_psi_sub_self_le_smoothed_contour_shift
    (hRH : RiemannHypothesis) {x h T U a : ℝ}
    (hx_sub : 1 ≤ x - h) (hh : 0 < h) (hT : 0 < T) (hTU : T ≤ U)
    (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          (∑ ρ ∈ nontrivialZetaZerosUpTo T,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) +
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          (∑ ρ ∈ nontrivialZetaZerosBetween T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) +
        contourDiffError x h a U := by
  have hx : 1 ≤ x := by linarith
  have hx_pos : 0 < x := zero_lt_one.trans_le hx
  have hU : 0 < U := hT.trans_le hTU
  set S_low : ℝ := ∑ ρ ∈ nontrivialZetaZerosUpTo T,
    (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖
  set S_high : ℝ := ∑ ρ ∈ nontrivialZetaZerosBetween T U,
    (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2
  have hS_low_nonneg : 0 ≤ S_low :=
    sum_nonneg fun ρ _ ↦ div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hS_high_nonneg : 0 ≤ S_high :=
    sum_nonneg fun ρ _ ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · -- Forward difference on `[x, x + h]`: bounds `Chebyshev.psi x - x`
    have h_sand := psi_le_psi1_add_sub_div x hh
    have h_fwd := abs_psi1_add_sub_div_sub_linear_le_of_neg hRH hx hh hT hTU ha ha_neg h_no_horiz
    have h_fwd_upper : (psi1 (x + h) - psi1 x) / h - (x + h / 2) ≤
        Real.log (2 * Real.pi) + Real.sqrt (x + h) * S_low +
          (2 * (x + h) ^ (3 / 2 : ℝ) / h) * S_high +
          (4 * (x + h) ^ (3 : ℝ) / (Real.pi * h * U) +
            (contourBoundaryError (x + h) a U + contourBoundaryError x a U) / h) :=
      (le_abs_self _).trans h_fwd
    have h_max : (contourBoundaryError (x + h) a U + contourBoundaryError x a U) / h ≤
        max ((contourBoundaryError (x + h) a U + contourBoundaryError x a U) / h)
          ((contourBoundaryError x a U + contourBoundaryError (x - h) a U) / h) :=
      le_max_left _ _
    unfold contourDiffError
    linarith
  · -- Backward difference on `[x - h, x]`: bounds `x - Chebyshev.psi x`
    have h_sand := psi1_sub_psi1_sub_div_le_psi x hh
    have h_bwd :=
      abs_psi1_add_sub_div_sub_linear_le_of_neg hRH hx_sub hh hT hTU ha ha_neg h_no_horiz
    have hx_add : x - h + h = x := sub_add_cancel x h
    rw [hx_add] at h_bwd
    have h_bwd_lower : -(Real.log (2 * Real.pi) + Real.sqrt x * S_low +
          (2 * x ^ (3 / 2 : ℝ) / h) * S_high +
          (4 * x ^ (3 : ℝ) / (Real.pi * h * U) +
            (contourBoundaryError x a U + contourBoundaryError (x - h) a U) / h)) ≤
        (psi1 x - psi1 (x - h)) / h - (x - h + h / 2) :=
      neg_le_of_abs_le h_bwd
    have h_sqrt_le : Real.sqrt x * S_low ≤ Real.sqrt (x + h) * S_low :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith)) hS_low_nonneg
    have h_rpow32_le : (2 * x ^ (3 / 2 : ℝ) / h) * S_high ≤
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) * S_high := by
      gcongr
      linarith
    have h_rpow3_le : 4 * x ^ (3 : ℝ) / (Real.pi * h * U) ≤
        4 * (x + h) ^ (3 : ℝ) / (Real.pi * h * U) := by
      gcongr
      linarith
    have h_max : (contourBoundaryError x a U + contourBoundaryError (x - h) a U) / h ≤
        max ((contourBoundaryError (x + h) a U + contourBoundaryError x a U) / h)
          ((contourBoundaryError x a U + contourBoundaryError (x - h) a U) / h) :=
      le_max_right _ _
    unfold contourDiffError
    linarith

/-!
## Section 1: Fourth-Order Euler–Maclaurin Identity & Low-Lying Zero-Free Region `|ρ.im| > 6`
-/

/-!
## Section 5: Multiplicity-Weighted Stieltjes Bounds (`weightedZeroCountingFunction`) & Asymptotic
Limit `U → ∞`
-/

/-- `weightedZeroCountingFunction` is monotone. -/
theorem weightedZeroCountingFunction_mono : Monotone weightedZeroCountingFunction := by
  intro t T htT
  unfold weightedZeroCountingFunction
  exact Finset.sum_le_sum_of_subset (nontrivialZetaZerosUpTo_subset_of_le htT)

/-- Under `RiemannHypothesis`, `weightedZeroCountingFunction 6 = 0`. -/
theorem weightedZeroCountingFunction_six_eq_zero (hRH : RiemannHypothesis) :
    weightedZeroCountingFunction 6 = 0 :=
  weightedZeroCountingFunction_eq_zero_of_le_six hRH le_rfl

/-- Whenever `weightedZeroCountingFunction t₀ = 0`, `nontrivialZetaZerosUpTo t₀ = ∅`. -/
theorem nontrivialZetaZerosUpTo_eq_empty_of_weightedZeroCountingFunction_eq_zero
    {t₀ : ℝ} (h0 : weightedZeroCountingFunction t₀ = 0) :
    nontrivialZetaZerosUpTo t₀ = ∅ := by
  unfold weightedZeroCountingFunction at h0
  rw [Finset.sum_eq_zero_iff] at h0
  rw [Finset.eq_empty_iff_forall_notMem]
  intro ρ hρ
  have h1 := one_le_analyticOrderNatAt_of_isNontrivialZetaZero
    (mem_nontrivialZetaZerosUpTo.mp hρ).1
  have h_zero := h0 ρ hρ
  omega

/-- Whenever `weightedZeroCountingFunction t₀ = 0`, `nontrivialZetaZerosUpTo T` coincides with
`nontrivialZetaZerosBetween t₀ T`. -/
theorem nontrivialZetaZerosUpTo_eq_between_of_weightedZeroCountingFunction_eq_zero
    {t₀ T : ℝ} (h0 : weightedZeroCountingFunction t₀ = 0) :
    nontrivialZetaZerosUpTo T = nontrivialZetaZerosBetween t₀ T := by
  have hempty := nontrivialZetaZerosUpTo_eq_empty_of_weightedZeroCountingFunction_eq_zero h0
  ext ρ
  simp only [mem_nontrivialZetaZerosUpTo, mem_nontrivialZetaZerosBetween]
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, h2, ?_⟩, fun ⟨h1, h2, _⟩ ↦ ⟨h1, h2⟩⟩
  by_contra! hle
  have hmem : ρ ∈ nontrivialZetaZerosUpTo t₀ := mem_nontrivialZetaZerosUpTo.mpr ⟨h1, hle⟩
  rw [hempty] at hmem
  exact Finset.notMem_empty ρ hmem

/-- For `T ≤ U`, the multiplicity sum over `nontrivialZetaZerosBetween T U` plus
`weightedZeroCountingFunction T` equals `weightedZeroCountingFunction U`. -/
theorem sum_weighted_nontrivialZetaZerosBetween_add_eq {T U : ℝ} (hTU : T ≤ U) :
    (∑ ρ ∈ nontrivialZetaZerosBetween T U, analyticOrderNatAt riemannZeta ρ) +
      weightedZeroCountingFunction T =
      weightedZeroCountingFunction U := by
  unfold nontrivialZetaZerosBetween weightedZeroCountingFunction
  rw [← filter_not_lt_abs_im_nontrivialZetaZerosUpTo hTU]
  exact sum_filter_add_sum_filter_not (nontrivialZetaZerosUpTo U) (fun ρ : ℂ ↦ T < |ρ.im|) _

/-- Real-cast version of `sum_weighted_nontrivialZetaZerosBetween_add_eq`. -/
theorem sum_weighted_nontrivialZetaZerosBetween_real {T U : ℝ} (hTU : T ≤ U) :
    (∑ ρ ∈ nontrivialZetaZerosBetween T U, (analyticOrderNatAt riemannZeta ρ : ℝ)) =
      (weightedZeroCountingFunction U : ℝ) - (weightedZeroCountingFunction T : ℝ) := by
  have h :
      (∑ ρ ∈ nontrivialZetaZerosBetween T U, (analyticOrderNatAt riemannZeta ρ : ℝ)) +
        (weightedZeroCountingFunction T : ℝ) =
        (weightedZeroCountingFunction U : ℝ) := by
    exact_mod_cast sum_weighted_nontrivialZetaZerosBetween_add_eq hTU
  linarith

/-- For `T ≤ t ≤ U`, the multiplicity-weighted indicator sum equals
`(weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ)`. -/
theorem sum_ite_abs_im_le_weighted_nontrivialZetaZerosBetween {T t U : ℝ}
    (hTt : T ≤ t) (htU : t ≤ U) :
    (∑ ρ ∈ nontrivialZetaZerosBetween T U,
      if |ρ.im| ≤ t then (analyticOrderNatAt riemannZeta ρ : ℝ) else 0) =
      (weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ) := by
  rw [← sum_filter, filter_abs_im_le_nontrivialZetaZerosBetween htU,
    sum_weighted_nontrivialZetaZerosBetween_real hTt]

/-- Pointwise decomposition of
`((weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g' t`
on `Set.Ioc T U` as a finite sum of weighted indicator functions over `nontrivialZetaZerosBetween T
U`. -/
theorem eqOn_sub_weightedZeroCountingFunction_mul_sum_indicator {T U : ℝ} (g' : ℝ → ℝ) :
    Set.EqOn
      (fun t : ℝ ↦
        ((weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g' t)
      (fun t : ℝ ↦
        ∑ ρ ∈ nontrivialZetaZerosBetween T U,
          (analyticOrderNatAt riemannZeta ρ : ℝ) * (Set.Ici |ρ.im|).indicator g' t)
      (Set.Ioc T U) := by
  intro t ht
  dsimp only
  rw [← sum_ite_abs_im_le_weighted_nontrivialZetaZerosBetween ht.1.le ht.2, sum_mul]
  refine sum_congr rfl fun ρ _ ↦ ?_
  simp only [Set.indicator, Set.mem_Ici]
  split_ifs <;> ring

/-- If `g'` is continuous on `Set.Icc T U` (`T ≤ U`), then
`fun t ↦ (weightedZeroCountingFunction t : ℝ) * g' t` is `IntervalIntegrable` on `T..U`. -/
theorem intervalIntegrable_weightedZeroCountingFunction_mul {T U : ℝ} (hTU : T ≤ U)
    {g' : ℝ → ℝ} (hcont : ContinuousOn g' (Set.Icc T U)) :
    IntervalIntegrable
      (fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) * g' t) volume T U := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hTU]
  have h_sub_int :
      IntegrableOn
        (fun t : ℝ ↦
          ((weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g' t)
        (Set.Ioc T U) := by
    refine IntegrableOn.congr_fun ?_
      (eqOn_sub_weightedZeroCountingFunction_mul_sum_indicator g').symm measurableSet_Ioc
    exact integrable_finsetSum (nontrivialZetaZerosBetween T U) fun ρ hρ ↦
      (integrableOn_indicator_of_continuousOn
        (mem_nontrivialZetaZerosBetween.mp hρ).2.2 hcont).const_mul _
  have h_const_int :
      IntegrableOn (fun t : ℝ ↦ (weightedZeroCountingFunction T : ℝ) * g' t) (Set.Ioc T U) :=
    (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).const_mul _
  have h_add := h_sub_int.add h_const_int
  refine h_add.congr_fun (fun t _ ↦ ?_) measurableSet_Ioc
  simp only [Pi.add_apply]
  ring

/-- **Multiplicity-Weighted Stieltjes Integration-by-Parts Identity**:
For any `T ≤ U` and any `g, g' : ℝ → ℝ` with `HasDerivAt g (g' t) t` on `Set.Icc T U` and
`ContinuousOn g' (Set.Icc T U)`,
$$\sum_{\rho \in \mathcal{Z}(T, U)} m_\rho \, g(|\operatorname{Im} \rho|)
  = N_{\text{mult}}(U) g(U) - N_{\text{mult}}(T) g(T) - \int_T^U N_{\text{mult}}(t) g'(t) \, dt.$$
-/
theorem sum_weighted_nontrivialZetaZerosBetween_eq_stieltjes {T U : ℝ} (hTU : T ≤ U)
    {g g' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc T U, HasDerivAt g (g' t) t)
    (hcont : ContinuousOn g' (Set.Icc T U)) :
    (∑ ρ ∈ nontrivialZetaZerosBetween T U,
      (analyticOrderNatAt riemannZeta ρ : ℝ) * g |ρ.im|) =
      (weightedZeroCountingFunction U : ℝ) * g U -
        (weightedZeroCountingFunction T : ℝ) * g T -
        ∫ t in T..U, (weightedZeroCountingFunction t : ℝ) * g' t := by
  have h_ind_int :
      (∫ t in Set.Ioc T U,
          ((weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g' t) =
        ((weightedZeroCountingFunction U : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g U -
          ∑ ρ ∈ nontrivialZetaZerosBetween T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) * g |ρ.im| := by
    rw [setIntegral_congr_fun measurableSet_Ioc
        (eqOn_sub_weightedZeroCountingFunction_mul_sum_indicator g'),
      integral_finsetSum (nontrivialZetaZerosBetween T U) fun ρ hρ ↦
        (integrableOn_indicator_of_continuousOn
          (mem_nontrivialZetaZerosBetween.mp hρ).2.2 hcont).const_mul _]
    calc
      (∑ ρ ∈ nontrivialZetaZerosBetween T U,
          ∫ t in Set.Ioc T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) * (Set.Ici |ρ.im|).indicator g' t)
        = ∑ ρ ∈ nontrivialZetaZerosBetween T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) * (g U - g |ρ.im|) := by
          refine sum_congr rfl fun ρ hρ ↦ ?_
          rw [integral_const_mul, setIntegral_indicator_deriv_eq_sub
            (mem_nontrivialZetaZerosBetween.mp hρ).2.2
            (mem_nontrivialZetaZerosBetween.mp hρ).2.1 hderiv hcont]
      _ = (∑ ρ ∈ nontrivialZetaZerosBetween T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) * g U) -
          ∑ ρ ∈ nontrivialZetaZerosBetween T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) * g |ρ.im| := by
          rw [← sum_sub_distrib]
          refine sum_congr rfl fun ρ _ ↦ by ring
      _ = ((weightedZeroCountingFunction U : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g U -
            ∑ ρ ∈ nontrivialZetaZerosBetween T U,
              (analyticOrderNatAt riemannZeta ρ : ℝ) * g |ρ.im| := by
          rw [← sum_mul, sum_weighted_nontrivialZetaZerosBetween_real hTU]
  have h_ftc : (∫ t in T..U, g' t) = g U - g T := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt ?_ ?_
    · intro t ht
      rw [Set.uIcc_of_le hTU] at ht
      exact hderiv t ht
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hTU]
      exact hcont.integrableOn_Icc
  have h_int_g' : IntervalIntegrable g' volume T U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hTU]
    exact hcont.integrableOn_Icc
  have h_int_N :
      IntervalIntegrable
        (fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) * g' t) volume T U :=
    intervalIntegrable_weightedZeroCountingFunction_mul hTU hcont
  have h_split :
      (∫ t in Set.Ioc T U,
          ((weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g' t) =
        (∫ t in T..U, (weightedZeroCountingFunction t : ℝ) * g' t) -
          (weightedZeroCountingFunction T : ℝ) * (g U - g T) := by
    rw [← intervalIntegral.integral_of_le hTU]
    have h_sub_fn :
        (fun t : ℝ ↦
            ((weightedZeroCountingFunction t : ℝ) - (weightedZeroCountingFunction T : ℝ)) * g' t) =
          fun t : ℝ ↦
            (weightedZeroCountingFunction t : ℝ) * g' t -
              (weightedZeroCountingFunction T : ℝ) * g' t := by
      ext t; ring
    rw [h_sub_fn, intervalIntegral.integral_sub h_int_N (h_int_g'.const_mul _),
      intervalIntegral.integral_const_mul, h_ftc]
  linarith

/-- Derivative of `1 / t ^ 2` at `t ≠ 0` is `-2 / t ^ 3`. -/
theorem hasDerivAt_one_div_sq {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ 1 / x ^ 2) (-2 / t ^ 3) t := by
  have hd : HasDerivAt (fun x : ℝ ↦ (x ^ 2)⁻¹) (-(2 * t ^ (2 - 1)) / (t ^ 2) ^ 2) t :=
    (hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht)
  simp only [one_div]
  refine hd.congr_deriv ?_
  field_simp [ht]
  ring

/-- **Multiplicity-Weighted Stieltjes Identity for $\sum_{t_0 < |\gamma| \le T}
\frac{m_\rho}{|\gamma|}$**:
For `0 < t₀ ≤ T`,
$$\sum_{\rho \in \mathcal{Z}(t_0, T)} \frac{m_\rho}{|\operatorname{Im} \rho|}
  = \frac{N_{\text{mult}}(T)}{T} - \frac{N_{\text{mult}}(t_0)}{t_0}
    + \int_{t_0}^T \frac{N_{\text{mult}}(t)}{t^2} \, dt.$$ -/
theorem sum_weighted_inv_abs_im_nontrivialZetaZerosBetween_eq
    {t₀ T : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) :
    (∑ ρ ∈ nontrivialZetaZerosBetween t₀ T,
      (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im|) =
      (weightedZeroCountingFunction T : ℝ) / T -
        (weightedZeroCountingFunction t₀ : ℝ) / t₀ +
        ∫ t in t₀..T, (weightedZeroCountingFunction t : ℝ) / t ^ 2 := by
  have hderiv : ∀ t ∈ Set.Icc t₀ T, HasDerivAt (fun x : ℝ ↦ 1 / x) (-1 / t ^ 2) t :=
    fun t ht ↦ hasDerivAt_one_div (ht₀.trans_le ht.1).ne'
  have hcont : ContinuousOn (fun t : ℝ ↦ -1 / t ^ 2) (Set.Icc t₀ T) := by
    refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    exact continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 ht_pos.ne')
  have h_eq :
      (∑ ρ ∈ nontrivialZetaZerosBetween t₀ T,
        (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im|) =
      ∑ ρ ∈ nontrivialZetaZerosBetween t₀ T,
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / |ρ.im|) := by
    refine sum_congr rfl fun ρ _ ↦ by ring
  rw [h_eq, sum_weighted_nontrivialZetaZerosBetween_eq_stieltjes ht₀T hderiv hcont]
  have h_pull :
      (∫ t in t₀..T, (weightedZeroCountingFunction t : ℝ) * (-1 / t ^ 2)) =
        -(∫ t in t₀..T, (weightedZeroCountingFunction t : ℝ) / t ^ 2) := by
    have h_fn :
        (fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) * (-1 / t ^ 2)) =
          fun t : ℝ ↦ -((weightedZeroCountingFunction t : ℝ) / t ^ 2) := by
      ext t; ring
    rw [h_fn, intervalIntegral.integral_neg]
  rw [h_pull]
  ring

/-- **Multiplicity-Weighted Low-Frequency Stieltjes Identity for `nontrivialZetaZerosUpTo T`**:
Whenever `0 < t₀ ≤ T` and `weightedZeroCountingFunction t₀ = 0`,
$$\sum_{\rho \in \mathcal{Z}(T)} \frac{m_\rho}{|\operatorname{Im} \rho|}
  = \frac{N_{\text{mult}}(T)}{T} + \int_{t_0}^T \frac{N_{\text{mult}}(t)}{t^2} \, dt.$$ -/
theorem sum_weighted_inv_abs_im_nontrivialZetaZerosUpTo_eq
    {t₀ T : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (h0 : weightedZeroCountingFunction t₀ = 0) :
    (∑ ρ ∈ nontrivialZetaZerosUpTo T,
      (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im|) =
      (weightedZeroCountingFunction T : ℝ) / T +
        ∫ t in t₀..T, (weightedZeroCountingFunction t : ℝ) / t ^ 2 := by
  rw [nontrivialZetaZerosUpTo_eq_between_of_weightedZeroCountingFunction_eq_zero h0,
    sum_weighted_inv_abs_im_nontrivialZetaZerosBetween_eq ht₀ ht₀T, h0]
  simp

/-- `(fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) / t ^ 2)` is `IntervalIntegrable` on `t₀..T`
for `0 < t₀ ≤ T`. -/
theorem intervalIntegrable_weightedZeroCountingFunction_div_sq {t₀ T : ℝ}
    (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) :
    IntervalIntegrable (fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) / t ^ 2) volume t₀ T := by
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / t ^ 2) (Set.Icc t₀ T) := by
    refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    exact continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 ht_pos.ne')
  have h := intervalIntegrable_weightedZeroCountingFunction_mul ht₀T hcont
  simpa only [mul_one_div] using h

/-- Whenever `0 < t₀` and `weightedZeroCountingFunction t₀ = 0`, every `ρ ∈ nontrivialZetaZerosUpTo
T`
satisfies `(analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) /
|ρ.im|`. -/
theorem sum_weighted_inv_norm_le_sum_weighted_inv_abs_im_nontrivialZetaZerosUpTo
    {t₀ T : ℝ} (ht₀ : 0 < t₀) (h0 : weightedZeroCountingFunction t₀ = 0) :
    (∑ ρ ∈ nontrivialZetaZerosUpTo T, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) ≤
      ∑ ρ ∈ nontrivialZetaZerosUpTo T, (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| := by
  rw [nontrivialZetaZerosUpTo_eq_between_of_weightedZeroCountingFunction_eq_zero h0]
  refine Finset.sum_le_sum fun ρ hρ ↦ ?_
  have him_gt : t₀ < |ρ.im| := (mem_nontrivialZetaZerosBetween.mp hρ).2.2
  have him_pos : 0 < |ρ.im| := ht₀.trans him_gt
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) him_pos (Complex.abs_im_le_norm ρ)

/-- **Multiplicity-Weighted Low-Frequency Stieltjes Bound on $\sum_{\rho \in \mathcal{Z}(T)}
\frac{m_\rho}{\|\rho\|}$**:
If `0 < t₀ ≤ T`, `weightedZeroCountingFunction t₀ = 0`, and
`(weightedZeroCountingFunction t : ℝ) ≤ a * t * Real.log t + C * t + D` for all `t ∈ Set.Icc t₀ T`,
then:
$$\sum_{\rho \in \text{nontrivialZetaZerosUpTo } T} \frac{m_\rho}{\|\rho\|}
  \le \frac{a}{2} (\log T)^2 + (a + C) \log T + C + \frac{D}{t_0}
      - \frac{a}{2} (\log t_0)^2 - C \log t_0.$$ -/
theorem sum_weighted_inv_norm_nontrivialZetaZerosUpTo_le_of_riemannVonMangoldt
    {t₀ T a C D : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (h0 : weightedZeroCountingFunction t₀ = 0)
    (hN_bound : ∀ t ∈ Set.Icc t₀ T,
      (weightedZeroCountingFunction t : ℝ) ≤ a * t * Real.log t + C * t + D) :
    (∑ ρ ∈ nontrivialZetaZerosUpTo T,
      (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) ≤
      a / 2 * (Real.log T) ^ 2 + (a + C) * Real.log T + C + D / t₀ -
        a / 2 * (Real.log t₀) ^ 2 - C * Real.log t₀ := by
  have hT_pos : 0 < T := ht₀.trans_le ht₀T
  have hT_ne : T ≠ 0 := hT_pos.ne'
  refine (sum_weighted_inv_norm_le_sum_weighted_inv_abs_im_nontrivialZetaZerosUpTo ht₀ h0).trans ?_
  rw [sum_weighted_inv_abs_im_nontrivialZetaZerosUpTo_eq ht₀ ht₀T h0]
  have hNT_le : (weightedZeroCountingFunction T : ℝ) / T ≤ a * Real.log T + C + D / T := by
    have hT_in : T ∈ Set.Icc t₀ T := ⟨ht₀T, le_rfl⟩
    have h1 : (weightedZeroCountingFunction T : ℝ) / T ≤
        (a * T * Real.log T + C * T + D) / T :=
      div_le_div_of_nonneg_right (hN_bound T hT_in) hT_pos.le
    have h2 : (a * T * Real.log T + C * T + D) / T = a * Real.log T + C + D / T := by
      field_simp [hT_ne]
    rwa [h2] at h1
  have hint_B :
      IntervalIntegrable (fun t : ℝ ↦ (a * t * Real.log t + C * t + D) / t ^ 2) volume t₀ T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht₀T]
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).integrableOn_Icc
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    have ht_ne : t ≠ 0 := ht_pos.ne'
    refine ContinuousAt.div ?_ (continuousAt_id.pow 2) (pow_ne_zero 2 ht_ne)
    exact (((continuousAt_const.mul continuousAt_id).mul (Real.continuousAt_log ht_ne)).add
      (continuousAt_const.mul continuousAt_id)).add continuousAt_const
  have hint_le :
      (∫ t in t₀..T, (weightedZeroCountingFunction t : ℝ) / t ^ 2) ≤
        (a / 2 * (Real.log T) ^ 2 + C * Real.log T - D / T) -
          (a / 2 * (Real.log t₀) ^ 2 + C * Real.log t₀ - D / t₀) := by
    rw [← intervalIntegral_riemannVonMangoldt_div_sq ht₀ ht₀T a C D]
    refine intervalIntegral.integral_mono_on ht₀T
      (intervalIntegrable_weightedZeroCountingFunction_div_sq ht₀ ht₀T) hint_B fun t ht ↦ ?_
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    exact div_le_div_of_nonneg_right (hN_bound t ht) (by positivity)
  linarith

/-- **Multiplicity-Weighted Stieltjes Identity for the Quadratic Zero Tail $\sum_{T < |\gamma| \le
U} \frac{m_\rho}{\gamma^2}$**:
For `0 < T ≤ U`,
$$\sum_{\rho \in \mathcal{Z}(T, U)} \frac{m_\rho}{|\operatorname{Im} \rho|^2}
  = \frac{N_{\text{mult}}(U)}{U^2} - \frac{N_{\text{mult}}(T)}{T^2}
    + 2 \int_T^U \frac{N_{\text{mult}}(t)}{t^3} \, dt.$$ -/
theorem sum_weighted_inv_sq_nontrivialZetaZerosBetween_eq {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U) :
    (∑ ρ ∈ nontrivialZetaZerosBetween T U,
      (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) =
      (weightedZeroCountingFunction U : ℝ) / U ^ 2 -
        (weightedZeroCountingFunction T : ℝ) / T ^ 2 +
        2 * ∫ t in T..U, (weightedZeroCountingFunction t : ℝ) / t ^ 3 := by
  have hderiv : ∀ t ∈ Set.Icc T U, HasDerivAt (fun x : ℝ ↦ 1 / x ^ 2) (-2 / t ^ 3) t :=
    fun t ht ↦ hasDerivAt_one_div_sq (hT.trans_le ht.1).ne'
  have hcont : ContinuousOn (fun t : ℝ ↦ -2 / t ^ 3) (Set.Icc T U) := by
    refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
    have ht_pos : 0 < t := hT.trans_le ht.1
    exact continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero 3 ht_pos.ne')
  have h_eq :
      (∑ ρ ∈ nontrivialZetaZerosBetween T U,
        (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) =
      ∑ ρ ∈ nontrivialZetaZerosBetween T U,
        (analyticOrderNatAt riemannZeta ρ : ℝ) * (1 / |ρ.im| ^ 2) := by
    refine sum_congr rfl fun ρ _ ↦ by ring
  rw [h_eq, sum_weighted_nontrivialZetaZerosBetween_eq_stieltjes hTU hderiv hcont]
  have h_pull :
      (∫ t in T..U, (weightedZeroCountingFunction t : ℝ) * (-2 / t ^ 3)) =
        -2 * ∫ t in T..U, (weightedZeroCountingFunction t : ℝ) / t ^ 3 := by
    have h_fn :
        (fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) * (-2 / t ^ 3)) =
          fun t : ℝ ↦ -2 * ((weightedZeroCountingFunction t : ℝ) / t ^ 3) := by
      ext t; ring
    rw [h_fn, intervalIntegral.integral_const_mul]
  rw [h_pull]
  ring

/-- `(fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) / t ^ 3)` is `IntervalIntegrable` on `T..U`
for `0 < T ≤ U`. -/
theorem intervalIntegrable_weightedZeroCountingFunction_div_cube {T U : ℝ}
    (hT : 0 < T) (hTU : T ≤ U) :
    IntervalIntegrable (fun t : ℝ ↦ (weightedZeroCountingFunction t : ℝ) / t ^ 3) volume T U := by
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / t ^ 3) (Set.Icc T U) := by
    refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
    have ht_pos : 0 < t := hT.trans_le ht.1
    exact continuousAt_const.div (continuousAt_id.pow 3) (pow_ne_zero 3 ht_pos.ne')
  have h := intervalIntegrable_weightedZeroCountingFunction_mul hTU hcont
  simpa only [mul_one_div] using h

/-- **Closed-Form Evaluation of the Cubic Riemann–von Mangoldt Stieltjes Integral**:
For `0 < T ≤ U` and any constants `a, C, D : ℝ`,
$$\int_T^U \frac{a t \log t + C t + D}{t^3} \, dt
  = \left(\frac{a \log T + a + C}{T} + \frac{D}{2 T^2}\right)
    - \left(\frac{a \log U + a + C}{U} + \frac{D}{2 U^2}\right).$$ -/
theorem intervalIntegral_riemannVonMangoldt_div_cube {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U)
    (a C D : ℝ) :
    (∫ t : ℝ in T..U, (a * t * Real.log t + C * t + D) / t ^ 3) =
      ((a * Real.log T + a + C) / T + D / (2 * T ^ 2)) -
        ((a * Real.log U + a + C) / U + D / (2 * U ^ 2)) := by
  have hderiv : ∀ t ∈ Set.uIcc T U,
      HasDerivAt (fun x : ℝ ↦ (-a * Real.log x - a - C) * x⁻¹ - (D / 2) * (x ^ 2)⁻¹)
        ((a * t * Real.log t + C * t + D) / t ^ 3) t := by
    intro t ht
    rw [Set.uIcc_of_le hTU] at ht
    have ht_pos : 0 < t := hT.trans_le ht.1
    have ht_ne : t ≠ 0 := ht_pos.ne'
    have hd1 : HasDerivAt (fun x : ℝ ↦ -a * Real.log x - a - C) (-a * t⁻¹) t :=
      (((Real.hasDerivAt_log ht_ne).const_mul (-a)).sub_const a).sub_const C
    have hd1_mul := hd1.mul (hasDerivAt_inv ht_ne)
    have hd2 : HasDerivAt (fun x : ℝ ↦ (D / 2) * (x ^ 2)⁻¹)
        ((D / 2) * (-(2 * t ^ (2 - 1)) / (t ^ 2) ^ 2)) t :=
      ((hasDerivAt_pow 2 t).inv (pow_ne_zero 2 ht_ne)).const_mul (D / 2)
    refine (hd1_mul.sub hd2).congr_deriv ?_
    field_simp [ht_ne]
    ring
  have hint :
      IntervalIntegrable (fun t : ℝ ↦ (a * t * Real.log t + C * t + D) / t ^ 3) volume T U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hTU]
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).integrableOn_Icc
    have ht_pos : 0 < t := hT.trans_le ht.1
    have ht_ne : t ≠ 0 := ht_pos.ne'
    refine ContinuousAt.div ?_ (continuousAt_id.pow 3) (pow_ne_zero 3 ht_ne)
    exact (((continuousAt_const.mul continuousAt_id).mul (Real.continuousAt_log ht_ne)).add
      (continuousAt_const.mul continuousAt_id)).add continuousAt_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- **Uniform Multiplicity-Weighted High-Frequency Quadratic Zero-Tail Bound**:
If `0 < T ≤ U`, `0 ≤ a`, `0 ≤ D`, and
`(weightedZeroCountingFunction t : ℝ) ≤ a * t * Real.log t + C * t + D` for all `t ∈ Set.Icc T U`,
then:
$$\sum_{\rho \in \mathcal{Z}(T, U)} \frac{m_\rho}{|\operatorname{Im} \rho|^2}
  \le \frac{2 a \log T + 2 a + 2 C}{T} + \frac{2 D}{T^2}$$
uniformly in `U` (completely independent of `U`!). -/
theorem sum_weighted_inv_sq_nontrivialZetaZerosBetween_le_of_riemannVonMangoldt
    {T U a C D : ℝ} (hT : 0 < T) (hTU : T ≤ U) (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hN_bound : ∀ t ∈ Set.Icc T U,
      (weightedZeroCountingFunction t : ℝ) ≤ a * t * Real.log t + C * t + D) :
    (∑ ρ ∈ nontrivialZetaZerosBetween T U,
      (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) ≤
      (2 * a * Real.log T + 2 * a + 2 * C) / T + 2 * D / T ^ 2 := by
  have hU_pos : 0 < U := hT.trans_le hTU
  have hU_ne : U ≠ 0 := hU_pos.ne'
  rw [sum_weighted_inv_sq_nontrivialZetaZerosBetween_eq hT hTU]
  have hNT_nonneg : 0 ≤ (weightedZeroCountingFunction T : ℝ) / T ^ 2 := by positivity
  have hNU_le : (weightedZeroCountingFunction U : ℝ) / U ^ 2 ≤
      (a * Real.log U + C) / U + D / U ^ 2 := by
    have hU_in : U ∈ Set.Icc T U := ⟨hTU, le_rfl⟩
    have h1 : (weightedZeroCountingFunction U : ℝ) / U ^ 2 ≤
        (a * U * Real.log U + C * U + D) / U ^ 2 :=
      div_le_div_of_nonneg_right (hN_bound U hU_in) (sq_nonneg U)
    have h2 : (a * U * Real.log U + C * U + D) / U ^ 2 =
        (a * Real.log U + C) / U + D / U ^ 2 := by
      field_simp [hU_ne]
    rwa [h2] at h1
  have hU_term_nonneg : 0 ≤ (a * Real.log U + C) / U + D / U ^ 2 :=
    (by positivity : 0 ≤ (weightedZeroCountingFunction U : ℝ) / U ^ 2).trans hNU_le
  have haU_nonneg : 0 ≤ 2 * a / U := by positivity
  have hD_le : D / U ^ 2 ≤ D / T ^ 2 := by
    gcongr
  have hint_B :
      IntervalIntegrable (fun t : ℝ ↦ (a * t * Real.log t + C * t + D) / t ^ 3) volume T U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hTU]
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).integrableOn_Icc
    have ht_pos : 0 < t := hT.trans_le ht.1
    have ht_ne : t ≠ 0 := ht_pos.ne'
    refine ContinuousAt.div ?_ (continuousAt_id.pow 3) (pow_ne_zero 3 ht_ne)
    exact (((continuousAt_const.mul continuousAt_id).mul (Real.continuousAt_log ht_ne)).add
      (continuousAt_const.mul continuousAt_id)).add continuousAt_const
  have hint_le :
      (∫ t in T..U, (weightedZeroCountingFunction t : ℝ) / t ^ 3) ≤
        ((a * Real.log T + a + C) / T + D / (2 * T ^ 2)) -
          ((a * Real.log U + a + C) / U + D / (2 * U ^ 2)) := by
    rw [← intervalIntegral_riemannVonMangoldt_div_cube hT hTU a C D]
    refine intervalIntegral.integral_mono_on hTU
      (intervalIntegrable_weightedZeroCountingFunction_div_cube hT hTU) hint_B fun t ht ↦ ?_
    have ht_pos : 0 < t := hT.trans_le ht.1
    exact div_le_div_of_nonneg_right (hN_bound t ht) (by positivity)
  have h_id :
      ((a * Real.log U + C) / U + D / U ^ 2) +
          2 * (((a * Real.log T + a + C) / T + D / (2 * T ^ 2)) -
            ((a * Real.log U + a + C) / U + D / (2 * U ^ 2))) =
        (2 * a * Real.log T + 2 * a + 2 * C) / T + D / T ^ 2 + D / U ^ 2 -
          ((a * Real.log U + C) / U + D / U ^ 2) - 2 * a / U := by
    field_simp [hT.ne', hU_ne]
    ring
  have h_two_D : D / T ^ 2 + D / T ^ 2 = 2 * D / T ^ 2 := by ring
  linarith

/-- **Contour-Shift Explicit Bound with Multiplicity-Weighted Riemann–von Mangoldt Zero Sums**:
Combining `abs_psi_sub_self_le_smoothed_contour_shift` with the multiplicity-weighted low-frequency
and high-frequency Stieltjes bounds replaces both zero sums by `U`-independent expressions, leaving
`contourDiffError x h a U` as the **only** `U`-dependent term! -/
theorem abs_psi_sub_self_le_weighted_riemannVonMangoldt_add_contourDiffError
    (hRH : RiemannHypothesis) {x h t₀ T U a a_rvM C D : ℝ}
    (hx_sub : 1 ≤ x - h) (hh : 0 < h) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (hTU : T ≤ U)
    (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h0 : weightedZeroCountingFunction t₀ = 0)
    (ha_rvM : 0 ≤ a_rvM) (hD : 0 ≤ D)
    (hN_bound : ∀ t ∈ Set.Icc t₀ U,
      (weightedZeroCountingFunction t : ℝ) ≤ a_rvM * t * Real.log t + C * t + D)
    (h_no_horiz : ∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / t₀ -
            a_rvM / 2 * (Real.log t₀) ^ 2 - C * Real.log t₀) +
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          ((2 * a_rvM * Real.log T + 2 * a_rvM + 2 * C) / T + 2 * D / T ^ 2) +
        contourDiffError x h a U := by
  have hT : 0 < T := ht₀.trans_le ht₀T
  have h_base :=
    abs_psi_sub_self_le_smoothed_contour_shift hRH hx_sub hh hT hTU ha ha_neg h_no_horiz
  have h_low := sum_weighted_inv_norm_nontrivialZetaZerosUpTo_le_of_riemannVonMangoldt
    ht₀ ht₀T h0 (fun t ht ↦ hN_bound t ⟨ht.1, ht.2.trans hTU⟩)
  have h_high := sum_weighted_inv_sq_nontrivialZetaZerosBetween_le_of_riemannVonMangoldt
    hT hTU ha_rvM hD (fun t ht ↦ hN_bound t ⟨ht₀T.trans ht.1, ht.2⟩)
  have h_low_mul :
      Real.sqrt (x + h) *
          (∑ ρ ∈ nontrivialZetaZerosUpTo T,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) ≤
        Real.sqrt (x + h) *
          (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / t₀ -
            a_rvM / 2 * (Real.log t₀) ^ 2 - C * Real.log t₀) :=
    mul_le_mul_of_nonneg_left h_low (Real.sqrt_nonneg _)
  have h_high_mul :
      (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          (∑ ρ ∈ nontrivialZetaZerosBetween T U,
            (analyticOrderNatAt riemannZeta ρ : ℝ) / |ρ.im| ^ 2) ≤
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          ((2 * a_rvM * Real.log T + 2 * a_rvM + 2 * C) / T + 2 * D / T ^ 2) := by
    have hxh_pos : 0 ≤ x + h := by linarith
    exact mul_le_mul_of_nonneg_left h_high (by positivity)
  linarith

/-- The left-vertical component of `contourBoundaryError y a U` along `Re s = a`. -/
noncomputable def contourLeftVerticalError (y a U : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ‖∫ t in (-U)..U, smoothedPerronIntegrand y (a + (t : ℂ) * I)‖

/-- The horizontal component of `contourBoundaryError y a U` along `[a, 2] ± i U`. -/
noncomputable def contourHorizontalError (y a U : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand y (σ + (U : ℂ) * I)‖ +
    (2 * Real.pi)⁻¹ * ‖∫ σ in a..2, smoothedPerronIntegrand y (σ - (U : ℂ) * I)‖

theorem contourBoundaryError_eq_leftVertical_add_horizontal (y a U : ℝ) :
    contourBoundaryError y a U =
      contourLeftVerticalError y a U + contourHorizontalError y a U := by
  unfold contourBoundaryError contourLeftVerticalError contourHorizontalError
  ring

/-- **Uniform `U`-Independent Bound on the Left-Vertical Integral**:
If `B_left : ℝ → ℝ` is integrable on `ℝ` and bounds `‖smoothedPerronIntegrand y (a + t * I)‖`
for all `t : ℝ`, then for all `U ≥ 0`,
`contourLeftVerticalError y a U ≤ (2 * Real.pi)⁻¹ * ∫ t : ℝ, B_left t` uniformly in `U`! -/
theorem contourLeftVerticalError_le_of_norm_le {y a U : ℝ} (hU : 0 ≤ U)
    {B_left : ℝ → ℝ} (hB_int : Integrable B_left)
    (hB_le : ∀ t : ℝ, ‖smoothedPerronIntegrand y (a + (t : ℂ) * I)‖ ≤ B_left t) :
    contourLeftVerticalError y a U ≤ (2 * Real.pi)⁻¹ * ∫ t : ℝ, B_left t := by
  unfold contourLeftVerticalError
  gcongr
  rw [intervalIntegral.integral_of_le (by linarith : -U ≤ U)]
  have h_ioc :
      ‖∫ t in Ioc (-U) U, smoothedPerronIntegrand y (a + (t : ℂ) * I)‖ ≤
        ∫ t in Ioc (-U) U, B_left t :=
    norm_integral_le_of_norm_le hB_int.integrableOn (ae_of_all _ hB_le)
  have hB_nonneg : 0 ≤ᵐ[volume] B_left :=
    ae_of_all _ fun t ↦ (norm_nonneg _).trans (hB_le t)
  exact h_ioc.trans (setIntegral_le_integral hB_int hB_nonneg)

/-- The left-vertical difference-quotient error across `[x - h, x]` and `[x, x + h]`. -/
noncomputable def contourLeftVerticalDiffError (x h a U : ℝ) : ℝ :=
  max ((contourLeftVerticalError (x + h) a U + contourLeftVerticalError x a U) / h)
    ((contourLeftVerticalError x a U + contourLeftVerticalError (x - h) a U) / h)

/-- The `U`-dependent vertical-tail and horizontal-segment part of `contourDiffError x h a U`
that vanishes along zero-free heights `U → ∞`. -/
noncomputable def contourTailAndHorizontalDiffError (x h a U : ℝ) : ℝ :=
  4 * (x + h) ^ (3 : ℝ) / (Real.pi * h * U) +
    max ((contourHorizontalError (x + h) a U + contourHorizontalError x a U) / h)
      ((contourHorizontalError x a U + contourHorizontalError (x - h) a U) / h)

/-- Subadditivity of `contourDiffError` into its left-vertical and tail+horizontal parts. -/
theorem contourDiffError_le_leftVertical_add_tailAndHorizontal (x h a U : ℝ) :
    contourDiffError x h a U ≤
      contourLeftVerticalDiffError x h a U + contourTailAndHorizontalDiffError x h a U := by
  unfold contourDiffError contourLeftVerticalDiffError contourTailAndHorizontalDiffError
  simp only [contourBoundaryError_eq_leftVertical_add_horizontal]
  set L_fwd := (contourLeftVerticalError (x + h) a U + contourLeftVerticalError x a U) / h
  set L_bwd := (contourLeftVerticalError x a U + contourLeftVerticalError (x - h) a U) / h
  set H_fwd := (contourHorizontalError (x + h) a U + contourHorizontalError x a U) / h
  set H_bwd := (contourHorizontalError x a U + contourHorizontalError (x - h) a U) / h
  have h_fwd_eq :
      (contourLeftVerticalError (x + h) a U + contourHorizontalError (x + h) a U +
        (contourLeftVerticalError x a U + contourHorizontalError x a U)) / h =
      L_fwd + H_fwd := by
    dsimp [L_fwd, H_fwd]
    ring
  have h_bwd_eq :
      (contourLeftVerticalError x a U + contourHorizontalError x a U +
        (contourLeftVerticalError (x - h) a U + contourHorizontalError (x - h) a U)) / h =
      L_bwd + H_bwd := by
    dsimp [L_bwd, H_bwd]
    ring
  rw [h_fwd_eq, h_bwd_eq]
  have hmax : max (L_fwd + H_fwd) (L_bwd + H_bwd) ≤ max L_fwd L_bwd + max H_fwd H_bwd := by
    refine max_le ?_ ?_
    · exact add_le_add (le_max_left _ _) (le_max_left _ _)
    · exact add_le_add (le_max_right _ _) (le_max_right _ _)
  linarith

/-- Uniform `U`-independent bound on `contourLeftVerticalDiffError x h a U` for `0 < h` and `0 ≤ U`
given integrable majorants `B_left y` on `Re s = a`. -/
theorem contourLeftVerticalDiffError_le_of_norm_le {x h a U : ℝ} (hh : 0 < h) (hU : 0 ≤ U)
    {B_left : ℝ → ℝ → ℝ}
    (hB_int_plus : Integrable (B_left (x + h)))
    (hB_int_x : Integrable (B_left x))
    (hB_int_minus : Integrable (B_left (x - h)))
    (hB_le_plus : ∀ t : ℝ, ‖smoothedPerronIntegrand (x + h) (a + (t : ℂ) * I)‖ ≤ B_left (x + h) t)
    (hB_le_x : ∀ t : ℝ, ‖smoothedPerronIntegrand x (a + (t : ℂ) * I)‖ ≤ B_left x t)
    (hB_le_minus : ∀ t : ℝ,
      ‖smoothedPerronIntegrand (x - h) (a + (t : ℂ) * I)‖ ≤ B_left (x - h) t) :
    contourLeftVerticalDiffError x h a U ≤
      max (((2 * Real.pi)⁻¹ * (∫ t : ℝ, B_left (x + h) t) +
            (2 * Real.pi)⁻¹ * (∫ t : ℝ, B_left x t)) / h)
        (((2 * Real.pi)⁻¹ * (∫ t : ℝ, B_left x t) +
            (2 * Real.pi)⁻¹ * (∫ t : ℝ, B_left (x - h) t)) / h) := by
  unfold contourLeftVerticalDiffError
  have h_plus := contourLeftVerticalError_le_of_norm_le hU hB_int_plus hB_le_plus
  have h_x := contourLeftVerticalError_le_of_norm_le hU hB_int_x hB_le_x
  have h_minus := contourLeftVerticalError_le_of_norm_le hU hB_int_minus hB_le_minus
  gcongr

/-- **Eliminating `U` by Arbitrarily Large Zero-Free Heights (`U → ∞` Limit Theorem)**:
If for every `ε > 0` there exists a zero-free height `U ≥ T` (`∀ ρ ∈ nontrivialZetaZerosUpTo U,
|ρ.im| < U`)
such that `contourDiffError x h a U ≤ E_left + ε`, then `|Chebyshev.psi x - x|` is bounded by the
`U`-independent explicit formula bound with only `E_left` remaining! -/
theorem abs_psi_sub_self_le_weighted_riemannVonMangoldt_of_forall_pos
    (hRH : RiemannHypothesis) {x h t₀ T a a_rvM C D E_left : ℝ}
    (hx_sub : 1 ≤ x - h) (hh : 0 < h) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h0 : weightedZeroCountingFunction t₀ = 0)
    (ha_rvM : 0 ≤ a_rvM) (hD : 0 ≤ D)
    (hN_bound : ∀ t ≥ t₀,
      (weightedZeroCountingFunction t : ℝ) ≤ a_rvM * t * Real.log t + C * t + D)
    (h_limit : ∀ ε > 0, ∃ U ≥ T,
      (∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) ∧
      contourDiffError x h a U ≤ E_left + ε) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / t₀ -
            a_rvM / 2 * (Real.log t₀) ^ 2 - C * Real.log t₀) +
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          ((2 * a_rvM * Real.log T + 2 * a_rvM + 2 * C) / T + 2 * D / T ^ 2) +
        E_left := by
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨U, hTU, h_no_horiz, h_err⟩ := h_limit ε hε
  have h_U := abs_psi_sub_self_le_weighted_riemannVonMangoldt_add_contourDiffError
    hRH hx_sub hh ht₀ ht₀T hTU ha ha_neg h0 ha_rvM hD
    (fun t ht ↦ hN_bound t ht.1) h_no_horiz
  linarith

/-- **Corollary Separating Uniform Left-Vertical Bound from Vanishing Tail + Horizontal Error**:
If `contourLeftVerticalDiffError x h a U ≤ E_left` for all `U ≥ T` and for every `ε > 0` there
exists a zero-free height `U ≥ T` with `contourTailAndHorizontalDiffError x h a U ≤ ε`, then
`|Chebyshev.psi x - x|` is bounded by the `U`-independent expression with `E_left`. -/
theorem abs_psi_sub_self_le_weighted_riemannVonMangoldt_add_left_vertical
    (hRH : RiemannHypothesis) {x h t₀ T a a_rvM C D E_left : ℝ}
    (hx_sub : 1 ≤ x - h) (hh : 0 < h) (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (ha : -1 / 2 < a) (ha_neg : a < 0)
    (h0 : weightedZeroCountingFunction t₀ = 0)
    (ha_rvM : 0 ≤ a_rvM) (hD : 0 ≤ D)
    (hN_bound : ∀ t ≥ t₀,
      (weightedZeroCountingFunction t : ℝ) ≤ a_rvM * t * Real.log t + C * t + D)
    (h_left : ∀ U ≥ T, contourLeftVerticalDiffError x h a U ≤ E_left)
    (h_tail_horiz : ∀ ε > 0, ∃ U ≥ T,
      (∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) ∧
      contourTailAndHorizontalDiffError x h a U ≤ ε) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / t₀ -
            a_rvM / 2 * (Real.log t₀) ^ 2 - C * Real.log t₀) +
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          ((2 * a_rvM * Real.log T + 2 * a_rvM + 2 * C) / T + 2 * D / T ^ 2) +
        E_left := by
  refine abs_psi_sub_self_le_weighted_riemannVonMangoldt_of_forall_pos
    hRH hx_sub hh ht₀ ht₀T ha ha_neg h0 ha_rvM hD hN_bound fun ε hε ↦ ?_
  obtain ⟨U, hTU, h_no_horiz, h_th⟩ := h_tail_horiz ε hε
  refine ⟨U, hTU, h_no_horiz, ?_⟩
  have h_split := contourDiffError_le_leftVertical_add_tailAndHorizontal x h a U
  have h_l := h_left U hTU
  linarith

/-- **Specialization to `t₀ = 6` under `RiemannHypothesis` (`weightedZeroCountingFunction 6 = 0`
discharged)**:
For `6 ≤ T`, `weightedZeroCountingFunction 6 = 0` holds unconditionally under `RiemannHypothesis`
by `weightedZeroCountingFunction_six_eq_zero hRH`. -/
theorem abs_psi_sub_self_le_weighted_riemannVonMangoldt_six_of_forall_pos
    (hRH : RiemannHypothesis) {x h T a a_rvM C D E_left : ℝ}
    (hx_sub : 1 ≤ x - h) (hh : 0 < h) (h6T : 6 ≤ T)
    (ha : -1 / 2 < a) (ha_neg : a < 0)
    (ha_rvM : 0 ≤ a_rvM) (hD : 0 ≤ D)
    (hN_bound : ∀ t ≥ 6,
      (weightedZeroCountingFunction t : ℝ) ≤ a_rvM * t * Real.log t + C * t + D)
    (h_limit : ∀ ε > 0, ∃ U ≥ T,
      (∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) ∧
      contourDiffError x h a U ≤ E_left + ε) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / 6 -
            a_rvM / 2 * (Real.log 6) ^ 2 - C * Real.log 6) +
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          ((2 * a_rvM * Real.log T + 2 * a_rvM + 2 * C) / T + 2 * D / T ^ 2) +
        E_left :=
  abs_psi_sub_self_le_weighted_riemannVonMangoldt_of_forall_pos
    hRH hx_sub hh (by norm_num) h6T ha ha_neg
    (weightedZeroCountingFunction_six_eq_zero hRH) ha_rvM hD hN_bound h_limit

/-!
## Section 6: Uniform Bound on `contourLeftVerticalError y (-1 / 4) U` & Horizontal Vanishing as `U
→ ∞`
-/

/-- On the line `Re s = -1 / 4`, `3 / 16 + t ^ 2 ≤ ‖((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I‖ * ‖((-1 / 4 :
ℝ) : ℂ) + (t : ℂ) * I + 1‖`. -/
theorem three_sixteenths_add_sq_le_norm_mul_neg_one_fourth (t : ℝ) :
    3 / 16 + t ^ 2 ≤
      ‖((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I‖ *
        ‖((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I + 1‖ := by
  set s : ℂ := ((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I
  have hs_sq : ‖s‖ ^ 2 = 1 / 16 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [s]
    ring
  have hs1_sq : ‖s + 1‖ ^ 2 = 9 / 16 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [s]
    ring
  rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow, hs_sq, hs1_sq]
  nlinarith [sq_nonneg t]

/-- For every `t : ℝ`,
`(|t| + 2) ^ 2 ≤ 32 * ‖(((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) * (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I +
1)‖`. -/
theorem sq_abs_add_two_le_thirty_two_mul_norm_neg_one_fourth (t : ℝ) :
    (|t| + 2) ^ 2 ≤
      32 * ‖(((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) *
        (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I + 1)‖ := by
  rw [norm_mul]
  have h1 := three_sixteenths_add_sq_le_norm_mul_neg_one_fourth t
  have h2 : (|t| + 2) ^ 2 ≤ 32 * (3 / 16 + t ^ 2) := by
    have h_abs_sq : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith [abs_nonneg t, sq_nonneg (5 * |t| - 1)]
  linarith

/-- On `Re s = -1 / 4`, for `0 < y` and `t : ℝ`,
`‖smoothedPerronKernel y ((-1 / 4 : ℝ) + (t : ℂ) * I)‖ ≤ 32 * y ^ (3 / 4 : ℝ) / (|t| + 2) ^ 2`. -/
theorem norm_smoothedPerronKernel_neg_one_fourth_le {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖smoothedPerronKernel y (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      32 * y ^ (3 / 4 : ℝ) / (|t| + 2) ^ 2 := by
  unfold smoothedPerronKernel
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : ((((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) + 1).re = 3 / 4 := by
    simp
    norm_num
  rw [hre]
  have hden := sq_abs_add_two_le_thirty_two_mul_norm_neg_one_fourth t
  have hpos_sq : 0 < (|t| + 2) ^ 2 := by positivity
  have hden_div : (|t| + 2) ^ 2 / 32 ≤
      ‖(((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) * (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I + 1)‖ := by
    linarith
  calc
    y ^ (3 / 4 : ℝ) /
        ‖(((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) * (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I + 1)‖
      ≤ y ^ (3 / 4 : ℝ) / ((|t| + 2) ^ 2 / 32) :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hy.le _) (by positivity) hden_div
    _ = 32 * y ^ (3 / 4 : ℝ) / (|t| + 2) ^ 2 := by
        rw [div_div_eq_mul_div]
        ring

/-- Pointwise bound on `‖smoothedPerronIntegrand y (-1 / 4 + t * I)‖` assuming a logarithmic bound
on `-ζ' / ζ` along `Re s = -1 / 4`. -/
theorem norm_smoothedPerronIntegrand_neg_one_fourth_le {y A B : ℝ} (hy : 0 < y) {t : ℝ}
    (h_zeta : ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) /
      riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.log (|t| + 2) + B) :
    ‖smoothedPerronIntegrand y (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      32 * y ^ (3 / 4 : ℝ) * ((A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2) := by
  unfold smoothedPerronIntegrand
  rw [norm_mul]
  have h_AB_nonneg : 0 ≤ A * Real.log (|t| + 2) + B :=
    (norm_nonneg _).trans h_zeta
  calc
    ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) /
        riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ *
        ‖smoothedPerronKernel y (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖
      ≤ (A * Real.log (|t| + 2) + B) * (32 * y ^ (3 / 4 : ℝ) / (|t| + 2) ^ 2) :=
        mul_le_mul h_zeta (norm_smoothedPerronKernel_neg_one_fourth_le hy t)
          (norm_nonneg _) h_AB_nonneg
    _ = 32 * y ^ (3 / 4 : ℝ) * ((A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2) := by ring

/-- Exact derivative of `-(A * (1 + Real.log (t + 2)) + B) * (t + 2)⁻¹` for `t + 2 ≠ 0`. -/
theorem hasDerivAt_leftVerticalAntideriv (A B : ℝ) {t : ℝ} (ht : t + 2 ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ -(A * (1 + Real.log (x + 2)) + B) * (x + 2)⁻¹)
      ((A * Real.log (t + 2) + B) / (t + 2) ^ 2) t := by
  have hd_add : HasDerivAt (fun x : ℝ ↦ x + 2) 1 t := (hasDerivAt_id t).add_const 2
  have hd_log : HasDerivAt (fun x : ℝ ↦ Real.log (x + 2)) (1 / (t + 2)) t :=
    hd_add.log ht
  have hd_inv : HasDerivAt (fun x : ℝ ↦ (x + 2)⁻¹) (-1 / (t + 2) ^ 2) t :=
    (hd_add.inv ht).congr_deriv (by ring)
  refine ((((hd_log.const_add 1).const_mul A).add_const B).neg.mul hd_inv).congr_deriv ?_
  simp only [Pi.neg_apply]
  field_simp [ht]
  ring

/-- **Exact Closed-Form Integral of `(A * Real.log (t + 2) + B) / (t + 2) ^ 2` on `[0, U]`**:
For `0 ≤ U`,
$$\int_0^U \frac{A \log(t + 2) + B}{(t + 2)^2} \, dt
  = \frac{A (1 + \log 2) + B}{2} - \frac{A (1 + \log(U + 2)) + B}{U + 2}.$$ -/
theorem intervalIntegral_log_add_two_div_sq_eq {U : ℝ} (hU : 0 ≤ U) (A B : ℝ) :
    (∫ t : ℝ in (0 : ℝ)..U, (A * Real.log (t + 2) + B) / (t + 2) ^ 2) =
      (A * (1 + Real.log 2) + B) / 2 -
        (A * (1 + Real.log (U + 2)) + B) / (U + 2) := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) U,
      HasDerivAt (fun x : ℝ ↦ -(A * (1 + Real.log (x + 2)) + B) * (x + 2)⁻¹)
        ((A * Real.log (t + 2) + B) / (t + 2) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hU] at ht
    exact hasDerivAt_leftVerticalAntideriv A B (by linarith [ht.1])
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ (A * Real.log (t + 2) + B) / (t + 2) ^ 2) volume 0 U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hU]
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).integrableOn_Icc
    have ht2 : t + 2 ≠ 0 := by linarith [ht.1]
    refine ContinuousAt.div ?_ ((continuousAt_id.add continuousAt_const).pow 2) (pow_ne_zero 2 ht2)
    exact ((continuousAt_const.mul ((continuousAt_id.add continuousAt_const).log ht2)).add
      continuousAt_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [zero_add]
  ring

/-- For `0 ≤ U`, `0 ≤ A`, and `0 ≤ B`,
`∫ t in 0..U, (A * Real.log (t + 2) + B) / (t + 2) ^ 2 ≤ (2 * A + B) / 2`. -/
theorem intervalIntegral_zero_to_U_log_add_two_div_sq_le
    {U A B : ℝ} (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∫ t : ℝ in (0 : ℝ)..U, (A * Real.log (t + 2) + B) / (t + 2) ^ 2) ≤
      (2 * A + B) / 2 := by
  rw [intervalIntegral_log_add_two_div_sq_eq hU A B]
  have hlogU : 0 ≤ Real.log (U + 2) := Real.log_nonneg (by linarith)
  have h_upper_nonneg : 0 ≤ (A * (1 + Real.log (U + 2)) + B) / (U + 2) := by positivity
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h_lower_le : (A * (1 + Real.log 2) + B) / 2 ≤ (2 * A + B) / 2 := by
    nlinarith
  linarith

/-- Continuity of `t ↦ (A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2` on `ℝ`. -/
theorem continuous_log_abs_add_two_div_sq (A B : ℝ) :
    Continuous (fun t : ℝ ↦ (A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2) := by
  have h_add : Continuous (fun t : ℝ ↦ |t| + 2) := continuous_abs.add continuous_const
  have h_ne : ∀ t : ℝ, |t| + 2 ≠ 0 := fun t ↦ by positivity
  refine Continuous.div ?_ (h_add.pow 2) (fun t ↦ pow_ne_zero 2 (h_ne t))
  exact (continuous_const.mul (h_add.log h_ne)).add continuous_const

/-- For `0 ≤ U`, `0 ≤ A`, and `0 ≤ B`,
`∫ t in (-U)..U, (A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2 ≤ 2 * A + B`. -/
theorem intervalIntegral_neg_U_to_U_log_abs_add_two_div_sq_le
    {U A B : ℝ} (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∫ t : ℝ in (-U)..U, (A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2) ≤
      2 * A + B := by
  let g : ℝ → ℝ := fun t ↦ (A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2
  have hg_cont : Continuous g := continuous_log_abs_add_two_div_sq A B
  have h_split : (∫ t in (-U)..U, g t) = (∫ t in (-U)..0, g t) + ∫ t in (0 : ℝ)..U, g t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.intervalIntegrable (-U) 0) (hg_cont.intervalIntegrable 0 U)).symm
  have h_neg : (∫ t in (-U)..0, g t) = ∫ t in (0 : ℝ)..U, g t := by
    have h1 := intervalIntegral.integral_comp_neg g (a := 0) (b := U)
    simp only [neg_zero, g, abs_neg] at h1
    exact h1.symm
  have h_pos_eq : (∫ t in (0 : ℝ)..U, g t) =
      ∫ t in (0 : ℝ)..U, (A * Real.log (t + 2) + B) / (t + 2) ^ 2 := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hU] at ht
    dsimp [g]
    rw [abs_of_nonneg ht.1]
  have h_pos_le := intervalIntegral_zero_to_U_log_add_two_div_sq_le hU hA hB
  linarith

/-- **Uniform Bound on `contourLeftVerticalError y (-1 / 4) U` (`U ≥ 0`)**:
If `‖-ζ'(-1 / 4 + t * I) / ζ(-1 / 4 + t * I)‖ ≤ A * Real.log (|t| + 2) + B` (`0 ≤ A, 0 ≤ B`),
then for all `y > 0` and `U ≥ 0`:
$$\text{contourLeftVerticalError}(y, -1/4, U)
  \le (2\pi)^{-1} \left(32 y^{3/4} (2 A + B)\right).$$ -/
theorem contourLeftVerticalError_neg_one_fourth_le
    {y U A B : ℝ} (hy : 0 < y) (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h_zeta : ∀ t : ℝ,
      ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) /
        riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.log (|t| + 2) + B) :
    contourLeftVerticalError y (-1 / 4) U ≤
      (2 * Real.pi)⁻¹ * (32 * y ^ (3 / 4 : ℝ) * (2 * A + B)) := by
  unfold contourLeftVerticalError
  gcongr
  let g : ℝ → ℝ := fun t ↦ (A * Real.log (|t| + 2) + B) / (|t| + 2) ^ 2
  have hg_cont : Continuous (fun t : ℝ ↦ 32 * y ^ (3 / 4 : ℝ) * g t) :=
    continuous_const.mul (continuous_log_abs_add_two_div_sq A B)
  have h_norm_le :
      ‖∫ t in (-U)..U, smoothedPerronIntegrand y (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        ∫ t in (-U)..U, 32 * y ^ (3 / 4 : ℝ) * g t := by
    rw [intervalIntegral.integral_of_le (by linarith : -U ≤ U),
      intervalIntegral.integral_of_le (by linarith : -U ≤ U)]
    exact norm_integral_le_of_norm_le
      (hg_cont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (ae_of_all _ fun t ↦ norm_smoothedPerronIntegrand_neg_one_fourth_le hy (h_zeta t))
  rw [intervalIntegral.integral_const_mul] at h_norm_le
  refine h_norm_le.trans ?_
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral_neg_U_to_U_log_abs_add_two_div_sq_le hU hA hB) (by positivity)

/-- **Uniform Bound on `contourLeftVerticalDiffError x h (-1 / 4) U` (`U ≥ 0`)**:
For `1 ≤ x - h`, `0 < h`, and `0 ≤ U`,
$$\text{contourLeftVerticalDiffError}(x, h, -1/4, U)
  \le \frac{32 (2 A + B)}{\pi h} (x + h)^{3/4}.$$ -/
theorem contourLeftVerticalDiffError_neg_one_fourth_le
    {x h U A B : ℝ} (hx_sub : 1 ≤ x - h) (hh : 0 < h) (hU : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h_zeta : ∀ t : ℝ,
      ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) /
        riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.log (|t| + 2) + B) :
    contourLeftVerticalDiffError x h (-1 / 4) U ≤
      32 * (2 * A + B) / (Real.pi * h) * (x + h) ^ (3 / 4 : ℝ) := by
  have hx_minus_pos : 0 < x - h := zero_lt_one.trans_le hx_sub
  have hx_pos : 0 < x := by linarith
  have hx_plus_pos : 0 < x + h := by linarith
  have h_plus := contourLeftVerticalError_neg_one_fourth_le hx_plus_pos hU hA hB h_zeta
  have h_x := contourLeftVerticalError_neg_one_fourth_le hx_pos hU hA hB h_zeta
  have h_minus := contourLeftVerticalError_neg_one_fourth_le hx_minus_pos hU hA hB h_zeta
  have hrpow_x : x ^ (3 / 4 : ℝ) ≤ (x + h) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hx_pos.le (by linarith) (by norm_num)
  have hrpow_minus : (x - h) ^ (3 / 4 : ℝ) ≤ (x + h) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hx_minus_pos.le (by linarith) (by norm_num)
  have h_x_le : (2 * Real.pi)⁻¹ * (32 * x ^ (3 / 4 : ℝ) * (2 * A + B)) ≤
      (2 * Real.pi)⁻¹ * (32 * (x + h) ^ (3 / 4 : ℝ) * (2 * A + B)) := by
    gcongr
  have h_minus_le : (2 * Real.pi)⁻¹ * (32 * (x - h) ^ (3 / 4 : ℝ) * (2 * A + B)) ≤
      (2 * Real.pi)⁻¹ * (32 * (x + h) ^ (3 / 4 : ℝ) * (2 * A + B)) := by
    gcongr
  have h_alg :
      ((2 * Real.pi)⁻¹ * (32 * (x + h) ^ (3 / 4 : ℝ) * (2 * A + B)) +
        (2 * Real.pi)⁻¹ * (32 * (x + h) ^ (3 / 4 : ℝ) * (2 * A + B))) / h =
      32 * (2 * A + B) / (Real.pi * h) * (x + h) ^ (3 / 4 : ℝ) := by
    field_simp [Real.pi_ne_zero, hh.ne']
    ring
  unfold contourLeftVerticalDiffError
  refine max_le ?_ ?_
  · rw [← h_alg]
    exact div_le_div_of_nonneg_right (by linarith) hh.le
  · rw [← h_alg]
    exact div_le_div_of_nonneg_right (by linarith) hh.le

/-- On any horizontal segment `s = σ + t * I` (`t ≠ 0`, `σ ≤ 2`) with `1 ≤ y`,
`‖smoothedPerronKernel y ((σ : ℂ) + (t : ℂ) * I)‖ ≤ y ^ (3 : ℝ) / t ^ 2`. -/
theorem norm_smoothedPerronKernel_horizontal_le
    {y σ t : ℝ} (hy : 1 ≤ y) (hσ : σ ≤ 2) (ht : t ≠ 0) :
    ‖smoothedPerronKernel y ((σ : ℂ) + (t : ℂ) * I)‖ ≤ y ^ (3 : ℝ) / t ^ 2 := by
  have hy_pos : 0 < y := zero_lt_one.trans_le hy
  unfold smoothedPerronKernel
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy_pos]
  have hre : (((σ : ℂ) + (t : ℂ) * I) + 1).re = σ + 1 := by simp
  rw [hre]
  have hrpow : y ^ (σ + 1) ≤ y ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hy (by linarith)
  have hden : t ^ 2 ≤ ‖((σ : ℂ) + (t : ℂ) * I) * (((σ : ℂ) + (t : ℂ) * I) + 1)‖ := by
    have h1 := sq_abs_im_le_norm_mul_add_one ((σ : ℂ) + (t : ℂ) * I)
    simpa [sq_abs] using h1
  have ht_sq_pos : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  calc
    y ^ (σ + 1) / ‖((σ : ℂ) + (t : ℂ) * I) * (((σ : ℂ) + (t : ℂ) * I) + 1)‖
      ≤ y ^ (3 : ℝ) / ‖((σ : ℂ) + (t : ℂ) * I) * (((σ : ℂ) + (t : ℂ) * I) + 1)‖ :=
        div_le_div_of_nonneg_right hrpow (norm_nonneg _)
    _ ≤ y ^ (3 : ℝ) / t ^ 2 :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hy_pos.le _) ht_sq_pos hden

/-- Bound on the top horizontal integral `∫ σ in (-1 / 4)..2, smoothedPerronIntegrand y (σ + U *
I)`. -/
theorem norm_integral_smoothedPerronIntegrand_top_neg_one_fourth_le
    {y U M_horiz : ℝ} (hy : 1 ≤ y) (hU : 0 < U)
    (h_top : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ M_horiz) :
    ‖∫ σ in (-1 / 4 : ℝ)..2, smoothedPerronIntegrand y ((σ : ℂ) + (U : ℂ) * I)‖ ≤
      9 / 4 * y ^ (3 : ℝ) * M_horiz / U ^ 2 := by
  have hy_pos : 0 < y := zero_lt_one.trans_le hy
  have hM_nonneg : 0 ≤ M_horiz :=
    (norm_nonneg _).trans (h_top 2 ⟨by norm_num, le_rfl⟩)
  have h_int :
      ‖∫ σ in (-1 / 4 : ℝ)..2, smoothedPerronIntegrand y ((σ : ℂ) + (U : ℂ) * I)‖ ≤
        (M_horiz * (y ^ (3 : ℝ) / U ^ 2)) * |2 - (-1 / 4 : ℝ)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ ↦ ?_
    have hσ_icc : σ ∈ Set.Icc (-1 / 4 : ℝ) 2 := by
      rw [← Set.uIcc_of_le (by norm_num : (-1 / 4 : ℝ) ≤ 2)]
      exact uIoc_subset_uIcc hσ
    unfold smoothedPerronIntegrand
    rw [norm_mul]
    exact mul_le_mul (h_top σ hσ_icc)
      (norm_smoothedPerronKernel_horizontal_le hy hσ_icc.2 hU.ne')
      (norm_nonneg _) hM_nonneg
  have habs : |2 - (-1 / 4 : ℝ)| = 9 / 4 := by norm_num
  rw [habs] at h_int
  refine h_int.trans_eq ?_
  ring

/-- Bound on the bottom horizontal integral `∫ σ in (-1 / 4)..2, smoothedPerronIntegrand y (σ - U *
I)`. -/
theorem norm_integral_smoothedPerronIntegrand_bottom_neg_one_fourth_le
    {y U M_horiz : ℝ} (hy : 1 ≤ y) (hU : 0 < U)
    (h_bot : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤ M_horiz) :
    ‖∫ σ in (-1 / 4 : ℝ)..2, smoothedPerronIntegrand y ((σ : ℂ) - (U : ℂ) * I)‖ ≤
      9 / 4 * y ^ (3 : ℝ) * M_horiz / U ^ 2 := by
  have hy_pos : 0 < y := zero_lt_one.trans_le hy
  have hM_nonneg : 0 ≤ M_horiz :=
    (norm_nonneg _).trans (h_bot 2 ⟨by norm_num, le_rfl⟩)
  have h_int :
      ‖∫ σ in (-1 / 4 : ℝ)..2, smoothedPerronIntegrand y ((σ : ℂ) - (U : ℂ) * I)‖ ≤
        (M_horiz * (y ^ (3 : ℝ) / U ^ 2)) * |2 - (-1 / 4 : ℝ)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ ↦ ?_
    have hσ_icc : σ ∈ Set.Icc (-1 / 4 : ℝ) 2 := by
      rw [← Set.uIcc_of_le (by norm_num : (-1 / 4 : ℝ) ≤ 2)]
      exact uIoc_subset_uIcc hσ
    have h_sub_eq : (σ : ℂ) - (U : ℂ) * I = (σ : ℂ) + ((-U : ℝ) : ℂ) * I := by
      push_cast
      ring
    unfold smoothedPerronIntegrand
    rw [norm_mul]
    refine mul_le_mul (h_bot σ hσ_icc) ?_ (norm_nonneg _) hM_nonneg
    rw [h_sub_eq]
    have h_k := norm_smoothedPerronKernel_horizontal_le (t := -U) hy hσ_icc.2
      (neg_ne_zero.mpr hU.ne')
    simpa using h_k
  have habs : |2 - (-1 / 4 : ℝ)| = 9 / 4 := by norm_num
  rw [habs] at h_int
  refine h_int.trans_eq ?_
  ring

/-- Combined bound on `contourHorizontalError y (-1 / 4) U`. -/
theorem contourHorizontalError_neg_one_fourth_le
    {y U M_horiz : ℝ} (hy : 1 ≤ y) (hU : 0 < U)
    (h_top : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ M_horiz)
    (h_bot : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤ M_horiz) :
    contourHorizontalError y (-1 / 4) U ≤
      9 / (4 * Real.pi) * y ^ (3 : ℝ) * M_horiz / U ^ 2 := by
  unfold contourHorizontalError
  have h1 := norm_integral_smoothedPerronIntegrand_top_neg_one_fourth_le hy hU h_top
  have h2 := norm_integral_smoothedPerronIntegrand_bottom_neg_one_fourth_le hy hU h_bot
  have h_alg :
      (2 * Real.pi)⁻¹ * (9 / 4 * y ^ (3 : ℝ) * M_horiz / U ^ 2) +
        (2 * Real.pi)⁻¹ * (9 / 4 * y ^ (3 : ℝ) * M_horiz / U ^ 2) =
      9 / (4 * Real.pi) * y ^ (3 : ℝ) * M_horiz / U ^ 2 := by
    field_simp [Real.pi_ne_zero, hU.ne']
    ring
  rw [← h_alg]
  gcongr

/-- **Explicit Bound on `contourTailAndHorizontalDiffError x h (-1 / 4) U`**:
For `1 ≤ x - h`, `0 < h`, and `0 < U`, if `‖-ζ' / ζ‖ ≤ M_horiz` along `[-1 / 4, 2] ± i U`, then:
$$\text{contourTailAndHorizontalDiffError}(x, h, -1/4, U)
  \le \frac{4 (x + h)^3}{\pi h U} + \frac{9 (x + h)^3 M_{\text{horiz}}}{2 \pi h U^2}.$$ -/
theorem contourTailAndHorizontalDiffError_neg_one_fourth_le
    {x h U M_horiz : ℝ} (hx_sub : 1 ≤ x - h) (hh : 0 < h) (hU : 0 < U)
    (h_top : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ M_horiz)
    (h_bot : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤ M_horiz) :
    contourTailAndHorizontalDiffError x h (-1 / 4) U ≤
      4 * (x + h) ^ (3 : ℝ) / (Real.pi * h * U) +
        9 * (x + h) ^ (3 : ℝ) * M_horiz / (2 * Real.pi * h * U ^ 2) := by
  have hx : 1 ≤ x := by linarith
  have hx_plus : 1 ≤ x + h := by linarith
  have hM_nonneg : 0 ≤ M_horiz :=
    (norm_nonneg _).trans (h_top 2 ⟨by norm_num, le_rfl⟩)
  have h_plus := contourHorizontalError_neg_one_fourth_le hx_plus hU h_top h_bot
  have h_x := contourHorizontalError_neg_one_fourth_le hx hU h_top h_bot
  have h_minus := contourHorizontalError_neg_one_fourth_le hx_sub hU h_top h_bot
  have hrpow_x : x ^ (3 : ℝ) ≤ (x + h) ^ (3 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have hrpow_minus : (x - h) ^ (3 : ℝ) ≤ (x + h) ^ (3 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  have h_x_le : 9 / (4 * Real.pi) * x ^ (3 : ℝ) * M_horiz / U ^ 2 ≤
      9 / (4 * Real.pi) * (x + h) ^ (3 : ℝ) * M_horiz / U ^ 2 := by
    gcongr
  have h_minus_le : 9 / (4 * Real.pi) * (x - h) ^ (3 : ℝ) * M_horiz / U ^ 2 ≤
      9 / (4 * Real.pi) * (x + h) ^ (3 : ℝ) * M_horiz / U ^ 2 := by
    gcongr
  have h_alg :
      (9 / (4 * Real.pi) * (x + h) ^ (3 : ℝ) * M_horiz / U ^ 2 +
        9 / (4 * Real.pi) * (x + h) ^ (3 : ℝ) * M_horiz / U ^ 2) / h =
      9 * (x + h) ^ (3 : ℝ) * M_horiz / (2 * Real.pi * h * U ^ 2) := by
    field_simp [Real.pi_ne_zero, hh.ne', hU.ne']
    ring
  unfold contourTailAndHorizontalDiffError
  gcongr
  refine max_le ?_ ?_
  · rw [← h_alg]
    exact div_le_div_of_nonneg_right (by linarith) hh.le
  · rw [← h_alg]
    exact div_le_div_of_nonneg_right (by linarith) hh.le

/-- Elementary quantitative decay bound: for all `1 ≤ U`, `(Real.log U) ^ 5 ≤ 3125 * U`. -/
theorem log_pow_five_le_mul_self {U : ℝ} (hU : 1 ≤ U) :
    (Real.log U) ^ 5 ≤ 3125 * U := by
  have hU_pos : 0 < U := zero_lt_one.trans_le hU
  have hrpow_pos : 0 < U ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hU_pos (1 / 5)
  have hlog_rpow : Real.log (U ^ (1 / 5 : ℝ)) = 1 / 5 * Real.log U :=
    Real.log_rpow hU_pos (1 / 5)
  have hlog_le : Real.log (U ^ (1 / 5 : ℝ)) ≤ U ^ (1 / 5 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hrpow_pos
  have hlog_bound : Real.log U ≤ 5 * U ^ (1 / 5 : ℝ) := by linarith
  calc
    (Real.log U) ^ 5 ≤ (5 * U ^ (1 / 5 : ℝ)) ^ 5 :=
      pow_le_pow_left₀ (Real.log_nonneg hU) hlog_bound 5
    _ = 3125 * (U ^ (1 / 5 : ℝ)) ^ (5 : ℕ) := by ring
    _ = 3125 * U := by
      rw [← Real.rpow_natCast (U ^ (1 / 5 : ℝ)) 5, ← Real.rpow_mul hU_pos.le]
      norm_num

/-- Consequently, for all `1 ≤ U`, `(Real.log U) ^ 5 / U ^ 2 ≤ 3125 / U`. -/
theorem log_pow_five_div_sq_le {U : ℝ} (hU : 1 ≤ U) :
    (Real.log U) ^ 5 / U ^ 2 ≤ 3125 / U := by
  have hU_pos : 0 < U := zero_lt_one.trans_le hU
  calc
    (Real.log U) ^ 5 / U ^ 2 ≤ (3125 * U) / U ^ 2 :=
      div_le_div_of_nonneg_right (log_pow_five_le_mul_self hU) (sq_nonneg U)
    _ = 3125 / U := by
      field_simp [hU_pos.ne']

/-- `(Real.log U) ^ 5 / U ^ 2 → 0` as `U → ∞`. -/
theorem tendsto_log_pow_five_div_sq_atTop :
    Tendsto (fun U : ℝ ↦ (Real.log U) ^ 5 / U ^ 2) atTop (𝓝 0) := by
  refine squeeze_zero' (eventually_ge_atTop 1 |>.mono fun U hU ↦ ?_)
    (eventually_ge_atTop 1 |>.mono fun U hU ↦ log_pow_five_div_sq_le hU)
    (tendsto_const_nhds.div_atTop tendsto_id)
  have hlog : 0 ≤ Real.log U := Real.log_nonneg hU
  positivity

/-- When `M_horiz ≤ C_h * (Real.log U) ^ 5` (`0 ≤ C_h`, `1 ≤ U`),
`contourTailAndHorizontalDiffError x h (-1 / 4) U` is bounded by `O(1 / U)`:
$$\text{contourTailAndHorizontalDiffError}(x, h, -1/4, U)
  \le \frac{(x + h)^3 (4 + \frac{28125}{2} C_h)}{\pi h U}.$$ -/
theorem contourTailAndHorizontalDiffError_neg_one_fourth_le_inv_U
    {x h U M_horiz C_h : ℝ} (hx_sub : 1 ≤ x - h) (hh : 0 < h) (hU : 1 ≤ U) (hCh : 0 ≤ C_h)
    (hM : M_horiz ≤ C_h * (Real.log U) ^ 5)
    (h_top : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ M_horiz)
    (h_bot : ∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
      ‖-deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤ M_horiz) :
    contourTailAndHorizontalDiffError x h (-1 / 4) U ≤
      (x + h) ^ (3 : ℝ) * (4 + 28125 / 2 * C_h) / (Real.pi * h * U) := by
  have hU_pos : 0 < U := zero_lt_one.trans_le hU
  have hx_plus_pos : 0 < x + h := by linarith
  have h1 := contourTailAndHorizontalDiffError_neg_one_fourth_le hx_sub hh hU_pos h_top h_bot
  have h2 : 9 * (x + h) ^ (3 : ℝ) * M_horiz / (2 * Real.pi * h * U ^ 2) ≤
      9 * (x + h) ^ (3 : ℝ) * (C_h * (3125 * U)) / (2 * Real.pi * h * U ^ 2) := by
    have hM_le : M_horiz ≤ C_h * (3125 * U) :=
      hM.trans (mul_le_mul_of_nonneg_left (log_pow_five_le_mul_self hU) hCh)
    gcongr
  have h3 :
      4 * (x + h) ^ (3 : ℝ) / (Real.pi * h * U) +
        9 * (x + h) ^ (3 : ℝ) * (C_h * (3125 * U)) / (2 * Real.pi * h * U ^ 2) =
      (x + h) ^ (3 : ℝ) * (4 + 28125 / 2 * C_h) / (Real.pi * h * U) := by
    field_simp [Real.pi_ne_zero, hh.ne', hU_pos.ne']
    ring
  linarith

/-- **Existence of Arbitrarily Large Zero-Free Heights with `contourTailAndHorizontalDiffError ≤
ε`**:
If for every `U₀ ≥ T` there exists a zero-free height `U ≥ U₀` (`∀ ρ ∈ nontrivialZetaZerosUpTo U,
|ρ.im| < U`)
where `‖-ζ' / ζ‖ ≤ C_h * (Real.log U) ^ 5` along `[-1 / 4, 2] ± i U`, then for every `ε > 0`
there exists `U ≥ T` with `contourTailAndHorizontalDiffError x h (-1 / 4) U ≤ ε`. -/
theorem exists_zero_free_height_with_small_tailAndHorizontal
    {x h T C_h : ℝ} (hx_sub : 1 ≤ x - h) (hh : 0 < h) (hCh : 0 ≤ C_h)
    (h_heights : ∀ U₀ ≥ T, ∃ U ≥ U₀,
      (∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) ∧
      (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
        ‖-deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ C_h * (Real.log U) ^ 5) ∧
      (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
        ‖-deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
          riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤ C_h * (Real.log U) ^ 5)) :
    ∀ ε > 0, ∃ U ≥ T,
      (∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) ∧
      contourTailAndHorizontalDiffError x h (-1 / 4) U ≤ ε := by
  intro ε hε
  set K : ℝ := (x + h) ^ (3 : ℝ) * (4 + 28125 / 2 * C_h) / (Real.pi * h)
  set U₀ : ℝ := max T (max 1 (K / ε))
  have hT_le_U₀ : T ≤ U₀ := le_max_left _ _
  have h1_le_U₀ : 1 ≤ U₀ := (le_max_left 1 (K / ε)).trans (le_max_right T _)
  have hKε_le_U₀ : K / ε ≤ U₀ := (le_max_right 1 (K / ε)).trans (le_max_right T _)
  obtain ⟨U, hU₀_le, h_no_horiz, h_top, h_bot⟩ := h_heights U₀ hT_le_U₀
  have hTU : T ≤ U := hT_le_U₀.trans hU₀_le
  have h1U : 1 ≤ U := h1_le_U₀.trans hU₀_le
  have hU_pos : 0 < U := zero_lt_one.trans_le h1U
  have hKε_le_U : K / ε ≤ U := hKε_le_U₀.trans hU₀_le
  refine ⟨U, hTU, h_no_horiz, ?_⟩
  have h_bound := contourTailAndHorizontalDiffError_neg_one_fourth_le_inv_U
    hx_sub hh h1U hCh le_rfl h_top h_bot
  have h_eq : (x + h) ^ (3 : ℝ) * (4 + 28125 / 2 * C_h) / (Real.pi * h * U) = K / U := by
    dsimp [K]
    rw [div_div]
  rw [h_eq] at h_bound
  refine h_bound.trans ?_
  rw [div_le_iff₀ hU_pos]
  have hK_le : K ≤ U * ε := (div_le_iff₀ hε).mp hKε_le_U
  linarith

/-- **Final `U`-Free Explicit Bound on `|Chebyshev.psi x - x|` via Contour Shift to `Re s = -1 /
4`**:
Combining the exact antiderivative bound on `Re s = -1 / 4`, the `O((log U) ^ 5 / U ^ 2)`
horizontal vanishing along zero-free heights `U → ∞`, and the multiplicity-weighted low/high
frequency Stieltjes bounds at `t₀ = 6` proves the complete `U`-independent explicit bound! -/
theorem abs_psi_sub_self_le_weighted_riemannVonMangoldt_six_neg_one_fourth
    (hRH : RiemannHypothesis) {x h T a_rvM C D A B C_h : ℝ}
    (hx_sub : 1 ≤ x - h) (hh : 0 < h) (h6T : 6 ≤ T)
    (ha_rvM : 0 ≤ a_rvM) (hD : 0 ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hCh : 0 ≤ C_h)
    (hN_bound : ∀ t ≥ 6,
      (weightedZeroCountingFunction t : ℝ) ≤ a_rvM * t * Real.log t + C * t + D)
    (h_left_zeta : ∀ t : ℝ,
      ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I) /
        riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ A * Real.log (|t| + 2) + B)
    (h_heights : ∀ U₀ ≥ T, ∃ U ≥ U₀,
      (∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) ∧
      (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
        ‖-deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ C_h * (Real.log U) ^ 5) ∧
      (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
        ‖-deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
          riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤ C_h * (Real.log U) ^ 5)) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) *
          (a_rvM / 2 * (Real.log T) ^ 2 + (a_rvM + C) * Real.log T + C + D / 6 -
            a_rvM / 2 * (Real.log 6) ^ 2 - C * Real.log 6) +
        (2 * (x + h) ^ (3 / 2 : ℝ) / h) *
          ((2 * a_rvM * Real.log T + 2 * a_rvM + 2 * C) / T + 2 * D / T ^ 2) +
        32 * (2 * A + B) / (Real.pi * h) * (x + h) ^ (3 / 4 : ℝ) := by
  refine abs_psi_sub_self_le_weighted_riemannVonMangoldt_add_left_vertical
    hRH hx_sub hh (by norm_num : (0 : ℝ) < 6) h6T
    (by norm_num : (-1 / 2 : ℝ) < -1 / 4) (by norm_num : (-1 / 4 : ℝ) < 0)
    (weightedZeroCountingFunction_six_eq_zero hRH) ha_rvM hD hN_bound
    (fun U hTU ↦ contourLeftVerticalDiffError_neg_one_fourth_le hx_sub hh
      (by linarith : (0 : ℝ) ≤ U) hA hB h_left_zeta)
    (exists_zero_free_height_with_small_tailAndHorizontal hx_sub hh hCh h_heights)

end ConjectureMachines.Riemann543.Semantics.WeightedStieltjes
