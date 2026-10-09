/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Local Zero-Counting, Symmetric Zero-Free Heights, and Full Horizontal `ζ'/ζ` Bounds

This standalone file proves with **zero `sorry`s**:
1. **Local Zero Count Bound (`card_criticalLineZerosInStrip_le` &
   `card_nontrivialZetaZeros_in_strip_le`)**:
   - Uses `sum_divisor_riemannZeta₁_closedBall_two_add_mul_I_le` with `r = 19 / 10`, `R = 39 / 20`
     at center `2 + (T + 1 / 2) * I` together with `1 ≤ divisor riemannZeta₁ (closedBall c |r|) ρ`
     for every zero `ρ` of `riemannZeta₁` in the ball to prove that for `T ≥ 0`, the number of
     critical-line zeros `ρ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`) in `[T - 1 / 2, T + 3 / 2]`
     is at most `156 * Real.log (T + 10)`.
   - Under `RiemannHypothesis`, every nontrivial zero `ρ` of `riemannZeta` has `ρ.re = 1 / 2`, so
     cardinality of nontrivial zeros in the strip `[T - 1 / 2, T + 3 / 2]` is at most
     `156 * Real.log (T + 10)`.
2. **Existence of Symmetric Zero-Free Height `U ∈ [T, T + 1]` (`exists_zero_free_height_in_Icc`)**:
   - Defines `localZeroHeights T : Finset ℝ` as the image under `fun ρ ↦ |ρ.im|` of the set of
     critical-line zeros `ρ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`) with
     `|ρ.im| ∈ [T - 1 / 2, T + 3 / 2]`,
     and bounds `(localZeroHeights T).card ≤ 156 * Real.log (T + 10)` via the injection
     `γ ↦ 1 / 2 + γ * I` into `criticalLineZerosInStrip T`.
   - Applies `exists_zero_free_gap_in_Icc (localZeroHeights T) T` to obtain `U ∈ Set.Icc T (T + 1)`
     and `Δ = 1 / (2 * ((localZeroHeights T).card + 1)) ≥ (1 / 314) / Real.log (T + 10)` such that
     for **ALL** critical-line zeros `ρ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`), BOTH
     `Δ ≤ |ρ.im - U|` AND `Δ ≤ |ρ.im - (-U)|` hold.
3. **Full Horizontal Segment Bound on `[-1 / 4, 2] ± U * I` via `logDeriv_riemannZeta_one_sub`**:
   - Proves `‖Complex.tan (π * ((σ : ℂ) + (V : ℂ) * I) / 2)‖ ≤ 2` for all `σ : ℝ` and `2 ≤ |V|`.
   - Proves the Euler–Maclaurin / Binet bound for `Complex.digamma` and deduces
     `‖Complex.digamma ((σ : ℂ) + (V : ℂ) * I)‖ ≤ Real.log (|V| + 2) + Real.pi + 11 / 6` for
     `σ ∈ [-1 / 4, 1 / 2]` and `2 ≤ |V|`.
   - Combines `logDeriv_riemannZeta_one_sub` on `[-1 / 4, 1 / 2]` with the Borel–Carathéodory
     horizontal bound `norm_logDeriv_riemannZeta_le_on_Icc_of_gap` on `[1 / 2, 2]` to bound
     `‖deriv riemannZeta ((σ : ℂ) ± (U : ℂ) * I) / riemannZeta ((σ : ℂ) ± (U : ℂ) * I)‖` across the
     entire horizontal segment `σ ∈ [-1 / 4, 2]`, and bounds the horizontal integrals of the
     smoothed Perron integrand across `[-1 / 4, 2] ± U * I`.
-/

@[expose] public section

namespace ConjectureMachines.Riemann543.Semantics.HorizontalBounds

open Complex Filter MeasureTheory Set Asymptotics Metric MeromorphicOn ComplexConjugate
open scoped Real Topology ArithmeticFunction LSeries.notation

/-!
## Section 0: Explicit Growth and Lower Bounds for `riemannZeta₁`
-/

/-- The fractional-part kernel on `(1, ∞)`:
`fractKernel t = t - ⌊t⌋₊` for `t > 1`, and `0` for `t ≤ 1`. -/
noncomputable def fractKernel : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator (fun t : ℝ ↦ ((t - ⌊t⌋₊ : ℝ) : ℂ))

/-- For `t ≥ 0`, `0 ≤ t - ⌊t⌋₊` and `t - ⌊t⌋₊ ≤ 1`. -/
theorem sub_floor_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t - (⌊t⌋₊ : ℝ) ∧ t - (⌊t⌋₊ : ℝ) ≤ 1 := by
  refine ⟨sub_nonneg.mpr (Nat.floor_le ht), ?_⟩
  linarith [Nat.lt_floor_add_one t]

/-- `‖fractKernel t‖ ≤ 1` for all `t : ℝ`. -/
theorem norm_fractKernel_le_one (t : ℝ) : ‖fractKernel t‖ ≤ 1 := by
  unfold fractKernel
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem ht, norm_real, Real.norm_eq_abs]
    have ht0 : 0 ≤ t := by linarith [mem_Ioi.mp ht]
    obtain ⟨h0, h1⟩ := sub_floor_bounds ht0
    rw [abs_of_nonneg h0]
    exact h1
  · rw [indicator_of_notMem ht, norm_zero]
    exact zero_le_one

/-- `fractKernel` is measurable. -/
theorem measurable_fractKernel : Measurable fractKernel := by
  unfold fractKernel
  refine Measurable.indicator ?_ measurableSet_Ioi
  exact Complex.measurable_ofReal.comp
    (measurable_id.sub (measurable_from_nat.comp Nat.measurable_floor))

/-- `fractKernel` is locally integrable on `Ioi 0`. -/
theorem locallyIntegrableOn_fractKernel : LocallyIntegrableOn fractKernel (Ioi 0) := by
  intro x _
  refine ⟨Metric.closedBall x 1, nhdsWithin_le_nhds (Metric.closedBall_mem_nhds x zero_lt_one), ?_⟩
  refine (integrableOn_const (C := (1 : ℝ))
    (hs := (isCompact_closedBall x 1).measure_lt_top.ne)).mono'
    measurable_fractKernel.aestronglyMeasurable ?_
  exact Eventually.of_forall norm_fractKernel_le_one

/-- `fractKernel` is `O(t ^ (-(0 : ℝ)))` as `t → ∞`. -/
theorem isBigO_fractKernel_atTop :
    fractKernel =O[atTop] (fun t : ℝ ↦ t ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t _
  simp [norm_fractKernel_le_one t]

/-- `fractKernel` vanishes on `Ioo 0 1`, so it is `O(t ^ (-b))` at `𝓝[>] 0` for every `b : ℝ`. -/
theorem isBigO_fractKernel_nhdsGT_zero (b : ℝ) :
    fractKernel =O[𝓝[>] 0] (fun t : ℝ ↦ t ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT zero_lt_one
  filter_upwards [hmem] with t ht
  have hnot : t ∉ Ioi (1 : ℝ) := notMem_Ioi.mpr ht.2.le
  simp [fractKernel, indicator_of_notMem hnot]

/-- For every `z : ℂ` with `z.re < 0`, `MellinConvergent fractKernel z` holds. -/
theorem mellinConvergent_fractKernel {z : ℂ} (hz : z.re < 0) :
    MellinConvergent fractKernel z :=
  mellinConvergent_of_isBigO_rpow locallyIntegrableOn_fractKernel
    isBigO_fractKernel_atTop hz (isBigO_fractKernel_nhdsGT_zero (z.re - 1)) (by linarith)

/-- For every `z : ℂ` with `z.re < 0`, `mellin fractKernel` is complex-differentiable at `z`. -/
theorem differentiableAt_mellin_fractKernel {z : ℂ} (hz : z.re < 0) :
    DifferentiableAt ℂ (mellin fractKernel) z :=
  mellin_differentiableAt_of_isBigO_rpow locallyIntegrableOn_fractKernel
    isBigO_fractKernel_atTop hz (isBigO_fractKernel_nhdsGT_zero (z.re - 1)) (by linarith)

/-- For every `s : ℂ` with `0 < s.re`, `s ↦ s * mellin fractKernel (-s)` is
differentiable at `s`. -/
theorem differentiableAt_mul_mellin_fractKernel_neg {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ ↦ z * mellin fractKernel (-z)) s := by
  refine DifferentiableAt.mul differentiableAt_id ?_
  exact (differentiableAt_mellin_fractKernel (by simpa using hs)).comp s differentiableAt_id.neg

/-- Rewriting `mellin fractKernel (-s)` as an integral over `Ioi 1`. -/
theorem mellin_fractKernel_neg_eq (s : ℂ) :
    mellin fractKernel (-s) =
      ∫ t in Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  unfold mellin fractKernel
  simp_rw [← indicator_smul, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [smul_eq_mul, mul_comm, show -s - 1 = -(s + 1) by ring]

/-- For `1 < s.re`, `riemannZeta s = s * ∫ t in Ioi 1, ⌊t⌋₊ * t ^ (-(s + 1))`. -/
theorem riemannZeta_eq_mul_integral_floor {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s =
      s * ∫ t in Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [← LSeries_one_eq_riemannZeta hs]
  have hO : (fun n : ℕ ↦ ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ)) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 0] with n _
    simp
  have h := LSeries_eq_mul_integral_of_nonneg (fun _ : ℕ ↦ (1 : ℝ)) zero_le_one hs hO
    (fun _ ↦ zero_le_one)
  have hL : LSeries (fun _ : ℕ ↦ ((1 : ℝ) : ℂ)) s = LSeries 1 s := by simp; rfl
  rw [← hL, h]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  simp

/-- For `1 < s.re`, `∫ t in Ioi 1, t * t ^ (-(s + 1)) = (s - 1)⁻¹`. -/
theorem integral_Ioi_one_mul_cpow_neg_add_one {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (s - 1)⁻¹ := by
  have hcongr : EqOn (fun t : ℝ ↦ (t : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (fun t : ℝ ↦ (t : ℂ) ^ (-s)) (Ioi (1 : ℝ)) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    calc
      (t : ℂ) * (t : ℂ) ^ (-(s + 1))
        = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := by rw [cpow_one]
      _ = (t : ℂ) ^ (1 + -(s + 1)) := (cpow_add _ _ ht0).symm
      _ = (t : ℂ) ^ (-s) := by ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
  have ha : (-s).re < -1 := by simpa using hs
  rw [integral_Ioi_cpow_of_lt ha zero_lt_one]
  have h1 : -s + 1 = -(s - 1) := by ring
  rw [ofReal_one, one_cpow, h1, div_neg, neg_div, neg_neg, one_div]

/-- For `1 < s.re`, `1 - riemannZeta₀ s = s * mellin fractKernel (-s)`. -/
theorem one_sub_riemannZeta₀_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    1 - riemannZeta₀ s = s * mellin fractKernel (-s) := by
  have hs1 : s ≠ 1 := by intro h; subst h; simp at hs
  have hs1_sub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hzeta := riemannZeta_eq_inv_sub_add hs1
  have hfloor := riemannZeta_eq_mul_integral_floor hs
  have hint_t := integral_Ioi_one_mul_cpow_neg_add_one hs
  have ha : (-s).re < -1 := by simpa using hs
  have hint1 : IntegrableOn (fun t : ℝ ↦ (t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi (1 : ℝ)) := by
    refine (integrableOn_Ioi_cpow_of_lt ha zero_lt_one).congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    calc
      (t : ℂ) ^ (-s) = (t : ℂ) ^ (1 + -(s + 1)) := by ring_nf
      _ = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := cpow_add _ _ ht0
      _ = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by rw [cpow_one]
  have hint_fract : IntegrableOn
      (fun t : ℝ ↦ ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi (1 : ℝ)) := by
    have hm := mellinConvergent_fractKernel (z := -s) (by simpa using zero_lt_one.trans hs)
    unfold MellinConvergent fractKernel at hm
    rw [IntegrableOn, ← indicator_smul, integrable_indicator_iff measurableSet_Ioi,
      IntegrableOn, Measure.restrict_restrict_of_subset (Ioi_subset_Ioi zero_le_one)] at hm
    change IntegrableOn _ (Ioi (1 : ℝ)) volume at hm
    refine hm.congr_fun ?_ measurableSet_Ioi
    intro t _
    dsimp only
    rw [smul_eq_mul, mul_comm, show -s - 1 = -(s + 1) by ring]
  have hint_floor : IntegrableOn
      (fun t : ℝ ↦ (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi (1 : ℝ)) := by
    refine (hint1.sub hint_fract).congr_fun ?_ measurableSet_Ioi
    intro t _
    rw [Pi.sub_apply]
    push_cast
    ring
  rw [mellin_fractKernel_neg_eq]
  have hsub : ∫ t in Ioi (1 : ℝ), ((t - ⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (∫ t in Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-(s + 1))) -
        ∫ t in Ioi (1 : ℝ), (⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    rw [← integral_sub hint1 hint_floor]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    push_cast
    ring
  rw [hsub, mul_sub, hint_t, ← hfloor, hzeta]
  have h1 : s * (s - 1)⁻¹ - (s - 1)⁻¹ = 1 := by
    calc
      s * (s - 1)⁻¹ - (s - 1)⁻¹ = (s - 1) * (s - 1)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hs1_sub
  linear_combination -h1

/-- The open right half-plane `{z : ℂ | 0 < z.re}` is preconnected. -/
theorem isPreconnected_re_pos : IsPreconnected {z : ℂ | 0 < z.re} := by
  have hConv : Convex ℝ {z : ℂ | 0 < z.re} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, add_re, smul_re, smul_eq_mul] at hx hy ⊢
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simp only [zero_mul, zero_add] at hab ⊢
      subst hab
      simpa using hy
    · have : 0 < a * x.re := mul_pos ha_pos hx
      have : 0 ≤ b * y.re := mul_nonneg hb hy.le
      linarith
  exact hConv.isPreconnected

/-- For every `s : ℂ` with `0 < s.re`, `1 - riemannZeta₀ s = s * mellin fractKernel (-s)`. -/
theorem one_sub_riemannZeta₀_eq_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    1 - riemannZeta₀ s = s * mellin fractKernel (-s) := by
  have hOpen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hAn1 : AnalyticOnNhd ℂ (fun z : ℂ ↦ 1 - riemannZeta₀ z) {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd ?_ hOpen
    exact (differentiable_const (1 : ℂ)).sub differentiable_riemannZeta₀ |>.differentiableOn
  have hAn2 : AnalyticOnNhd ℂ (fun z : ℂ ↦ z * mellin fractKernel (-z)) {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hOpen
    exact (differentiableAt_mul_mellin_fractKernel_neg hz).differentiableWithinAt
  have hEv : (fun z : ℂ ↦ 1 - riemannZeta₀ z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ ↦ z * mellin fractKernel (-z)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact one_sub_riemannZeta₀_eq_of_one_lt_re hz
  exact hAn1.eqOn_of_preconnected_of_eventuallyEq hAn2 isPreconnected_re_pos
    (by norm_num : (2 : ℂ) ∈ _) hEv hs

/-- For `0 < a`, `∫ t in Ioi 1, t ^ (-(a + 1)) = 1 / a`. -/
theorem integral_Ioi_one_rpow_neg_add_one {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (1 : ℝ), t ^ (-(a + 1)) = 1 / a := by
  have hlt : -(a + 1) < -1 := by linarith
  rw [integral_Ioi_rpow_of_lt hlt zero_lt_one]
  have h1 : -(a + 1) + 1 = -a := by ring
  rw [Real.one_rpow, h1, div_neg, neg_div, neg_neg, one_div]

/-- For every `s : ℂ` with `0 < s.re`, `‖mellin fractKernel (-s)‖ ≤ 1 / s.re`. -/
theorem norm_mellin_fractKernel_neg_le {s : ℂ} (hs : 0 < s.re) :
    ‖mellin fractKernel (-s)‖ ≤ 1 / s.re := by
  rw [mellin_fractKernel_neg_eq, ← integral_Ioi_one_rpow_neg_add_one hs]
  have hlt : -(s.re + 1) < -1 := by linarith
  refine norm_integral_le_of_norm_le
    (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht_pos : 0 < t := zero_lt_one.trans ht
  rw [norm_mul, norm_real, Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos ht_pos]
  obtain ⟨h0, h1⟩ := sub_floor_bounds ht_pos.le
  rw [abs_of_nonneg h0, show (-(s + 1)).re = -(s.re + 1) by simp]
  exact mul_le_of_le_one_left (Real.rpow_nonneg ht_pos.le _) h1

/-- For every `s : ℂ` with `0 < s.re`, `‖1 - riemannZeta₀ s‖ ≤ ‖s‖ / s.re`. -/
theorem norm_one_sub_riemannZeta₀_le {s : ℂ} (hs : 0 < s.re) :
    ‖1 - riemannZeta₀ s‖ ≤ ‖s‖ / s.re := by
  rw [one_sub_riemannZeta₀_eq_of_re_pos hs, norm_mul, div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left (norm_mellin_fractKernel_neg_le hs) (norm_nonneg s)

/-- For every `s : ℂ` with `0 < s.re`, `‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / s.re`. -/
theorem norm_riemannZeta₀_le {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₀ s‖ ≤ 1 + ‖s‖ / s.re := by
  have h1 : ‖riemannZeta₀ s‖ ≤ 1 + ‖1 - riemannZeta₀ s‖ := by
    calc
      ‖riemannZeta₀ s‖ = ‖1 - (1 - riemannZeta₀ s)‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖1 - riemannZeta₀ s‖ := norm_sub_le 1 (1 - riemannZeta₀ s)
      _ = 1 + ‖1 - riemannZeta₀ s‖ := by rw [norm_one]
  linarith [norm_one_sub_riemannZeta₀_le hs]

/-- **Explicit Upper Bound on `riemannZeta₁ s`**:
For every `s : ℂ` with `0 < s.re`, `‖riemannZeta₁ s‖ ≤ 1 + ‖s - 1‖ * (1 + ‖s‖ / s.re)`. -/
theorem norm_riemannZeta₁_le {s : ℂ} (hs : 0 < s.re) :
    ‖riemannZeta₁ s‖ ≤ 1 + ‖s - 1‖ * (1 + ‖s‖ / s.re) := by
  unfold riemannZeta₁
  have h1 : ‖1 + (s - 1) * riemannZeta₀ s‖ ≤ 1 + ‖s - 1‖ * ‖riemannZeta₀ s‖ := by
    calc
      ‖1 + (s - 1) * riemannZeta₀ s‖
        ≤ ‖(1 : ℂ)‖ + ‖(s - 1) * riemannZeta₀ s‖ := norm_add_le _ _
      _ = 1 + ‖s - 1‖ * ‖riemannZeta₀ s‖ := by rw [norm_one, norm_mul]
  have h2 : ‖s - 1‖ * ‖riemannZeta₀ s‖ ≤ ‖s - 1‖ * (1 + ‖s‖ / s.re) :=
    mul_le_mul_of_nonneg_left (norm_riemannZeta₀_le hs) (norm_nonneg _)
  linarith

/-- For every `s : ℂ` with `0 < s.re` and `s ≠ 1`,
`‖riemannZeta s‖ ≤ 1 / ‖s - 1‖ + 1 + ‖s‖ / s.re`. -/
theorem norm_riemannZeta_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / ‖s - 1‖ + 1 + ‖s‖ / s.re := by
  rw [riemannZeta_eq_inv_sub_add hs1]
  have h1 : ‖(s - 1)⁻¹ + riemannZeta₀ s‖ ≤ 1 / ‖s - 1‖ + ‖riemannZeta₀ s‖ := by
    calc
      ‖(s - 1)⁻¹ + riemannZeta₀ s‖
        ≤ ‖(s - 1)⁻¹‖ + ‖riemannZeta₀ s‖ := norm_add_le _ _
      _ = 1 / ‖s - 1‖ + ‖riemannZeta₀ s‖ := by rw [norm_inv, one_div]
  linarith [norm_riemannZeta₀_le hs]

/-- For `1 < s.re`, the Möbius L-series satisfies
`‖L ↗ArithmeticFunction.moebius s‖ ≤ 1 / (s.re - 1) + 2`. -/
theorem norm_LSeries_moebius_le {s : ℂ} (hs : 1 < s.re) :
    ‖L ↗ArithmeticFunction.moebius s‖ ≤ 1 / (s.re - 1) + 2 := by
  have h_sum_one : LSeriesSummable 1 (s.re : ℂ) :=
    LSeriesSummable_one_iff.mpr (by simpa using hs)
  have h_term_le : ∀ n : ℕ,
      ‖LSeries.term ↗ArithmeticFunction.moebius s n‖ ≤ (LSeries.term 1 (s.re : ℂ) n).re := by
    intro n
    rw [LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp only [hn, ↓reduceIte, LSeries.term_of_ne_zero hn, Pi.one_apply,
         ← ofReal_natCast, ← ofReal_cpow (Nat.cast_nonneg n), ← ofReal_one, ← ofReal_div, ofReal_re]
      gcongr
      have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      simpa [Complex.norm_intCast] using hμ
  have h_re_sum : Summable (fun n : ℕ ↦ (LSeries.term 1 (s.re : ℂ) n).re) :=
    (Complex.hasSum_re h_sum_one.hasSum).summable
  have h1 : ‖L ↗ArithmeticFunction.moebius s‖ ≤ ∑' n : ℕ, (LSeries.term 1 (s.re : ℂ) n).re := by
    calc
      ‖L ↗ArithmeticFunction.moebius s‖ ≤
        ∑' n : ℕ, ‖LSeries.term ↗ArithmeticFunction.moebius s n‖ :=
        norm_tsum_le_tsum_norm (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).norm
      _ ≤ ∑' n : ℕ, (LSeries.term 1 (s.re : ℂ) n).re :=
        Summable.tsum_le_tsum h_term_le
          (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).norm h_re_sum
  have h2 : (∑' n : ℕ, (LSeries.term 1 (s.re : ℂ) n).re) = (riemannZeta (s.re : ℂ)).re := by
    rw [(Complex.hasSum_re h_sum_one.hasSum).tsum_eq]
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

/-- For every `s : ℂ` with `1 < s.re`, `(s.re - 1) / (2 * s.re - 1) ≤ ‖riemannZeta s‖`. -/
theorem le_norm_riemannZeta_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (s.re - 1) / (2 * s.re - 1) ≤ ‖riemannZeta s‖ := by
  have h_inv : riemannZeta s * L ↗ArithmeticFunction.moebius s = 1 := by
    rw [← LSeries_one_eq_riemannZeta hs]
    exact LSeries_one_mul_Lseries_moebius hs
  have h_norm_mul : ‖riemannZeta s‖ * ‖L ↗ArithmeticFunction.moebius s‖ = 1 := by
    simpa [norm_mul] using congrArg norm h_inv
  have h_mu := norm_LSeries_moebius_le hs
  have h_rhs : 1 / (s.re - 1) + 2 = (2 * s.re - 1) / (s.re - 1) := by
    have : s.re - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [h_rhs] at h_mu
  have h_zeta_pos : 0 < ‖riemannZeta s‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re hs)
  have h_denom_pos : 0 < 2 * s.re - 1 := by linarith
  have h_sub_pos : 0 < s.re - 1 := by linarith
  rw [div_le_iff₀ h_denom_pos]
  have h_le : 1 ≤ ‖riemannZeta s‖ * ((2 * s.re - 1) / (s.re - 1)) := by
    calc
      1 = ‖riemannZeta s‖ * ‖L ↗ArithmeticFunction.moebius s‖ := h_norm_mul.symm
      _ ≤ ‖riemannZeta s‖ * ((2 * s.re - 1) / (s.re - 1)) :=
        mul_le_mul_of_nonneg_left h_mu h_zeta_pos.le
  rw [mul_div_assoc', le_div_iff₀ h_sub_pos, one_mul] at h_le
  exact h_le

/-- On the vertical line `s.re = 2`, `1 / 3 ≤ ‖riemannZeta s‖`. -/
theorem one_third_le_norm_riemannZeta_of_re_eq_two {s : ℂ} (hs : s.re = 2) :
    1 / 3 ≤ ‖riemannZeta s‖ := by
  have h := le_norm_riemannZeta_of_one_lt_re (s := s) (by linarith)
  rw [hs] at h
  norm_num at h
  exact h

/-- On the vertical line `s.re = 2`, `1 / 3 ≤ ‖riemannZeta₁ s‖`. -/
theorem one_third_le_norm_riemannZeta₁_of_re_eq_two {s : ℂ} (hs : s.re = 2) :
    1 / 3 ≤ ‖riemannZeta₁ s‖ := by
  have hs1 : s ≠ 1 := by intro h; subst h; simp at hs
  have h_eq : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hs1, ← mul_assoc,
      mul_inv_cancel₀ (sub_ne_zero.mpr hs1), one_mul]
  have h_sub : 1 ≤ ‖s - 1‖ := by
    calc
      (1 : ℝ) = (s - 1).re := by simp [hs]; ring
      _ ≤ ‖s - 1‖ := re_le_norm (s - 1)
  rw [h_eq, norm_mul]
  calc
    (1 / 3 : ℝ) = 1 * (1 / 3) := by ring
    _ ≤ ‖s - 1‖ * ‖riemannZeta s‖ :=
      mul_le_mul h_sub (one_third_le_norm_riemannZeta_of_re_eq_two hs) (by positivity)
        (norm_nonneg _)

/-!
## Section 1: Nonvanishing of `riemannZeta` and `riemannZeta₁` on `{s : ℂ | 1 / 2 < s.re}` under RH
-/

/-- Under `RiemannHypothesis`, `riemannZeta s ≠ 0` for all `s : ℂ` with
`1 / 2 < s.re` and `s ≠ 1`. -/
theorem riemannZeta_ne_zero_of_one_half_lt_re (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, rfl⟩
    have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hre := hRH s hz htriv hs1
  linarith

/-- Under `RiemannHypothesis`, `riemannZeta₁ s ≠ 0` for all `s : ℂ` with `1 / 2 < s.re`. -/
theorem riemannZeta₁_ne_zero_of_one_half_lt_re (hRH : RiemannHypothesis) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    riemannZeta₁ s ≠ 0 := by
  rcases eq_or_ne s 1 with rfl | hs1
  · rw [riemannZeta₁_one]
    exact one_ne_zero
  · intro hz
    have h_eq := riemannZeta_eq_inv_sub_mul hs1
    rw [hz, mul_zero] at h_eq
    exact riemannZeta_ne_zero_of_one_half_lt_re hRH hs hs1 h_eq

/-- Every `w ∈ Metric.ball (2 + t * I) (3 / 2)` satisfies `1 / 2 < w.re`. -/
theorem one_half_lt_re_of_mem_ball_two_add_mul_I {t : ℝ} {w : ℂ}
    (hw : w ∈ Metric.ball (2 + (t : ℂ) * I) (3 / 2)) :
    1 / 2 < w.re := by
  rw [mem_ball_iff_norm] at hw
  have h1 : (2 + (t : ℂ) * I - w).re ≤ ‖2 + (t : ℂ) * I - w‖ := re_le_norm _
  rw [norm_sub_rev] at h1
  have h2 : (2 + (t : ℂ) * I - w).re = 2 - w.re := by simp
  linarith

/-- Under `RiemannHypothesis`, `z ↦ deriv riemannZeta₁ z / riemannZeta₁ z` is differentiable
at every `z : ℂ` with `1 / 2 < z.re`. -/
theorem differentiableAt_logDeriv_riemannZeta₁ (hRH : RiemannHypothesis) {z : ℂ}
    (hz : 1 / 2 < z.re) :
    DifferentiableAt ℂ (fun w ↦ deriv riemannZeta₁ w / riemannZeta₁ w) z :=
  (differentiable_riemannZeta₁.deriv z).div (differentiable_riemannZeta₁ z)
    (riemannZeta₁_ne_zero_of_one_half_lt_re hRH hz)

/-- Under `RiemannHypothesis`, `z ↦ deriv riemannZeta₁ z / riemannZeta₁ z` is differentiable
on `Metric.ball (2 + t * I) (3 / 2)`. -/
theorem differentiableOn_logDeriv_riemannZeta₁_ball (hRH : RiemannHypothesis) (t : ℝ) :
    DifferentiableOn ℂ (fun w ↦ deriv riemannZeta₁ w / riemannZeta₁ w)
      (Metric.ball (2 + (t : ℂ) * I) (3 / 2)) :=
  fun _ hz ↦ (differentiableAt_logDeriv_riemannZeta₁ hRH
    (one_half_lt_re_of_mem_ball_two_add_mul_I hz)).differentiableWithinAt

/-!
## Section 2: Holomorphic Branch `logRiemannZeta₁Branch` on `Metric.ball (2 + t * I) (3 / 2)`
-/

/-- The holomorphic branch of `log (riemannZeta₁ w / riemannZeta₁ (2 + t * I))` on
`Metric.ball (2 + t * I) (3 / 2)`, constructed via `Complex.wedgeIntegral` of
`deriv riemannZeta₁ / riemannZeta₁` from the basepoint `2 + t * I`. -/
noncomputable def logRiemannZeta₁Branch (t : ℝ) (w : ℂ) : ℂ :=
  Complex.wedgeIntegral (2 + (t : ℂ) * I) w (fun z ↦ deriv riemannZeta₁ z / riemannZeta₁ z)

/-- At the center `2 + t * I`, `logRiemannZeta₁Branch t (2 + t * I) = 0`. -/
@[simp]
theorem logRiemannZeta₁Branch_self (t : ℝ) :
    logRiemannZeta₁Branch t (2 + (t : ℂ) * I) = 0 := by
  simp [logRiemannZeta₁Branch, Complex.wedgeIntegral]

/-- Under `RiemannHypothesis`, for every `w ∈ Metric.ball (2 + t * I) (3 / 2)`,
`logRiemannZeta₁Branch t` has derivative `deriv riemannZeta₁ w / riemannZeta₁ w` at `w`. -/
theorem hasDerivAt_logRiemannZeta₁Branch (hRH : RiemannHypothesis) {t : ℝ} {w : ℂ}
    (hw : w ∈ Metric.ball (2 + (t : ℂ) * I) (3 / 2)) :
    HasDerivAt (logRiemannZeta₁Branch t) (deriv riemannZeta₁ w / riemannZeta₁ w) w := by
  have hd := differentiableOn_logDeriv_riemannZeta₁_ball hRH t
  exact hd.isConservativeOn.hasDerivAt_wedgeIntegral hd.continuousOn hw

/-- Under `RiemannHypothesis`, `logRiemannZeta₁Branch t` is differentiable at every
`w ∈ Metric.ball (2 + t * I) (3 / 2)`. -/
theorem differentiableAt_logRiemannZeta₁Branch (hRH : RiemannHypothesis) {t : ℝ} {w : ℂ}
    (hw : w ∈ Metric.ball (2 + (t : ℂ) * I) (3 / 2)) :
    DifferentiableAt ℂ (logRiemannZeta₁Branch t) w :=
  (hasDerivAt_logRiemannZeta₁Branch hRH hw).differentiableAt

/-- Under `RiemannHypothesis`, `logRiemannZeta₁Branch t` is differentiable on
`Metric.ball (2 + t * I) (3 / 2)`. -/
theorem differentiableOn_logRiemannZeta₁Branch (hRH : RiemannHypothesis) (t : ℝ) :
    DifferentiableOn ℂ (logRiemannZeta₁Branch t) (Metric.ball (2 + (t : ℂ) * I) (3 / 2)) :=
  fun _ hw ↦ (differentiableAt_logRiemannZeta₁Branch hRH hw).differentiableWithinAt

/-- Under `RiemannHypothesis`, for every `w ∈ Metric.ball (2 + t * I) (3 / 2)`,
`deriv (logRiemannZeta₁Branch t) w = deriv riemannZeta₁ w / riemannZeta₁ w`. -/
theorem deriv_logRiemannZeta₁Branch (hRH : RiemannHypothesis) {t : ℝ} {w : ℂ}
    (hw : w ∈ Metric.ball (2 + (t : ℂ) * I) (3 / 2)) :
    deriv (logRiemannZeta₁Branch t) w = deriv riemannZeta₁ w / riemannZeta₁ w :=
  (hasDerivAt_logRiemannZeta₁Branch hRH hw).deriv

/-- Under `RiemannHypothesis`, for every `w ∈ Metric.ball (2 + t * I) (3 / 2)`,
`riemannZeta₁ w * Complex.exp (-logRiemannZeta₁Branch t w) = riemannZeta₁ (2 + t * I)`. -/
theorem riemannZeta₁_mul_exp_neg_logRiemannZeta₁Branch (hRH : RiemannHypothesis) {t : ℝ} {w : ℂ}
    (hw : w ∈ Metric.ball (2 + (t : ℂ) * I) (3 / 2)) :
    riemannZeta₁ w * Complex.exp (-logRiemannZeta₁Branch t w) =
      riemannZeta₁ (2 + (t : ℂ) * I) := by
  let c : ℂ := 2 + (t : ℂ) * I
  let g : ℂ → ℂ := fun z ↦ riemannZeta₁ z * Complex.exp (-logRiemannZeta₁Branch t z)
  have hg_hasDeriv : ∀ z ∈ Metric.ball c (3 / 2), HasDerivAt g 0 z := by
    intro z hz
    have hz_ne : riemannZeta₁ z ≠ 0 :=
      riemannZeta₁_ne_zero_of_one_half_lt_re hRH (one_half_lt_re_of_mem_ball_two_add_mul_I hz)
    have h1 : HasDerivAt riemannZeta₁ (deriv riemannZeta₁ z) z :=
      (differentiable_riemannZeta₁ z).hasDerivAt
    have h2 : HasDerivAt (fun u ↦ Complex.exp (-logRiemannZeta₁Branch t u))
        (Complex.exp (-logRiemannZeta₁Branch t z) * -(deriv riemannZeta₁ z / riemannZeta₁ z)) z :=
      (hasDerivAt_logRiemannZeta₁Branch hRH hz).neg.cexp
    convert h1.mul h2 using 1
    field_simp [hz_ne]
    ring
  have hg_diff : DifferentiableOn ℂ g (Metric.ball c (3 / 2)) :=
    fun z hz ↦ (hg_hasDeriv z hz).differentiableAt.differentiableWithinAt
  have hg_deriv : (Metric.ball c (3 / 2)).EqOn (deriv g) 0 :=
    fun z hz ↦ (hg_hasDeriv z hz).deriv
  have hc_mem : c ∈ Metric.ball c (3 / 2) := mem_ball_self (by norm_num)
  have h_eq := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c (3 / 2)).isPreconnected
    hg_diff hg_deriv hw hc_mem
  simpa [g, c] using h_eq

/-- Under `RiemannHypothesis`, for every `w ∈ Metric.ball (2 + t * I) (3 / 2)`,
`Complex.exp (logRiemannZeta₁Branch t w) = riemannZeta₁ w / riemannZeta₁ (2 + t * I)`. -/
theorem exp_logRiemannZeta₁Branch (hRH : RiemannHypothesis) {t : ℝ} {w : ℂ}
    (hw : w ∈ Metric.ball (2 + (t : ℂ) * I) (3 / 2)) :
    Complex.exp (logRiemannZeta₁Branch t w) =
      riemannZeta₁ w / riemannZeta₁ (2 + (t : ℂ) * I) := by
  have hc_ne : riemannZeta₁ (2 + (t : ℂ) * I) ≠ 0 :=
    riemannZeta₁_ne_zero_of_one_half_lt_re hRH (by simp; norm_num)
  have h_id := riemannZeta₁_mul_exp_neg_logRiemannZeta₁Branch hRH hw
  rw [eq_div_iff hc_ne]
  calc
    Complex.exp (logRiemannZeta₁Branch t w) * riemannZeta₁ (2 + (t : ℂ) * I)
      = Complex.exp (logRiemannZeta₁Branch t w) *
          (riemannZeta₁ w * Complex.exp (-logRiemannZeta₁Branch t w)) := by rw [← h_id]
    _ = riemannZeta₁ w *
          (Complex.exp (logRiemannZeta₁Branch t w) * Complex.exp (-logRiemannZeta₁Branch t w)) := by
        ring
    _ = riemannZeta₁ w * 1 := by rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    _ = riemannZeta₁ w := mul_one _

/-- Under `RiemannHypothesis`, for every `w ∈ Metric.ball (2 + t * I) (3 / 2)`,
`(logRiemannZeta₁Branch t w).re = Real.log (‖riemannZeta₁ w‖ / ‖riemannZeta₁ (2 + t * I)‖)`. -/
theorem re_logRiemannZeta₁Branch (hRH : RiemannHypothesis) {t : ℝ} {w : ℂ}
    (hw : w ∈ Metric.ball (2 + (t : ℂ) * I) (3 / 2)) :
    (logRiemannZeta₁Branch t w).re =
      Real.log (‖riemannZeta₁ w‖ / ‖riemannZeta₁ (2 + (t : ℂ) * I)‖) := by
  have h_norm := congrArg norm (exp_logRiemannZeta₁Branch hRH hw)
  rw [Complex.norm_exp, norm_div] at h_norm
  rw [← h_norm, Real.log_exp]

/-- Under `RiemannHypothesis`, for every `w ∈ Metric.ball (2 + t * I) (3 / 2)`,
`(logRiemannZeta₁Branch t w).re ≤ Real.log (3 * ‖riemannZeta₁ w‖)`. -/
theorem re_logRiemannZeta₁Branch_le (hRH : RiemannHypothesis) {t : ℝ} {w : ℂ}
    (hw : w ∈ Metric.ball (2 + (t : ℂ) * I) (3 / 2)) :
    (logRiemannZeta₁Branch t w).re ≤ Real.log (3 * ‖riemannZeta₁ w‖) := by
  rw [re_logRiemannZeta₁Branch hRH hw]
  have hw_pos : 0 < ‖riemannZeta₁ w‖ :=
    norm_pos_iff.mpr (riemannZeta₁_ne_zero_of_one_half_lt_re hRH
      (one_half_lt_re_of_mem_ball_two_add_mul_I hw))
  have hc_norm : 1 / 3 ≤ ‖riemannZeta₁ (2 + (t : ℂ) * I)‖ :=
    one_third_le_norm_riemannZeta₁_of_re_eq_two (by simp)
  have hc_pos : 0 < ‖riemannZeta₁ (2 + (t : ℂ) * I)‖ := by linarith
  refine Real.log_le_log (div_pos hw_pos hc_pos) ?_
  rw [div_le_iff₀ hc_pos]
  calc
    ‖riemannZeta₁ w‖ = 3 * ‖riemannZeta₁ w‖ * (1 / 3) := by ring
    _ ≤ 3 * ‖riemannZeta₁ w‖ * ‖riemannZeta₁ (2 + (t : ℂ) * I)‖ :=
      mul_le_mul_of_nonneg_left hc_norm (by positivity)

/-!
## Section 3: Centered Borel–Carathéodory Theorem and Bound on `‖logRiemannZeta₁Branch t w‖`
-/

/-- **Centered Borel–Carathéodory Theorem on `Metric.ball c R`**:
If `f` is complex-differentiable on `Metric.ball c R` (`0 < R`), `f c = 0`, and `(f w).re ≤ M`
(`0 < M`) for all `w ∈ Metric.ball c R`, then for every `z ∈ Metric.ball c R`,
`‖f z‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖)`. -/
theorem borelCaratheodory_ball {c z : ℂ} {R M : ℝ} {f : ℂ → ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hf₁ : ∀ w ∈ Metric.ball c R, (f w).re ≤ M) (hR : 0 < R)
    (hz : z ∈ Metric.ball c R) (hf₂ : f c = 0) :
    ‖f z‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖) := by
  let g : ℂ → ℂ := fun u ↦ f (c + u)
  have h_maps_ball : MapsTo (fun u : ℂ ↦ c + u) (Metric.ball 0 R) (Metric.ball c R) := by
    intro u hu
    rw [mem_ball_zero_iff] at hu
    rw [mem_ball_iff_norm, add_sub_cancel_left]
    exact hu
  have hg_diff : DifferentiableOn ℂ g (Metric.ball 0 R) :=
    hf.comp (differentiable_id.const_add c).differentiableOn h_maps_ball
  have hg_re : MapsTo g (Metric.ball 0 R) {w : ℂ | w.re ≤ M} :=
    fun u hu ↦ hf₁ (c + u) (h_maps_ball hu)
  have hz0 : z - c ∈ Metric.ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]
    exact mem_ball_iff_norm.mp hz
  have hg0 : g 0 = 0 := by simp [g, hf₂]
  have h_bc := Complex.borelCaratheodory_zero hM hg_diff hg_re hR hz0 hg0
  simpa [g] using h_bc

/-- Explicit growth bound for `‖riemannZeta₁ w‖` on `Metric.closedBall (2 + t * I) R`
for `0 ≤ R < 2`. -/
noncomputable def zeta₁BallBound (t R : ℝ) : ℝ :=
  1 + (‖(1 : ℂ) + (t : ℂ) * I‖ + R) * (1 + (‖(2 : ℂ) + (t : ℂ) * I‖ + R) / (2 - R))

/-- For `0 ≤ R < 2`, `1 ≤ zeta₁BallBound t R`. -/
theorem one_le_zeta₁BallBound (t : ℝ) {R : ℝ} (hR : 0 ≤ R) (hR2 : R < 2) :
    1 ≤ zeta₁BallBound t R := by
  unfold zeta₁BallBound
  have h1 : 0 ≤ ‖(1 : ℂ) + (t : ℂ) * I‖ + R := by positivity
  have h2 : 0 ≤ 1 + (‖(2 : ℂ) + (t : ℂ) * I‖ + R) / (2 - R) :=
    add_nonneg zero_le_one (div_nonneg (by positivity) (by linarith))
  linarith [mul_nonneg h1 h2]

/-- For `0 ≤ R < 2`, `0 < Real.log (3 * zeta₁BallBound t R)`. -/
theorem log_three_mul_zeta₁BallBound_pos (t : ℝ) {R : ℝ} (hR : 0 ≤ R) (hR2 : R < 2) :
    0 < Real.log (3 * zeta₁BallBound t R) := by
  refine Real.log_pos ?_
  linarith [one_le_zeta₁BallBound t hR hR2]

/-- For `0 ≤ R < 2` and `w ∈ Metric.closedBall (2 + t * I) R`,
`‖riemannZeta₁ w‖ ≤ zeta₁BallBound t R`. -/
theorem norm_riemannZeta₁_le_zeta₁BallBound {t R : ℝ} {w : ℂ}
    (hR : 0 ≤ R) (hR2 : R < 2) (hw : w ∈ Metric.closedBall (2 + (t : ℂ) * I) R) :
    ‖riemannZeta₁ w‖ ≤ zeta₁BallBound t R := by
  let c : ℂ := 2 + (t : ℂ) * I
  rw [mem_closedBall_iff_norm] at hw
  have hw_re : 2 - R ≤ w.re := by
    have h1 : (c - w).re ≤ ‖c - w‖ := re_le_norm (c - w)
    rw [norm_sub_rev] at h1
    have h2 : (c - w).re = 2 - w.re := by simp [c]
    linarith
  have hw_re_pos : 0 < w.re := by linarith
  have hw_norm : ‖w‖ ≤ ‖c‖ + R := by
    calc
      ‖w‖ = ‖c + (w - c)‖ := by ring_nf
      _ ≤ ‖c‖ + ‖w - c‖ := norm_add_le _ _
      _ ≤ ‖c‖ + R := by linarith
  have hw_sub_one : ‖w - 1‖ ≤ ‖(1 : ℂ) + (t : ℂ) * I‖ + R := by
    have hc1 : c - 1 = (1 : ℂ) + (t : ℂ) * I := by simp [c]; ring
    calc
      ‖w - 1‖ = ‖(c - 1) + (w - c)‖ := by ring_nf
      _ ≤ ‖c - 1‖ + ‖w - c‖ := norm_add_le _ _
      _ ≤ ‖(1 : ℂ) + (t : ℂ) * I‖ + R := by rw [hc1]; linarith
  have h_div : ‖w‖ / w.re ≤ (‖c‖ + R) / (2 - R) :=
    div_le_div₀ (by positivity) hw_norm (by linarith) hw_re
  refine (norm_riemannZeta₁_le hw_re_pos).trans ?_
  unfold zeta₁BallBound
  gcongr

/-- Under `RiemannHypothesis`, for `0 < R ≤ 3 / 2` and `w ∈ Metric.ball (2 + t * I) R`,
`(logRiemannZeta₁Branch t w).re ≤ Real.log (3 * zeta₁BallBound t R)`. -/
theorem re_logRiemannZeta₁Branch_le_zeta₁BallBound (hRH : RiemannHypothesis) {t R : ℝ} {w : ℂ}
    (hR : 0 < R) (hR_le : R ≤ 3 / 2) (hw : w ∈ Metric.ball (2 + (t : ℂ) * I) R) :
    (logRiemannZeta₁Branch t w).re ≤ Real.log (3 * zeta₁BallBound t R) := by
  have hw_32 : w ∈ Metric.ball (2 + (t : ℂ) * I) (3 / 2) :=
    ball_subset_ball hR_le hw
  refine (re_logRiemannZeta₁Branch_le hRH hw_32).trans ?_
  have hw_pos : 0 < ‖riemannZeta₁ w‖ :=
    norm_pos_iff.mpr (riemannZeta₁_ne_zero_of_one_half_lt_re hRH
      (one_half_lt_re_of_mem_ball_two_add_mul_I hw_32))
  refine Real.log_le_log (by positivity) ?_
  exact mul_le_mul_of_nonneg_left
    (norm_riemannZeta₁_le_zeta₁BallBound hR.le (by linarith) (ball_subset_closedBall hw))
    (by positivity)

/-- **Explicit Borel–Carathéodory Bound on `‖logRiemannZeta₁Branch t w‖`**:
Under `RiemannHypothesis`, for `0 < R ≤ 3 / 2` and `w ∈ Metric.ball (2 + t * I) R`,
`‖logRiemannZeta₁Branch t w‖ ≤`
`2 * Real.log (3 * zeta₁BallBound t R) * ‖w - (2 + t * I)‖ / (R - ‖w - (2 + t * I)‖)`. -/
theorem norm_logRiemannZeta₁Branch_le_of_mem_ball (hRH : RiemannHypothesis) {t R : ℝ} {w : ℂ}
    (hR : 0 < R) (hR_le : R ≤ 3 / 2) (hw : w ∈ Metric.ball (2 + (t : ℂ) * I) R) :
    ‖logRiemannZeta₁Branch t w‖ ≤
      2 * Real.log (3 * zeta₁BallBound t R) * ‖w - (2 + (t : ℂ) * I)‖ /
        (R - ‖w - (2 + (t : ℂ) * I)‖) := by
  refine borelCaratheodory_ball
    (log_three_mul_zeta₁BallBound_pos t hR.le (by linarith))
    ((differentiableOn_logRiemannZeta₁Branch hRH t).mono (ball_subset_ball hR_le))
    (fun z hz ↦ re_logRiemannZeta₁Branch_le_zeta₁BallBound hRH hR hR_le hz)
    hR hw (logRiemannZeta₁Branch_self t)

/-- **Uniform Borel–Carathéodory Bound on `Metric.closedBall (2 + t * I) r`**:
Under `RiemannHypothesis`, for `0 ≤ r < R ≤ 3 / 2` and `w ∈ Metric.closedBall (2 + t * I) r`,
`‖logRiemannZeta₁Branch t w‖ ≤ 2 * Real.log (3 * zeta₁BallBound t R) * r / (R - r)`. -/
theorem norm_logRiemannZeta₁Branch_le_of_mem_closedBall (hRH : RiemannHypothesis) {t r R : ℝ}
    {w : ℂ}
    (hr : 0 ≤ r) (hrR : r < R) (hR_le : R ≤ 3 / 2)
    (hw : w ∈ Metric.closedBall (2 + (t : ℂ) * I) r) :
    ‖logRiemannZeta₁Branch t w‖ ≤
      2 * Real.log (3 * zeta₁BallBound t R) * r / (R - r) := by
  have hR_pos : 0 < R := hr.trans_lt hrR
  have hw_norm : ‖w - (2 + (t : ℂ) * I)‖ ≤ r := mem_closedBall_iff_norm.mp hw
  have hw_ball : w ∈ Metric.ball (2 + (t : ℂ) * I) R :=
    mem_ball_iff_norm.mpr (hw_norm.trans_lt hrR)
  refine (norm_logRiemannZeta₁Branch_le_of_mem_ball hRH hR_pos hR_le hw_ball).trans ?_
  have hM_pos : 0 ≤ 2 * Real.log (3 * zeta₁BallBound t R) :=
    mul_nonneg zero_le_two (log_three_mul_zeta₁BallBound_pos t hR_pos.le (by linarith)).le
  exact div_le_div₀ (mul_nonneg hM_pos hr)
    (mul_le_mul_of_nonneg_left hw_norm hM_pos)
    (by linarith) (by linarith)

/-!
## Section 4: Explicit Cauchy Derivative Estimates on `ζ₁'/ζ₁` and `ζ'/ζ`
-/

/-- **Explicit Cauchy Derivative Bound on `‖deriv riemannZeta₁ w / riemannZeta₁ w‖`**:
Under `RiemannHypothesis`, for `0 ≤ r`, `0 < ρ`, `r + ρ < R ≤ 3 / 2`, and
`w ∈ Metric.closedBall (2 + t * I) r`,
`‖deriv riemannZeta₁ w / riemannZeta₁ w‖ ≤`
`2 * Real.log (3 * zeta₁BallBound t R) * (r + ρ) / (ρ * (R - (r + ρ)))`. -/
theorem norm_logDeriv_riemannZeta₁_le_of_mem_closedBall (hRH : RiemannHypothesis)
    {t r ρ R : ℝ} {w : ℂ} (hr : 0 ≤ r) (hρ : 0 < ρ) (hrρR : r + ρ < R) (hR_le : R ≤ 3 / 2)
    (hw : w ∈ Metric.closedBall (2 + (t : ℂ) * I) r) :
    ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ ≤
      2 * Real.log (3 * zeta₁BallBound t R) * (r + ρ) / (ρ * (R - (r + ρ))) := by
  let c : ℂ := 2 + (t : ℂ) * I
  have hw_norm : ‖w - c‖ ≤ r := mem_closedBall_iff_norm.mp hw
  have hw_ball : w ∈ Metric.ball c (3 / 2) :=
    mem_ball_iff_norm.mpr (by linarith)
  rw [← deriv_logRiemannZeta₁Branch hRH hw_ball]
  have h_sub_closed : Metric.closedBall w ρ ⊆ Metric.ball c (3 / 2) := by
    intro z hz
    rw [mem_closedBall_iff_norm] at hz
    rw [mem_ball_iff_norm]
    have h1 : ‖z - c‖ ≤ ‖z - w‖ + ‖w - c‖ := by
      calc
        ‖z - c‖ = ‖(z - w) + (w - c)‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w - c‖ := norm_add_le _ _
    linarith
  have hd : DiffContOnCl ℂ (logRiemannZeta₁Branch t) (Metric.ball w ρ) :=
    ((differentiableOn_logRiemannZeta₁Branch hRH t).mono
      (closure_ball_subset_closedBall.trans h_sub_closed)).diffContOnCl
  have h_sphere : ∀ z ∈ Metric.sphere w ρ,
      ‖logRiemannZeta₁Branch t z‖ ≤
        2 * Real.log (3 * zeta₁BallBound t R) * (r + ρ) / (R - (r + ρ)) := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hz_closed : z ∈ Metric.closedBall c (r + ρ) := by
      rw [mem_closedBall_iff_norm]
      calc
        ‖z - c‖ = ‖(z - w) + (w - c)‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w - c‖ := norm_add_le _ _
        _ ≤ r + ρ := by linarith
    exact norm_logRiemannZeta₁Branch_le_of_mem_closedBall hRH (by linarith) hrρR hR_le hz_closed
  have h_cauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hd h_sphere
  rw [div_div, mul_comm (R - (r + ρ)) ρ] at h_cauchy
  exact h_cauchy

/-- **Explicit Strip Bound on `‖deriv riemannZeta₁ w / riemannZeta₁ w‖` under `RiemannHypothesis`**:
For any `0 < d ≤ 1 / 2` and `w : ℂ` with `1 / 2 + 2 * d ≤ w.re` and `w.re ≤ 2`,
`‖deriv riemannZeta₁ w / riemannZeta₁ w‖ ≤`
`(6 / d ^ 2) * Real.log (3 * zeta₁BallBound w.im (3 / 2 - d / 2))`. -/
theorem norm_logDeriv_riemannZeta₁_le_of_strip (hRH : RiemannHypothesis) {d : ℝ} {w : ℂ}
    (hd_pos : 0 < d) (hd_le : d ≤ 1 / 2)
    (hw_lo : 1 / 2 + 2 * d ≤ w.re) (hw_hi : w.re ≤ 2) :
    ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ ≤
      (6 / d ^ 2) * Real.log (3 * zeta₁BallBound w.im (3 / 2 - d / 2)) := by
  let t : ℝ := w.im
  let r : ℝ := 3 / 2 - 2 * d
  let ρ : ℝ := d
  let R : ℝ := 3 / 2 - d / 2
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hrρR : r + ρ < R := by dsimp [r, ρ, R]; linarith
  have hR_le : R ≤ 3 / 2 := by dsimp [R]; linarith
  have hw_closed : w ∈ Metric.closedBall (2 + (t : ℂ) * I) r := by
    rw [mem_closedBall_iff_norm]
    have h_sub : w - (2 + (t : ℂ) * I) = ((w.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [t]
    rw [h_sub, norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    dsimp [r]
    linarith
  have h_bound := norm_logDeriv_riemannZeta₁_le_of_mem_closedBall hRH hr hd_pos hrρR hR_le hw_closed
  refine h_bound.trans ?_
  have h_log_pos : 0 ≤ Real.log (3 * zeta₁BallBound t R) :=
    (log_three_mul_zeta₁BallBound_pos t (by dsimp [R]; linarith) (by dsimp [R]; linarith)).le
  have h_denom : ρ * (R - (r + ρ)) = d ^ 2 / 2 := by dsimp [r, ρ, R]; ring
  have h_num : r + ρ ≤ 3 / 2 := by dsimp [r, ρ]; linarith
  rw [h_denom]
  calc
    2 * Real.log (3 * zeta₁BallBound t R) * (r + ρ) / (d ^ 2 / 2)
      ≤ 2 * Real.log (3 * zeta₁BallBound t R) * (3 / 2) / (d ^ 2 / 2) := by
        gcongr
    _ = (6 / d ^ 2) * Real.log (3 * zeta₁BallBound t R) := by
        have : d ^ 2 ≠ 0 := pow_ne_zero 2 hd_pos.ne'
        field_simp
        ring

/-- For every `w : ℂ` with `w ≠ 1` and `riemannZeta₁ w ≠ 0`,
`deriv riemannZeta w / riemannZeta w = deriv riemannZeta₁ w / riemannZeta₁ w - 1 / (w - 1)`. -/
theorem logDeriv_riemannZeta_eq_sub {w : ℂ} (hw1 : w ≠ 1) (hz1 : riemannZeta₁ w ≠ 0) :
    deriv riemannZeta w / riemannZeta w =
      deriv riemannZeta₁ w / riemannZeta₁ w - 1 / (w - 1) := by
  have hw_sub : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
  have h_ev : riemannZeta =ᶠ[𝓝 w] (fun z ↦ (z - 1)⁻¹ * riemannZeta₁ z) := by
    filter_upwards [isOpen_ne.mem_nhds hw1] with z hz
    exact riemannZeta_eq_inv_sub_mul hz
  have h_deriv_inv : HasDerivAt (fun z : ℂ ↦ (z - 1)⁻¹) (-1 / (w - 1) ^ 2) w :=
    ((hasDerivAt_id w).sub_const (1 : ℂ)).inv hw_sub
  have h_deriv_prod : HasDerivAt (fun z : ℂ ↦ (z - 1)⁻¹ * riemannZeta₁ z)
      (-1 / (w - 1) ^ 2 * riemannZeta₁ w + (w - 1)⁻¹ * deriv riemannZeta₁ w) w :=
    h_deriv_inv.mul (differentiable_riemannZeta₁ w).hasDerivAt
  have h_deriv_zeta : deriv riemannZeta w =
      -1 / (w - 1) ^ 2 * riemannZeta₁ w + (w - 1)⁻¹ * deriv riemannZeta₁ w :=
    (h_ev.hasDerivAt_iff.mpr h_deriv_prod).deriv
  rw [h_deriv_zeta, riemannZeta_eq_inv_sub_mul hw1]
  field_simp [hw_sub, hz1]
  ring

/-- **Explicit Strip Bound on `‖deriv riemannZeta w / riemannZeta w‖` under `RiemannHypothesis`**:
For any `0 < d ≤ 1 / 2` and `w : ℂ` with `1 / 2 + 2 * d ≤ w.re`, `w.re ≤ 2`, and `w ≠ 1`,
`‖deriv riemannZeta w / riemannZeta w‖ ≤`
`(6 / d ^ 2) * Real.log (3 * zeta₁BallBound w.im (3 / 2 - d / 2)) + 1 / ‖w - 1‖`. -/
theorem norm_logDeriv_riemannZeta_le_of_strip (hRH : RiemannHypothesis) {d : ℝ} {w : ℂ}
    (hd_pos : 0 < d) (hd_le : d ≤ 1 / 2)
    (hw_lo : 1 / 2 + 2 * d ≤ w.re) (hw_hi : w.re ≤ 2) (hw1 : w ≠ 1) :
    ‖deriv riemannZeta w / riemannZeta w‖ ≤
      (6 / d ^ 2) * Real.log (3 * zeta₁BallBound w.im (3 / 2 - d / 2)) + 1 / ‖w - 1‖ := by
  have hz1 : riemannZeta₁ w ≠ 0 :=
    riemannZeta₁_ne_zero_of_one_half_lt_re hRH (by linarith)
  rw [logDeriv_riemannZeta_eq_sub hw1 hz1]
  have h_tri : ‖deriv riemannZeta₁ w / riemannZeta₁ w - 1 / (w - 1)‖ ≤
      ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ + 1 / ‖w - 1‖ := by
    calc
      ‖deriv riemannZeta₁ w / riemannZeta₁ w - 1 / (w - 1)‖
        ≤ ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ + ‖1 / (w - 1)‖ := norm_sub_le _ _
      _ = ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ + 1 / ‖w - 1‖ := by
        rw [norm_div 1 (w - 1), norm_one]
  linarith [norm_logDeriv_riemannZeta₁_le_of_strip hRH hd_pos hd_le hw_lo hw_hi]

/-- For `0 ≤ R ≤ 3 / 2` and `t : ℝ`,
`3 * zeta₁BallBound t R ≤ (10 * (1 + |t|)) ^ 2`. -/
theorem three_mul_zeta₁BallBound_le_sq (t : ℝ) {R : ℝ} (hR : 0 ≤ R) (hR_le : R ≤ 3 / 2) :
    3 * zeta₁BallBound t R ≤ (10 * (1 + |t|)) ^ 2 := by
  unfold zeta₁BallBound
  have h_norm1 : ‖(1 : ℂ) + (t : ℂ) * I‖ ≤ 1 + |t| := by
    calc
      ‖(1 : ℂ) + (t : ℂ) * I‖ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 1 + |t| := by simp
  have h_norm2 : ‖(2 : ℂ) + (t : ℂ) * I‖ ≤ 2 + |t| := by
    calc
      ‖(2 : ℂ) + (t : ℂ) * I‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |t| := by simp
  have h_div : (‖(2 : ℂ) + (t : ℂ) * I‖ + R) / (2 - R) ≤ 2 * (4 + |t|) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg t]
  have h_prod : (‖(1 : ℂ) + (t : ℂ) * I‖ + R) * (1 + (‖(2 : ℂ) + (t : ℂ) * I‖ + R) / (2 - R)) ≤
      (3 + |t|) * (9 + 2 * |t|) := by
    refine mul_le_mul (by linarith) (by linarith)
      (add_nonneg zero_le_one (div_nonneg (by positivity) (by linarith)))
      (by linarith [abs_nonneg t])
  nlinarith [abs_nonneg t, sq_nonneg |t|]

/-- For `0 ≤ R ≤ 3 / 2` and `t : ℝ`,
`Real.log (3 * zeta₁BallBound t R) ≤ 2 * Real.log (10 * (1 + |t|))`. -/
theorem log_three_mul_zeta₁BallBound_le (t : ℝ) {R : ℝ} (hR : 0 ≤ R) (hR_le : R ≤ 3 / 2) :
    Real.log (3 * zeta₁BallBound t R) ≤ 2 * Real.log (10 * (1 + |t|)) := by
  have h_pos : 0 < 3 * zeta₁BallBound t R := by
    linarith [one_le_zeta₁BallBound t hR (by linarith)]
  have h_base_pos : 0 < 10 * (1 + |t|) := by positivity
  have h_le := Real.log_le_log h_pos (three_mul_zeta₁BallBound_le_sq t hR hR_le)
  rwa [Real.log_pow, Nat.cast_ofNat] at h_le

/-- **Explicit Logarithmic-Height Bound on `‖deriv riemannZeta₁ w / riemannZeta₁ w‖` under RH**:
For any `0 < d ≤ 1 / 2` and `w : ℂ` with `1 / 2 + 2 * d ≤ w.re` and `w.re ≤ 2`,
`‖deriv riemannZeta₁ w / riemannZeta₁ w‖ ≤ (12 / d ^ 2) * Real.log (10 * (1 + |w.im|))`. -/
theorem norm_logDeriv_riemannZeta₁_le_log_abs_im (hRH : RiemannHypothesis) {d : ℝ} {w : ℂ}
    (hd_pos : 0 < d) (hd_le : d ≤ 1 / 2)
    (hw_lo : 1 / 2 + 2 * d ≤ w.re) (hw_hi : w.re ≤ 2) :
    ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ ≤
      (12 / d ^ 2) * Real.log (10 * (1 + |w.im|)) := by
  have h1 := norm_logDeriv_riemannZeta₁_le_of_strip hRH hd_pos hd_le hw_lo hw_hi
  have h2 := log_three_mul_zeta₁BallBound_le w.im (R := 3 / 2 - d / 2) (by linarith) (by linarith)
  calc
    ‖deriv riemannZeta₁ w / riemannZeta₁ w‖
      ≤ (6 / d ^ 2) * Real.log (3 * zeta₁BallBound w.im (3 / 2 - d / 2)) := h1
    _ ≤ (6 / d ^ 2) * (2 * Real.log (10 * (1 + |w.im|))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (12 / d ^ 2) * Real.log (10 * (1 + |w.im|)) := by ring

/-- **Explicit Logarithmic-Height Bound on `‖deriv riemannZeta w / riemannZeta w‖` under RH**:
For any `0 < d ≤ 1 / 2` and `w : ℂ` with `1 / 2 + 2 * d ≤ w.re`, `w.re ≤ 2`, and `w ≠ 1`,
`‖deriv riemannZeta w / riemannZeta w‖ ≤`
`(12 / d ^ 2) * Real.log (10 * (1 + |w.im|)) + 1 / ‖w - 1‖`. -/
theorem norm_logDeriv_riemannZeta_le_log_abs_im (hRH : RiemannHypothesis) {d : ℝ} {w : ℂ}
    (hd_pos : 0 < d) (hd_le : d ≤ 1 / 2)
    (hw_lo : 1 / 2 + 2 * d ≤ w.re) (hw_hi : w.re ≤ 2) (hw1 : w ≠ 1) :
    ‖deriv riemannZeta w / riemannZeta w‖ ≤
      (12 / d ^ 2) * Real.log (10 * (1 + |w.im|)) + 1 / ‖w - 1‖ := by
  have hz1 : riemannZeta₁ w ≠ 0 :=
    riemannZeta₁_ne_zero_of_one_half_lt_re hRH (by linarith)
  rw [logDeriv_riemannZeta_eq_sub hw1 hz1]
  have h_tri : ‖deriv riemannZeta₁ w / riemannZeta₁ w - 1 / (w - 1)‖ ≤
      ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ + 1 / ‖w - 1‖ := by
    calc
      ‖deriv riemannZeta₁ w / riemannZeta₁ w - 1 / (w - 1)‖
        ≤ ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ + ‖1 / (w - 1)‖ := norm_sub_le _ _
      _ = ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ + 1 / ‖w - 1‖ := by
        rw [norm_div 1 (w - 1), norm_one]
  linarith [norm_logDeriv_riemannZeta₁_le_log_abs_im hRH hd_pos hd_le hw_lo hw_hi]

/-!
## Section 5: Geometric Extension to `w.re = 1 / 2` at Zero-Free Heights `U`
-/

/-- Every `w ∈ Metric.ball (2 + U * I) R` with `R < 2` satisfies `0 < w.re`. -/
theorem re_pos_of_mem_ball_two_add_mul_I_of_lt_two {U R : ℝ} {w : ℂ}
    (hR2 : R < 2) (hw : w ∈ Metric.ball (2 + (U : ℂ) * I) R) :
    0 < w.re := by
  rw [mem_ball_iff_norm] at hw
  have h1 : (2 + (U : ℂ) * I - w).re ≤ ‖2 + (U : ℂ) * I - w‖ := re_le_norm _
  rw [norm_sub_rev] at h1
  have h2 : (2 + (U : ℂ) * I - w).re = 2 - w.re := by simp
  linarith

/-- **Nonvanishing of `riemannZeta₁` on `Metric.ball (2 + U * I) (3 / 2 + Δ ^ 2 / 4)`
at Zero-Free Height `U`**:
Under `RiemannHypothesis`, if `0 < Δ ≤ 1 / 2` and every critical-line zero `ρ` of `riemannZeta`
satisfies `Δ ≤ |ρ.im - U|`, then `riemannZeta₁ w ≠ 0` for all
`w ∈ Metric.ball (2 + U * I) (3 / 2 + Δ ^ 2 / 4)`. -/
theorem riemannZeta₁_ne_zero_of_mem_ball_of_gap (hRH : RiemannHypothesis) {U Δ : ℝ} {w : ℂ}
    (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - U|)
    (hw : w ∈ Metric.ball (2 + (U : ℂ) * I) (3 / 2 + Δ ^ 2 / 4)) :
    riemannZeta₁ w ≠ 0 := by
  have hR_lt_two : 3 / 2 + Δ ^ 2 / 4 < 2 := by nlinarith
  have hw_re_pos : 0 < w.re := re_pos_of_mem_ball_two_add_mul_I_of_lt_two hR_lt_two hw
  rcases eq_or_ne w 1 with rfl | hw1
  · rw [riemannZeta₁_one]
    exact one_ne_zero
  · intro hz1
    have hz : riemannZeta w = 0 := by
      have h_eq := riemannZeta_eq_inv_sub_mul hw1
      rw [hz1, mul_zero] at h_eq
      exact h_eq
    have htriv : ¬∃ n : ℕ, w = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, rfl⟩
      have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hre : w.re = 1 / 2 := hRH w hz htriv hw1
    have h_im : Δ ≤ |w.im - U| := hgap w hz hre
    have h_im_sq : Δ ^ 2 ≤ (w.im - U) ^ 2 := by
      have h_abs_sq : Δ ^ 2 ≤ |w.im - U| ^ 2 :=
         pow_le_pow_left₀ hΔ_pos.le h_im 2
      rwa [sq_abs] at h_abs_sq
    rw [mem_ball_iff_norm] at hw
    have hw_sq : ‖w - (2 + (U : ℂ) * I)‖ ^ 2 < (3 / 2 + Δ ^ 2 / 4) ^ 2 :=
      pow_lt_pow_left₀ hw (norm_nonneg _) (by norm_num)
    have h_norm_sq : ‖w - (2 + (U : ℂ) * I)‖ ^ 2 = 9 / 4 + (w.im - U) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have h_sub_re : (w - (2 + (U : ℂ) * I)).re = -3 / 2 := by simp [hre]; ring
      have h_sub_im : (w - (2 + (U : ℂ) * I)).im = w.im - U := by simp
      rw [h_sub_re, h_sub_im]
      ring
    rw [h_norm_sq] at hw_sq
    have hΔ4 : Δ ^ 4 ≤ (1 / 4) * Δ ^ 2 := by
      have hΔ2_le : Δ ^ 2 ≤ 1 / 4 := by nlinarith
      nlinarith [sq_nonneg Δ]
    nlinarith

/-- General holomorphicity of `logRiemannZeta₁Branch U` on any ball `Metric.ball (2 + U * I) R₀`
on which `riemannZeta₁` is nonvanishing. -/
theorem hasDerivAt_logRiemannZeta₁Branch_of_ne_zero {U R₀ : ℝ} {w : ℂ}
    (h_ne : ∀ z ∈ Metric.ball (2 + (U : ℂ) * I) R₀, riemannZeta₁ z ≠ 0)
    (hw : w ∈ Metric.ball (2 + (U : ℂ) * I) R₀) :
    HasDerivAt (logRiemannZeta₁Branch U) (deriv riemannZeta₁ w / riemannZeta₁ w) w := by
  have hd : DifferentiableOn ℂ (fun z ↦ deriv riemannZeta₁ z / riemannZeta₁ z)
      (Metric.ball (2 + (U : ℂ) * I) R₀) := by
    intro z hz
    exact ((differentiable_riemannZeta₁.deriv z).div (differentiable_riemannZeta₁ z)
      (h_ne z hz)).differentiableWithinAt
  exact hd.isConservativeOn.hasDerivAt_wedgeIntegral hd.continuousOn hw

/-- General exponential identity for `logRiemannZeta₁Branch U` on `Metric.ball (2 + U * I) R₀`. -/
theorem exp_logRiemannZeta₁Branch_of_ne_zero {U R₀ : ℝ} {w : ℂ}
    (hR₀ : 0 < R₀) (h_ne : ∀ z ∈ Metric.ball (2 + (U : ℂ) * I) R₀, riemannZeta₁ z ≠ 0)
    (hw : w ∈ Metric.ball (2 + (U : ℂ) * I) R₀) :
    Complex.exp (logRiemannZeta₁Branch U w) =
      riemannZeta₁ w / riemannZeta₁ (2 + (U : ℂ) * I) := by
  let c : ℂ := 2 + (U : ℂ) * I
  let g : ℂ → ℂ := fun z ↦ riemannZeta₁ z * Complex.exp (-logRiemannZeta₁Branch U z)
  have hg_hasDeriv : ∀ z ∈ Metric.ball c R₀, HasDerivAt g 0 z := by
    intro z hz
    have hz_ne : riemannZeta₁ z ≠ 0 := h_ne z hz
    have h1 : HasDerivAt riemannZeta₁ (deriv riemannZeta₁ z) z :=
      (differentiable_riemannZeta₁ z).hasDerivAt
    have h2 : HasDerivAt (fun u ↦ Complex.exp (-logRiemannZeta₁Branch U u))
        (Complex.exp (-logRiemannZeta₁Branch U z) * -(deriv riemannZeta₁ z / riemannZeta₁ z)) z :=
      (hasDerivAt_logRiemannZeta₁Branch_of_ne_zero h_ne hz).neg.cexp
    convert h1.mul h2 using 1
    field_simp [hz_ne]
    ring
  have hg_diff : DifferentiableOn ℂ g (Metric.ball c R₀) :=
    fun z hz ↦ (hg_hasDeriv z hz).differentiableAt.differentiableWithinAt
  have hg_deriv : (Metric.ball c R₀).EqOn (deriv g) 0 :=
    fun z hz ↦ (hg_hasDeriv z hz).deriv
  have hc_mem : c ∈ Metric.ball c R₀ := mem_ball_self hR₀
  have h_id : riemannZeta₁ w * Complex.exp (-logRiemannZeta₁Branch U w) = riemannZeta₁ c := by
    have h_eq := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R₀).isPreconnected
      hg_diff hg_deriv hw hc_mem
    simpa [g, c] using h_eq
  have hc_ne : riemannZeta₁ c ≠ 0 := h_ne c hc_mem
  rw [eq_div_iff hc_ne]
  calc
    Complex.exp (logRiemannZeta₁Branch U w) * riemannZeta₁ c
      = Complex.exp (logRiemannZeta₁Branch U w) *
          (riemannZeta₁ w * Complex.exp (-logRiemannZeta₁Branch U w)) := by rw [← h_id]
    _ = riemannZeta₁ w *
          (Complex.exp (logRiemannZeta₁Branch U w) * Complex.exp (-logRiemannZeta₁Branch U w)) := by
        ring
    _ = riemannZeta₁ w * 1 := by rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    _ = riemannZeta₁ w := mul_one _

/-- General real-part upper bound for `logRiemannZeta₁Branch U` on `Metric.ball (2 + U * I) R₀`. -/
theorem re_logRiemannZeta₁Branch_le_of_ne_zero {U R₀ : ℝ} {w : ℂ}
    (hR₀ : 0 < R₀) (h_ne : ∀ z ∈ Metric.ball (2 + (U : ℂ) * I) R₀, riemannZeta₁ z ≠ 0)
    (hw : w ∈ Metric.ball (2 + (U : ℂ) * I) R₀) :
    (logRiemannZeta₁Branch U w).re ≤ Real.log (3 * ‖riemannZeta₁ w‖) := by
  have h_norm := congrArg norm (exp_logRiemannZeta₁Branch_of_ne_zero hR₀ h_ne hw)
  rw [Complex.norm_exp, norm_div] at h_norm
  have h_re : (logRiemannZeta₁Branch U w).re =
      Real.log (‖riemannZeta₁ w‖ / ‖riemannZeta₁ (2 + (U : ℂ) * I)‖) := by
    rw [← h_norm, Real.log_exp]
  rw [h_re]
  have hw_pos : 0 < ‖riemannZeta₁ w‖ := norm_pos_iff.mpr (h_ne w hw)
  have hc_norm : 1 / 3 ≤ ‖riemannZeta₁ (2 + (U : ℂ) * I)‖ :=
    one_third_le_norm_riemannZeta₁_of_re_eq_two (by simp)
  have hc_pos : 0 < ‖riemannZeta₁ (2 + (U : ℂ) * I)‖ := by linarith
  refine Real.log_le_log (div_pos hw_pos hc_pos) ?_
  rw [div_le_iff₀ hc_pos]
  calc
    ‖riemannZeta₁ w‖ = 3 * ‖riemannZeta₁ w‖ * (1 / 3) := by ring
    _ ≤ 3 * ‖riemannZeta₁ w‖ * ‖riemannZeta₁ (2 + (U : ℂ) * I)‖ :=
      mul_le_mul_of_nonneg_left hc_norm (by positivity)

/-!
## Section 6: Borel–Carathéodory, FTC, and Cauchy Derivative Bounds Across `w.re = 1 / 2`
-/

/-- For `0 ≤ R ≤ 7 / 4` and `t : ℝ`,
`3 * zeta₁BallBound t R ≤ (14 * (1 + |t|)) ^ 2`. -/
theorem three_mul_zeta₁BallBound_le_sq_of_le_seven_fourths (t : ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hR_le : R ≤ 7 / 4) :
    3 * zeta₁BallBound t R ≤ (14 * (1 + |t|)) ^ 2 := by
  unfold zeta₁BallBound
  have h_norm1 : ‖(1 : ℂ) + (t : ℂ) * I‖ ≤ 1 + |t| := by
    calc
      ‖(1 : ℂ) + (t : ℂ) * I‖ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 1 + |t| := by simp
  have h_norm2 : ‖(2 : ℂ) + (t : ℂ) * I‖ ≤ 2 + |t| := by
    calc
      ‖(2 : ℂ) + (t : ℂ) * I‖ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |t| := by simp
  have h_div : (‖(2 : ℂ) + (t : ℂ) * I‖ + R) / (2 - R) ≤ 4 * (4 + |t|) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg t]
  have h_prod : (‖(1 : ℂ) + (t : ℂ) * I‖ + R) * (1 + (‖(2 : ℂ) + (t : ℂ) * I‖ + R) / (2 - R)) ≤
      (3 + |t|) * (17 + 4 * |t|) := by
    refine mul_le_mul (by linarith) (by linarith)
      (add_nonneg zero_le_one (div_nonneg (by positivity) (by linarith)))
      (by linarith [abs_nonneg t])
  nlinarith [abs_nonneg t, sq_nonneg |t|]

/-- For `0 ≤ R ≤ 7 / 4` and `t : ℝ`,
`Real.log (3 * zeta₁BallBound t R) ≤ 2 * Real.log (14 * (1 + |t|))`. -/
theorem log_three_mul_zeta₁BallBound_le_of_le_seven_fourths (t : ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hR_le : R ≤ 7 / 4) :
    Real.log (3 * zeta₁BallBound t R) ≤ 2 * Real.log (14 * (1 + |t|)) := by
  have h_pos : 0 < 3 * zeta₁BallBound t R := by
    linarith [one_le_zeta₁BallBound t hR (by linarith)]
  have h_le := Real.log_le_log h_pos (three_mul_zeta₁BallBound_le_sq_of_le_seven_fourths t hR hR_le)
  rwa [Real.log_pow, Nat.cast_ofNat] at h_le

/-- Under `RiemannHypothesis` and a zero-free gap `Δ` at height `U`,
for `0 ≤ r < R ≤ 3 / 2 + Δ ^ 2 / 4`
and `w ∈ Metric.closedBall (2 + U * I) r`,
`‖logRiemannZeta₁Branch U w‖ ≤ 2 * Real.log (3 * zeta₁BallBound U R) * r / (R - r)`. -/
theorem norm_logRiemannZeta₁Branch_le_of_gap (hRH : RiemannHypothesis) {U Δ r R : ℝ} {w : ℂ}
    (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - U|)
    (hr : 0 ≤ r) (hrR : r < R) (hR_le : R ≤ 3 / 2 + Δ ^ 2 / 4)
    (hw : w ∈ Metric.closedBall (2 + (U : ℂ) * I) r) :
    ‖logRiemannZeta₁Branch U w‖ ≤
      2 * Real.log (3 * zeta₁BallBound U R) * r / (R - r) := by
  have hR_pos : 0 < R := hr.trans_lt hrR
  have hR_lt_two : R < 2 := by nlinarith
  have h_ne : ∀ z ∈ Metric.ball (2 + (U : ℂ) * I) R, riemannZeta₁ z ≠ 0 :=
    fun z hz ↦ riemannZeta₁_ne_zero_of_mem_ball_of_gap hRH hΔ_pos hΔ_le hgap
      (ball_subset_ball hR_le hz)
  have hf_diff : DifferentiableOn ℂ (logRiemannZeta₁Branch U) (Metric.ball (2 + (U : ℂ) * I) R) :=
    fun z hz ↦
      (hasDerivAt_logRiemannZeta₁Branch_of_ne_zero h_ne hz).differentiableAt.differentiableWithinAt
  have hf_re : ∀ z ∈ Metric.ball (2 + (U : ℂ) * I) R,
      (logRiemannZeta₁Branch U z).re ≤ Real.log (3 * zeta₁BallBound U R) := by
    intro z hz
    refine (re_logRiemannZeta₁Branch_le_of_ne_zero hR_pos h_ne hz).trans ?_
    have hz_pos : 0 < ‖riemannZeta₁ z‖ := norm_pos_iff.mpr (h_ne z hz)
    refine Real.log_le_log (by positivity) ?_
    exact mul_le_mul_of_nonneg_left
      (norm_riemannZeta₁_le_zeta₁BallBound hR_pos.le hR_lt_two (ball_subset_closedBall hz))
      (by positivity)
  have hw_norm : ‖w - (2 + (U : ℂ) * I)‖ ≤ r := mem_closedBall_iff_norm.mp hw
  have hw_ball : w ∈ Metric.ball (2 + (U : ℂ) * I) R :=
    mem_ball_iff_norm.mpr (hw_norm.trans_lt hrR)
  have h_bc := borelCaratheodory_ball
    (log_three_mul_zeta₁BallBound_pos U hR_pos.le hR_lt_two)
    hf_diff hf_re hR_pos hw_ball (logRiemannZeta₁Branch_self U)
  refine h_bc.trans ?_
  have hM_pos : 0 ≤ 2 * Real.log (3 * zeta₁BallBound U R) :=
    mul_nonneg zero_le_two (log_three_mul_zeta₁BallBound_pos U hR_pos.le hR_lt_two).le
  exact div_le_div₀ (mul_nonneg hM_pos hr)
    (mul_le_mul_of_nonneg_left hw_norm hM_pos)
    (by linarith) (by linarith)

/-- Every point `(σ : ℂ) + (U : ℂ) * I` with `σ ∈ Set.Icc (1 / 2 : ℝ) 2` lies in
`Metric.closedBall (2 + (U : ℂ) * I) (3 / 2)`. -/
theorem mem_closedBall_three_halves_of_mem_Icc {U σ : ℝ} (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 2) :
    (σ : ℂ) + (U : ℂ) * I ∈ Metric.closedBall (2 + (U : ℂ) * I) (3 / 2) := by
  rw [mem_closedBall_iff_norm]
  have h_sub : (σ : ℂ) + (U : ℂ) * I - (2 + (U : ℂ) * I) = ((σ - 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h_sub, norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hσ.2])]
  linarith [hσ.1]

/-- **Uniform Borel–Carathéodory Bound on `[1 / 2, 2]` at Zero-Free Height `U`**:
Under `RiemannHypothesis` and a zero-free gap `0 < Δ ≤ 1 / 2` at height `U`, for every
`σ ∈ Set.Icc (1 / 2 : ℝ) 2` (including `σ = 1 / 2`),
`‖logRiemannZeta₁Branch U ((σ : ℂ) + (U : ℂ) * I)‖ ≤ (48 / Δ ^ 2) * Real.log (14 * (1 + |U|))`. -/
theorem norm_logRiemannZeta₁Branch_le_on_Icc_of_gap (hRH : RiemannHypothesis) {U Δ σ : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - U|)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 2) :
    ‖logRiemannZeta₁Branch U ((σ : ℂ) + (U : ℂ) * I)‖ ≤
      (48 / Δ ^ 2) * Real.log (14 * (1 + |U|)) := by
  let R : ℝ := 3 / 2 + Δ ^ 2 / 8
  have hrR : (3 / 2 : ℝ) < R := by dsimp [R]; nlinarith
  have hR_le : R ≤ 3 / 2 + Δ ^ 2 / 4 := by dsimp [R]; nlinarith
  have hR_74 : R ≤ 7 / 4 := by dsimp [R]; nlinarith
  have h1 := norm_logRiemannZeta₁Branch_le_of_gap hRH hΔ_pos hΔ_le hgap
    (by norm_num : (0 : ℝ) ≤ 3 / 2) hrR hR_le (mem_closedBall_three_halves_of_mem_Icc hσ)
  have h2 := log_three_mul_zeta₁BallBound_le_of_le_seven_fourths U (R := R)
    (by dsimp [R]; positivity) hR_74
  have h_sub : R - 3 / 2 = Δ ^ 2 / 8 := by dsimp [R]; ring
  rw [h_sub] at h1
  calc
    ‖logRiemannZeta₁Branch U ((σ : ℂ) + (U : ℂ) * I)‖
      ≤ 2 * Real.log (3 * zeta₁BallBound U R) * (3 / 2) / (Δ ^ 2 / 8) := h1
    _ = (24 / Δ ^ 2) * Real.log (3 * zeta₁BallBound U R) := by
        have : Δ ^ 2 ≠ 0 := pow_ne_zero 2 hΔ_pos.ne'
        field_simp
        ring
    _ ≤ (24 / Δ ^ 2) * (2 * Real.log (14 * (1 + |U|))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (48 / Δ ^ 2) * Real.log (14 * (1 + |U|)) := by ring

/-- **Fundamental Theorem of Calculus Along Horizontal Segment `[1 / 2 + U * I, 2 + U * I]`**:
Under `RiemannHypothesis` and a zero-free gap `0 < Δ ≤ 1 / 2` at height `U`,
`∫ σ in (1 / 2 : ℝ)..2, (deriv riemannZeta₁ (σ + U * I) / riemannZeta₁ (σ + U * I)) =`
`-logRiemannZeta₁Branch U ((1 / 2 : ℂ) + (U : ℂ) * I)`. -/
theorem intervalIntegral_logDeriv_riemannZeta₁_eq_neg_logRiemannZeta₁Branch
    (hRH : RiemannHypothesis) {U Δ : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - U|) :
    (∫ σ in (1 / 2 : ℝ)..2,
      deriv riemannZeta₁ ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta₁ ((σ : ℂ) + (U : ℂ) * I)) =
      -logRiemannZeta₁Branch U ((1 / 2 : ℂ) + (U : ℂ) * I) := by
  let R₀ : ℝ := 3 / 2 + Δ ^ 2 / 4
  have h_ne : ∀ z ∈ Metric.ball (2 + (U : ℂ) * I) R₀, riemannZeta₁ z ≠ 0 :=
    fun z hz ↦ riemannZeta₁_ne_zero_of_mem_ball_of_gap hRH hΔ_pos hΔ_le hgap hz
  have h_mem_ball : ∀ σ ∈ Set.uIcc (1 / 2 : ℝ) 2,
      (σ : ℂ) + (U : ℂ) * I ∈ Metric.ball (2 + (U : ℂ) * I) R₀ := by
    intro σ hσ
    rw [Set.uIcc_of_le (by norm_num)] at hσ
    have h_closed := mem_closedBall_three_halves_of_mem_Icc (U := U) hσ
    rw [mem_closedBall_iff_norm] at h_closed
    rw [mem_ball_iff_norm]
    have : (3 / 2 : ℝ) < R₀ := by dsimp [R₀]; nlinarith
    linarith
  have h_deriv : ∀ σ ∈ Set.uIcc (1 / 2 : ℝ) 2,
      HasDerivAt (fun x : ℝ ↦ logRiemannZeta₁Branch U ((x : ℂ) + (U : ℂ) * I))
        (deriv riemannZeta₁ ((σ : ℂ) + (U : ℂ) * I) /
          riemannZeta₁ ((σ : ℂ) + (U : ℂ) * I)) σ := by
    intro σ hσ
    have hg : HasDerivAt (logRiemannZeta₁Branch U)
        (deriv riemannZeta₁ ((σ : ℂ) + (U : ℂ) * I) /
          riemannZeta₁ ((σ : ℂ) + (U : ℂ) * I))
        ((σ : ℂ) + (U : ℂ) * I) :=
      hasDerivAt_logRiemannZeta₁Branch_of_ne_zero h_ne (h_mem_ball σ hσ)
    exact (hg.comp_add_const (σ : ℂ) ((U : ℂ) * I)).comp_ofReal
  have h_cont : ContinuousOn
      (fun σ : ℝ ↦ deriv riemannZeta₁ ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta₁ ((σ : ℂ) + (U : ℂ) * I))
      (Set.uIcc (1 / 2 : ℝ) 2) := by
    intro σ hσ
    have h_path : ContinuousAt (fun x : ℝ ↦ (x : ℂ) + (U : ℂ) * I) σ :=
      (continuous_ofReal.add continuous_const).continuousAt
    have h_logDeriv : ContinuousAt (fun z : ℂ ↦ deriv riemannZeta₁ z / riemannZeta₁ z)
        ((σ : ℂ) + (U : ℂ) * I) :=
      ((differentiable_riemannZeta₁.deriv _).div (differentiable_riemannZeta₁ _)
        (h_ne _ (h_mem_ball σ hσ))).continuousAt
    exact (ContinuousAt.comp (g := fun z : ℂ ↦ deriv riemannZeta₁ z / riemannZeta₁ z)
      (f := fun x : ℝ ↦ (x : ℂ) + (U : ℂ) * I) h_logDeriv h_path).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_cont.intervalIntegrable]
  simp

/-- **Explicit Norm Bound on the Horizontal Integral of `deriv riemannZeta₁ / riemannZeta₁`
Across `[1 / 2, 2]`**:
Under `RiemannHypothesis` and a zero-free gap `0 < Δ ≤ 1 / 2` at height `U`,
`‖∫ σ in (1 / 2 : ℝ)..2, (deriv riemannZeta₁ (σ + U * I) / riemannZeta₁ (σ + U * I))‖ ≤`
`(48 / Δ ^ 2) * Real.log (14 * (1 + |U|))`. -/
theorem norm_intervalIntegral_logDeriv_riemannZeta₁_le_of_gap
    (hRH : RiemannHypothesis) {U Δ : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - U|) :
    ‖∫ σ in (1 / 2 : ℝ)..2,
      deriv riemannZeta₁ ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta₁ ((σ : ℂ) + (U : ℂ) * I)‖ ≤
      (48 / Δ ^ 2) * Real.log (14 * (1 + |U|)) := by
  rw [intervalIntegral_logDeriv_riemannZeta₁_eq_neg_logRiemannZeta₁Branch hRH hΔ_pos hΔ_le hgap,
    norm_neg]
  simpa using norm_logRiemannZeta₁Branch_le_on_Icc_of_gap hRH hΔ_pos hΔ_le hgap
    ⟨le_rfl, by norm_num⟩

/-- **Uniform Cauchy Derivative Bound on `deriv riemannZeta₁ / riemannZeta₁` Across `[1 / 2, 2]`**:
Under `RiemannHypothesis` and a zero-free gap `0 < Δ ≤ 1 / 2` at height `U`, for every
`w ∈ Metric.closedBall (2 + U * I) (3 / 2)` (and in particular for `w = σ + U * I` for all
`σ ∈ Set.Icc (1 / 2 : ℝ) 2`),
`‖deriv riemannZeta₁ w / riemannZeta₁ w‖ ≤ (2048 / Δ ^ 4) * Real.log (14 * (1 + |U|))`. -/
theorem norm_logDeriv_riemannZeta₁_le_of_gap (hRH : RiemannHypothesis) {U Δ : ℝ} {w : ℂ}
    (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - U|)
    (hw : w ∈ Metric.closedBall (2 + (U : ℂ) * I) (3 / 2)) :
    ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ ≤
      (2048 / Δ ^ 4) * Real.log (14 * (1 + |U|)) := by
  let c : ℂ := 2 + (U : ℂ) * I
  let r : ℝ := 3 / 2
  let ρ : ℝ := Δ ^ 2 / 16
  let R : ℝ := 3 / 2 + Δ ^ 2 / 8
  let R₀ : ℝ := 3 / 2 + Δ ^ 2 / 4
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hrρR : r + ρ < R := by dsimp [r, ρ, R]; nlinarith
  have hR_le : R ≤ R₀ := by dsimp [R, R₀]; nlinarith
  have h_ne : ∀ z ∈ Metric.ball c R₀, riemannZeta₁ z ≠ 0 :=
    fun z hz ↦ riemannZeta₁_ne_zero_of_mem_ball_of_gap hRH hΔ_pos hΔ_le hgap hz
  have hw_norm : ‖w - c‖ ≤ r := mem_closedBall_iff_norm.mp hw
  have hw_ball : w ∈ Metric.ball c R₀ :=
    mem_ball_iff_norm.mpr (by dsimp [r, R₀] at hw_norm ⊢; nlinarith)
  rw [← (hasDerivAt_logRiemannZeta₁Branch_of_ne_zero h_ne hw_ball).deriv]
  have h_sub_closed : Metric.closedBall w ρ ⊆ Metric.ball c R₀ := by
    intro z hz
    rw [mem_closedBall_iff_norm] at hz
    rw [mem_ball_iff_norm]
    have h1 : ‖z - c‖ ≤ ‖z - w‖ + ‖w - c‖ := by
      calc
        ‖z - c‖ = ‖(z - w) + (w - c)‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w - c‖ := norm_add_le _ _
    dsimp [r, ρ, R₀] at hw_norm hz ⊢
    nlinarith
  have hf_diff : DifferentiableOn ℂ (logRiemannZeta₁Branch U) (Metric.ball c R₀) :=
    fun z hz ↦
      (hasDerivAt_logRiemannZeta₁Branch_of_ne_zero h_ne hz).differentiableAt.differentiableWithinAt
  have hd : DiffContOnCl ℂ (logRiemannZeta₁Branch U) (Metric.ball w ρ) :=
    (hf_diff.mono (closure_ball_subset_closedBall.trans h_sub_closed)).diffContOnCl
  have h_sphere : ∀ z ∈ Metric.sphere w ρ,
      ‖logRiemannZeta₁Branch U z‖ ≤
        2 * Real.log (3 * zeta₁BallBound U R) * (r + ρ) / (R - (r + ρ)) := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hz_closed : z ∈ Metric.closedBall c (r + ρ) := by
      rw [mem_closedBall_iff_norm]
      calc
        ‖z - c‖ = ‖(z - w) + (w - c)‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w - c‖ := norm_add_le _ _
        _ ≤ r + ρ := by linarith
    exact norm_logRiemannZeta₁Branch_le_of_gap hRH hΔ_pos hΔ_le hgap
      (by dsimp [r, ρ]; positivity) hrρR hR_le hz_closed
  have h_cauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hd h_sphere
  refine h_cauchy.trans ?_
  have h_log_le := log_three_mul_zeta₁BallBound_le_of_le_seven_fourths U (R := R)
    (by dsimp [R]; positivity) (by dsimp [R]; nlinarith)
  have h_log_pos : 0 ≤ Real.log (3 * zeta₁BallBound U R) :=
    (log_three_mul_zeta₁BallBound_pos U (by dsimp [R]; positivity) (by dsimp [R]; nlinarith)).le
  have h_rρ : r + ρ ≤ 2 := by dsimp [r, ρ]; nlinarith
  have h_sub_R : R - (r + ρ) = Δ ^ 2 / 16 := by dsimp [r, ρ, R]; ring
  rw [div_div, h_sub_R]
  have h_denom : (Δ ^ 2 / 16) * ρ = Δ ^ 4 / 256 := by dsimp [ρ]; ring
  rw [h_denom]
  calc
    2 * Real.log (3 * zeta₁BallBound U R) * (r + ρ) / (Δ ^ 4 / 256)
      ≤ 2 * Real.log (3 * zeta₁BallBound U R) * 2 / (Δ ^ 4 / 256) := by gcongr
    _ = (1024 / Δ ^ 4) * Real.log (3 * zeta₁BallBound U R) := by
        have : Δ ^ 4 ≠ 0 := pow_ne_zero 4 hΔ_pos.ne'
        field_simp
        ring
    _ ≤ (1024 / Δ ^ 4) * (2 * Real.log (14 * (1 + |U|))) :=
        mul_le_mul_of_nonneg_left h_log_le (by positivity)
    _ = (2048 / Δ ^ 4) * Real.log (14 * (1 + |U|)) := by ring

/-- **Uniform Bound on `‖deriv riemannZeta / riemannZeta‖` Across `σ ∈ [1 / 2, 2]`
at Zero-Free Height `U ≠ 0`**:
Under `RiemannHypothesis` and a zero-free gap `0 < Δ ≤ 1 / 2` at height `U ≠ 0`, for every
`σ ∈ Set.Icc (1 / 2 : ℝ) 2`,
`‖deriv riemannZeta (σ + U * I) / riemannZeta (σ + U * I)‖ ≤`
`(2048 / Δ ^ 4) * Real.log (14 * (1 + |U|)) + 1 / |U|`. -/
theorem norm_logDeriv_riemannZeta_le_on_Icc_of_gap (hRH : RiemannHypothesis) {U Δ σ : ℝ}
    (hU : U ≠ 0) (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - U|)
    (hσ : σ ∈ Set.Icc (1 / 2 : ℝ) 2) :
    ‖deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤
      (2048 / Δ ^ 4) * Real.log (14 * (1 + |U|)) + 1 / |U| := by
  let w : ℂ := (σ : ℂ) + (U : ℂ) * I
  have hw_closed : w ∈ Metric.closedBall (2 + (U : ℂ) * I) (3 / 2) :=
    mem_closedBall_three_halves_of_mem_Icc hσ
  have hw_ball : w ∈ Metric.ball (2 + (U : ℂ) * I) (3 / 2 + Δ ^ 2 / 4) := by
    rw [mem_closedBall_iff_norm] at hw_closed
    rw [mem_ball_iff_norm]
    nlinarith
  have hz1 : riemannZeta₁ w ≠ 0 :=
    riemannZeta₁_ne_zero_of_mem_ball_of_gap hRH hΔ_pos hΔ_le hgap hw_ball
  have hw1 : w ≠ 1 := by
    intro h
    have : w.im = (1 : ℂ).im := congrArg Complex.im h
    simp [w, hU] at this
  rw [logDeriv_riemannZeta_eq_sub hw1 hz1]
  have h_im_le : |U| ≤ ‖w - 1‖ := by
    have h_im : (w - 1).im = U := by simp [w]
    simpa [h_im] using abs_im_le_norm (w - 1)
  have h_inv_le : 1 / ‖w - 1‖ ≤ 1 / |U| :=
    div_le_div_of_nonneg_left zero_le_one (abs_pos.mpr hU) h_im_le
  have h_tri : ‖deriv riemannZeta₁ w / riemannZeta₁ w - 1 / (w - 1)‖ ≤
      ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ + 1 / ‖w - 1‖ := by
    calc
      ‖deriv riemannZeta₁ w / riemannZeta₁ w - 1 / (w - 1)‖
        ≤ ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ + ‖1 / (w - 1)‖ := norm_sub_le _ _
      _ = ‖deriv riemannZeta₁ w / riemannZeta₁ w‖ + 1 / ‖w - 1‖ := by
        rw [norm_div 1 (w - 1), norm_one]
  linarith [norm_logDeriv_riemannZeta₁_le_of_gap hRH hΔ_pos hΔ_le hgap hw_closed]

/-!
## Section 7: Pigeonhole Existence of a Zero-Free Height `U ∈ [T, T + 1]`
-/

/-- **Pigeonhole Existence of a Zero-Free Height in `[T, T + 1]`**:
For any finite set of heights `S : Finset ℝ` and any `T : ℝ`, there exists `U ∈ Set.Icc T (T + 1)`
such that every `γ ∈ S` satisfies `1 / (2 * (S.card + 1)) ≤ |γ - U|`. -/
theorem exists_zero_free_gap_in_Icc (S : Finset ℝ) (T : ℝ) :
    ∃ U ∈ Set.Icc T (T + 1),
      ∀ γ ∈ S, 1 / (2 * ((S.card : ℝ) + 1)) ≤ |γ - U| := by
  let N : ℕ := S.card + 1
  let Δ : ℝ := 1 / (2 * ((S.card : ℝ) + 1))
  have hN_pos : 0 < (S.card : ℝ) + 1 := by positivity
  have hΔ_pos : 0 < Δ := by dsimp [Δ]; positivity
  have hN_mul : 2 * ((S.card : ℝ) + 1) * Δ = 1 := by
    dsimp [Δ]
    field_simp
  let u : ℕ → ℝ := fun k ↦ T + (2 * (k : ℝ) + 1) * Δ
  have hu_mem : ∀ k ∈ Finset.range N, u k ∈ Set.Icc T (T + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hk_le : (k : ℝ) + 1 ≤ (S.card : ℝ) + 1 := by exact_mod_cast hk
    have hk_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    refine ⟨by dsimp [u]; nlinarith, ?_⟩
    dsimp [u]
    nlinarith
  by_contra! h_all
  have h_ex : ∀ k ∈ Finset.range N, ∃ γ ∈ S, |γ - u k| < Δ :=
    fun k hk ↦ h_all (u k) (hu_mem k hk)
  classical
  let f : ℕ → ℝ := fun k ↦ if h : ∃ γ ∈ S, |γ - u k| < Δ then h.choose else 0
  have hf_mem : ∀ k ∈ Finset.range N, f k ∈ S := by
    intro k hk
    simp only [f, h_ex k hk, ↓reduceDIte]
    exact (h_ex k hk).choose_spec.1
  have hf_dist : ∀ k ∈ Finset.range N, |f k - u k| < Δ := by
    intro k hk
    simp only [f, h_ex k hk, ↓reduceDIte]
    exact (h_ex k hk).choose_spec.2
  have hf_inj : (Finset.range N : Set ℕ).InjOn f := by
    intro k₁ hk₁ k₂ hk₂ h_eq
    rw [Finset.mem_coe] at hk₁ hk₂
    have hd₁ := hf_dist k₁ hk₁
    have hd₂ := hf_dist k₂ hk₂
    rw [← h_eq] at hd₂
    have h_diff_lt : |u k₁ - u k₂| < 2 * Δ := by
      calc
        |u k₁ - u k₂| = |(f k₁ - u k₂) - (f k₁ - u k₁)| := by ring_nf
        _ ≤ |f k₁ - u k₂| + |f k₁ - u k₁| := abs_sub _ _
        _ < Δ + Δ := add_lt_add hd₂ hd₁
        _ = 2 * Δ := by ring
    have h_u_diff : |u k₁ - u k₂| = 2 * |(k₁ : ℝ) - (k₂ : ℝ)| * Δ := by
      have h_sub : u k₁ - u k₂ = 2 * ((k₁ : ℝ) - (k₂ : ℝ)) * Δ := by dsimp [u]; ring
      rw [h_sub, abs_mul, abs_mul, abs_of_pos two_pos, abs_of_pos hΔ_pos]
    rw [h_u_diff] at h_diff_lt
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h_ge1 : (1 : ℝ) ≤ (k₂ : ℝ) - (k₁ : ℝ) := by
        have : k₁ + 1 ≤ k₂ := hlt
        have : (k₁ : ℝ) + 1 ≤ (k₂ : ℝ) := by exact_mod_cast this
        linarith
      have h_abs_ge1 : (1 : ℝ) ≤ |(k₁ : ℝ) - (k₂ : ℝ)| := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        exact h_ge1
      nlinarith
    · have h_ge1 : (1 : ℝ) ≤ (k₁ : ℝ) - (k₂ : ℝ) := by
        have : k₂ + 1 ≤ k₁ := hgt
        have : (k₂ : ℝ) + 1 ≤ (k₁ : ℝ) := by exact_mod_cast this
        linarith
      have h_abs_ge1 : (1 : ℝ) ≤ |(k₁ : ℝ) - (k₂ : ℝ)| := by
        rw [abs_of_nonneg (by linarith)]
        exact h_ge1
      nlinarith
  have h_card := Finset.card_le_card_of_injOn f
    (fun k hk ↦ Finset.mem_coe.mpr (hf_mem k (Finset.mem_coe.mp hk))) hf_inj
  rw [Finset.card_range] at h_card
  omega

/-!
## Section 8: Local Zero Count Bound and Symmetric Zero-Free Height in `[T, T + 1]`
-/

/-- `riemannZeta₁` is analytic on a neighborhood of every set `U : Set ℂ`. -/
theorem analyticOnNhd_riemannZeta₁ (U : Set ℂ) : AnalyticOnNhd ℂ riemannZeta₁ U :=
  (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ U)

/-- **Jensen's Inequality for `riemannZeta₁`**:
For any center `c : ℂ` with `riemannZeta₁ c ≠ 0` and radii `0 < |r| < |R|`, if
`‖riemannZeta₁ z‖ ≤ M` on `sphere c |R|` with `1 ≤ M`, then the divisor sum of zeros of
`riemannZeta₁` in `closedBall c |r|` is at most
`Real.log (M / ‖riemannZeta₁ c‖) / Real.log (R / r)`. -/
theorem sum_divisor_riemannZeta₁_le {c : ℂ} {r R M : ℝ}
    (r_pos : 0 < |r|) (r_lt_R : |r| < |R|) (hM : 1 ≤ M) (hc : riemannZeta₁ c ≠ 0)
    (f_bound : ∀ z ∈ sphere c |R|, ‖riemannZeta₁ z‖ ≤ M) :
    ∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u ≤
      Real.log (M / ‖riemannZeta₁ c‖) / Real.log (R / r) :=
  (analyticOnNhd_riemannZeta₁ (closedBall c |R|)).sum_divisor_le r_pos r_lt_R hM hc f_bound

/-- Explicit upper bound on `‖riemannZeta₁ z‖` on the sphere `sphere c R` when `0 ≤ R < c.re`. -/
theorem norm_riemannZeta₁_le_on_sphere {c z : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hcR : R < c.re) (hz : z ∈ sphere c R) :
    ‖riemannZeta₁ z‖ ≤
      1 + (‖c - 1‖ + R) * (1 + (‖c‖ + R) / (c.re - R)) := by
  rw [mem_sphere_iff_norm] at hz
  have hz_re : c.re - R ≤ z.re := by
    have h1 : (c - z).re ≤ ‖c - z‖ := re_le_norm (c - z)
    rw [norm_sub_rev, hz, sub_re] at h1
    linarith
  have hz_re_pos : 0 < z.re := by linarith
  have hz_norm : ‖z‖ ≤ ‖c‖ + R := by
    calc
      ‖z‖ = ‖c + (z - c)‖ := by ring_nf
      _ ≤ ‖c‖ + ‖z - c‖ := norm_add_le _ _
      _ = ‖c‖ + R := by rw [hz]
  have hz_sub_one : ‖z - 1‖ ≤ ‖c - 1‖ + R := by
    calc
      ‖z - 1‖ = ‖(c - 1) + (z - c)‖ := by ring_nf
      _ ≤ ‖c - 1‖ + ‖z - c‖ := norm_add_le _ _
      _ = ‖c - 1‖ + R := by rw [hz]
  have h_div : ‖z‖ / z.re ≤ (‖c‖ + R) / (c.re - R) :=
    div_le_div₀ (by positivity) hz_norm (by linarith) hz_re
  refine (norm_riemannZeta₁_le hz_re_pos).trans ?_
  gcongr

/-- **Explicit Backlund-Jensen Zero-Counting Bound for `riemannZeta₁` on Vertical Strips**:
For any `T : ℝ` and radii `0 < r < R < 2`, the number of zeros of `riemannZeta₁` (counted with
multiplicity) in `closedBall (2 + T * I) r` is at most
`Real.log (3 * (1 + (‖1 + T * I‖ + R) * (1 + (‖2 + T * I‖ + R) / (2 - R)))) / Real.log (R / r)`. -/
theorem sum_divisor_riemannZeta₁_closedBall_two_add_mul_I_le (T : ℝ) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR2 : R < 2) :
    ∑ᶠ u, divisor riemannZeta₁ (closedBall (2 + (T : ℂ) * I) |r|) u ≤
      Real.log (3 * (1 + (‖(1 : ℂ) + (T : ℂ) * I‖ + R) *
        (1 + (‖(2 : ℂ) + (T : ℂ) * I‖ + R) / (2 - R)))) / Real.log (R / r) := by
  let c : ℂ := 2 + (T : ℂ) * I
  let M : ℝ := 1 + (‖(1 : ℂ) + (T : ℂ) * I‖ + R) * (1 + (‖c‖ + R) / (2 - R))
  have hc_re : c.re = 2 := by simp [c]
  have hc_sub : c - 1 = 1 + (T : ℂ) * I := by simp [c]; ring
  have hR_pos : 0 < R := hr.trans hrR
  have hM_ge_one : 1 ≤ M := by
    dsimp [M]
    have : 0 ≤ (‖(1 : ℂ) + (T : ℂ) * I‖ + R) * (1 + (‖c‖ + R) / (2 - R)) :=
      mul_nonneg (by positivity) (add_nonneg zero_le_one (div_nonneg (by positivity) (by linarith)))
    linarith
  have hc_norm : 1 / 3 ≤ ‖riemannZeta₁ c‖ :=
    one_third_le_norm_riemannZeta₁_of_re_eq_two hc_re
  have hc_ne : riemannZeta₁ c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hc_norm
    linarith
  have h_jensen : ∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u ≤
      Real.log (M / ‖riemannZeta₁ c‖) / Real.log (R / r) := by
    refine sum_divisor_riemannZeta₁_le (by rwa [abs_of_pos hr])
      (by rwa [abs_of_pos hr, abs_of_pos hR_pos]) hM_ge_one hc_ne ?_
    intro z hz
    rw [abs_of_pos hR_pos] at hz
    have h := norm_riemannZeta₁_le_on_sphere hR_pos.le (by linarith [hc_re]) hz
    rwa [hc_re, hc_sub] at h
  refine h_jensen.trans ?_
  have h_log_pos : 0 < Real.log (R / r) := Real.log_pos ( (one_lt_div hr).mpr hrR )
  refine div_le_div_of_nonneg_right ?_ h_log_pos.le
  refine Real.log_le_log (div_pos (by linarith) (norm_pos_iff.mpr hc_ne)) ?_
  rw [div_le_iff₀ (norm_pos_iff.mpr hc_ne)]
  calc
    M = 3 * M * (1 / 3) := by ring
    _ ≤ 3 * M * ‖riemannZeta₁ c‖ := by gcongr

/-- Because `riemannZeta₁` is analytic on `ℂ` and `riemannZeta₁ 1 = 1 ≠ 0`, `riemannZeta₁` does not
vanish identically in any neighborhood of any point `z : ℂ`,
i.e., `analyticOrderAt riemannZeta₁ z ≠ ⊤`. -/
theorem analyticOrderAt_riemannZeta₁_ne_top (z : ℂ) :
    analyticOrderAt riemannZeta₁ z ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hzero : EqOn riemannZeta₁ 0 univ :=
    (analyticOnNhd_riemannZeta₁ univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z) htop
  have h1 : riemannZeta₁ 1 = 0 := hzero (mem_univ 1)
  rw [riemannZeta₁_one] at h1
  exact one_ne_zero h1

/-- Every zero `z ∈ U` of `riemannZeta₁` has `1 ≤ divisor riemannZeta₁ U z`. -/
theorem one_le_divisor_riemannZeta₁ {U : Set ℂ} {z : ℂ} (hzU : z ∈ U)
    (hz0 : riemannZeta₁ z = 0) :
    1 ≤ divisor riemannZeta₁ U z := by
  have hAn : AnalyticOnNhd ℂ riemannZeta₁ U := analyticOnNhd_riemannZeta₁ U
  rw [hAn.divisor_apply hzU]
  have h_ne_top : analyticOrderAt riemannZeta₁ z ≠ ⊤ := analyticOrderAt_riemannZeta₁_ne_top z
  have h_ne_zero : analyticOrderAt riemannZeta₁ z ≠ 0 :=
    (hAn z hzU).analyticOrderAt_ne_zero.mpr hz0
  have h_nat : (analyticOrderNatAt riemannZeta₁ z : ℕ∞) = analyticOrderAt riemannZeta₁ z :=
    Nat.cast_analyticOrderNatAt h_ne_top
  have h_pos : 1 ≤ analyticOrderNatAt riemannZeta₁ z := by
    by_contra! hlt
    have h0 : analyticOrderNatAt riemannZeta₁ z = 0 := Nat.lt_one_iff.mp hlt
    rw [h0, Nat.cast_zero] at h_nat
    exact h_ne_zero h_nat.symm
  rw [← h_nat]
  simpa using h_pos

/-- For any finite set `F : Finset ℂ` of zeros of `riemannZeta₁` contained in `closedBall c |r|`,
its cardinality is at most `∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u`. -/
theorem card_finset_zeros_le_sum_divisor_riemannZeta₁ {c : ℂ} {r : ℝ} (F : Finset ℂ)
    (hF : ∀ ρ ∈ F, ρ ∈ closedBall c |r| ∧ riemannZeta₁ ρ = 0) :
    (F.card : ℝ) ≤ (∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u : ℤ) := by
  have h_supp :=
    (divisor riemannZeta₁ (closedBall c |r|)).finiteSupport (isCompact_closedBall c |r|)
  have h_sub : F ⊆ h_supp.toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset, Function.mem_support]
    have h1 := one_le_divisor_riemannZeta₁ (hF ρ hρ).1 (hF ρ hρ).2
    omega
  have h_int : (F.card : ℤ) ≤ ∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u := by
    calc
      (F.card : ℤ) = ∑ _ρ ∈ F, (1 : ℤ) := by simp
      _ ≤ ∑ ρ ∈ F, divisor riemannZeta₁ (closedBall c |r|) ρ :=
        Finset.sum_le_sum fun ρ hρ ↦ one_le_divisor_riemannZeta₁ (hF ρ hρ).1 (hF ρ hρ).2
      _ ≤ ∑ u ∈ h_supp.toFinset, divisor riemannZeta₁ (closedBall c |r|) u :=
        Finset.sum_le_sum_of_subset_of_nonneg h_sub fun u _ _ ↦
          (analyticOnNhd_riemannZeta₁ _).divisor_nonneg u
      _ = ∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u :=
        (finsum_eq_sum _ h_supp).symm
  exact_mod_cast h_int

/-- Every zero `ρ ≠ 1` of `riemannZeta` is a zero of `riemannZeta₁`. -/
theorem riemannZeta₁_eq_zero_of_riemannZeta_eq_zero {ρ : ℂ} (hζ : riemannZeta ρ = 0)
    (h1 : ρ ≠ 1) :
    riemannZeta₁ ρ = 0 := by
  have h_eq := riemannZeta_eq_inv_sub_mul h1
  rw [hζ] at h_eq
  rcases mul_eq_zero.mp h_eq.symm with hinv | hz1
  · exact absurd (inv_eq_zero.mp hinv) (sub_ne_zero.mpr h1)
  · exact hz1

/-- Finiteness of the set of critical-line zeros `ρ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`) with
`ρ.im ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)`. -/
theorem finite_criticalLineZerosInStrip (T : ℝ) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ ρ.im ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)}.Finite := by
  have hcompact : IsCompact (Set.Icc (1 / 2 : ℝ) (1 / 2) ×ℂ Set.Icc (T - 1 / 2) (T + 3 / 2)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  refine hcompact.inter_riemannZetaZeros_finite.subset ?_
  rintro ρ ⟨hζ, hre, him⟩
  exact ⟨⟨⟨hre.symm.le, hre.le⟩, him⟩, hζ⟩

/-- The canonical `Finset ℂ` of critical-line zeros `ρ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`) with
`ρ.im ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)`. -/
noncomputable def criticalLineZerosInStrip (T : ℝ) : Finset ℂ :=
  (finite_criticalLineZerosInStrip T).toFinset

@[simp]
theorem mem_criticalLineZerosInStrip {T : ℝ} {ρ : ℂ} :
    ρ ∈ criticalLineZerosInStrip T ↔
      riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ ρ.im ∈ Set.Icc (T - 1 / 2) (T + 3 / 2) :=
  Set.Finite.mem_toFinset (finite_criticalLineZerosInStrip T)

/-- Finiteness of the symmetric set of critical-line zeros `ρ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`)
with `|ρ.im| ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)`. -/
theorem finite_symmetricCriticalLineZerosInStrip (T : ℝ) :
    {ρ : ℂ | riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧
      |ρ.im| ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)}.Finite := by
  have hcompact : IsCompact (Set.Icc (1 / 2 : ℝ) (1 / 2) ×ℂ Set.Icc (-(T + 3 / 2)) (T + 3 / 2)) :=
    isCompact_Icc.reProdIm isCompact_Icc
  refine hcompact.inter_riemannZetaZeros_finite.subset ?_
  rintro ρ ⟨hζ, hre, him⟩
  exact ⟨⟨⟨hre.symm.le, hre.le⟩, abs_le.mp him.2⟩, hζ⟩

/-- The canonical `Finset ℂ` of critical-line zeros `ρ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`) with
`|ρ.im| ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)`. -/
noncomputable def symmetricCriticalLineZerosInStrip (T : ℝ) : Finset ℂ :=
  (finite_symmetricCriticalLineZerosInStrip T).toFinset

@[simp]
theorem mem_symmetricCriticalLineZerosInStrip {T : ℝ} {ρ : ℂ} :
    ρ ∈ symmetricCriticalLineZerosInStrip T ↔
      riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ |ρ.im| ∈ Set.Icc (T - 1 / 2) (T + 3 / 2) :=
  Set.Finite.mem_toFinset (finite_symmetricCriticalLineZerosInStrip T)

/-- The finite set of absolute heights `|ρ.im|` of critical-line zeros in the local strip
`[T - 1 / 2, T + 3 / 2]`. -/
noncomputable def localZeroHeights (T : ℝ) : Finset ℝ :=
  (symmetricCriticalLineZerosInStrip T).image (fun ρ ↦ |ρ.im|)

@[simp]
theorem mem_localZeroHeights {T : ℝ} {γ : ℝ} :
    γ ∈ localZeroHeights T ↔
      ∃ ρ : ℂ, (riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ |ρ.im| ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)) ∧
        |ρ.im| = γ := by
  simp [localZeroHeights]

/-- Every critical-line zero `ρ` with `ρ.im ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)` lies in
`Metric.closedBall (2 + ((T + 1 / 2 : ℝ) : ℂ) * I) |(19 / 10 : ℝ)|`. -/
theorem mem_closedBall_nineteen_tenths_of_mem_criticalLineZerosInStrip {T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ criticalLineZerosInStrip T) :
    ρ ∈ Metric.closedBall (2 + ((T + 1 / 2 : ℝ) : ℂ) * I) |(19 / 10 : ℝ)| := by
  obtain ⟨_, hre, him1, him2⟩ := mem_criticalLineZerosInStrip.mp hρ
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 19 / 10), mem_closedBall_iff_norm]
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 19 / 10)]
  rw [Complex.sq_norm, Complex.normSq_apply]
  have h_re : (ρ - (2 + ((T + 1 / 2 : ℝ) : ℂ) * I)).re = -3 / 2 := by
    simp [hre]
    ring
  have h_im : (ρ - (2 + ((T + 1 / 2 : ℝ) : ℂ) * I)).im = ρ.im - (T + 1 / 2) := by
    simp
  rw [h_re, h_im]
  have h_im_sq : (ρ.im - (T + 1 / 2)) * (ρ.im - (T + 1 / 2)) ≤ 1 := by
    nlinarith
  nlinarith

/-- Explicit lower bound `1 / 39 ≤ Real.log (39 / 38)`. -/
theorem one_div_thirty_nine_le_log_thirty_nine_div_thirty_eight :
    (1 / 39 : ℝ) ≤ Real.log (39 / 38) := by
  have h_exp : (38 / 39 : ℝ) ≤ Real.exp (-1 / 39) := by
    linarith [Real.add_one_le_exp (-1 / 39 : ℝ)]
  have h_log := Real.log_le_log (by norm_num) h_exp
  rw [Real.log_exp, show (38 / 39 : ℝ) = (39 / 38 : ℝ)⁻¹ by norm_num, Real.log_inv] at h_log
  linarith

/-- **Explicit Local Zero Count Bound (`156 * Real.log (T + 10)`)**:
For every `T ≥ 0`, the number of critical-line zeros `ρ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`)
with `ρ.im ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)` is at most `156 * Real.log (T + 10)`. -/
theorem card_criticalLineZerosInStrip_le {T : ℝ} (hT : 0 ≤ T) :
    ((criticalLineZerosInStrip T).card : ℝ) ≤ 156 * Real.log (T + 10) := by
  let T' : ℝ := T + 1 / 2
  let r : ℝ := 19 / 10
  let R : ℝ := 39 / 20
  have hr : 0 < r := by dsimp [r]; norm_num
  have hrR : r < R := by dsimp [r, R]; norm_num
  have hR2 : R < 2 := by dsimp [R]; norm_num
  have h_card_le : ((criticalLineZerosInStrip T).card : ℝ) ≤
      (∑ᶠ u, divisor riemannZeta₁ (closedBall (2 + (T' : ℂ) * I) |r|) u : ℤ) := by
    refine card_finset_zeros_le_sum_divisor_riemannZeta₁ (criticalLineZerosInStrip T) ?_
    intro ρ hρ
    refine ⟨mem_closedBall_nineteen_tenths_of_mem_criticalLineZerosInStrip hρ, ?_⟩
    obtain ⟨hζ, hre, _⟩ := mem_criticalLineZerosInStrip.mp hρ
    refine riemannZeta₁_eq_zero_of_riemannZeta_eq_zero hζ ?_
    intro h1
    rw [h1] at hre
    norm_num at hre
  have h_jensen := sum_divisor_riemannZeta₁_closedBall_two_add_mul_I_le T' hr hrR hR2
  have h_norm1 : ‖(1 : ℂ) + (T' : ℂ) * I‖ + R ≤ T + 10 := by
    have h1 : ‖(1 : ℂ) + (T' : ℂ) * I‖ ≤ 1 + T' := by
      calc
        ‖(1 : ℂ) + (T' : ℂ) * I‖ ≤ ‖(1 : ℂ)‖ + ‖(T' : ℂ) * I‖ := norm_add_le _ _
        _ = 1 + |T'| := by simp
        _ = 1 + T' := by rw [abs_of_pos (by dsimp [T']; linarith)]
    dsimp [T', R] at h1 ⊢
    linarith
  have h_norm2 : ‖(2 : ℂ) + (T' : ℂ) * I‖ + R ≤ T + 10 := by
    have h2 : ‖(2 : ℂ) + (T' : ℂ) * I‖ ≤ 2 + T' := by
      calc
        ‖(2 : ℂ) + (T' : ℂ) * I‖ ≤ ‖(2 : ℂ)‖ + ‖(T' : ℂ) * I‖ := norm_add_le _ _
        _ = 2 + |T'| := by simp
        _ = 2 + T' := by rw [abs_of_pos (by dsimp [T']; linarith)]
    dsimp [T', R] at h2 ⊢
    linarith
  have h_div2 : 1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R) ≤ 21 * (T + 10) := by
    have h_sub : 2 - R = 1 / 20 := by dsimp [R]; norm_num
    rw [h_sub]
    have h_eq : 1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (1 / 20) =
        1 + 20 * (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) := by ring
    rw [h_eq]
    linarith
  have h_prod : 3 * (1 + (‖(1 : ℂ) + (T' : ℂ) * I‖ + R) *
      (1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R))) ≤ (T + 10) ^ 4 := by
    have h_a_nonneg : 0 ≤ ‖(1 : ℂ) + (T' : ℂ) * I‖ + R := by dsimp [R]; positivity
    have h_b_nonneg : 0 ≤ 1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R) := by
      dsimp [R]; positivity
    have h_mul : (‖(1 : ℂ) + (T' : ℂ) * I‖ + R) *
        (1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R)) ≤
        (T + 10) * (21 * (T + 10)) :=
      mul_le_mul h_norm1 h_div2 h_b_nonneg (by linarith)
    have h_sq : 100 ≤ (T + 10) ^ 2 := by nlinarith
    have h_pow4 : (T + 10) ^ 4 = (T + 10) ^ 2 * (T + 10) ^ 2 := by ring
    nlinarith
  have h_pos_lhs : 0 < 3 * (1 + (‖(1 : ℂ) + (T' : ℂ) * I‖ + R) *
      (1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R))) := by
    dsimp [R]; positivity
  have h_log_num : Real.log (3 * (1 + (‖(1 : ℂ) + (T' : ℂ) * I‖ + R) *
      (1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R)))) ≤ 4 * Real.log (T + 10) := by
    calc
      Real.log (3 * (1 + (‖(1 : ℂ) + (T' : ℂ) * I‖ + R) *
          (1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R))))
        ≤ Real.log ((T + 10) ^ 4) := Real.log_le_log h_pos_lhs h_prod
      _ = 4 * Real.log (T + 10) := by rw [Real.log_pow]; push_cast; ring
  have h_Rr : R / r = 39 / 38 := by dsimp [r, R]; norm_num
  have h_log_den : (1 / 39 : ℝ) ≤ Real.log (R / r) := by
    rw [h_Rr]
    exact one_div_thirty_nine_le_log_thirty_nine_div_thirty_eight
  have h_logT10_nonneg : 0 ≤ 4 * Real.log (T + 10) := by
    have : 1 ≤ T + 10 := by linarith
    exact mul_nonneg (by norm_num) (Real.log_nonneg this)
  calc
    ((criticalLineZerosInStrip T).card : ℝ)
      ≤ Real.log (3 * (1 + (‖(1 : ℂ) + (T' : ℂ) * I‖ + R) *
          (1 + (‖(2 : ℂ) + (T' : ℂ) * I‖ + R) / (2 - R)))) / Real.log (R / r) :=
        h_card_le.trans h_jensen
    _ ≤ (4 * Real.log (T + 10)) / (1 / 39) :=
        div_le_div₀ h_logT10_nonneg h_log_num (by norm_num) h_log_den
    _ = 156 * Real.log (T + 10) := by ring

/-- Every `γ ∈ localZeroHeights T` maps under `γ ↦ (1 / 2 : ℂ) + (γ : ℂ) * I` into
`criticalLineZerosInStrip T`. -/
theorem half_add_mul_I_mem_criticalLineZerosInStrip_of_mem_localZeroHeights {T γ : ℝ}
    (hγ : γ ∈ localZeroHeights T) :
    (1 / 2 : ℂ) + (γ : ℂ) * I ∈ criticalLineZerosInStrip T := by
  obtain ⟨ρ, ⟨hζ, hre, him⟩, rfl⟩ := mem_localZeroHeights.mp hγ
  refine mem_criticalLineZerosInStrip.mpr ⟨?_, by simp, by simpa using him⟩
  rcases le_or_gt 0 ρ.im with h_nonneg | h_neg
  · have h_eq : (1 / 2 : ℂ) + ((|ρ.im| : ℝ) : ℂ) * I = ρ := by
      rw [abs_of_nonneg h_nonneg]
      apply Complex.ext <;> simp [hre]
    rw [h_eq]
    exact hζ
  · have h_eq : (1 / 2 : ℂ) + ((|ρ.im| : ℝ) : ℂ) * I = conj ρ := by
      rw [abs_of_neg h_neg]
      apply Complex.ext <;> simp [hre]
    rw [h_eq, riemannZeta_conj, hζ, map_zero]

/-- The cardinality of `localZeroHeights T` is at most the cardinality of
`criticalLineZerosInStrip T`. -/
theorem card_localZeroHeights_le_card_criticalLineZerosInStrip (T : ℝ) :
    (localZeroHeights T).card ≤ (criticalLineZerosInStrip T).card := by
  refine Finset.card_le_card_of_injOn (fun γ : ℝ ↦ (1 / 2 : ℂ) + (γ : ℂ) * I) ?_ ?_
  · intro γ hγ
    exact Finset.mem_coe.mpr
      (half_add_mul_I_mem_criticalLineZerosInStrip_of_mem_localZeroHeights (Finset.mem_coe.mp hγ))
  · intro γ₁ _ γ₂ _ h_eq
    have h_im := congrArg Complex.im h_eq
    simpa using h_im

/-- **Explicit Bound on `(localZeroHeights T).card`**:
For every `T ≥ 0`, `((localZeroHeights T).card : ℝ) ≤ 156 * Real.log (T + 10)`. -/
theorem card_localZeroHeights_le {T : ℝ} (hT : 0 ≤ T) :
    ((localZeroHeights T).card : ℝ) ≤ 156 * Real.log (T + 10) := by
  have h1 : ((localZeroHeights T).card : ℝ) ≤ ((criticalLineZerosInStrip T).card : ℝ) := by
    exact_mod_cast card_localZeroHeights_le_card_criticalLineZerosInStrip T
  exact h1.trans (card_criticalLineZerosInStrip_le hT)

/-- A complex number `s` is a nontrivial zero of `riemannZeta` if `riemannZeta s = 0`,
`s` is not a trivial zero `-2 * (n + 1)` (`n : ℕ`), and `s ≠ 1`. -/
def IsNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

/-- Under `RiemannHypothesis`, every nontrivial zero `ρ` of `riemannZeta` has `ρ.re = 1 / 2`. -/
theorem re_eq_half_of_isNontrivialZetaZero (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : IsNontrivialZetaZero ρ) :
    ρ.re = 1 / 2 :=
  hRH ρ hρ.1 hρ.2.1 hρ.2.2

/-- Under `RiemannHypothesis`, the set of nontrivial zeros `ρ` with
`ρ.im ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)` is finite and has cardinality at most
`156 * Real.log (T + 10)` for `T ≥ 0`. -/
theorem card_nontrivialZetaZeros_in_strip_le (hRH : RiemannHypothesis) {T : ℝ} (hT : 0 ≤ T)
    (F : Finset ℂ)
    (hF : ∀ ρ ∈ F, IsNontrivialZetaZero ρ ∧ ρ.im ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)) :
    (F.card : ℝ) ≤ 156 * Real.log (T + 10) := by
  have h_sub : F ⊆ criticalLineZerosInStrip T := by
    intro ρ hρ
    obtain ⟨h_nt, him⟩ := hF ρ hρ
    exact mem_criticalLineZerosInStrip.mpr
      ⟨h_nt.1, re_eq_half_of_isNontrivialZetaZero hRH h_nt, him⟩
  have h_le : (F.card : ℝ) ≤ ((criticalLineZerosInStrip T).card : ℝ) := by
    exact_mod_cast Finset.card_le_card h_sub
  exact h_le.trans (card_criticalLineZerosInStrip_le hT)

/-- For any `y U : ℝ` with `0 ≤ U`, `|(|y| - U)| ≤ |y - U|`. -/
theorem abs_abs_sub_le_abs_sub_of_nonneg {y U : ℝ} (hU : 0 ≤ U) :
    |(|y| - U)| ≤ |y - U| := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
  · rw [abs_of_neg hy, abs_of_neg (by linarith : y - U < 0), abs_le]
    constructor <;> linarith

/-- For any `y U : ℝ` with `0 ≤ U`, `|(|y| - U)| ≤ |y - (-U)|`. -/
theorem abs_abs_sub_le_abs_sub_neg_of_nonneg {y U : ℝ} (hU : 0 ≤ U) :
    |(|y| - U)| ≤ |y - (-U)| := by
  have h := abs_abs_sub_le_abs_sub_of_nonneg (y := -y) hU
  rwa [abs_neg, show -y - U = -(y - (-U)) by ring, abs_neg] at h

/-- **Existence of a Symmetric Zero-Free Height `U ∈ [T, T + 1]`**:
For every `T ≥ 0`, there exist `U ∈ Set.Icc T (T + 1)` and `Δ : ℝ` such that:
1. `0 < Δ` and `Δ ≤ 1 / 2`,
2. `1 / (314 * Real.log (T + 10)) ≤ Δ`,
3. For **all** critical-line zeros `ρ : ℂ` (`riemannZeta ρ = 0 ∧ ρ.re = 1 / 2`),
   `Δ ≤ |(|ρ.im| - U)|`, `Δ ≤ |ρ.im - U|`, and `Δ ≤ |ρ.im - (-U)|`. -/
theorem exists_zero_free_height_in_Icc {T : ℝ} (hT : 0 ≤ T) :
    ∃ U ∈ Set.Icc T (T + 1), ∃ Δ : ℝ,
      0 < Δ ∧ Δ ≤ 1 / 2 ∧
      1 / (314 * Real.log (T + 10)) ≤ Δ ∧
      (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 →
        Δ ≤ |(|ρ.im| - U)| ∧ Δ ≤ |ρ.im - U| ∧ Δ ≤ |ρ.im - (-U)|) := by
  let S := localZeroHeights T
  obtain ⟨U, hU_mem, hU_gap⟩ := exists_zero_free_gap_in_Icc S T
  let Δ : ℝ := 1 / (2 * ((S.card : ℝ) + 1))
  have hU_nonneg : 0 ≤ U := hT.trans hU_mem.1
  have hS_nonneg : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg S.card
  have hΔ_pos : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ_le : Δ ≤ 1 / 2 := by
    dsimp [Δ]
    exact one_div_le_one_div_of_le two_pos (by linarith)
  have h_log_ge_one : 1 ≤ Real.log (T + 10) := by
    have h_exp : Real.exp 1 ≤ T + 10 := by
      linarith [Real.exp_one_lt_d9]
    have h_log := Real.log_le_log (Real.exp_pos 1) h_exp
    rwa [Real.log_exp] at h_log
  have hS_le : (S.card : ℝ) ≤ 156 * Real.log (T + 10) := card_localZeroHeights_le hT
  have hΔ_lb : 1 / (314 * Real.log (T + 10)) ≤ Δ := by
    dsimp [Δ]
    refine one_div_le_one_div_of_le (by positivity) ?_
    linarith
  refine ⟨U, hU_mem, Δ, hΔ_pos, hΔ_le, hΔ_lb, ?_⟩
  intro ρ hζ hre
  have h_abs_gap : Δ ≤ |(|ρ.im| - U)| := by
    by_cases h_strip : |ρ.im| ∈ Set.Icc (T - 1 / 2) (T + 3 / 2)
    · refine hU_gap |ρ.im| ?_
      exact mem_localZeroHeights.mpr ⟨ρ, ⟨hζ, hre, h_strip⟩, rfl⟩
    · rw [Set.mem_Icc, not_and_or, not_le, not_le] at h_strip
      rcases h_strip with h_lt | h_gt
      · have h1 : 1 / 2 ≤ U - |ρ.im| := by linarith [hU_mem.1]
        have h2 : U - |ρ.im| ≤ |(|ρ.im| - U)| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        linarith
      · have h1 : 1 / 2 ≤ |ρ.im| - U := by linarith [hU_mem.2]
        have h2 : |ρ.im| - U ≤ |(|ρ.im| - U)| := le_abs_self _
        linarith
  exact ⟨h_abs_gap,
    h_abs_gap.trans (abs_abs_sub_le_abs_sub_of_nonneg hU_nonneg),
    h_abs_gap.trans (abs_abs_sub_le_abs_sub_neg_of_nonneg hU_nonneg)⟩

/-!
## Section 9: Trigonometric `tan` Bound and Binet `digamma` Bound on Horizontal Lines
-/

/-- Exact identity for `Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * I))`:
for all `x y : ℝ`,
$$\operatorname{normSq}(\sin(x + y i)) = \sin^2 x + \sinh^2 y.$$ -/
theorem normSq_sin_add_mul_I (x y : ℝ) :
    Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * I)) =
      Real.sin x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.sin_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Complex.normSq_apply]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, zero_mul,
    add_zero, I_im, mul_one, sub_self, add_im, mul_im]
  calc
    Real.sin x * Real.cosh y * (Real.sin x * Real.cosh y) +
        (0 + Real.cos x * Real.sinh y) * (0 + Real.cos x * Real.sinh y)
      = Real.sin x ^ 2 * (Real.cosh y ^ 2 - Real.sinh y ^ 2) +
          (Real.sin x ^ 2 + Real.cos x ^ 2) * Real.sinh y ^ 2 := by ring
    _ = Real.sin x ^ 2 + Real.sinh y ^ 2 := by
      rw [Real.cosh_sq_sub_sinh_sq y, Real.sin_sq_add_cos_sq x]
      ring

/-- Exact identity for `Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * I))`:
for all `x y : ℝ`,
$$\operatorname{normSq}(\cos(x + y i)) = \cos^2 x + \sinh^2 y.$$ -/
theorem normSq_cos_add_mul_I (x y : ℝ) :
    Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * I)) =
      Real.cos x ^ 2 + Real.sinh y ^ 2 := by
  rw [Complex.cos_add_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Complex.normSq_apply]
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, zero_mul,
    add_zero, I_im, mul_one, sub_self, sub_im, mul_im]
  calc
    Real.cos x * Real.cosh y * (Real.cos x * Real.cosh y) +
        (0 - Real.sin x * Real.sinh y) * (0 - Real.sin x * Real.sinh y)
      = Real.cos x ^ 2 * (Real.cosh y ^ 2 - Real.sinh y ^ 2) +
          (Real.sin x ^ 2 + Real.cos x ^ 2) * Real.sinh y ^ 2 := by ring
    _ = Real.cos x ^ 2 + Real.sinh y ^ 2 := by
      rw [Real.cosh_sq_sub_sinh_sq y, Real.sin_sq_add_cos_sq x]
      ring

/-- For `1 ≤ |y|`, `9 / 16 ≤ Real.sinh y ^ 2`. -/
theorem nine_sixteenths_le_sinh_sq_of_one_le_abs {y : ℝ} (hy : 1 ≤ |y|) :
    9 / 16 ≤ Real.sinh y ^ 2 := by
  have h_exp_ge : 2 ≤ Real.exp |y| := by
    linarith [Real.add_one_le_exp |y|]
  have h_exp_neg_le : Real.exp (-|y|) ≤ 1 / 2 := by
    have h_prod : Real.exp (-|y|) * Real.exp |y| = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h_pos : 0 < Real.exp (-|y|) := Real.exp_pos _
    nlinarith
  have h_sinh_abs : 3 / 4 ≤ Real.sinh |y| := by
    rw [Real.sinh_eq]
    linarith
  have h_sq_eq : Real.sinh y ^ 2 = Real.sinh |y| ^ 2 := by
    rcases le_or_gt 0 y with h0 | h0
    · rw [abs_of_nonneg h0]
    · rw [abs_of_neg h0, Real.sinh_neg, neg_sq]
  rw [h_sq_eq]
  nlinarith

/-- **Explicit Horizontal `Complex.tan` Bound (`‖tan (π * (σ + V * I) / 2)‖ ≤ 2`)**:
For all `σ : ℝ` and `V : ℝ` with `2 ≤ |V|`,
`Complex.cos (π * ((σ : ℂ) + (V : ℂ) * I) / 2) ≠ 0` and
`‖Complex.tan (π * ((σ : ℂ) + (V : ℂ) * I) / 2)‖ ≤ 2`. -/
theorem cos_ne_zero_and_norm_tan_le_two_of_two_le_abs (σ : ℝ) {V : ℝ} (hV : 2 ≤ |V|) :
    Complex.cos (π * ((σ : ℂ) + (V : ℂ) * I) / 2) ≠ 0 ∧
      ‖Complex.tan (π * ((σ : ℂ) + (V : ℂ) * I) / 2)‖ ≤ 2 := by
  set x : ℝ := Real.pi * σ / 2
  set y : ℝ := Real.pi * V / 2
  have h_arg : π * ((σ : ℂ) + (V : ℂ) * I) / 2 = (x : ℂ) + (y : ℂ) * I := by
    dsimp [x, y]
    push_cast
    ring
  rw [h_arg]
  have hy : 1 ≤ |y| := by
    have h1 : |y| = Real.pi * |V| / 2 := by
      dsimp [y]
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, show |(2 : ℝ)| = 2 by norm_num]
    have hpi : 2 ≤ Real.pi := Real.two_le_pi
    nlinarith
  have h_sinh_sq := nine_sixteenths_le_sinh_sq_of_one_le_abs hy
  have h_sin_sq := normSq_sin_add_mul_I x y
  have h_cos_sq := normSq_cos_add_mul_I x y
  have h_cos_nonneg : 0 ≤ Real.cos x ^ 2 := sq_nonneg _
  have h_sin_le_one : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
  have h_cos_pos : 0 < Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * I)) := by linarith
  have h_cos_ne : Complex.cos ((x : ℂ) + (y : ℂ) * I) ≠ 0 :=
    Complex.normSq_pos.mp h_cos_pos
  refine ⟨h_cos_ne, ?_⟩
  rw [Complex.tan_eq_sin_div_cos, norm_div]
  have h_norm_cos_pos : 0 < ‖Complex.cos ((x : ℂ) + (y : ℂ) * I)‖ := norm_pos_iff.mpr h_cos_ne
  rw [div_le_iff₀ h_norm_cos_pos]
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  linarith

/-- Corollary: `‖Complex.tan (π * ((σ : ℂ) + (V : ℂ) * I) / 2)‖ ≤ 2` for `2 ≤ |V|`. -/
theorem norm_tan_pi_mul_div_two_le_two (σ : ℝ) {V : ℝ} (hV : 2 ≤ |V|) :
    ‖Complex.tan (π * ((σ : ℂ) + (V : ℂ) * I) / 2)‖ ≤ 2 :=
  (cos_ne_zero_and_norm_tan_le_two_of_two_le_abs σ hV).2

/-- For `x > 0`, `(x : ℂ) ≠ -(m : ℂ)` for all `m : ℕ`. -/
theorem ofReal_ne_neg_natCast_of_pos {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (x : ℂ) ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- For `s : ℂ` with `0 < s.re`, `s ≠ -(m : ℂ)` for all `m : ℕ`. -/
theorem ne_neg_natCast_of_re_pos {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    s ≠ -(m : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- For `x : ℝ` with `0 < x`, `deriv Complex.Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ)`. -/
theorem deriv_Gamma_ofReal_eq {x : ℝ} (hx : 0 < x) :
    deriv Complex.Gamma (x : ℂ) = ((deriv Real.Gamma x : ℝ) : ℂ) := by
  have hC : DifferentiableAt ℂ Complex.Gamma (x : ℂ) :=
    Complex.differentiableAt_Gamma _ (ofReal_ne_neg_natCast_of_pos hx)
  have hR : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma fun m ↦ ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have h1 : HasDerivAt (fun y : ℝ ↦ Complex.Gamma (y : ℂ)) (deriv Complex.Gamma (x : ℂ)) x :=
    hC.hasDerivAt.comp_ofReal
  have h2 : HasDerivAt (fun y : ℝ ↦ Complex.Gamma (y : ℂ)) ((deriv Real.Gamma x : ℝ) : ℂ) x := by
    rw [show (fun y : ℝ ↦ Complex.Gamma (y : ℂ)) = fun y : ℝ ↦ (Real.Gamma y : ℂ) from
      funext Complex.Gamma_ofReal]
    exact hR.hasDerivAt.ofReal_comp
  exact h1.unique h2

/-- For `x : ℝ` with `0 < x`,
`Complex.digamma (x : ℂ) = ((deriv (Real.log ∘ Real.Gamma) x : ℝ) : ℂ)`. -/
theorem digamma_ofReal_eq_deriv_log_Gamma {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = ((deriv (Real.log ∘ Real.Gamma) x : ℝ) : ℂ) := by
  have hR : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma fun m ↦ ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  rw [Complex.digamma_def, logDeriv_apply, deriv_Gamma_ofReal_eq hx, Complex.Gamma_ofReal,
    Function.comp_def, deriv.log hR hpos.ne', Complex.ofReal_div]

/-- For `x : ℝ` with `0 < x`, `(Complex.digamma (x : ℂ)).re = deriv (Real.log ∘ Real.Gamma) x`. -/
theorem digamma_ofReal_re {x : ℝ} (hx : 0 < x) :
    (Complex.digamma (x : ℂ)).re = deriv (Real.log ∘ Real.Gamma) x := by
  rw [digamma_ofReal_eq_deriv_log_Gamma hx, Complex.ofReal_re]

/-- **Bohr–Mollerup Convexity Sandwich for `Complex.digamma (x + 1)`**:
For all real `x > 0`, `Real.log x ≤ (Complex.digamma ((x : ℂ) + 1)).re ≤ Real.log (x + 1)`. -/
theorem digamma_add_one_re_sandwich {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ (Complex.digamma ((x : ℂ) + 1)).re ∧
      (Complex.digamma ((x : ℂ) + 1)).re ≤ Real.log (x + 1) := by
  let f : ℝ → ℝ := Real.log ∘ Real.Gamma
  have hc : ConvexOn ℝ (Ioi 0) f := Real.convexOn_log_Gamma
  have h_rec (y : ℝ) (hy : 0 < y) : f (y + 1) = f y + Real.log y := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have hder {y : ℝ} (hy : 0 < y) : DifferentiableAt ℝ f y := by
    refine (Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_) <;>
      exact fun m ↦ ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hx1_cast : ((x : ℂ) + 1) = ((x + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hx1_cast, digamma_ofReal_re (by positivity)]
  constructor
  · refine (le_of_eq ?_).trans <|
      hc.slope_le_deriv (mem_Ioi.mpr hx) (by positivity : (0 : ℝ) < x + 1)
        (by linarith) (hder (by positivity))
    rw [slope_def_field, show x + 1 - x = (1 : ℝ) by ring, div_one, h_rec x hx,
      add_sub_cancel_left]
  · refine (hc.deriv_le_slope (by positivity : (0 : ℝ) < x + 1)
      (by positivity : (0 : ℝ) < x + 2) (by linarith) (hder (by positivity))).trans (le_of_eq ?_)
    rw [slope_def_field, show x + 2 - (x + 1) = (1 : ℝ) by ring, div_one,
      show x + 2 = (x + 1) + 1 by ring, h_rec (x + 1) (by positivity), add_sub_cancel_left]

/-- **Bohr–Mollerup Convexity Sandwich for `Complex.digamma x`**:
For all real `x > 0`, `Real.log x - 1 / x ≤ (Complex.digamma (x : ℂ)).re ≤ Real.log x`. -/
theorem digamma_ofReal_re_sandwich {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / x ≤ (Complex.digamma (x : ℂ)).re ∧
      (Complex.digamma (x : ℂ)).re ≤ Real.log x := by
  let f : ℝ → ℝ := Real.log ∘ Real.Gamma
  have hc : ConvexOn ℝ (Ioi 0) f := Real.convexOn_log_Gamma
  have h_rec : f (x + 1) = f x + Real.log x := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hx.ne',
      Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne', add_comm]
  have hder : DifferentiableAt ℝ f x := by
    refine (Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_) <;>
      exact fun m ↦ ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have h_step := Complex.digamma_apply_add_one (x : ℂ) (ofReal_ne_neg_natCast_of_pos hx)
  have h_re_step : (Complex.digamma ((x : ℂ) + 1)).re = (Complex.digamma (x : ℂ)).re + 1 / x := by
    rw [h_step, add_re, inv_re, normSq_ofReal, ofReal_re, div_self_mul_self', one_div]
  have h_lb := (digamma_add_one_re_sandwich hx).1
  constructor
  · linarith
  · rw [digamma_ofReal_re hx]
    refine (hc.deriv_le_slope (mem_Ioi.mpr hx) (by positivity : (0 : ℝ) < x + 1)
      (by linarith) hder).trans (le_of_eq ?_)
    rw [slope_def_field, show x + 1 - x = (1 : ℝ) by ring, div_one, h_rec, add_sub_cancel_left]

/-- For all real `x > 0`, `‖Complex.digamma (x : ℂ) - Complex.log (x : ℂ)‖ ≤ 1 / x`. -/
theorem norm_digamma_ofReal_sub_log_le {x : ℝ} (hx : 0 < x) :
    ‖Complex.digamma (x : ℂ) - Complex.log (x : ℂ)‖ ≤ 1 / x := by
  have h_eq :
      Complex.digamma (x : ℂ) - Complex.log (x : ℂ) =
        ((deriv (Real.log ∘ Real.Gamma) x - Real.log x : ℝ) : ℂ) := by
    rw [digamma_ofReal_eq_deriv_log_Gamma hx, ← Complex.ofReal_log hx.le, Complex.ofReal_sub]
  rw [h_eq, Complex.norm_real, Real.norm_eq_abs, ← digamma_ofReal_re hx, abs_le]
  have h_sand := digamma_ofReal_re_sandwich hx
  have hx_inv : 0 ≤ 1 / x := by positivity
  constructor <;> linarith

/-- **Asymptotic Vanishing of `ψ(x + n) - log(x + n)` as `n → ∞`**:
For all real `x > 0`,
`Tendsto (fun n : ℕ ↦ Complex.digamma (x + n) - Complex.log (x + n)) atTop (𝓝 0)`. -/
theorem tendsto_digamma_add_nat_sub_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ ↦ Complex.digamma ((x : ℂ) + n) - Complex.log ((x : ℂ) + n))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (g := fun n : ℕ ↦ 1 / (x + (n : ℝ))) (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) ?_
  · have hxn_pos : 0 < x + (n : ℝ) := by positivity
    have h_cast : (x : ℂ) + (n : ℂ) = ((x + n : ℝ) : ℂ) := by push_cast; ring
    rw [h_cast]
    exact norm_digamma_ofReal_sub_log_le hxn_pos
  · have h_tendsto : Tendsto (fun n : ℕ ↦ x + (n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop
    simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp h_tendsto

/-- The sawtooth / first periodic Bernoulli function `B₁(t - ⌊t⌋₊) = t - ⌊t⌋₊ - 1 / 2`. -/
noncomputable def sawtoothB1 (t : ℝ) : ℝ :=
  t - ⌊t⌋₊ - 1 / 2

/-- For all `t ≥ 0`, `|sawtoothB1 t| ≤ 1 / 2`. -/
theorem abs_sawtoothB1_le_half {t : ℝ} (ht : 0 ≤ t) :
    |sawtoothB1 t| ≤ 1 / 2 := by
  unfold sawtoothB1
  have h1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
  have h2 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  rw [abs_le]
  constructor <;> linarith

/-- Measurability of `sawtoothB1`. -/
theorem measurable_sawtoothB1 : Measurable sawtoothB1 := by
  unfold sawtoothB1
  exact (measurable_id.sub (measurable_from_nat.comp Nat.measurable_floor)).sub measurable_const

/-- The Euler–Maclaurin / Binet integrand `(t - ⌊t⌋₊ - 1 / 2 : ℂ) / (s + t) ^ 2`. -/
noncomputable def binetIntegrand (s : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) - ⌊t⌋₊ - 1 / 2) / (s + t) ^ 2

theorem binetIntegrand_eq_sawtoothB1 (s : ℂ) (t : ℝ) :
    binetIntegrand s t = (sawtoothB1 t : ℂ) / (s + t) ^ 2 := by
  unfold binetIntegrand sawtoothB1
  push_cast
  rfl

/-- For `s : ℂ` with `0 < s.re` and `t ≥ 0`, `s + t ∈ Complex.slitPlane`. -/
theorem add_ofReal_mem_slitPlane {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 ≤ t) :
    s + (t : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simp only [add_re, ofReal_re]
  linarith

/-- For `s : ℂ` with `0 < s.re` and `t ≥ 0`, `s.re + t ≤ ‖s + t‖`. -/
theorem re_add_le_norm_add_ofReal {s : ℂ} {t : ℝ} :
    s.re + t ≤ ‖s + (t : ℂ)‖ := by
  have h : (s + (t : ℂ)).re ≤ ‖s + (t : ℂ)‖ := Complex.re_le_norm (s + (t : ℂ))
  simpa using h

/-- For `s : ℂ` with `0 < s.re` and `t ≥ 0`, `s + (t : ℂ) ≠ 0`. -/
theorem add_ofReal_ne_zero {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 ≤ t) :
    s + (t : ℂ) ≠ 0 :=
  Complex.slitPlane_ne_zero (add_ofReal_mem_slitPlane hs ht)

/-- Pointwise norm bound on `binetIntegrand s t` for `0 < s.re` and `0 ≤ t`:
`‖binetIntegrand s t‖ ≤ (1 / 2) / (s.re + t) ^ 2`. -/
theorem norm_binetIntegrand_le {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖binetIntegrand s t‖ ≤ (1 / 2) / (s.re + t) ^ 2 := by
  rw [binetIntegrand_eq_sawtoothB1, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow]
  have hpos : 0 < s.re + t := by linarith
  have h_norm : (s.re + t) ^ 2 ≤ ‖s + (t : ℂ)‖ ^ 2 :=
    pow_le_pow_left₀ hpos.le re_add_le_norm_add_ofReal 2
  exact div_le_div₀ (by norm_num) (abs_sawtoothB1_le_half ht) (sq_pos_of_pos hpos) h_norm

/-- Exact improper integral `∫ t in Ioi (0 : ℝ), 1 / (a + t) ^ 2 = 1 / a` for `a > 0`. -/
theorem integral_Ioi_one_div_add_sq {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, 1 / (a + t) ^ 2) = 1 / a := by
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun u : ℝ ↦ -(a + u)⁻¹) (1 / (a + t) ^ 2) t := by
    intro t ht
    have hat : a + t ≠ 0 := by linarith [mem_Ici.mp ht]
    have hd := ((hasDerivAt_id t).const_add a).inv hat |>.neg
    refine hd.congr_deriv ?_
    dsimp only [id]
    ring
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / (a + t) ^ 2 := fun t _ ↦ by positivity
  have htend : Tendsto (fun u : ℝ ↦ -(a + u)⁻¹) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = -0 by ring]
    exact (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop a tendsto_id)).neg
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos htend]
  ring

/-- Integrability of `t ↦ 1 / (a + t) ^ 2` on `Ioi (0 : ℝ)` for `a > 0`. -/
theorem integrableOn_Ioi_one_div_add_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ 1 / (a + t) ^ 2) (Ioi 0) := by
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun u : ℝ ↦ -(a + u)⁻¹) (1 / (a + t) ^ 2) t := by
    intro t ht
    have hat : a + t ≠ 0 := by linarith [mem_Ici.mp ht]
    have hd := ((hasDerivAt_id t).const_add a).inv hat |>.neg
    refine hd.congr_deriv ?_
    dsimp only [id]
    ring
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / (a + t) ^ 2 := fun t _ ↦ by positivity
  have htend : Tendsto (fun u : ℝ ↦ -(a + u)⁻¹) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = -0 by ring]
    exact (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop a tendsto_id)).neg
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend

/-- Measurability of `binetIntegrand s`. -/
theorem measurable_binetIntegrand (s : ℂ) : Measurable (binetIntegrand s) := by
  rw [funext (binetIntegrand_eq_sawtoothB1 s)]
  refine (Complex.measurable_ofReal.comp measurable_sawtoothB1).div ?_
  exact (measurable_const.add Complex.measurable_ofReal).pow_const 2

/-- `binetIntegrand s` is `IntegrableOn` `Ioi (0 : ℝ)` for every `s : ℂ` with `0 < s.re`. -/
theorem integrableOn_Ioi_binetIntegrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (binetIntegrand s) (Ioi 0) := by
  have h_dom : IntegrableOn (fun t : ℝ ↦ (1 / 2) * (1 / (s.re + t) ^ 2)) (Ioi 0) :=
    (integrableOn_Ioi_one_div_add_sq hs).const_mul (1 / 2)
  refine h_dom.mono' (measurable_binetIntegrand s).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [mul_one_div]
  exact norm_binetIntegrand_le hs (mem_Ioi.mp ht).le

/-- For every `s : ℂ` with `0 < s.re` and every `a b : ℝ` with `0 ≤ a ≤ b`, `binetIntegrand s`
is `IntervalIntegrable` on `a..b`. -/
theorem intervalIntegrable_binetIntegrand {s : ℂ} (hs : 0 < s.re) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (binetIntegrand s) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine (integrableOn_Ioi_binetIntegrand hs).mono_set ?_
  intro t ht
  exact mem_Ioi.mpr (ha.trans_lt ht.1)

/-- The 1D antiderivative on $[k, k + 1]$ for the Euler–Maclaurin formula:
$$\Phi_{\text{EM}}(s, k, t) := \log(s + t) - \frac{t - k - 1/2}{s + t}.$$ -/
noncomputable def eulerMaclaurinAntideriv (s : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  Complex.log (s + t) - ((t : ℂ) - k - 1 / 2) / (s + t)

/-- Exact derivative of `eulerMaclaurinAntideriv s k` for `0 < s.re` and `0 ≤ t`. -/
theorem hasDerivAt_eulerMaclaurinAntideriv {s : ℂ} (hs : 0 < s.re) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (eulerMaclaurinAntideriv s k) (((t : ℂ) - k - 1 / 2) / (s + t) ^ 2) t := by
  unfold eulerMaclaurinAntideriv
  have h_slit : s + (t : ℂ) ∈ Complex.slitPlane := add_ofReal_mem_slitPlane hs ht
  have h_ne : s + (t : ℂ) ≠ 0 := Complex.slitPlane_ne_zero h_slit
  have hd_st : HasDerivAt (fun u : ℝ ↦ s + (u : ℂ)) 1 t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_add s
  have hd_log : HasDerivAt (fun u : ℝ ↦ Complex.log (s + u)) (1 / (s + t)) t :=
    hd_st.clog_real h_slit
  have hd_num : HasDerivAt (fun u : ℝ ↦ (u : ℂ) - k - 1 / 2) 1 t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).sub_const (k : ℂ)).sub_const (1 / 2 : ℂ)
  have hd_quot := hd_num.div hd_st h_ne
  refine (hd_log.sub hd_quot).congr_deriv ?_
  rw [div_sub_div _ _ h_ne (pow_ne_zero 2 h_ne)]
  have h_num_eq :
      1 * (s + (t : ℂ)) ^ 2 - (s + (t : ℂ)) * (1 * (s + (t : ℂ)) - ((t : ℂ) - k - 1 / 2) * 1) =
        ((t : ℂ) - k - 1 / 2) * (s + (t : ℂ)) := by
    ring
  rw [h_num_eq]
  have h_pow : (s + (t : ℂ)) * (s + (t : ℂ)) ^ 2 = (s + (t : ℂ)) ^ 2 * (s + (t : ℂ)) := by ring
  rw [h_pow, mul_div_mul_right _ _ h_ne]

/-- **Unit-Interval Euler–Maclaurin Identity**:
For `0 < s.re` and `k : ℕ`,
`∫ t in k..(k + 1), (t - k - 1 / 2) / (s + t) ^ 2 =`
`log (s + k + 1) - log (s + k) - 1 / (2 * (s + k + 1)) - 1 / (2 * (s + k))`. -/
theorem intervalIntegral_eulerMaclaurin_unit {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    (∫ t : ℝ in (k : ℝ)..(k + 1 : ℝ), (((t : ℂ) - k - 1 / 2) / (s + t) ^ 2)) =
      Complex.log (s + k + 1) - Complex.log (s + k) -
        1 / (2 * (s + k + 1)) - 1 / (2 * (s + k)) := by
  have hk_le : (k : ℝ) ≤ k + 1 := by linarith
  have hderiv : ∀ t ∈ Set.uIcc (k : ℝ) (k + 1 : ℝ),
      HasDerivAt (eulerMaclaurinAntideriv s k) (((t : ℂ) - k - 1 / 2) / (s + t) ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hk_le] at ht
    have ht_nonneg : 0 ≤ t := (Nat.cast_nonneg k).trans ht.1
    exact hasDerivAt_eulerMaclaurinAntideriv hs k ht_nonneg
  have hint : IntervalIntegrable (fun t : ℝ ↦ (((t : ℂ) - k - 1 / 2) / (s + t) ^ 2))
      volume (k : ℝ) (k + 1 : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hk_le]
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).integrableOn_Icc
    have ht_nonneg : 0 ≤ t := (Nat.cast_nonneg k).trans ht.1
    have h_ne : (s + (t : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (add_ofReal_ne_zero hs ht_nonneg)
    refine ContinuousAt.div ?_ ?_ h_ne
    · fun_prop
    · fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold eulerMaclaurinAntideriv
  push_cast
  have h1 : s + ((k : ℂ) + 1) = s + (k : ℂ) + 1 := by ring
  have h2 : (k : ℂ) + 1 - (k : ℂ) - 1 / 2 = 1 / 2 := by ring
  have h3 : (k : ℂ) - (k : ℂ) - 1 / 2 = -(1 / 2) := by ring
  rw [h1, h2, h3]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Replacing `k` by `⌊t⌋₊` on `(k : ℝ)..(k + 1 : ℝ)` in `intervalIntegral_eulerMaclaurin_unit`. -/
theorem intervalIntegral_binetIntegrand_unit {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    (∫ t : ℝ in (k : ℝ)..(k + 1 : ℝ), binetIntegrand s t) =
      (Complex.log (s + (k + 1 : ℕ)) - 1 / (2 * (s + (k + 1 : ℕ)))) -
        (Complex.log (s + (k : ℕ)) - 1 / (2 * (s + (k : ℕ)))) -
        (s + (k : ℕ))⁻¹ := by
  have hk_le : (k : ℝ) ≤ k + 1 := by linarith
  have h_congr :
      (∫ t : ℝ in (k : ℝ)..(k + 1 : ℝ), binetIntegrand s t) =
        ∫ t : ℝ in (k : ℝ)..(k + 1 : ℝ), (((t : ℂ) - k - 1 / 2) / (s + t) ^ 2) := by
    refine intervalIntegral.integral_congr_Ioo_of_le hk_le fun t ht ↦ ?_
    unfold binetIntegrand
    have ht_nonneg : 0 ≤ t := (Nat.cast_nonneg k).trans ht.1.le
    have h_floor : ⌊t⌋₊ = k := Nat.floor_eq_iff ht_nonneg |>.mpr ⟨ht.1.le, ht.2⟩
    rw [h_floor]
  rw [h_congr, intervalIntegral_eulerMaclaurin_unit hs k]
  push_cast
  have h1 : s + ((k : ℂ) + 1) = s + (k : ℂ) + 1 := by ring
  rw [h1]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- **Telescoped Finite Euler–Maclaurin Identity on `[0, n]`**:
For all `s : ℂ` with `0 < s.re` and all `n : ℕ`,
`∫ t in 0..n, binetIntegrand s t =`
`log (s + n) - log s + 1 / (2 * s) - 1 / (2 * (s + n)) - ∑ k ∈ range n, (s + k)⁻¹`. -/
theorem intervalIntegral_binetIntegrand_range {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..(n : ℝ), binetIntegrand s t) =
      Complex.log (s + n) - Complex.log s + 1 / (2 * s) - 1 / (2 * (s + n)) -
        ∑ k ∈ Finset.range n, (s + k)⁻¹ := by
  have h_adj :
      (∑ k ∈ Finset.range n, ∫ t : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), binetIntegrand s t) =
        ∫ t : ℝ in ((0 : ℕ) : ℝ)..(n : ℝ), binetIntegrand s t := by
    refine intervalIntegral.sum_integral_adjacent_intervals fun k _ ↦ ?_
    push_cast
    exact intervalIntegrable_binetIntegrand hs (Nat.cast_nonneg k) (by linarith)
  simp only [Nat.cast_zero] at h_adj
  rw [← h_adj]
  have h_sum_eq :
      (∑ k ∈ Finset.range n, ∫ t : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), binetIntegrand s t) =
        ∑ k ∈ Finset.range n,
          (((Complex.log (s + (k + 1 : ℕ)) - 1 / (2 * (s + (k + 1 : ℕ)))) -
              (Complex.log (s + (k : ℕ)) - 1 / (2 * (s + (k : ℕ))))) -
            (s + (k : ℕ))⁻¹) := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    push_cast
    simpa [Nat.cast_add, Nat.cast_one] using intervalIntegral_binetIntegrand_unit hs k
  rw [h_sum_eq, Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun k : ℕ ↦ Complex.log (s + (k : ℕ)) - 1 / (2 * (s + (k : ℕ)))) n]
  simp only [Nat.cast_zero, add_zero]
  ring

/-- **Finite Euler–Maclaurin Formula for `Complex.digamma s`**:
For all `s : ℂ` with `0 < s.re` and all `n : ℕ`. -/
theorem digamma_eq_log_sub_half_inv_sub_intervalIntegral_add_rem {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Complex.digamma s =
      Complex.log s - 1 / (2 * s) + (∫ t : ℝ in (0 : ℝ)..(n : ℝ), binetIntegrand s t) +
        (Complex.digamma (s + n) - Complex.log (s + n)) + 1 / (2 * (s + n)) := by
  have h_rec := Complex.digamma_apply_add_nat (ne_neg_natCast_of_re_pos hs) n
  have h_int := intervalIntegral_binetIntegrand_range hs n
  linear_combination -h_rec - h_int

/-- **Euler–Maclaurin / Binet Integral Representation for Real `x > 0`**. -/
theorem digamma_ofReal_eq_eulerMaclaurin {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) =
      Complex.log (x : ℂ) - 1 / (2 * (x : ℂ)) +
        ∫ t : ℝ in Ioi 0, binetIntegrand (x : ℂ) t := by
  have hx_re : 0 < (x : ℂ).re := by simpa using hx
  have h_int_tendsto :
      Tendsto (fun n : ℕ ↦ ∫ t : ℝ in (0 : ℝ)..(n : ℝ), binetIntegrand (x : ℂ) t)
        atTop (𝓝 (∫ t : ℝ in Ioi 0, binetIntegrand (x : ℂ) t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_Ioi_binetIntegrand hx_re) tendsto_natCast_atTop_atTop
  have h_rem1 :
      Tendsto (fun n : ℕ ↦ Complex.digamma ((x : ℂ) + n) - Complex.log ((x : ℂ) + n))
        atTop (𝓝 0) :=
    tendsto_digamma_add_nat_sub_log hx
  have h_rem2 : Tendsto (fun n : ℕ ↦ (1 : ℂ) / (2 * ((x : ℂ) + n))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun n : ℕ ↦ 1 / (2 * (x + (n : ℝ))))
      (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) ?_
    · have hxn_pos : 0 < x + (n : ℝ) := by positivity
      have h_norm : x + (n : ℝ) ≤ ‖(x : ℂ) + (n : ℂ)‖ := by
        simpa using re_add_le_norm_add_ofReal (s := (x : ℂ)) (t := (n : ℝ))
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    · have h_tend : Tendsto (fun n : ℕ ↦ 2 * (x + (n : ℝ))) atTop atTop :=
        (tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop).const_mul_atTop
          (by norm_num)
      have h_inv := tendsto_inv_atTop_zero.comp h_tend
      refine h_inv.congr fun n ↦ ?_
      dsimp [Function.comp]
      ring
  have h_rhs :=
    (((tendsto_const_nhds (x := Complex.log (x : ℂ) - 1 / (2 * (x : ℂ)))).add h_int_tendsto).add
      h_rem1).add h_rem2
  simp only [add_zero] at h_rhs
  have h_const :
      Tendsto (fun _ : ℕ ↦ Complex.digamma (x : ℂ)) atTop (𝓝 (Complex.digamma (x : ℂ))) :=
    tendsto_const_nhds
  refine tendsto_nhds_unique h_const (h_rhs.congr fun n ↦ ?_)
  exact (digamma_eq_log_sub_half_inv_sub_intervalIntegral_add_rem hx_re n).symm

/-- Complex differentiability of `s ↦ ∫ t in Ioi 0, binetIntegrand s t` on `{s : ℂ | 0 < s.re}`. -/
theorem differentiableOn_integral_binetIntegrand :
    DifferentiableOn ℂ (fun s : ℂ ↦ ∫ t : ℝ in Ioi 0, binetIntegrand s t)
      {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hs₀_re : 0 < s₀.re := hs₀
  set c : ℝ := s₀.re / 2
  have hc : 0 < c := half_pos hs₀_re
  let V : Set ℂ := {z : ℂ | c < z.re}
  have hV_open : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hs₀_V : s₀ ∈ V := by simp [V, c, half_lt_self hs₀_re]
  have hV_nhds : V ∈ 𝓝 s₀ := hV_open.mem_nhds hs₀_V
  let F : ℂ → ℝ → ℂ := binetIntegrand
  let F' : ℂ → ℝ → ℂ := fun z t ↦ -2 * (sawtoothB1 t : ℂ) / (z + t) ^ 3
  let bound : ℝ → ℝ := fun t ↦ (1 / c) * (1 / (c + t) ^ 2)
  have hF'_meas : ∀ z : ℂ, Measurable (F' z) := by
    intro z
    refine (measurable_const.mul (Complex.measurable_ofReal.comp measurable_sawtoothB1)).div ?_
    exact (measurable_const.add Complex.measurable_ofReal).pow_const 3
  have h_hasDeriv :
      HasDerivAt (fun z : ℂ ↦ ∫ t : ℝ in Ioi 0, F z t)
        (∫ t : ℝ in Ioi 0, F' s₀ t) s₀ := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := bound) hV_nhds
      (Eventually.of_forall fun z ↦ (measurable_binetIntegrand z).aestronglyMeasurable)
      (integrableOn_Ioi_binetIntegrand hs₀_re)
      (hF'_meas s₀).aestronglyMeasurable ?_ ?_ ?_).2
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      have ht_pos : 0 < t := mem_Ioi.mp ht
      have hz_re : c < z.re := hz
      have hct_pos : 0 < c + t := by linarith
      have h_norm_ge : c + t ≤ ‖z + (t : ℂ)‖ := by
        have h1 : c + t ≤ z.re + t := by linarith
        exact h1.trans re_add_le_norm_add_ofReal
      have h_num : ‖-2 * (sawtoothB1 t : ℂ)‖ ≤ 1 := by
        rw [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
        linarith [abs_sawtoothB1_le_half ht_pos.le]
      have h_den : c * (c + t) ^ 2 ≤ ‖z + (t : ℂ)‖ ^ 3 := by
        calc
          c * (c + t) ^ 2 ≤ (c + t) * (c + t) ^ 2 := by gcongr; linarith
          _ = (c + t) ^ 3 := by ring
          _ ≤ ‖z + (t : ℂ)‖ ^ 3 := pow_le_pow_left₀ hct_pos.le h_norm_ge 3
      dsimp [F', bound]
      rw [norm_div, norm_pow, one_div_mul_one_div]
      exact div_le_div₀ (by positivity) h_num (by positivity) h_den
    · exact (integrableOn_Ioi_one_div_add_sq hc).const_mul (1 / c)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
      have ht_pos : 0 < t := mem_Ioi.mp ht
      have hz_re : 0 < z.re := hc.trans hz
      have h_ne : z + (t : ℂ) ≠ 0 := add_ofReal_ne_zero hz_re ht_pos.le
      have hd_pow : HasDerivAt (fun w : ℂ ↦ (w + (t : ℂ)) ^ 2) (2 * (z + (t : ℂ))) z := by
        simpa [Pi.pow_def, pow_one] using ((hasDerivAt_id z).add_const (t : ℂ)).pow 2
      have hd_inv := (hd_pow.inv (pow_ne_zero 2 h_ne)).const_mul (sawtoothB1 t : ℂ)
      dsimp [F, F']
      rw [funext (fun w ↦ binetIntegrand_eq_sawtoothB1 w t)]
      simp only [div_eq_mul_inv]
      refine hd_inv.congr_deriv ?_
      simp only [div_eq_mul_inv]
      have h_pow4 : ((z + (t : ℂ)) ^ 2) ^ 2 = (z + (t : ℂ)) ^ 3 * (z + (t : ℂ)) := by ring
      rw [h_pow4, mul_inv]
      linear_combination -2 * (sawtoothB1 t : ℂ) * ((z + (t : ℂ)) ^ 3)⁻¹ * mul_inv_cancel₀ h_ne
  exact h_hasDeriv.differentiableAt.differentiableWithinAt

/-- Complex differentiability of `Complex.digamma` on `{s : ℂ | 0 < s.re}`. -/
theorem differentiableOn_digamma_rightHalfPlane :
    DifferentiableOn ℂ Complex.digamma {s : ℂ | 0 < s.re} := by
  have hU_open : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGamma : DifferentiableOn ℂ Complex.Gamma {s : ℂ | 0 < s.re} := fun s hs ↦
    (Complex.differentiableAt_Gamma s (ne_neg_natCast_of_re_pos hs)).differentiableWithinAt
  have hGamma' : DifferentiableOn ℂ (deriv Complex.Gamma) {s : ℂ | 0 < s.re} :=
    hGamma.deriv hU_open
  rw [Complex.digamma_def]
  intro s hs
  exact (hGamma' s hs).div (hGamma s hs) (Complex.Gamma_ne_zero_of_re_pos hs)

/-- **Euler–Maclaurin / Binet Integral Formula for `Complex.digamma s` (`0 < s.re`)**:
For all `s : ℂ` with `0 < s.re`,
$$\psi(s) = \log s - \frac{1}{2s}
  + \int_{t \in \operatorname{Ioi} 0} \frac{t - \lfloor t \rfloor - 1/2}{(s + t)^2} \, dt.$$ -/
theorem digamma_eq_log_sub_half_inv_sub_integral {s : ℂ} (hs : 0 < s.re) :
    Complex.digamma s =
      Complex.log s - 1 / (2 * s) +
        ∫ t : ℝ in Ioi 0, (((t : ℂ) - ⌊t⌋₊ - 1 / 2) / (s + t) ^ 2) := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h1_mem : (1 : ℂ) ∈ U := by simp [U]
  have h_an1 : AnalyticOnNhd ℂ Complex.digamma U :=
    differentiableOn_digamma_rightHalfPlane.analyticOnNhd hU_open
  have h_diff_rhs :
      DifferentiableOn ℂ
        (fun z : ℂ ↦ Complex.log z - 1 / (2 * z) + ∫ t : ℝ in Ioi 0, binetIntegrand z t) U := by
    refine (DifferentiableOn.sub ?_ ?_).add differentiableOn_integral_binetIntegrand
    · refine fun z hz ↦ (Complex.differentiableAt_log ?_).differentiableWithinAt
      exact Complex.mem_slitPlane_iff.mpr (Or.inl hz)
    · refine fun z hz ↦ DifferentiableAt.differentiableWithinAt ?_
      have hz_ne : 2 * z ≠ 0 := mul_ne_zero two_ne_zero (by
        intro h0; rw [h0] at hz; simp [U] at hz)
      exact (differentiableAt_const 1).div (differentiableAt_id.const_mul 2) hz_ne
  have h_an2 := h_diff_rhs.analyticOnNhd hU_open
  have h_tendsto : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 1) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨tendsto_nhdsWithin_of_tendsto_nhds continuous_ofReal.continuousAt,
      eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun t ht ↦ ofReal_ne_one.mpr ht)⟩
  have h_freq :
      ∃ᶠ z in 𝓝[≠] (1 : ℂ),
        Complex.digamma z =
          Complex.log z - 1 / (2 * z) + ∫ t : ℝ in Ioi 0, binetIntegrand z t := by
    refine h_tendsto.frequently ?_
    refine ((Eventually.filter_mono nhdsWithin_le_nhds) ?_).frequently
    refine (eventually_gt_nhds zero_lt_one).mp (Eventually.of_forall fun t ht ↦ ?_)
    exact digamma_ofReal_eq_eulerMaclaurin ht
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq h_an1 h_an2 isPreconnected_re_pos h1_mem
    h_freq hs

/-- **First Binet Remainder Bound (`1 / (2 * s.re)`)**:
For all `s : ℂ` with `0 < s.re`,
`‖Complex.digamma s - Complex.log s + 1 / (2 * s)‖ ≤ 1 / (2 * s.re)`. -/
theorem norm_digamma_sub_log_add_half_inv_le_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.digamma s - Complex.log s + 1 / (2 * s)‖ ≤ 1 / (2 * s.re) := by
  have h_eq :
      Complex.digamma s - Complex.log s + 1 / (2 * s) =
        ∫ t : ℝ in Ioi 0, binetIntegrand s t := by
    have h := digamma_eq_log_sub_half_inv_sub_integral hs
    unfold binetIntegrand
    linear_combination h
  rw [h_eq]
  have h_bound :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
        ‖binetIntegrand s t‖ ≤ (1 / 2) * (1 / (s.re + t) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [mul_one_div]
    exact norm_binetIntegrand_le hs (mem_Ioi.mp ht).le
  have h_int_le :=
    norm_integral_le_of_norm_le ((integrableOn_Ioi_one_div_add_sq hs).const_mul (1 / 2)) h_bound
  rw [MeasureTheory.integral_const_mul, integral_Ioi_one_div_add_sq hs,
    one_div_mul_one_div] at h_int_le
  exact h_int_le

/-- Corollary: for all `s : ℂ` with `0 < s.re`,
`‖Complex.digamma s - Complex.log s‖ ≤ 1 / (2 * ‖s‖) + 1 / (2 * s.re)`. -/
theorem norm_digamma_sub_log_le_norm_add_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.digamma s - Complex.log s‖ ≤ 1 / (2 * ‖s‖) + 1 / (2 * s.re) := by
  have h_decomp :
      Complex.digamma s - Complex.log s =
        (-1 / (2 * s)) + (Complex.digamma s - Complex.log s + 1 / (2 * s)) := by ring
  rw [h_decomp]
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_digamma_sub_log_add_half_inv_le_re hs))
  rw [norm_div, norm_neg, norm_one, norm_mul, Complex.norm_ofNat]

/-- Bound on `‖Complex.log (((σ + 1 : ℝ) : ℂ) + (V : ℂ) * I)‖` for `σ ∈ [-1 / 4, 1 / 2]`:
`‖Complex.log (((σ + 1 : ℝ) : ℂ) + (V : ℂ) * I)‖ ≤ Real.log (|V| + 2) + Real.pi`. -/
theorem norm_log_horizontal_add_one_le {σ V : ℝ} (hσ : σ ∈ Set.Icc (-1 / 4 : ℝ) (1 / 2)) :
    ‖Complex.log (((σ + 1 : ℝ) : ℂ) + (V : ℂ) * I)‖ ≤ Real.log (|V| + 2) + Real.pi := by
  set w : ℂ := ((σ + 1 : ℝ) : ℂ) + (V : ℂ) * I
  have hw_re : w.re = σ + 1 := by simp [w]
  have hw_im : w.im = V := by simp [w]
  have hw_re_ge : 3 / 4 ≤ w.re := by linarith [hσ.1]
  have hw_re_le : w.re ≤ 3 / 2 := by linarith [hσ.2]
  have hw_norm_ge : 3 / 4 ≤ ‖w‖ := hw_re_ge.trans (Complex.re_le_norm w)
  have hw_norm_le : ‖w‖ ≤ |V| + 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im w
    rw [hw_re, hw_im, abs_of_pos (by linarith : 0 < σ + 1)] at h
    linarith [hσ.2]
  have hw_norm_pos : 0 < ‖w‖ := by linarith
  have h_inv_le : (|V| + 2)⁻¹ ≤ ‖w‖ := by
    have h1 : (|V| + 2)⁻¹ ≤ (2 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) (by linarith [abs_nonneg V])
    linarith
  have h_abs_log : |Real.log ‖w‖| ≤ Real.log (|V| + 2) := by
    rw [abs_le]
    refine ⟨?_, Real.log_le_log hw_norm_pos hw_norm_le⟩
    rw [← Real.log_inv]
    exact Real.log_le_log (by positivity) h_inv_le
  rw [Complex.log]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_I, mul_one]
  exact add_le_add h_abs_log (Complex.abs_arg_le_pi w)

/-- **Uniform Horizontal `Complex.digamma` Bound on `σ ∈ [-1 / 4, 1 / 2]` for `2 ≤ |V|`**:
For all `σ ∈ Set.Icc (-1 / 4 : ℝ) (1 / 2)` and `2 ≤ |V|`,
`‖Complex.digamma ((σ : ℂ) + (V : ℂ) * I)‖ ≤ Real.log (|V| + 2) + Real.pi + 11 / 6`. -/
theorem norm_digamma_horizontal_le {σ V : ℝ} (hσ : σ ∈ Set.Icc (-1 / 4 : ℝ) (1 / 2))
    (hV : 2 ≤ |V|) :
    ‖Complex.digamma ((σ : ℂ) + (V : ℂ) * I)‖ ≤ Real.log (|V| + 2) + Real.pi + 11 / 6 := by
  set s : ℂ := (σ : ℂ) + (V : ℂ) * I
  set w : ℂ := ((σ + 1 : ℝ) : ℂ) + (V : ℂ) * I
  have h_sw : s + 1 = w := by dsimp [s, w]; push_cast; ring
  have hs_nat : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m hm
    have him := congrArg Complex.im hm
    have hV0 : V = 0 := by simpa [s] using him
    rw [hV0, abs_zero] at hV
    linarith
  have h_step : Complex.digamma s = (Complex.digamma w - Complex.log w) + Complex.log w - s⁻¹ := by
    have h := Complex.digamma_apply_add_one s hs_nat
    rw [h_sw] at h
    linear_combination -h
  have hw_re_ge : 3 / 4 ≤ w.re := by simp [w]; linarith [hσ.1]
  have hw_re_pos : 0 < w.re := by linarith
  have hw_norm_ge : 3 / 4 ≤ ‖w‖ := hw_re_ge.trans (Complex.re_le_norm w)
  have hs_norm_ge : 2 ≤ ‖s‖ := by
    have h : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    simp [s] at h
    linarith
  have h1 : ‖Complex.digamma w - Complex.log w‖ ≤ 4 / 3 := by
    refine (norm_digamma_sub_log_le_norm_add_re hw_re_pos).trans ?_
    have h_a : 1 / (2 * ‖w‖) ≤ 2 / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    have h_b : 1 / (2 * w.re) ≤ 2 / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have h2 : ‖Complex.log w‖ ≤ Real.log (|V| + 2) + Real.pi :=
    norm_log_horizontal_add_one_le hσ
  have h3 : ‖s⁻¹‖ ≤ 1 / 2 := by
    rw [norm_inv, one_div]
    exact inv_anti₀ two_pos hs_norm_ge
  rw [h_step]
  have h_tri1 := norm_sub_le ((Complex.digamma w - Complex.log w) + Complex.log w) s⁻¹
  have h_tri2 := norm_add_le (Complex.digamma w - Complex.log w) (Complex.log w)
  linarith

/-!
## Section 10: Full Horizontal Segment Bounds on `[-1 / 4, 2] ± U * I`
-/

/-- For any `σ V : ℝ` with `V ≠ 0` and any `n : ℤ`, `(σ : ℂ) + (V : ℂ) * I ≠ (n : ℂ)`. -/
theorem ofReal_add_mul_I_ne_intCast (σ : ℝ) {V : ℝ} (hV : V ≠ 0) (n : ℤ) :
    (σ : ℂ) + (V : ℂ) * I ≠ (n : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  exact hV (by simpa using him)

/-- Under `RiemannHypothesis`, if `V ≠ 0` has a positive gap `0 < Δ` from all critical-line zeros
(`∀ ρ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - V|`), then
`riemannZeta ((σ : ℂ) + (V : ℂ) * I) ≠ 0` for all `σ : ℝ`. -/
theorem riemannZeta_ofReal_add_mul_I_ne_zero_of_gap (hRH : RiemannHypothesis) (σ : ℝ)
    {V Δ : ℝ} (hV : V ≠ 0) (hΔ_pos : 0 < Δ)
    (hgap : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - V|) :
    riemannZeta ((σ : ℂ) + (V : ℂ) * I) ≠ 0 := by
  set s : ℂ := (σ : ℂ) + (V : ℂ) * I
  intro hz
  have hs_im : s.im = V := by simp [s]
  have hs_triv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
    rintro ⟨n, hn⟩
    have him := congrArg Complex.im hn
    exact hV (by simpa [s] using him)
  have hs_one : s ≠ 1 := by
    intro h1
    have him := congrArg Complex.im h1
    exact hV (by simpa [s] using him)
  have hs_re : s.re = 1 / 2 := hRH s hz hs_triv hs_one
  have h_le := hgap s hz hs_re
  rw [hs_im, sub_self, abs_zero] at h_le
  linarith

/-- **Horizontal Bound on `‖deriv riemannZeta / riemannZeta‖` Across `σ ∈ [-1 / 4, 1 / 2]`**:
Under `RiemannHypothesis` and symmetric zero-free gaps `0 < Δ ≤ 1 / 2` at `±V` (`2 ≤ |V|`),
for every `σ ∈ Set.Icc (-1 / 4 : ℝ) (1 / 2)`,
`‖deriv riemannZeta (σ + V * I) / riemannZeta (σ + V * I)‖ ≤`
`(2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + |V|)) + 14`. -/
theorem norm_logDeriv_riemannZeta_le_on_Icc_left_of_gap (hRH : RiemannHypothesis) {V Δ σ : ℝ}
    (hV : 2 ≤ |V|) (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap_pos : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - V|)
    (hgap_neg : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - (-V)|)
    (hσ : σ ∈ Set.Icc (-1 / 4 : ℝ) (1 / 2)) :
    ‖deriv riemannZeta ((σ : ℂ) + (V : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (V : ℂ) * I)‖ ≤
      (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + |V|)) + 14 := by
  set s : ℂ := (σ : ℂ) + (V : ℂ) * I
  have hV_ne : V ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hV; linarith
  have h_negV_ne : -V ≠ 0 := neg_ne_zero.mpr hV_ne
  have hs_int : ∀ n : ℤ, s ≠ (n : ℂ) := ofReal_add_mul_I_ne_intCast σ hV_ne
  have hz : riemannZeta s ≠ 0 :=
    riemannZeta_ofReal_add_mul_I_ne_zero_of_gap hRH σ hV_ne hΔ_pos hgap_pos
  have h_fe := logDeriv_riemannZeta_one_sub hs_int hz
  rw [← logDeriv_apply]
  have h_1s_eq : 1 - s = ((1 - σ : ℝ) : ℂ) + ((-V : ℝ) : ℂ) * I := by
    dsimp [s]; push_cast; ring
  have h_1σ_mem : 1 - σ ∈ Set.Icc (1 / 2 : ℝ) 2 :=
    ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  have h1 : ‖-logDeriv riemannZeta (1 - s)‖ ≤
      (2048 / Δ ^ 4) * Real.log (14 * (1 + |V|)) + 1 / |V| := by
    rw [norm_neg, logDeriv_apply, h_1s_eq]
    have h_right := norm_logDeriv_riemannZeta_le_on_Icc_of_gap hRH h_negV_ne hΔ_pos hΔ_le
      hgap_neg h_1σ_mem
    rwa [abs_neg] at h_right
  have h_inv_V : 1 / |V| ≤ 1 / 2 :=
    one_div_le_one_div_of_le two_pos hV
  have h2 : ‖Complex.log (2 * π)‖ ≤ 3 := by
    have h_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    have h_gt1 : 1 < 2 * Real.pi := by linarith [Real.two_le_pi]
    rw [show (2 * π : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log h_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos h_gt1)]
    have h_le_exp : 2 * Real.pi ≤ Real.exp 3 := by
      have h_pi : Real.pi ≤ 4 := Real.pi_le_four
      have h_e1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h_e2 : (4 : ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
      have h_e3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [show (3 : ℝ) = 1 + 1 + 1 by ring, Real.exp_add, Real.exp_add]
      nlinarith
    have h_log_le := Real.log_le_log h_pos h_le_exp
    rwa [Real.log_exp] at h_log_le
  have h3 : ‖Complex.digamma s‖ ≤ Real.log (14 * (1 + |V|)) + 6 := by
    have hd : ‖Complex.digamma s‖ ≤ Real.log (|V| + 2) + Real.pi + 11 / 6 :=
      norm_digamma_horizontal_le hσ hV
    have h_log_le : Real.log (|V| + 2) ≤ Real.log (14 * (1 + |V|)) :=
      Real.log_le_log (by positivity) (by linarith [abs_nonneg V])
    have h_pi : Real.pi ≤ 4 := Real.pi_le_four
    linarith
  have h4 : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ 4 := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_ofNat]
    have h_tan := norm_tan_pi_mul_div_two_le_two σ hV
    have h_pi : Real.pi ≤ 4 := Real.pi_le_four
    nlinarith [Real.pi_pos]
  rw [h_fe]
  have h_tri1 :=
    norm_add_le (-logDeriv riemannZeta (1 - s) + Complex.log (2 * π) - Complex.digamma s)
      (π / 2 * Complex.tan (π * s / 2))
  have h_tri2 :=
    norm_sub_le (-logDeriv riemannZeta (1 - s) + Complex.log (2 * π)) (Complex.digamma s)
  have h_tri3 := norm_add_le (-logDeriv riemannZeta (1 - s)) (Complex.log (2 * π))
  linarith

/-- **Full Horizontal Segment Bound on `‖deriv riemannZeta / riemannZeta‖`
Across `σ ∈ [-1 / 4, 2]`**:
Under `RiemannHypothesis` and symmetric zero-free gaps `0 < Δ ≤ 1 / 2` at `±V` (`2 ≤ |V|`),
for every `σ ∈ Set.Icc (-1 / 4 : ℝ) 2`,
`‖deriv riemannZeta (σ + V * I) / riemannZeta (σ + V * I)‖ ≤`
`(2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + |V|)) + 14`. -/
theorem norm_logDeriv_riemannZeta_le_on_Icc_neg_quarter_two_of_gap (hRH : RiemannHypothesis)
    {V Δ σ : ℝ} (hV : 2 ≤ |V|) (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap_pos : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - V|)
    (hgap_neg : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - (-V)|)
    (hσ : σ ∈ Set.Icc (-1 / 4 : ℝ) 2) :
    ‖deriv riemannZeta ((σ : ℂ) + (V : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (V : ℂ) * I)‖ ≤
      (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + |V|)) + 14 := by
  rcases le_or_gt σ (1 / 2) with h_left | h_right
  · exact norm_logDeriv_riemannZeta_le_on_Icc_left_of_gap hRH hV hΔ_pos hΔ_le
      hgap_pos hgap_neg ⟨hσ.1, h_left⟩
  · have hV_ne : V ≠ 0 := by intro h0; rw [h0, abs_zero] at hV; linarith
    have h_r := norm_logDeriv_riemannZeta_le_on_Icc_of_gap hRH hV_ne hΔ_pos hΔ_le
      hgap_pos ⟨h_right.le, hσ.2⟩
    have h_inv_V : 1 / |V| ≤ 1 / 2 := one_div_le_one_div_of_le two_pos hV
    have h_log_pos : 0 ≤ Real.log (14 * (1 + |V|)) :=
      Real.log_nonneg (by linarith [abs_nonneg V])
    linarith

/-- **Simultaneous Top and Bottom Horizontal Segment Bounds at Zero-Free Height `U ≥ 2`**:
Under `RiemannHypothesis`, if `2 ≤ U`, `0 < Δ ≤ 1 / 2`, and every critical-line zero `ρ` satisfies
both `Δ ≤ |ρ.im - U|` and `Δ ≤ |ρ.im - (-U)|`, then for every `σ ∈ Set.Icc (-1 / 4 : ℝ) 2`,
both `‖deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) / riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖` and
`‖deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) / riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖` are at most
`(2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) + 14`. -/
theorem norm_logDeriv_riemannZeta_top_and_bot_le_of_gap (hRH : RiemannHypothesis)
    {U Δ σ : ℝ} (hU : 2 ≤ U) (hΔ_pos : 0 < Δ) (hΔ_le : Δ ≤ 1 / 2)
    (hgap_pos : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - U|)
    (hgap_neg : ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 → Δ ≤ |ρ.im - (-U)|)
    (hσ : σ ∈ Set.Icc (-1 / 4 : ℝ) 2) :
    ‖deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤
      (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) + 14 ∧
    ‖deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
        riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤
      (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) + 14 := by
  have hU_abs : |U| = U := abs_of_pos (by linarith)
  have hV_top : 2 ≤ |U| := by linarith
  have hV_bot : 2 ≤ |-U| := by rw [abs_neg]; linarith
  constructor
  · have h := norm_logDeriv_riemannZeta_le_on_Icc_neg_quarter_two_of_gap hRH hV_top hΔ_pos hΔ_le
      hgap_pos hgap_neg hσ
    rwa [hU_abs] at h
  · have h_sub_eq : (σ : ℂ) - (U : ℂ) * I = (σ : ℂ) + ((-U : ℝ) : ℂ) * I := by push_cast; ring
    rw [h_sub_eq]
    have h := norm_logDeriv_riemannZeta_le_on_Icc_neg_quarter_two_of_gap hRH hV_bot hΔ_pos hΔ_le
      hgap_neg (by simpa [neg_neg] using hgap_pos) hσ
    rwa [abs_neg, hU_abs] at h

/-- **Main Existential Theorem: Symmetric Zero-Free Height `U ∈ [T, T + 1]`
with Full Horizontal Bounds**:
For every `T ≥ 2`, under `RiemannHypothesis`, there exist `U ∈ Set.Icc T (T + 1)` and `Δ : ℝ`
such that:
1. `0 < Δ ≤ 1 / 2` and `1 / (314 * Real.log (T + 10)) ≤ Δ`,
2. Every critical-line zero `ρ` satisfies `Δ ≤ |(|ρ.im| - U)|`, `Δ ≤ |ρ.im - U|`,
   and `Δ ≤ |ρ.im - (-U)|`,
3. Every `σ ∈ Set.Icc (-1 / 4 : ℝ) 2` satisfies both top and bottom horizontal bounds:
   `‖deriv riemannZeta (σ ± U * I) / riemannZeta (σ ± U * I)‖ ≤`
   `(2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) + 14`. -/
theorem exists_zero_free_height_with_horizontal_bounds (hRH : RiemannHypothesis)
    {T : ℝ} (hT : 2 ≤ T) :
    ∃ U ∈ Set.Icc T (T + 1), ∃ Δ : ℝ,
      0 < Δ ∧ Δ ≤ 1 / 2 ∧
      1 / (314 * Real.log (T + 10)) ≤ Δ ∧
      (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 →
        Δ ≤ |(|ρ.im| - U)| ∧ Δ ≤ |ρ.im - U| ∧ Δ ≤ |ρ.im - (-U)|) ∧
      (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
        ‖deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
            riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤
          (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) + 14 ∧
        ‖deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
            riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤
          (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) + 14) := by
  obtain ⟨U, hU_mem, Δ, hΔ_pos, hΔ_le, hΔ_lb, hgap⟩ :=
    exists_zero_free_height_in_Icc (by linarith : 0 ≤ T)
  have hU_ge2 : 2 ≤ U := hT.trans hU_mem.1
  refine ⟨U, hU_mem, Δ, hΔ_pos, hΔ_le, hΔ_lb, hgap, ?_⟩
  intro σ hσ
  exact norm_logDeriv_riemannZeta_top_and_bot_le_of_gap hRH hU_ge2 hΔ_pos hΔ_le
    (fun ρ hζ hre ↦ (hgap ρ hζ hre).2.1)
    (fun ρ hζ hre ↦ (hgap ρ hζ hre).2.2) hσ

/-!
## Section 11: `nontrivialZetaZerosUpTo` and `O((log U) ^ 5)` Horizontal Bound Corollary
-/

theorem isNontrivialZetaZero_ne_zero {s : ℂ} (hs : IsNontrivialZetaZero s) : s ≠ 0 := by
  rintro rfl
  have h0 := hs.1
  rw [riemannZeta_zero] at h0
  norm_num at h0

theorem re_lt_one_of_isNontrivialZetaZero {s : ℂ} (hs : IsNontrivialZetaZero s) : s.re < 1 := by
  by_contra! hle
  exact riemannZeta_ne_zero_of_one_le_re hle hs.1

theorem zero_lt_re_of_isNontrivialZetaZero {s : ℂ} (hs : IsNontrivialZetaZero s) : 0 < s.re := by
  by_contra! hle
  have hs0 : s ≠ 0 := isNontrivialZetaZero_ne_zero hs
  have h1s_re : 1 ≤ (1 - s).re := by simp [hle]
  have h1s_ne_neg_nat : ∀ n : ℕ, 1 - s ≠ -n := by
    intro n heq
    have hre := congrArg Complex.re heq
    simp at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1s_ne_one : 1 - s ≠ 1 := by simpa using hs0
  have hfe := riemannZeta_one_sub h1s_ne_neg_nat h1s_ne_one
  rw [sub_sub_cancel, hs.1] at hfe
  have h2pi : (2 * π : ℂ) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    left
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hGamma : Complex.Gamma (1 - s) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hZeta : riemannZeta (1 - s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re h1s_re
  have hcos : cos (π * (1 - s) / 2) = 0 := by
    rcases mul_eq_zero.mp hfe.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · norm_num at h
          · exact absurd h h2pi
        · exact absurd h hGamma
      · exact h
    · exact absurd h hZeta
  rw [cos_eq_zero_iff] at hcos
  obtain ⟨k, hk⟩ := hcos
  have hpi_ne : (π : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
  have h1s_eq : 1 - s = 2 * k + 1 := by
    apply mul_right_cancel₀ hpi_ne
    calc
      (1 - s) * π = (π * (1 - s) / 2) * 2 := by ring
      _ = ((2 * k + 1) * π / 2) * 2 := by rw [hk]
      _ = (2 * k + 1) * π := by ring
  have hs_eq : s = -2 * (k : ℂ) := by linear_combination -h1s_eq
  have hk_re : (k : ℝ) ≥ 0 := by
    have hre := congrArg Complex.re hs_eq
    simp at hre
    linarith
  have hk_int : 0 ≤ k := by exact_mod_cast hk_re
  have hk_ne_zero : k ≠ 0 := by
    rintro rfl
    exact hs0 (by simpa using hs_eq)
  have hk_pos : 1 ≤ k := by omega
  refine hs.2.1 ⟨(k - 1).toNat, ?_⟩
  have hk_nat : ((k - 1).toNat : ℂ) + 1 = (k : ℂ) := by
    have : ((k - 1).toNat : ℤ) + 1 = k := by omega
    exact_mod_cast this
  rw [hk_nat, hs_eq]

theorem mem_criticalStrip_of_isNontrivialZetaZero {s : ℂ} (hs : IsNontrivialZetaZero s) :
    0 < s.re ∧ s.re < 1 :=
  ⟨zero_lt_re_of_isNontrivialZetaZero hs, re_lt_one_of_isNontrivialZetaZero hs⟩

theorem finite_nontrivialZetaZeros_le (T : ℝ) :
    {s : ℂ | IsNontrivialZetaZero s ∧ |s.im| ≤ T}.Finite := by
  have hcompact : IsCompact (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc (-T) T) :=
    isCompact_Icc.reProdIm isCompact_Icc
  refine (hcompact.inter_riemannZetaZeros_finite).subset ?_
  rintro s ⟨hs, him⟩
  obtain ⟨hre0, hre1⟩ := mem_criticalStrip_of_isNontrivialZetaZero hs
  refine ⟨⟨⟨hre0.le, hre1.le⟩, abs_le.mp him⟩, hs.1⟩

/-- The canonical `Finset ℂ` of nontrivial zeros of `riemannZeta` with `|s.im| ≤ T`. -/
noncomputable def nontrivialZetaZerosUpTo (T : ℝ) : Finset ℂ :=
  (finite_nontrivialZetaZeros_le T).toFinset

@[simp]
theorem mem_nontrivialZetaZerosUpTo {T : ℝ} {s : ℂ} :
    s ∈ nontrivialZetaZerosUpTo T ↔ IsNontrivialZetaZero s ∧ |s.im| ≤ T :=
  Set.Finite.mem_toFinset (finite_nontrivialZetaZeros_le T)

/-- **Existential `O((log U) ^ 5)` Horizontal Bound at Arbitrarily Large Zero-Free Heights**:
For every `T ≥ 6`, under `RiemannHypothesis`, there exists a constant `C_h ≥ 0` such that
for every `U₀ ≥ T`, there exists a zero-free height `U ≥ U₀` (in fact `U ∈ Set.Icc U₀ (U₀ + 1)`)
such that:
1. Every `ρ ∈ nontrivialZetaZerosUpTo U` satisfies `|ρ.im| < U`,
2. Every `σ ∈ Set.Icc (-1 / 4 : ℝ) 2` satisfies
   `‖-deriv riemannZeta (σ + U * I) / riemannZeta (σ + U * I)‖ ≤ C_h * (Real.log U) ^ 5`,
3. Every `σ ∈ Set.Icc (-1 / 4 : ℝ) 2` satisfies
   `‖-deriv riemannZeta (σ - U * I) / riemannZeta (σ - U * I)‖ ≤ C_h * (Real.log U) ^ 5`. -/
theorem exists_zero_free_height_with_log_pow_five_bound
    (hRH : RiemannHypothesis) {T : ℝ} (hT : 6 ≤ T) :
    ∃ C_h : ℝ, 0 ≤ C_h ∧ ∀ U₀ ≥ T, ∃ U ≥ U₀,
      (∀ ρ ∈ nontrivialZetaZerosUpTo U, |ρ.im| < U) ∧
      (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
        ‖-deriv riemannZeta ((σ : ℂ) + (U : ℂ) * I) /
          riemannZeta ((σ : ℂ) + (U : ℂ) * I)‖ ≤ C_h * (Real.log U) ^ 5) ∧
      (∀ σ ∈ Set.Icc (-1 / 4 : ℝ) 2,
        ‖-deriv riemannZeta ((σ : ℂ) - (U : ℂ) * I) /
          riemannZeta ((σ : ℂ) - (U : ℂ) * I)‖ ≤ C_h * (Real.log U) ^ 5) := by
  let C_h : ℝ := 3 * (2048 * 628 ^ 4 + 1) + 14
  refine ⟨C_h, by dsimp [C_h]; norm_num, ?_⟩
  intro U₀ hU₀
  have hU₀_ge6 : 6 ≤ U₀ := hT.trans hU₀
  obtain ⟨U, hU_mem, Δ, hΔ_pos, _hΔ_le, hΔ_lb, hgap, h_horiz⟩ :=
    exists_zero_free_height_with_horizontal_bounds hRH (T := U₀) (by linarith)
  have hU_ge_U₀ : U₀ ≤ U := hU_mem.1
  have hU_ge6 : 6 ≤ U := hU₀_ge6.trans hU_ge_U₀
  have hU_pos : 0 < U := by linarith
  have h_logU_ge_one : 1 ≤ Real.log U := by
    have h_exp : Real.exp 1 ≤ U := by linarith [Real.exp_one_lt_d9]
    have h_log := Real.log_le_log (Real.exp_pos 1) h_exp
    rwa [Real.log_exp] at h_log
  have h_logU_pos : 0 < Real.log U := zero_lt_one.trans_le h_logU_ge_one
  have h_log_U₀_add10 : Real.log (U₀ + 10) ≤ 2 * Real.log U := by
    have h_le_sq : U₀ + 10 ≤ U ^ 2 := by nlinarith
    calc
      Real.log (U₀ + 10) ≤ Real.log (U ^ 2) :=
        Real.log_le_log (by linarith) h_le_sq
      _ = 2 * Real.log U := by rw [Real.log_pow]; push_cast; ring
  have h_log_14 : Real.log (14 * (1 + U)) ≤ 3 * Real.log U := by
    have h_le_cube : 14 * (1 + U) ≤ U ^ 3 := by
      have hU2 : 36 ≤ U ^ 2 := by nlinarith
      have hU3 : U ^ 3 = U ^ 2 * U := by ring
      nlinarith
    calc
      Real.log (14 * (1 + U)) ≤ Real.log (U ^ 3) :=
        Real.log_le_log (by positivity) h_le_cube
      _ = 3 * Real.log U := by rw [Real.log_pow]; push_cast; ring
  have h_inv_Δ : 1 / Δ ≤ 628 * Real.log U := by
    have h_den_pos : 0 < 314 * Real.log (U₀ + 10) := by
      have : 1 < U₀ + 10 := by linarith
      exact mul_pos (by norm_num) (Real.log_pos this)
    have h_prod : 1 ≤ Δ * (314 * Real.log (U₀ + 10)) :=
      (div_le_iff₀ h_den_pos).mp hΔ_lb
    have h1 : 1 / Δ ≤ 314 * Real.log (U₀ + 10) := by
      rw [div_le_iff₀ hΔ_pos]
      linarith
    linarith
  have h_inv_Δ4 : 2048 / Δ ^ 4 + 1 ≤ (2048 * 628 ^ 4 + 1) * (Real.log U) ^ 4 := by
    have h_pow4 : (1 / Δ) ^ 4 ≤ (628 * Real.log U) ^ 4 :=
      pow_le_pow_left₀ (by positivity) h_inv_Δ 4
    have h_div_eq : 2048 / Δ ^ 4 = 2048 * (1 / Δ) ^ 4 := by ring
    have h_one_le : (1 : ℝ) ≤ (Real.log U) ^ 4 := one_le_pow₀ h_logU_ge_one
    have h_rhs_eq :
        2048 * (628 * Real.log U) ^ 4 + (Real.log U) ^ 4 =
          (2048 * 628 ^ 4 + 1) * (Real.log U) ^ 4 := by ring
    linarith
  have h_main_bound :
      (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) + 14 ≤ C_h * (Real.log U) ^ 5 := by
    have h_mul :
        (2048 / Δ ^ 4 + 1) * Real.log (14 * (1 + U)) ≤
          ((2048 * 628 ^ 4 + 1) * (Real.log U) ^ 4) * (3 * Real.log U) :=
      mul_le_mul h_inv_Δ4 h_log_14 (Real.log_nonneg (by linarith)) (by positivity)
    have h_one_le5 : (1 : ℝ) ≤ (Real.log U) ^ 5 := one_le_pow₀ h_logU_ge_one
    have h_alg :
        ((2048 * 628 ^ 4 + 1) * (Real.log U) ^ 4) * (3 * Real.log U) + 14 * (Real.log U) ^ 5 =
          C_h * (Real.log U) ^ 5 := by
      dsimp [C_h]
      ring
    linarith
  refine ⟨U, hU_ge_U₀, ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨h_nt, him_le⟩ := mem_nontrivialZetaZerosUpTo.mp hρ
    have hre : ρ.re = 1 / 2 := re_eq_half_of_isNontrivialZetaZero hRH h_nt
    have h_abs_gap := (hgap ρ h_nt.1 hre).1
    have h_ne : |ρ.im| ≠ U := by
      intro h_eq
      rw [h_eq, sub_self, abs_zero] at h_abs_gap
      linarith
    exact lt_of_le_of_ne him_le h_ne
  · intro σ hσ
    rw [neg_div, norm_neg]
    exact (h_horiz σ hσ).1.trans h_main_bound
  · intro σ hσ
    rw [neg_div, norm_neg]
    exact (h_horiz σ hσ).2.trans h_main_bound

end ConjectureMachines.Riemann543.Semantics.HorizontalBounds
