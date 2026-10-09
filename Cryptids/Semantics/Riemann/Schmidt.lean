/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Positivity
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Convex.Topology

open Complex Finset Filter MeasureTheory Asymptotics Set Topology
open scoped Real Topology Nat ENNReal LSeries.notation ArithmeticFunction

namespace RiemannSchmidt

/-!
## Part 1: Nonvanishing of `riemannZeta` on the Positive Real Axis `(0, ∞)`
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

/-- For every `s : ℂ` with `0 < s.re`, `s ↦ s * mellin fractKernel (-s)` is differentiable
at `s`. -/
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
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]
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
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (by intro h; subst h; simp at hs)
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
      IntegrableOn, Measure.restrict_restrict_of_subset (Set.Ioi_subset_Ioi zero_le_one)] at hm
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

/-- Open right half-planes `{z : ℂ | σ₀ < z.re}` are convex. -/
theorem convex_halfPlane_re_gt (σ₀ : ℝ) : Convex ℝ {z : ℂ | σ₀ < z.re} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_ofPred_eq, add_re, smul_re, smul_eq_mul] at hx hy ⊢
  rcases eq_or_lt_of_le ha with rfl | ha_pos
  · simp only [zero_mul, zero_add] at hab ⊢
    subst hab
    simpa using hy
  · have : a * σ₀ < a * x.re := mul_lt_mul_of_pos_left hx ha_pos
    have : b * σ₀ ≤ b * y.re := mul_le_mul_of_nonneg_left hy.le hb
    calc
      σ₀ = (a + b) * σ₀ := by rw [hab, one_mul]
      _ = a * σ₀ + b * σ₀ := add_mul a b σ₀
      _ < a * x.re + b * y.re := by linarith

/-- For every `s : ℂ` with `0 < s.re`, `1 - riemannZeta₀ s = s * mellin fractKernel (-s)`. -/
theorem one_sub_riemannZeta₀_eq_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    1 - riemannZeta₀ s = s * mellin fractKernel (-s) := by
  have hOpen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hPre : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfPlane_re_gt 0).isPreconnected
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
  exact hAn1.eqOn_of_preconnected_of_eventuallyEq hAn2 hPre (by norm_num : (2 : ℂ) ∈ _) hEv hs

/-- For every real `σ > 0`, `0 ≤ (mellin fractKernel (-σ)).re`. -/
theorem mellin_fractKernel_neg_re_nonneg {σ : ℝ} (hσ : 0 < σ) :
    0 ≤ (mellin fractKernel (-σ)).re := by
  have hm : MellinConvergent fractKernel (-σ) :=
    mellinConvergent_fractKernel (by simpa using hσ)
  unfold mellin
  change 0 ≤ RCLike.re (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (-(σ : ℂ) - 1) • fractKernel t)
  rw [← integral_re hm]
  refine setIntegral_nonneg measurableSet_Ioi fun t ht ↦ ?_
  change 0 ≤ ((t : ℂ) ^ (-(σ : ℂ) - 1) • fractKernel t).re
  unfold fractKernel
  by_cases ht1 : t ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem ht1, smul_eq_mul, ← ofReal_neg, ← ofReal_one, ← ofReal_sub,
      ← ofReal_cpow ht.le, ← ofReal_mul, ofReal_re]
    have ht0 : 0 ≤ t := ht.le
    obtain ⟨h0, _⟩ := sub_floor_bounds ht0
    positivity
  · rw [indicator_of_notMem ht1, smul_zero, zero_re]

/-- For every real `σ > 0`, `(riemannZeta₀ σ).re ≤ 1`. -/
theorem riemannZeta₀_re_le_one_of_pos {σ : ℝ} (hσ : 0 < σ) :
    (riemannZeta₀ (σ : ℂ)).re ≤ 1 := by
  have h := congrArg Complex.re
    (one_sub_riemannZeta₀_eq_of_re_pos (s := (σ : ℂ)) (by simpa using hσ))
  rw [sub_re, one_re, re_ofReal_mul] at h
  have hnonneg : 0 ≤ σ * (mellin fractKernel (-σ)).re :=
    mul_nonneg hσ.le (mellin_fractKernel_neg_re_nonneg hσ)
  linarith

/-- For every real `σ ∈ (0, 1)`, `(riemannZeta σ).re < 0`. -/
theorem riemannZeta_re_lt_zero_of_mem_Ioo {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    (riemannZeta (σ : ℂ)).re < 0 := by
  have hne : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1.ne
  rw [riemannZeta_eq_inv_sub_add hne, add_re]
  have hinv : (((σ : ℂ) - 1)⁻¹).re = (σ - 1)⁻¹ := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_inv, ofReal_re]
  rw [hinv]
  have h0 := riemannZeta₀_re_le_one_of_pos hσ0
  have hsub_neg : σ - 1 < 0 := by linarith
  have hdiv_neg : σ / (σ - 1) < 0 := div_neg_of_pos_of_neg hσ0 hsub_neg
  have hring : (σ - 1)⁻¹ + 1 = σ / (σ - 1) := by
    have : σ - 1 ≠ 0 := hsub_neg.ne
    field_simp
    ring
  linarith

/-- For every real `σ > 0`, `riemannZeta (σ : ℂ) ≠ 0`. -/
theorem riemannZeta_ofReal_ne_zero_of_pos {σ : ℝ} (hσ : 0 < σ) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  rcases le_or_gt 1 σ with hge1 | hlt1
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa using hge1)
  · intro hz
    have hre := riemannZeta_re_lt_zero_of_mem_Ioo hσ hlt1
    rw [hz, zero_re] at hre
    exact lt_irrefl 0 hre

/-!
## Part 2: Iterated Derivatives of Mellin Transforms & Landau–Tonelli Continuation
-/

/-- The `k`-th formal derivative of the Mellin transform of `g` on `(1, ∞)`, given by
`∫_{1}^{∞} (-1)^k g(t) (log t)^k t^{-(s + 1)} dt`. -/
noncomputable def mellinLogDeriv (g : ℝ → ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∫ t in Set.Ioi (1 : ℝ), (-1 : ℂ) ^ k * (g t * (Real.log t) ^ k : ℝ) * (t : ℂ) ^ (-(s + 1))

/-- For any `c : ℂ`, `t ↦ (t : ℂ) ^ c` is a.e. strongly measurable on `(1, ∞)`. -/
theorem aestronglyMeasurable_ofReal_cpow_const (c : ℂ) :
    AEStronglyMeasurable (fun t : ℝ ↦ (t : ℂ) ^ c) (volume.restrict (Set.Ioi (1 : ℝ))) := by
  refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioi
  exact (continuousAt_ofReal_cpow_const _ _ <|
    Or.inr (zero_lt_one.trans ht).ne').continuousWithinAt

/-- If `t ↦ g t * t ^ (-(σ + 1))` is integrable on `(1, ∞)` for some `σ`, then `g` is
a.e. strongly measurable on `(1, ∞)`. -/
theorem aestronglyMeasurable_of_integrableOn_mul_rpow {g : ℝ → ℝ} {σ : ℝ}
    (h : IntegrableOn (fun t : ℝ ↦ g t * t ^ (-(σ + 1))) (Set.Ioi 1)) :
    AEStronglyMeasurable g (volume.restrict (Set.Ioi (1 : ℝ))) := by
  have h1 : AEStronglyMeasurable
      (fun t : ℝ ↦ (g t * t ^ (-(σ + 1))) * t ^ (σ + 1))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    h.aestronglyMeasurable.mul (measurable_id.pow_const (σ + 1)).aestronglyMeasurable
  refine h1.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht_pos : 0 < t := zero_lt_one.trans ht
  rw [mul_assoc, ← Real.rpow_add ht_pos, neg_add_cancel, Real.rpow_zero, mul_one]

/-- Real integrability with `(Real.log t) ^ k` for `σ > σ₀`. -/
theorem integrableOn_mul_log_pow_rpow {g : ℝ → ℝ} {σ₀ : ℝ}
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ g t)
    (hInt : ∀ σ : ℝ, σ₀ < σ → IntegrableOn (fun t : ℝ ↦ g t * t ^ (-(σ + 1))) (Set.Ioi 1))
    (k : ℕ) {σ : ℝ} (hσ : σ₀ < σ) :
    IntegrableOn (fun t : ℝ ↦ g t * (Real.log t) ^ k * t ^ (-(σ + 1))) (Set.Ioi 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hInt σ hσ
  · let ε : ℝ := (σ - σ₀) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    let σ' : ℝ := σ - ε
    have hσ' : σ₀ < σ' := by dsimp [σ', ε]; linarith
    have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
    have hεk : 0 < ε / k := div_pos hε hk_pos
    have hg_meas : AEStronglyMeasurable g (volume.restrict (Set.Ioi (1 : ℝ))) :=
      aestronglyMeasurable_of_integrableOn_mul_rpow (hInt σ hσ)
    have h_meas : AEStronglyMeasurable
        (fun t : ℝ ↦ g t * (Real.log t) ^ k * t ^ (-(σ + 1)))
        (volume.restrict (Set.Ioi (1 : ℝ))) :=
      (hg_meas.mul (Real.measurable_log.pow_const k).aestronglyMeasurable).mul
        (measurable_id.pow_const (-(σ + 1))).aestronglyMeasurable
    refine ((hInt σ' hσ').const_mul ((k / ε) ^ k)).mono' h_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 ≤ t := ht.le
    have ht_pos : 0 < t := zero_lt_one.trans ht
    have hgt : 0 ≤ g t := hg_nonneg t ht1
    have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hrpow_nonneg : 0 ≤ t ^ (-(σ + 1)) := Real.rpow_nonneg ht_pos.le _
    rw [Real.norm_of_nonneg (by positivity)]
    have hlog_le : Real.log t ≤ (k / ε) * t ^ (ε / k) := by
      have h1 := Real.log_le_rpow_div ht_pos.le hεk
      rwa [div_div_eq_mul_div, mul_comm (t ^ (ε / k)), ← div_mul_eq_mul_div] at h1
    have hlog_pow_le : (Real.log t) ^ k ≤ (k / ε) ^ k * t ^ ε := by
      calc
        (Real.log t) ^ k ≤ ((k / ε) * t ^ (ε / k)) ^ k :=
          pow_le_pow_left₀ hlog_nonneg hlog_le k
        _ = (k / ε) ^ k * (t ^ (ε / k)) ^ k := mul_pow _ _ _
        _ = (k / ε) ^ k * t ^ ε := by
          rw [← Real.rpow_natCast (t ^ (ε / k)) k, ← Real.rpow_mul ht_pos.le,
            div_mul_cancel₀ _ hk_pos.ne']
    calc
      g t * (Real.log t) ^ k * t ^ (-(σ + 1))
        ≤ g t * ((k / ε) ^ k * t ^ ε) * t ^ (-(σ + 1)) := by
          gcongr
      _ = (k / ε) ^ k * (g t * (t ^ ε * t ^ (-(σ + 1)))) := by ring
      _ = (k / ε) ^ k * (g t * t ^ (-(σ' + 1))) := by
          rw [← Real.rpow_add ht_pos]
          congr 3
          dsimp [σ']
          ring

/-- Complex integrability with `(Real.log t) ^ k` for `σ₀ < s.re`. -/
theorem integrableOn_mul_log_pow_cpow {g : ℝ → ℝ} {σ₀ : ℝ}
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ g t)
    (hInt : ∀ σ : ℝ, σ₀ < σ → IntegrableOn (fun t : ℝ ↦ g t * t ^ (-(σ + 1))) (Set.Ioi 1))
    (k : ℕ) {s : ℂ} (hs : σ₀ < s.re) :
    IntegrableOn
      (fun t : ℝ ↦ (-1 : ℂ) ^ k * (g t * (Real.log t) ^ k : ℝ) * (t : ℂ) ^ (-(s + 1)))
      (Set.Ioi 1) := by
  have hg_meas : AEStronglyMeasurable g (volume.restrict (Set.Ioi (1 : ℝ))) :=
    aestronglyMeasurable_of_integrableOn_mul_rpow (hInt s.re hs)
  have h_meas : AEStronglyMeasurable
      (fun t : ℝ ↦ (-1 : ℂ) ^ k * (g t * (Real.log t) ^ k : ℝ) * (t : ℂ) ^ (-(s + 1)))
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    refine ((aestronglyMeasurable_const.mul ?_).mul (aestronglyMeasurable_ofReal_cpow_const _))
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hg_meas.mul (Real.measurable_log.pow_const k).aestronglyMeasurable)
  refine (integrableOn_mul_log_pow_rpow hg_nonneg hInt k hs).mono' h_meas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : 1 ≤ t := ht.le
  have ht_pos : 0 < t := zero_lt_one.trans ht
  have hgt : 0 ≤ g t := hg_nonneg t ht1
  have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht1
  rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
  have hre : (-(s + 1)).re = -(s.re + 1) := by
    simp only [neg_re, add_re, one_re]
  rw [hre]

/-- First derivative under the integral sign for `mellinLogDeriv g k`. -/
theorem hasDerivAt_mellinLogDeriv {g : ℝ → ℝ} {σ₀ : ℝ}
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ g t)
    (hInt : ∀ σ : ℝ, σ₀ < σ → IntegrableOn (fun t : ℝ ↦ g t * t ^ (-(σ + 1))) (Set.Ioi 1))
    (k : ℕ) {s₀ : ℂ} (hs₀ : σ₀ < s₀.re) :
    HasDerivAt (mellinLogDeriv g k) (mellinLogDeriv g (k + 1) s₀) s₀ := by
  let ε : ℝ := (s₀.re - σ₀) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let σ' : ℝ := s₀.re - ε
  have hσ' : σ₀ < σ' := by dsimp [σ', ε]; linarith
  have hg_meas : AEStronglyMeasurable g (volume.restrict (Set.Ioi (1 : ℝ))) :=
    aestronglyMeasurable_of_integrableOn_mul_rpow (hInt s₀.re hs₀)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball s₀ ε)
    (F := fun s t ↦ (-1 : ℂ) ^ k * (g t * (Real.log t) ^ k : ℝ) * (t : ℂ) ^ (-(s + 1)))
    (F' := fun s t ↦
      (-1 : ℂ) ^ (k + 1) * (g t * (Real.log t) ^ (k + 1) : ℝ) * (t : ℂ) ^ (-(s + 1)))
    (bound := fun t ↦ g t * (Real.log t) ^ (k + 1) * t ^ (-(σ' + 1)))
    (Metric.ball_mem_nhds s₀ hε) ?_ ?_ ?_ ?_ ?_ ?_).2
  · refine Eventually.of_forall fun s ↦ ?_
    refine ((aestronglyMeasurable_const.mul ?_).mul (aestronglyMeasurable_ofReal_cpow_const _))
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hg_meas.mul (Real.measurable_log.pow_const k).aestronglyMeasurable)
  · exact integrableOn_mul_log_pow_cpow hg_nonneg hInt k hs₀
  · exact (integrableOn_mul_log_pow_cpow hg_nonneg hInt (k + 1) hs₀).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s hs_ball
    have ht1 : 1 ≤ t := ht.le
    have ht_pos : 0 < t := zero_lt_one.trans ht
    have hgt : 0 ≤ g t := hg_nonneg t ht1
    have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hs_re : σ' ≤ s.re := by
      have hdist : ‖s - s₀‖ < ε := by simpa [dist_eq_norm] using Metric.mem_ball.mp hs_ball
      have hre_le : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
        simpa [sub_re] using Complex.abs_re_le_norm (s - s₀)
      have h1 : -(s.re - s₀.re) ≤ |s.re - s₀.re| := neg_le_abs _
      dsimp [σ']
      linarith
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Complex.norm_cpow_eq_rpow_re_of_pos ht_pos]
    have hre : (-(s + 1)).re = -(s.re + 1) := by
      simp only [neg_re, add_re, one_re]
    rw [hre]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  · exact integrableOn_mul_log_pow_rpow hg_nonneg hInt (k + 1) hσ'
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht s _
    have ht_pos : 0 < t := zero_lt_one.trans ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_pos.ne'
    have h_exp : HasDerivAt (fun z : ℂ ↦ -(z + 1)) (-1) s :=
      ((hasDerivAt_id s).add_const (1 : ℂ)).neg
    have h_cpow : HasDerivAt (fun z : ℂ ↦ (t : ℂ) ^ (-(z + 1)))
        ((t : ℂ) ^ (-(s + 1)) * Complex.log (t : ℂ) * (-1)) s :=
      h_exp.const_cpow (Or.inl ht0)
    have h_mul := h_cpow.const_mul ((-1 : ℂ) ^ k * (g t * (Real.log t) ^ k : ℝ))
    refine h_mul.congr_deriv ?_
    rw [← Complex.ofReal_log ht_pos.le]
    push_cast
    ring

/-- The `n`-th iterated derivative of `mellinLogDeriv g k` on `σ₀ < s.re` is
`mellinLogDeriv g (k + n)`. -/
theorem iteratedDeriv_mellinLogDeriv {g : ℝ → ℝ} {σ₀ : ℝ}
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ g t)
    (hInt : ∀ σ : ℝ, σ₀ < σ → IntegrableOn (fun t : ℝ ↦ g t * t ^ (-(σ + 1))) (Set.Ioi 1))
    (n : ℕ) (k : ℕ) {s : ℂ} (hs : σ₀ < s.re) :
    iteratedDeriv n (mellinLogDeriv g k) s = mellinLogDeriv g (k + n) s := by
  induction n generalizing k s with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have h_open : IsOpen {z : ℂ | σ₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h_ev : deriv (mellinLogDeriv g k) =ᶠ[𝓝 s] mellinLogDeriv g (k + 1) := by
      filter_upwards [h_open.mem_nhds hs] with z hz
      exact (hasDerivAt_mellinLogDeriv hg_nonneg hInt k hz).deriv
    rw [(h_ev.iteratedDeriv n).eq_of_nhds, ih (k + 1) hs, Nat.add_right_comm, Nat.add_assoc]

/-- For all `n : ℕ` and `s : ℂ` with `σ₀ < s.re`,
`iteratedDeriv n (mellinLogDeriv g 0) s = mellinLogDeriv g n s`. -/
theorem iteratedDeriv_mellinLogDeriv_zero {g : ℝ → ℝ} {σ₀ : ℝ}
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ g t)
    (hInt : ∀ σ : ℝ, σ₀ < σ → IntegrableOn (fun t : ℝ ↦ g t * t ^ (-(σ + 1))) (Set.Ioi 1))
    (n : ℕ) {s : ℂ} (hs : σ₀ < s.re) :
    iteratedDeriv n (mellinLogDeriv g 0) s = mellinLogDeriv g n s := by
  simpa using iteratedDeriv_mellinLogDeriv hg_nonneg hInt n 0 hs

/-- Real-axis evaluation of iterated derivatives of `mellinLogDeriv g 0`. -/
theorem neg_one_pow_mul_iteratedDeriv_mellinLogDeriv_zero_real {g : ℝ → ℝ} {σ₀ : ℝ}
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ g t)
    (hInt : ∀ σ : ℝ, σ₀ < σ → IntegrableOn (fun t : ℝ ↦ g t * t ^ (-(σ + 1))) (Set.Ioi 1))
    (n : ℕ) {c : ℝ} (hc : σ₀ < c) :
    (-1 : ℂ) ^ n * iteratedDeriv n (mellinLogDeriv g 0) (c : ℂ) =
      ((∫ t in Set.Ioi (1 : ℝ), g t * (Real.log t) ^ n * t ^ (-(c + 1)) : ℝ) : ℂ) := by
  have hc_re : σ₀ < (c : ℂ).re := by simpa using hc
  rw [iteratedDeriv_mellinLogDeriv_zero hg_nonneg hInt n hc_re, mellinLogDeriv,
    ← integral_const_mul]
  refine (setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_).trans integral_ofReal
  have ht_pos : 0 < t := zero_lt_one.trans ht
  have h_neg_one : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, ← mul_assoc, h_neg_one, one_mul, RCLike.ofReal_eq_complex_ofReal,
    Complex.ofReal_mul (g t * Real.log t ^ n), Complex.ofReal_cpow ht_pos.le]
  congr 2
  push_cast
  rfl

/-- Tonelli / Taylor step across `σ₀`: analyticity on `Metric.ball (c : ℂ) r` extends
integrability to `c - r < σ < c`. -/
theorem integrableOn_of_analyticAt_real {g : ℝ → ℝ} {σ₀ c r σ : ℝ} {F : ℂ → ℂ}
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ g t)
    (hInt : ∀ σ' : ℝ, σ₀ < σ' → IntegrableOn (fun t : ℝ ↦ g t * t ^ (-(σ' + 1))) (Set.Ioi 1))
    (hc : σ₀ < c) (_hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.ball (c : ℂ) r))
    (hEq : F =ᶠ[𝓝 (c : ℂ)] mellinLogDeriv g 0)
    (hσ_gt : c - r < σ) (hσ_lt : σ < c) :
    IntegrableOn (fun t : ℝ ↦ g t * t ^ (-(σ + 1))) (Set.Ioi 1) := by
  have hσ_mem : (σ : ℂ) ∈ Metric.ball (c : ℂ) r := by
    rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_neg (by linarith)]
    linarith
  have h_taylor := Complex.hasSum_taylorSeries_on_ball hF hσ_mem
  let I : ℕ → ℝ := fun n ↦ ∫ t in Set.Ioi (1 : ℝ), g t * (Real.log t) ^ n * t ^ (-(c + 1))
  let a : ℕ → ℝ := fun n ↦ (c - σ) ^ n / n ! * I n
  have h_term : ∀ n : ℕ,
      (n ! : ℂ)⁻¹ • ((σ : ℂ) - (c : ℂ)) ^ n • iteratedDeriv n F (c : ℂ) = ((a n : ℝ) : ℂ) := by
    intro n
    have h_iter : iteratedDeriv n F (c : ℂ) = iteratedDeriv n (mellinLogDeriv g 0) (c : ℂ) :=
      (hEq.iteratedDeriv n).eq_of_nhds
    have h_sub : ((σ : ℂ) - (c : ℂ)) ^ n = ((c - σ : ℝ) : ℂ) ^ n * (-1 : ℂ) ^ n := by
      rw [← mul_pow]
      congr 1
      push_cast
      ring
    rw [h_iter, smul_eq_mul, smul_eq_mul, h_sub]
    calc
      (n ! : ℂ)⁻¹ * (((c - σ : ℝ) : ℂ) ^ n * (-1 : ℂ) ^ n *
          iteratedDeriv n (mellinLogDeriv g 0) (c : ℂ))
        = (((c - σ : ℝ) : ℂ) ^ n / (n ! : ℂ)) *
            ((-1 : ℂ) ^ n * iteratedDeriv n (mellinLogDeriv g 0) (c : ℂ)) := by ring
      _ = (((c - σ) ^ n / n ! : ℝ) : ℂ) * ((I n : ℝ) : ℂ) := by
          rw [neg_one_pow_mul_iteratedDeriv_mellinLogDeriv_zero_real hg_nonneg hInt n hc]
          congr 1
          push_cast
          rfl
      _ = ((a n : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul]
  have h_hasSum_complex : HasSum (fun n : ℕ ↦ ((a n : ℝ) : ℂ)) (F (σ : ℂ)) := by
    simpa only [h_term] using h_taylor
  have h_hasSum_real : HasSum a (F (σ : ℂ)).re := by
    simpa using Complex.hasSum_re h_hasSum_complex
  have ha_summable : Summable a := h_hasSum_real.summable
  let μ := volume.restrict (Set.Ioi (1 : ℝ))
  let u : ℕ → ℝ → ℝ := fun n t ↦ (c - σ) ^ n / n ! * (g t * (Real.log t) ^ n * t ^ (-(c + 1)))
  have hc_sub_σ : 0 < c - σ := by linarith
  have hu_int : ∀ n : ℕ, Integrable (u n) μ := fun n ↦
    (integrableOn_mul_log_pow_rpow hg_nonneg hInt n hc).const_mul ((c - σ) ^ n / n !)
  have hu_nonneg : ∀ n : ℕ, ∀ t ∈ Set.Ioi (1 : ℝ), 0 ≤ u n t := by
    intro n t ht
    have ht1 : 1 ≤ t := ht.le
    have ht_pos : 0 < t := zero_lt_one.trans ht
    have hgt : 0 ≤ g t := hg_nonneg t ht1
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1
    dsimp [u]
    positivity
  have hu_ae_nonneg : ∀ n : ℕ, 0 ≤ᵐ[μ] u n := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hu_nonneg n t ht
  have ha_nonneg : ∀ n : ℕ, 0 ≤ a n := by
    intro n
    have hI_nonneg : 0 ≤ I n := by
      refine setIntegral_nonneg measurableSet_Ioi fun t ht ↦ ?_
      have ht1 : 1 ≤ t := ht.le
      have ht_pos : 0 < t := zero_lt_one.trans ht
      have hgt : 0 ≤ g t := hg_nonneg t ht1
      have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1
      positivity
    dsimp [a]
    positivity
  have h_lintegral_u : ∀ n : ℕ, ∫⁻ t, ENNReal.ofReal (u n t) ∂μ = ENNReal.ofReal (a n) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hu_int n) (hu_ae_nonneg n)]
    dsimp [u, a, I, μ]
    rw [integral_const_mul]
  have h_lintegral_tsum :
      (∫⁻ t, (∑' n : ℕ, ENNReal.ofReal (u n t)) ∂μ) = ENNReal.ofReal (∑' n : ℕ, a n) := by
    rw [MeasureTheory.lintegral_tsum
      (fun n ↦ (hu_int n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    simp_rw [h_lintegral_u]
    rw [← ENNReal.ofReal_tsum_of_nonneg ha_nonneg ha_summable]
  have h_pointwise : ∀ t ∈ Set.Ioi (1 : ℝ),
      (∑' n : ℕ, ENNReal.ofReal (u n t)) = ENNReal.ofReal (g t * t ^ (-(σ + 1))) := by
    intro t ht
    have ht_pos : 0 < t := zero_lt_one.trans ht
    let x : ℝ := (c - σ) * Real.log t
    have h_exp : HasSum (fun n : ℕ ↦ x ^ n / (n ! : ℝ)) (Real.exp x) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp x
    have h_mul := h_exp.mul_left (g t * t ^ (-(c + 1)))
    have h_u_eq : (fun n : ℕ ↦ u n t) =
        fun n : ℕ ↦ (g t * t ^ (-(c + 1))) * (x ^ n / (n ! : ℝ)) := by
      ext n
      dsimp [u, x]
      rw [mul_pow]
      ring
    have h_rhs_eq : (g t * t ^ (-(c + 1))) * Real.exp x = g t * t ^ (-(σ + 1)) := by
      dsimp [x]
      rw [mul_comm (c - σ) (Real.log t), ← Real.rpow_def_of_pos ht_pos, mul_assoc,
        ← Real.rpow_add ht_pos]
      congr 2
      ring
    rw [← h_u_eq, h_rhs_eq] at h_mul
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ hu_nonneg n t ht) h_mul.summable, h_mul.tsum_eq]
  have h_lintegral_eq :
      (∫⁻ t, ENNReal.ofReal (g t * t ^ (-(σ + 1))) ∂μ) = ENNReal.ofReal (∑' n : ℕ, a n) := by
    rw [← h_lintegral_tsum]
    exact setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ (h_pointwise t ht).symm
  have hg_meas : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_integrableOn_mul_rpow (hInt c hc)
  have h_meas : AEStronglyMeasurable (fun t : ℝ ↦ g t * t ^ (-(σ + 1))) μ :=
    hg_meas.mul (measurable_id.pow_const (-(σ + 1))).aestronglyMeasurable
  have h_nonneg_σ : 0 ≤ᵐ[μ] fun t : ℝ ↦ g t * t ^ (-(σ + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 ≤ t := ht.le
    have ht_pos : 0 < t := zero_lt_one.trans ht
    have hgt : 0 ≤ g t := hg_nonneg t ht1
    positivity
  refine ⟨h_meas, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal h_nonneg_σ, h_lintegral_eq]
  exact ENNReal.ofReal_lt_top

/-- Full half-plane integrability extension across `σ₀` for all `σ > c - r`. -/
theorem integrableOn_of_analyticAt_real_of_gt {g : ℝ → ℝ} {σ₀ c r σ : ℝ} {F : ℂ → ℂ}
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ g t)
    (hInt : ∀ σ' : ℝ, σ₀ < σ' → IntegrableOn (fun t : ℝ ↦ g t * t ^ (-(σ' + 1))) (Set.Ioi 1))
    (hc : σ₀ < c) (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (Metric.ball (c : ℂ) r))
    (hEq : F =ᶠ[𝓝 (c : ℂ)] mellinLogDeriv g 0)
    (hσ_gt : c - r < σ) :
    IntegrableOn (fun t : ℝ ↦ g t * t ^ (-(σ + 1))) (Set.Ioi 1) := by
  rcases lt_or_ge σ c with hσ_lt | hσ_ge
  · exact integrableOn_of_analyticAt_real hg_nonneg hInt hc hr hF hEq hσ_gt hσ_lt
  · exact hInt σ (hc.trans_le hσ_ge)

/-!
## Part 3: Zero Extraction, Chebyshev Mellin Identity, and Pole Analysis
-/

/-- Negating `RiemannHypothesis` yields a nontrivial zero `s` of `riemannZeta` off the critical
line `s.re = 1 / 2`. -/
theorem not_riemannHypothesis_iff_exists_zero :
    ¬ RiemannHypothesis ↔
      ∃ s : ℂ, riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1 ∧ s.re ≠ 1 / 2 := by
  unfold RiemannHypothesis
  push Not
  rfl

/-- If `s` is a nontrivial zero of `riemannZeta`, then `1 - s` is also a zero of `riemannZeta`. -/
theorem riemannZeta_one_sub_eq_zero_of_nontrivial_zero {s : ℂ}
    (hz : riemannZeta s = 0) (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) (hs1 : s ≠ 1) :
    riemannZeta (1 - s) = 0 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  have hGamma : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    rcases n with _ | m
    · apply hs0
      simpa using hn
    · apply htriv
      refine ⟨m, ?_⟩
      push_cast at hn ⊢
      rw [hn]
      ring
  have hcomp : completedRiemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hz
    exact hz.resolve_right hGamma
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  rw [riemannZeta_def_of_ne_zero h1s0, completedRiemannZeta_one_sub, hcomp, zero_div]

/-- Any nontrivial zero `s` of `riemannZeta` lies in the open critical strip `0 < s.re < 1`. -/
theorem mem_critical_strip_of_nontrivial_zero {s : ℂ}
    (hz : riemannZeta s = 0) (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) (hs1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 := by
  have hlt1 : s.re < 1 := by
    by_contra! hle
    exact riemannZeta_ne_zero_of_one_le_re hle hz
  have hgt0 : 0 < s.re := by
    by_contra! hle
    have h1s : 1 ≤ (1 - s).re := by
      simp only [sub_re, one_re]
      linarith
    exact riemannZeta_ne_zero_of_one_le_re h1s
      (riemannZeta_one_sub_eq_zero_of_nontrivial_zero hz htriv hs1)
  exact ⟨hgt0, hlt1⟩

/-- If `RiemannHypothesis` is false, there exists a zero `ρ` of `riemannZeta` in the
right half of the critical strip `1 / 2 < ρ.re < 1`. -/
theorem exists_zero_in_right_critical_strip_of_not_riemannHypothesis
    (hNotRH : ¬ RiemannHypothesis) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1 := by
  rw [not_riemannHypothesis_iff_exists_zero] at hNotRH
  obtain ⟨s, hz, htriv, hs1, hre⟩ := hNotRH
  obtain ⟨hgt0, hlt1⟩ := mem_critical_strip_of_nontrivial_zero hz htriv hs1
  rcases lt_or_gt_of_ne hre with hlt | hgt
  · refine ⟨1 - s, riemannZeta_one_sub_eq_zero_of_nontrivial_zero hz htriv hs1, ?_, ?_⟩
    · simp only [sub_re, one_re]
      linarith
    · simp only [sub_re, one_re]
      linarith
  · exact ⟨s, hz, hgt, hlt1⟩

/-- Chebyshev's `ψ(t)` equals the sum of `Λ k` over `k ∈ Icc 1 ⌊t⌋₊`. -/
theorem psi_eq_sum_Icc_one (t : ℝ) :
    Chebyshev.psi t = ∑ k ∈ Icc 1 ⌊t⌋₊, Λ k := by
  rw [Chebyshev.psi, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

/-- The partial sums `∑ k ∈ Icc 1 n, Λ k` are `O(n ^ (1 : ℝ))`. -/
theorem sum_vonMangoldt_isBigO_rpow_one :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, Λ k) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ) := by
  rw [isBigO_iff]
  refine ⟨Real.log 4 + 4, Eventually.of_forall fun n ↦ ?_⟩
  have hpsi : ∑ k ∈ Icc 1 n, Λ k = Chebyshev.psi n := by
    rw [psi_eq_sum_Icc_one, Nat.floor_natCast]
  rw [hpsi, Real.rpow_one, Real.norm_of_nonneg (Chebyshev.psi_nonneg _),
    Real.norm_of_nonneg (Nat.cast_nonneg n)]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)

/-- Mellin transform representation of `-ζ'(s) / ζ(s)` in terms of `Chebyshev.psi`
for `1 < s.re`. -/
theorem neg_deriv_riemannZeta_div_eq_mul_integral_psi {s : ℂ} (hs : 1 < s.re) :
    -deriv riemannZeta s / riemannZeta s =
      s * ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  have h := LSeries_eq_mul_integral_of_nonneg (fun n ↦ Λ n) zero_le_one hs
    sum_vonMangoldt_isBigO_rpow_one (fun n ↦ ArithmeticFunction.vonMangoldt_nonneg)
  refine h.trans ?_
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [psi_eq_sum_Icc_one, ofReal_sum]

/-- If `ψ(x) - x < √x * (1 + log x)^2` for all natural numbers `x > 253`,
then for all real `t ≥ 1`, `ψ(t) - t ≤ (ψ(253) + 1) * √t * (1 + log t)^2`. -/
theorem psi_sub_le_const_mul_sqrt_mul_one_add_log_sq_of_forall_nat
    (h : ∀ x : ℕ, 253 < x → Chebyshev.psi x - x < Real.sqrt x * (1 + Real.log x) ^ 2)
    {t : ℝ} (ht : 1 ≤ t) :
    Chebyshev.psi t - t ≤ (Chebyshev.psi 253 + 1) * Real.sqrt t * (1 + Real.log t) ^ 2 := by
  have ht0 : 0 ≤ t := by linarith
  have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht
  have hsqrt_ge_one : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht
  have hsq_ge_one : 1 ≤ (1 + Real.log t) ^ 2 := by nlinarith
  have hprod_ge_one : 1 ≤ Real.sqrt t * (1 + Real.log t) ^ 2 :=
    one_le_mul_of_one_le_of_one_le hsqrt_ge_one hsq_ge_one
  have hpsi253_nonneg : 0 ≤ Chebyshev.psi 253 := Chebyshev.psi_nonneg 253
  by_cases hfloor : 253 < ⌊t⌋₊
  · have h_nat := (h ⌊t⌋₊ hfloor).le
    have hfl_le : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0
    have hfl_pos : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast (by omega : 0 < ⌊t⌋₊)
    have hfl_one : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast (by omega : 1 ≤ ⌊t⌋₊)
    have hlog_fl_nonneg : 0 ≤ Real.log ⌊t⌋₊ := Real.log_nonneg hfl_one
    have hlog_mono : Real.log ⌊t⌋₊ ≤ Real.log t := Real.log_le_log hfl_pos hfl_le
    have hsq_mono : (1 + Real.log ⌊t⌋₊) ^ 2 ≤ (1 + Real.log t) ^ 2 := by
      nlinarith
    have hsqrt_mono : Real.sqrt ⌊t⌋₊ ≤ Real.sqrt t := Real.sqrt_le_sqrt hfl_le
    have hmul_mono :
        Real.sqrt ⌊t⌋₊ * (1 + Real.log ⌊t⌋₊) ^ 2 ≤ Real.sqrt t * (1 + Real.log t) ^ 2 :=
      mul_le_mul hsqrt_mono hsq_mono (by positivity) (by positivity)
    calc
      Chebyshev.psi t - t = Chebyshev.psi ⌊t⌋₊ - t := by
        rw [Chebyshev.psi_eq_psi_coe_floor]
      _ ≤ Chebyshev.psi ⌊t⌋₊ - ⌊t⌋₊ := by linarith
      _ ≤ Real.sqrt ⌊t⌋₊ * (1 + Real.log ⌊t⌋₊) ^ 2 := h_nat
      _ ≤ Real.sqrt t * (1 + Real.log t) ^ 2 := hmul_mono
      _ = 1 * (Real.sqrt t * (1 + Real.log t) ^ 2) := by ring
      _ ≤ (Chebyshev.psi 253 + 1) * (Real.sqrt t * (1 + Real.log t) ^ 2) := by
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (Chebyshev.psi 253 + 1) * Real.sqrt t * (1 + Real.log t) ^ 2 := by ring
  · push Not at hfloor
    have hfl_le : (⌊t⌋₊ : ℝ) ≤ 253 := by exact_mod_cast hfloor
    have hpsi_le : Chebyshev.psi t ≤ Chebyshev.psi 253 := by
      rw [Chebyshev.psi_eq_psi_coe_floor]
      exact Chebyshev.psi_mono hfl_le
    calc
      Chebyshev.psi t - t ≤ Chebyshev.psi 253 - 1 := by linarith
      _ ≤ Chebyshev.psi 253 + 1 := by linarith
      _ = (Chebyshev.psi 253 + 1) * 1 := by ring
      _ ≤ (Chebyshev.psi 253 + 1) * (Real.sqrt t * (1 + Real.log t) ^ 2) :=
        mul_le_mul_of_nonneg_left hprod_ge_one (by positivity)
      _ = (Chebyshev.psi 253 + 1) * Real.sqrt t * (1 + Real.log t) ^ 2 := by ring

/-- For any `α > 1 / 2`, if `ψ(x) - x < √x * (1 + log x)^2` for all `x > 253`,
there exists an explicit `C > 0` such that `ψ(t) - t ≤ C * t ^ α` for all `t ≥ 1`. -/
theorem exists_pos_const_psi_sub_le_rpow_of_forall_nat
    (h : ∀ x : ℕ, 253 < x → Chebyshev.psi x - x < Real.sqrt x * (1 + Real.log x) ^ 2)
    {α : ℝ} (hα : 1 / 2 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t → Chebyshev.psi t - t ≤ C * t ^ α := by
  set ε := (α - 1 / 2) / 2
  have hε : 0 < ε := by positivity
  refine ⟨(Chebyshev.psi 253 + 1) * (1 + 1 / ε) ^ 2, by positivity, fun t ht ↦ ?_⟩
  have ht0 : 0 ≤ t := by linarith
  have ht_pos : 0 < t := by linarith
  have h1 := psi_sub_le_const_mul_sqrt_mul_one_add_log_sq_of_forall_nat h ht
  have hlog : Real.log t ≤ t ^ ε / ε := Real.log_le_rpow_div ht0 hε
  have hrpow_ge_one : 1 ≤ t ^ ε := Real.one_le_rpow ht hε.le
  have h1log : 1 + Real.log t ≤ (1 + 1 / ε) * t ^ ε := by
    calc
      1 + Real.log t ≤ t ^ ε + t ^ ε / ε := add_le_add hrpow_ge_one hlog
      _ = (1 + 1 / ε) * t ^ ε := by ring
  have h1log_nonneg : 0 ≤ 1 + Real.log t := by
    have := Real.log_nonneg ht
    linarith
  have hsq : (1 + Real.log t) ^ 2 ≤ (1 + 1 / ε) ^ 2 * t ^ (α - 1 / 2) := by
    calc
      (1 + Real.log t) ^ 2 ≤ ((1 + 1 / ε) * t ^ ε) ^ 2 :=
        pow_le_pow_left₀ h1log_nonneg h1log 2
      _ = (1 + 1 / ε) ^ 2 * (t ^ ε) ^ (2 : ℕ) := by ring
      _ = (1 + 1 / ε) ^ 2 * t ^ (ε * 2) := by
        rw [← Real.rpow_natCast (t ^ ε) 2, ← Real.rpow_mul ht0]
        norm_num
      _ = (1 + 1 / ε) ^ 2 * t ^ (α - 1 / 2) := by
        congr 2
        ring
  calc
    Chebyshev.psi t - t
      ≤ (Chebyshev.psi 253 + 1) * Real.sqrt t * (1 + Real.log t) ^ 2 := h1
    _ ≤ (Chebyshev.psi 253 + 1) * Real.sqrt t * ((1 + 1 / ε) ^ 2 * t ^ (α - 1 / 2)) := by
      refine mul_le_mul_of_nonneg_left hsq ?_
      have := Chebyshev.psi_nonneg 253
      positivity
    _ = (Chebyshev.psi 253 + 1) * (1 + 1 / ε) ^ 2 * (t ^ (1 / 2 : ℝ) * t ^ (α - 1 / 2)) := by
      rw [Real.sqrt_eq_rpow]
      ring
    _ = (Chebyshev.psi 253 + 1) * (1 + 1 / ε) ^ 2 * t ^ α := by
      rw [← Real.rpow_add ht_pos]
      congr 2
      ring

/-- Integrability of `ψ(t) * t ^ (-(s + 1))` on `(1, ∞)` for `1 < s.re`. -/
theorem integrableOn_psi_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ ↦ (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  rw [← integrableOn_Ici_iff_integrableOn_Ioi]
  have hloc : LocallyIntegrableOn
      (fun t : ℝ ↦ (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ici 1) := by
    have hcongr : (fun t : ℝ ↦ (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1))) =
        (fun t : ℝ ↦ (t : ℂ) ^ (-(s + 1)) * ∑ k ∈ Icc 1 ⌊t⌋₊, (Λ k : ℂ)) := by
      ext t
      rw [psi_eq_sum_Icc_one, ofReal_sum, mul_comm]
    rw [hcongr]
    refine locallyIntegrableOn_mul_sum_Icc (fun k ↦ (Λ k : ℂ)) zero_le_one ?_
    refine ContinuousOn.locallyIntegrableOn (fun t ht ↦ ?_) measurableSet_Ici
    exact (continuousAt_ofReal_cpow_const _ _ <|
      Or.inr (zero_lt_one.trans_le ht).ne').continuousWithinAt
  refine hloc.integrableOn_of_isBigO_atTop (g := fun t : ℝ ↦ t ^ (-s.re)) ?_ ?_
  · rw [isBigO_iff]
    refine ⟨Real.log 4 + 4, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht_pos : 0 < t := zero_lt_one.trans_le ht
    rw [norm_mul, norm_real, Real.norm_of_nonneg (Chebyshev.psi_nonneg t),
      norm_cpow_eq_rpow_re_of_pos ht_pos, Real.norm_of_nonneg (Real.rpow_nonneg ht_pos.le _)]
    have hre : (-(s + 1)).re = -s.re - 1 := by
      simp only [neg_re, add_re, one_re]
      ring
    rw [hre]
    calc
      Chebyshev.psi t * t ^ (-s.re - 1)
        ≤ (Real.log 4 + 4) * t * t ^ (-s.re - 1) := by
          exact mul_le_mul_of_nonneg_right
            (Chebyshev.psi_le_const_mul_self ht_pos.le) (Real.rpow_nonneg ht_pos.le _)
      _ = (Real.log 4 + 4) * (t ^ (1 : ℝ) * t ^ (-s.re - 1)) := by
          rw [Real.rpow_one, mul_assoc]
      _ = (Real.log 4 + 4) * t ^ (-s.re) := by
          rw [← Real.rpow_add ht_pos]
          congr 2
          ring
  · exact integrableAtFilter_rpow_atTop_iff.mpr (by linarith)

/-- Integrability of `(t ^ α : ℂ) * t ^ (-(s + 1))` on `(1, ∞)` for `α < s.re`. -/
theorem integrableOn_rpow_mul_cpow {s : ℂ} {α : ℝ} (hα : α < s.re) :
    IntegrableOn (fun t : ℝ ↦ ((t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hlt : ((α : ℂ) - s - 1).re < -1 := by
    simp only [sub_re, ofReal_re, one_re]
    linarith
  refine (integrableOn_Ioi_cpow_of_lt hlt zero_lt_one).congr_fun (fun t ht ↦ ?_) measurableSet_Ioi
  have ht_pos : 0 < t := zero_lt_one.trans ht
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht_pos.ne'
  rw [ofReal_cpow ht_pos.le, ← cpow_add _ _ ht0, show (α : ℂ) + -(s + 1) = (α : ℂ) - s - 1 by ring]

/-- Mellin integral of `t ^ α` against `t ^ (-(s + 1))` on `(1, ∞)` for `α < s.re`. -/
theorem integral_Ioi_rpow_mul_cpow {s : ℂ} {α : ℝ} (hα : α < s.re) :
    ∫ t in Set.Ioi (1 : ℝ), ((t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) = 1 / (s - α) := by
  have hlt : ((α : ℂ) - s - 1).re < -1 := by
    simp only [sub_re, ofReal_re, one_re]
    linarith
  have hcongr :
      ∫ t in Set.Ioi (1 : ℝ), ((t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ ((α : ℂ) - s - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    have ht_pos : 0 < t := zero_lt_one.trans ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht_pos.ne'
    rw [ofReal_cpow ht_pos.le, ← cpow_add _ _ ht0,
      show (α : ℂ) + -(s + 1) = (α : ℂ) - s - 1 by ring]
  rw [hcongr, integral_Ioi_cpow_of_lt hlt zero_lt_one, ofReal_one, one_cpow,
    show (α : ℂ) - s - 1 + 1 = -(s - α) by ring, neg_div_neg_eq]

/-- Integrability of `t * t ^ (-(s + 1))` on `(1, ∞)` for `1 < s.re`. -/
theorem integrableOn_self_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  simpa [Real.rpow_one] using integrableOn_rpow_mul_cpow (α := 1) hs

/-- Mellin integral of `t` against `t ^ (-(s + 1))` on `(1, ∞)` for `1 < s.re`. -/
theorem integral_Ioi_self_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = 1 / (s - 1) := by
  simpa [Real.rpow_one] using integral_Ioi_rpow_mul_cpow (α := 1) hs

/-- Integrability of `((C * t ^ α + t - ψ(t) : ℝ) : ℂ) * t ^ (-(s + 1))` on `(1, ∞)` for
`1 < s.re` and `α < s.re`. -/
theorem integrableOn_const_rpow_add_self_sub_psi_mul_cpow {s : ℂ} {C α : ℝ}
    (hα : α < s.re) (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ ↦
      ((C * t ^ α + t - Chebyshev.psi t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hint_rpow :
      IntegrableOn (fun t : ℝ ↦ ((C * t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
    refine IntegrableOn.congr_fun ((integrableOn_rpow_mul_cpow hα).const_mul (C : ℂ))
      (fun t _ ↦ ?_) measurableSet_Ioi
    push_cast
    ring
  refine IntegrableOn.congr_fun
    ((hint_rpow.add (integrableOn_self_mul_cpow hs)).sub (integrableOn_psi_mul_cpow hs))
    (fun t _ ↦ ?_) measurableSet_Ioi
  simp only [Pi.sub_apply, Pi.add_apply]
  push_cast
  ring

/-- Mellin transform identity for the defect function `C * t ^ α + t - ψ(t)` on
`1 < s.re` with `α < s.re`. -/
theorem mellin_const_rpow_add_self_sub_psi {s : ℂ} {C α : ℝ} (hα : α < s.re) (hs : 1 < s.re) :
    (C : ℂ) / (s - α) + 1 / (s - 1) + deriv riemannZeta s / (s * riemannZeta s) =
      ∫ t in Set.Ioi (1 : ℝ),
        ((C * t ^ α + t - Chebyshev.psi t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hs0 : s ≠ 0 := ne_zero_of_one_lt_re hs
  have hpsi := neg_deriv_riemannZeta_div_eq_mul_integral_psi hs
  have hpsi_div :
      -deriv riemannZeta s / (s * riemannZeta s) =
        ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    calc
      -deriv riemannZeta s / (s * riemannZeta s)
        = (-deriv riemannZeta s / riemannZeta s) / s := by ring
      _ = (s * ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1))) / s := by
          rw [hpsi]
      _ = ∫ t in Set.Ioi (1 : ℝ), (Chebyshev.psi t : ℂ) * (t : ℂ) ^ (-(s + 1)) :=
          mul_div_cancel_left₀ _ hs0
  have hrpow :
      (C : ℂ) / (s - α) =
        ∫ t in Set.Ioi (1 : ℝ), ((C * t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    calc
      (C : ℂ) / (s - α)
        = (C : ℂ) * ∫ t in Set.Ioi (1 : ℝ), ((t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
          rw [integral_Ioi_rpow_mul_cpow hα, mul_one_div]
      _ = ∫ t in Set.Ioi (1 : ℝ), (C : ℂ) * (((t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) :=
          (integral_const_mul _ _).symm
      _ = ∫ t in Set.Ioi (1 : ℝ), ((C * t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
          push_cast
          ring
  have hself := (integral_Ioi_self_mul_cpow hs).symm
  have hint_rpow :
      IntegrableOn (fun t : ℝ ↦ ((C * t ^ α : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
    refine IntegrableOn.congr_fun ((integrableOn_rpow_mul_cpow hα).const_mul (C : ℂ))
      (fun t _ ↦ ?_) measurableSet_Ioi
    push_cast
    ring
  have hsub :
      (C : ℂ) / (s - α) + 1 / (s - 1) + deriv riemannZeta s / (s * riemannZeta s) =
        (C : ℂ) / (s - α) + 1 / (s - 1) - (-deriv riemannZeta s / (s * riemannZeta s)) := by
    ring
  rw [hsub, hrpow, hself, hpsi_div, ← integral_add hint_rpow (integrableOn_self_mul_cpow hs)]
  have hint_add :
      IntegrableOn (fun a : ℝ ↦ ((C * a ^ α : ℝ) : ℂ) * (a : ℂ) ^ (-(s + 1)) +
        (a : ℂ) * (a : ℂ) ^ (-(s + 1))) (Set.Ioi 1) :=
    hint_rpow.add (integrableOn_self_mul_cpow hs)
  rw [← integral_sub hint_add (integrableOn_psi_mul_cpow hs)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  push_cast
  ring

/-- The entire function `G(s) = (s - 1) * ζ(s)` (with removable singularity value `1`
at `s = 1`). -/
noncomputable def completedPoleZeta : ℂ → ℂ :=
  Function.update (fun s : ℂ ↦ (s - 1) * riemannZeta s) 1 1

@[simp]
theorem completedPoleZeta_one : completedPoleZeta 1 = 1 :=
  Function.update_self 1 1 _

theorem completedPoleZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    completedPoleZeta s = (s - 1) * riemannZeta s :=
  Function.update_of_ne hs 1 _

/-- `completedPoleZeta` is differentiable on all of `ℂ` (entire). -/
theorem differentiable_completedPoleZeta : Differentiable ℂ completedPoleZeta := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · refine ((differentiableAt_id.sub (differentiableAt_const 1)).mul
      (differentiableAt_riemannZeta hs)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_ne_nhds hs] with z hz using completedPoleZeta_of_ne_one hz
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with z hz
      refine ((differentiableAt_id.sub (differentiableAt_const 1)).mul
        (differentiableAt_riemannZeta hz)).congr_of_eventuallyEq ?_
      filter_upwards [eventually_ne_nhds hz] with w hw using completedPoleZeta_of_ne_one hw
    · rw [completedPoleZeta, continuousAt_update_same]
      exact riemannZeta_residue_one

/-- Away from `s = 1` and zeros of `riemannZeta`, the logarithmic derivative of
`completedPoleZeta` cancels the simple pole of `ζ'(s) / ζ(s)` at `s = 1`. -/
theorem deriv_completedPoleZeta_div_eq {s : ℂ} (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    deriv completedPoleZeta s / completedPoleZeta s =
      1 / (s - 1) + deriv riemannZeta s / riemannZeta s := by
  have heq : completedPoleZeta =ᶠ[𝓝 s] fun z ↦ (z - 1) * riemannZeta z := by
    filter_upwards [eventually_ne_nhds hs1] with z hz using completedPoleZeta_of_ne_one hz
  have hder : deriv completedPoleZeta s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
    rw [heq.deriv_eq]
    have hd : HasDerivAt (fun z : ℂ ↦ (z - 1) * riemannZeta z)
        (1 * riemannZeta s + (s - 1) * deriv riemannZeta s) s :=
      ((hasDerivAt_id s).sub_const (1 : ℂ)).mul (differentiableAt_riemannZeta hs1).hasDerivAt
    rw [hd.deriv, one_mul]
  rw [hder, completedPoleZeta_of_ne_one hs1]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp

/-- Pole-free expression for the Mellin transform of `C * t ^ α + t - ψ(t)` in terms of the entire
function `completedPoleZeta`, valid for all `s ≠ 0, 1` with `s ≠ α` and `riemannZeta s ≠ 0`. -/
theorem mellin_lhs_eq_completedPoleZeta {s : ℂ} {C α : ℝ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    (C : ℂ) / (s - α) + 1 / (s - 1) + deriv riemannZeta s / (s * riemannZeta s) =
      (C : ℂ) / (s - α) + 1 / s + deriv completedPoleZeta s / (s * completedPoleZeta s) := by
  have h1 : deriv completedPoleZeta s / (s * completedPoleZeta s) =
      (deriv completedPoleZeta s / completedPoleZeta s) / s := by ring
  rw [h1, deriv_completedPoleZeta_div_eq hs1 hz]
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

/-- The Riemann zeta function does not have infinite analytic order at any point `ρ ≠ 1`. -/
theorem analyticOrderAt_riemannZeta_ne_top {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  have hconn : IsConnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by simp) 1
  have h2 : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by simp
  have h2_ne_top : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr
      (Or.inr (riemannZeta_ne_zero_of_one_le_re (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re)))]
    exact ENat.zero_ne_top
  exact analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    hconn.isPreconnected h2 hρ1 h2_ne_top

/-- Any zero `ρ ≠ 1` of `riemannZeta` has finite positive vanishing order
`1 ≤ analyticOrderNatAt riemannZeta ρ`. -/
theorem one_le_analyticOrderNatAt_of_riemannZeta_eq_zero {ρ : ℂ} (hρ1 : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) :
    1 ≤ analyticOrderNatAt riemannZeta ρ := by
  have han : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 := han.analyticOrderAt_ne_zero.mpr hz
  have hnetop : analyticOrderAt riemannZeta ρ ≠ ⊤ := analyticOrderAt_riemannZeta_ne_top hρ1
  have hpos : 0 < analyticOrderNatAt riemannZeta ρ := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    apply hne0
    rw [← Nat.cast_analyticOrderNatAt hnetop, h0, Nat.cast_zero]
  omega

/-- At any zero `ρ ≠ 1` of `riemannZeta`, the logarithmic derivative `ζ'(z) / ζ(z)` has a simple
pole with positive integer residue `analyticOrderNatAt riemannZeta ρ ≥ 1`. -/
theorem tendsto_sub_mul_deriv_riemannZeta_div_of_eq_zero {ρ : ℂ} (hρ1 : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) :
    Tendsto (fun z : ℂ ↦ (z - ρ) * (deriv riemannZeta z / riemannZeta z))
      (𝓝[≠] ρ) (𝓝 (analyticOrderNatAt riemannZeta ρ : ℂ)) := by
  set m := analyticOrderNatAt riemannZeta ρ
  have hm : 1 ≤ m := one_le_analyticOrderNatAt_of_riemannZeta_eq_zero hρ1 hz
  have han : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  have hnetop : analyticOrderAt riemannZeta ρ ≠ ⊤ := analyticOrderAt_riemannZeta_ne_top hρ1
  obtain ⟨g, hga, hg0, hfg⟩ := han.analyticOrderAt_ne_top.mp hnetop
  simp only [smul_eq_mul] at hfg
  have hderiv : deriv riemannZeta =ᶠ[𝓝 ρ] deriv (fun z ↦ (z - ρ) ^ m * g z) := hfg.deriv
  have hg_ne : ∀ᶠ z in 𝓝 ρ, g z ≠ 0 := hga.continuousAt.eventually_ne hg0
  have hg_diff : ∀ᶠ z in 𝓝 ρ, DifferentiableAt ℂ g z :=
    hga.eventually_analyticAt.mono fun _ h ↦ h.differentiableAt
  have hcont : ContinuousAt (fun z : ℂ ↦ (m : ℂ) + (z - ρ) * (deriv g z / g z)) ρ :=
    continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul
      (hga.deriv.continuousAt.div hga.continuousAt hg0))
  have h_lim : Tendsto (fun z : ℂ ↦ (m : ℂ) + (z - ρ) * (deriv g z / g z))
      (𝓝 ρ) (𝓝 (m : ℂ)) := by
    simpa using hcont.tendsto
  refine (h_lim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [
    eventually_nhdsWithin_of_eventually_nhds (hfg.and (hderiv.and (hg_ne.and hg_diff))),
    self_mem_nhdsWithin] with z ⟨hz_eq, hz_der, hgz0, hgz_diff⟩ hz_ne
  have hsub0 : z - ρ ≠ 0 := sub_ne_zero.mpr hz_ne
  have hmul_der : deriv (fun w : ℂ ↦ (w - ρ) ^ m * g w) z =
      (m : ℂ) * (z - ρ) ^ (m - 1) * g z + (z - ρ) ^ m * deriv g z := by
    have hd : HasDerivAt (fun w : ℂ ↦ (w - ρ) ^ m * g w)
        (((m : ℂ) * (z - ρ) ^ (m - 1) * 1) * g z + (z - ρ) ^ m * deriv g z) z :=
      (((hasDerivAt_id z).sub_const ρ).pow m).mul hgz_diff.hasDerivAt
    rw [hd.deriv, mul_one]
  rw [hz_eq, hz_der, hmul_der]
  have hpow_split : (z - ρ) ^ m = (z - ρ) * (z - ρ) ^ (m - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hm, pow_succ']
  have hpow_ne : (z - ρ) ^ (m - 1) ≠ 0 := pow_ne_zero _ hsub0
  rw [hpow_split]
  field_simp

/-!
## Part 4: Landau–Schmidt Analytic Continuation & Final Contradiction
-/

/-- Nonvanishing of `completedPoleZeta` on the positive real axis `(0, ∞)`. -/
theorem completedPoleZeta_ofReal_ne_zero_of_pos {σ : ℝ} (hσ : 0 < σ) :
    completedPoleZeta (σ : ℂ) ≠ 0 := by
  rcases eq_or_ne σ 1 with rfl | hne
  · simp
  · have hne_c : (σ : ℂ) ≠ 1 := by exact_mod_cast hne
    rw [completedPoleZeta_of_ne_one hne_c]
    exact mul_ne_zero (sub_ne_zero.mpr hne_c) (riemannZeta_ofReal_ne_zero_of_pos hσ)

/-- The nonnegative defect function `g(t) = C * t ^ α + t - ψ(t)`. -/
noncomputable def psiDefect (C α : ℝ) (t : ℝ) : ℝ :=
  C * t ^ α + t - Chebyshev.psi t

/-- Real integrability of `psiDefect C α t * t ^ (-(σ + 1))` on `(1, ∞)` for `σ > 1` and `σ > α`. -/
theorem integrableOn_psiDefect_rpow_of_one_lt {C α σ : ℝ} (hα : α < σ) (hσ : 1 < σ) :
    IntegrableOn (fun t : ℝ ↦ psiDefect C α t * t ^ (-(σ + 1))) (Set.Ioi 1) := by
  have hα_c : α < (σ : ℂ).re := by simpa using hα
  have hσ_c : 1 < (σ : ℂ).re := by simpa using hσ
  have h_cpow := integrableOn_const_rpow_add_self_sub_psi_mul_cpow (C := C) hα_c hσ_c
  have h_re : IntegrableOn
      (fun t : ℝ ↦ (((C * t ^ α + t - Chebyshev.psi t : ℝ) : ℂ) *
        (t : ℂ) ^ (-((σ : ℂ) + 1))).re) (Set.Ioi 1) :=
    Complex.reCLM.integrable_comp h_cpow
  refine h_re.congr_fun (fun t ht ↦ ?_) measurableSet_Ioi
  have ht_pos : 0 < t := zero_lt_one.trans ht
  have h_exp : -((σ : ℂ) + 1) = ((-(σ + 1) : ℝ) : ℂ) := by push_cast; ring
  dsimp [psiDefect]
  rw [h_exp, ← Complex.ofReal_cpow ht_pos.le, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- For `1 < s.re` and `α < s.re`, `mellinLogDeriv (psiDefect C α) 0 s` equals the pole-free
formula in terms of `completedPoleZeta`. -/
theorem mellinLogDeriv_zero_psiDefect_eq_of_one_lt_re {C α : ℝ} {s : ℂ}
    (hα : α < s.re) (hs : 1 < s.re) :
    mellinLogDeriv (psiDefect C α) 0 s =
      (C : ℂ) / (s - α) + 1 / s + deriv completedPoleZeta s / (s * completedPoleZeta s) := by
  have hs0 : s ≠ 0 := ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by
    intro h
    subst h
    simp at hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  rw [← mellin_lhs_eq_completedPoleZeta hs0 hs1 hz, mellin_const_rpow_add_self_sub_psi hα hs,
    mellinLogDeriv]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  simp [psiDefect]

/-- Identity theorem on the right half-plane `{s : ℂ | σ₀ < s.re}` after clearing the denominator
`completedPoleZeta s`. -/
theorem completedPoleZeta_mul_mellinLogDeriv_zero_psiDefect_eq {C α σ₀ : ℝ}
    (hα0 : 0 < α) (hασ₀ : α ≤ σ₀) (hσ₀1 : σ₀ ≤ 1)
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ psiDefect C α t)
    (hInt : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ ↦ psiDefect C α t * t ^ (-(σ + 1))) (Set.Ioi 1))
    {s : ℂ} (hs : σ₀ < s.re) :
    completedPoleZeta s * mellinLogDeriv (psiDefect C α) 0 s =
      ((C : ℂ) / (s - α) + 1 / s) * completedPoleZeta s + deriv completedPoleZeta s / s := by
  let U : Set ℂ := {z : ℂ | σ₀ < z.re}
  have hOpen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hPre : IsPreconnected U := (convex_halfPlane_re_gt σ₀).isPreconnected
  let G_lhs : ℂ → ℂ := fun z ↦ completedPoleZeta z * mellinLogDeriv (psiDefect C α) 0 z
  let G_rhs : ℂ → ℂ := fun z ↦
    ((C : ℂ) / (z - α) + 1 / z) * completedPoleZeta z + deriv completedPoleZeta z / z
  have hAn_lhs : AnalyticOnNhd ℂ G_lhs U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hOpen
    exact (differentiable_completedPoleZeta z).differentiableWithinAt.mul
      (hasDerivAt_mellinLogDeriv hg_nonneg hInt 0 hz).differentiableAt.differentiableWithinAt
  have hAn_rhs : AnalyticOnNhd ℂ G_rhs U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hOpen
    have hz_re : σ₀ < z.re := hz
    have hz_sub_ne : z - (α : ℂ) ≠ 0 := by
      intro hsub
      have hre := congrArg Complex.re (sub_eq_zero.mp hsub)
      simp only [ofReal_re] at hre
      linarith
    have hz_ne : z ≠ 0 := by
      intro hz0
      have hre := congrArg Complex.re hz0
      simp only [zero_re] at hre
      linarith
    have hd1 : DifferentiableAt ℂ (fun w : ℂ ↦ (C : ℂ) / (w - α) + 1 / w) z :=
      ((differentiableAt_const (C : ℂ)).div
        (differentiableAt_id.sub (differentiableAt_const (α : ℂ))) hz_sub_ne).add
        ((differentiableAt_const (1 : ℂ)).div differentiableAt_id hz_ne)
    have hd2 : DifferentiableAt ℂ (fun w : ℂ ↦ deriv completedPoleZeta w / w) z :=
      (differentiable_completedPoleZeta.deriv z).div differentiableAt_id hz_ne
    exact ((hd1.mul (differentiable_completedPoleZeta z)).add hd2).differentiableWithinAt
  have h2_mem : (2 : ℂ) ∈ U := by
    simp only [U, Set.mem_ofPred_eq]
    have : (2 : ℂ).re = 2 := by norm_num
    linarith
  have hEv : G_lhs =ᶠ[𝓝 (2 : ℂ)] G_rhs := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz_re : 1 < z.re := hz
    have hα_z : α < z.re := by linarith
    have hz0 : z ≠ 0 := ne_zero_of_one_lt_re hz_re
    have hz1 : z ≠ 1 := by
      intro h
      subst h
      simp at hz_re
    have hG_ne : completedPoleZeta z ≠ 0 := by
      rw [completedPoleZeta_of_ne_one hz1]
      exact mul_ne_zero (sub_ne_zero.mpr hz1) (riemannZeta_ne_zero_of_one_le_re hz_re.le)
    dsimp [G_lhs, G_rhs]
    rw [mellinLogDeriv_zero_psiDefect_eq_of_one_lt_re hα_z hz_re]
    field_simp
  exact hAn_lhs.eqOn_of_preconnected_of_eventuallyEq hAn_rhs hPre h2_mem hEv hs

/-- Whenever `σ₀ < s.re` and `completedPoleZeta s ≠ 0`, `mellinLogDeriv (psiDefect C α) 0 s`
equals `(C : ℂ) / (s - α) + 1 / s + deriv completedPoleZeta s / (s * completedPoleZeta s)`. -/
theorem mellinLogDeriv_zero_psiDefect_eq_of_completedPoleZeta_ne_zero {C α σ₀ : ℝ}
    (hα0 : 0 < α) (hασ₀ : α ≤ σ₀) (hσ₀1 : σ₀ ≤ 1)
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ psiDefect C α t)
    (hInt : ∀ σ : ℝ, σ₀ < σ →
      IntegrableOn (fun t : ℝ ↦ psiDefect C α t * t ^ (-(σ + 1))) (Set.Ioi 1))
    {s : ℂ} (hs : σ₀ < s.re) (hG : completedPoleZeta s ≠ 0) :
    mellinLogDeriv (psiDefect C α) 0 s =
      (C : ℂ) / (s - α) + 1 / s + deriv completedPoleZeta s / (s * completedPoleZeta s) := by
  have h_cleared :=
    completedPoleZeta_mul_mellinLogDeriv_zero_psiDefect_eq hα0 hασ₀ hσ₀1 hg_nonneg hInt hs
  have hs0 : s ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp only [zero_re] at hre
    linarith
  calc
    mellinLogDeriv (psiDefect C α) 0 s
      = (completedPoleZeta s * mellinLogDeriv (psiDefect C α) 0 s) / completedPoleZeta s := by
        rw [mul_div_cancel_left₀ _ hG]
    _ = (((C : ℂ) / (s - α) + 1 / s) * completedPoleZeta s + deriv completedPoleZeta s / s) /
          completedPoleZeta s := by
        rw [h_cleared]
    _ = (C : ℂ) / (s - α) + 1 / s + deriv completedPoleZeta s / (s * completedPoleZeta s) := by
        field_simp

/-- **Key Landau Continuation Theorem**:
Because `completedPoleZeta (σ : ℂ) ≠ 0` for all real `σ > 0`, the abscissa of integrability of
`psiDefect C α t * t ^ (-(σ + 1))` extends all the way down to `α`: for every `σ > α`,
`t ↦ psiDefect C α t * t ^ (-(σ + 1))` is integrable on `(1, ∞)`. -/
theorem integrableOn_psiDefect_rpow_of_gt_alpha {C α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ psiDefect C α t) :
    ∀ σ : ℝ, α < σ → IntegrableOn (fun t : ℝ ↦ psiDefect C α t * t ^ (-(σ + 1))) (Set.Ioi 1) := by
  let S : Set ℝ := {σ₀ : ℝ | α ≤ σ₀ ∧
    ∀ σ : ℝ, σ₀ < σ → IntegrableOn (fun t : ℝ ↦ psiDefect C α t * t ^ (-(σ + 1))) (Set.Ioi 1)}
  have h1_mem : 1 ∈ S :=
    ⟨hα1.le, fun σ hσ ↦ integrableOn_psiDefect_rpow_of_one_lt (hα1.trans hσ) hσ⟩
  have hS_nonempty : S.Nonempty := ⟨1, h1_mem⟩
  have hS_bdd : BddBelow S := ⟨α, fun _ h ↦ h.1⟩
  let σ_star : ℝ := sInf S
  have hσ_star_ge : α ≤ σ_star := le_csInf hS_nonempty (fun _ h ↦ h.1)
  have hσ_star_le : σ_star ≤ 1 := csInf_le hS_bdd h1_mem
  have hσ_star_mem : σ_star ∈ S := by
    refine ⟨hσ_star_ge, fun σ hσ ↦ ?_⟩
    obtain ⟨σ₀, hσ₀_mem, hσ₀_lt⟩ := (csInf_lt_iff hS_bdd hS_nonempty).mp hσ
    exact hσ₀_mem.2 σ hσ₀_lt
  suffices h_eq : σ_star = α by
    intro σ hσ
    exact hσ_star_mem.2 σ (h_eq.symm ▸ hσ)
  by_contra h_ne
  have h_gt : α < σ_star := lt_of_le_of_ne hσ_star_ge (Ne.symm h_ne)
  have hσ_star_pos : 0 < σ_star := hα0.trans h_gt
  let F : ℂ → ℂ := fun s ↦
    (C : ℂ) / (s - α) + 1 / s + deriv completedPoleZeta s / (s * completedPoleZeta s)
  let W : Set ℂ := {s : ℂ | s - (α : ℂ) ≠ 0 ∧ s ≠ 0 ∧ completedPoleZeta s ≠ 0}
  have hW_open : IsOpen W := by
    refine IsOpen.inter (IsOpen.preimage (continuous_id.sub continuous_const) isOpen_ne) ?_
    exact IsOpen.inter isOpen_ne (isOpen_ne.preimage differentiable_completedPoleZeta.continuous)
  have hF_diff_W : DifferentiableOn ℂ F W := by
    intro s hs
    obtain ⟨hs_α, hs_0, hs_G⟩ := hs
    have hd1 : DifferentiableAt ℂ (fun w : ℂ ↦ (C : ℂ) / (w - α) + 1 / w) s :=
      ((differentiableAt_const (C : ℂ)).div
        (differentiableAt_id.sub (differentiableAt_const (α : ℂ))) hs_α).add
        ((differentiableAt_const (1 : ℂ)).div differentiableAt_id hs_0)
    have hd2 : DifferentiableAt ℂ
        (fun w : ℂ ↦ deriv completedPoleZeta w / (w * completedPoleZeta w)) s :=
      (differentiable_completedPoleZeta.deriv s).div
        (differentiableAt_id.mul (differentiable_completedPoleZeta s))
        (mul_ne_zero hs_0 hs_G)
    exact (hd1.add hd2).differentiableWithinAt
  have hz₀_mem : (σ_star : ℂ) ∈ W := by
    refine ⟨?_, ?_, completedPoleZeta_ofReal_ne_zero_of_pos hσ_star_pos⟩
    · intro hsub
      have hre := congrArg Complex.re (sub_eq_zero.mp hsub)
      simp only [ofReal_re] at hre
      linarith
    · exact Complex.ofReal_ne_zero.mpr hσ_star_pos.ne'
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.isOpen_iff.mp hW_open (σ_star : ℂ) hz₀_mem
  let r : ℝ := min (r₀ / 3) ((σ_star - α) / 2)
  have hr_pos : 0 < r := lt_min (by linarith) (by linarith)
  have hr_lt_r₀ : r ≤ r₀ / 3 := min_le_left _ _
  have hr_le_sub : r ≤ (σ_star - α) / 2 := min_le_right _ _
  let c : ℝ := σ_star + r / 2
  have hc_gt : σ_star < c := by dsimp [c]; linarith
  have hball_sub : Metric.ball (c : ℂ) r ⊆ W := by
    intro z hz
    apply hr₀_sub
    rw [Metric.mem_ball] at hz ⊢
    have hdist_c : dist (c : ℂ) (σ_star : ℂ) = r / 2 := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have : c - σ_star = r / 2 := by dsimp [c]; ring
      rw [this, abs_of_pos (by linarith)]
    calc
      dist z (σ_star : ℂ) ≤ dist z (c : ℂ) + dist (c : ℂ) (σ_star : ℂ) := dist_triangle _ _ _
      _ < r + r / 2 := by linarith
      _ < r₀ := by linarith
  have hF_ball : DifferentiableOn ℂ F (Metric.ball (c : ℂ) r) := hF_diff_W.mono hball_sub
  have hc_mem_W : (c : ℂ) ∈ W := hball_sub (Metric.mem_ball_self hr_pos)
  have hEq : F =ᶠ[𝓝 (c : ℂ)] mellinLogDeriv (psiDefect C α) 0 := by
    have h_nhds : W ∩ {z : ℂ | σ_star < z.re} ∈ 𝓝 (c : ℂ) :=
      Filter.inter_mem (hW_open.mem_nhds hc_mem_W)
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simpa using hc_gt))
    filter_upwards [h_nhds] with z ⟨hzW, hz_re⟩
    exact (mellinLogDeriv_zero_psiDefect_eq_of_completedPoleZeta_ne_zero
      hα0 hσ_star_ge hσ_star_le hg_nonneg hσ_star_mem.2 hz_re hzW.2.2).symm
  have h_ext_mem : σ_star - r / 2 ∈ S := by
    refine ⟨by linarith, fun σ hσ ↦ ?_⟩
    have hσ_gt : c - r < σ := by dsimp [c]; linarith
    exact integrableOn_of_analyticAt_real_of_gt hg_nonneg hσ_star_mem.2 hc_gt hr_pos
      hF_ball hEq hσ_gt
  have h_le := csInf_le hS_bdd h_ext_mem
  linarith

/-- **Main Theorem (Schmidt–Landau Oscillation Theorem for `ψ(x) - x`)**:
If the Riemann Hypothesis is false (`¬ RiemannHypothesis`), then there exists a natural number
`x > 253` such that `Real.sqrt x * (1 + Real.log x) ^ 2 ≤ Chebyshev.psi x - x`. -/
theorem not_riemannHypothesis_imp_exists_psi_sub_ge_sqrt_mul_one_add_log_sq
    (hNotRH : ¬ RiemannHypothesis) :
    ∃ x : ℕ, 253 < x ∧ Real.sqrt x * (1 + Real.log x) ^ 2 ≤ Chebyshev.psi x - x := by
  by_contra! h_no
  obtain ⟨ρ, hρ_zero, hρ_gt, hρ_lt⟩ :=
    exists_zero_in_right_critical_strip_of_not_riemannHypothesis hNotRH
  let α : ℝ := (1 / 2 + ρ.re) / 2
  have hα_gt_half : 1 / 2 < α := by dsimp [α]; linarith
  have hα_lt_ρ : α < ρ.re := by dsimp [α]; linarith
  have hα_lt_one : α < 1 := hα_lt_ρ.trans hρ_lt
  have hα_pos : 0 < α := by linarith
  obtain ⟨C, _hC_pos, h_bound⟩ :=
    exists_pos_const_psi_sub_le_rpow_of_forall_nat h_no hα_gt_half
  have hg_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ psiDefect C α t := by
    intro t ht
    dsimp [psiDefect]
    linarith [h_bound t ht]
  have hInt_α :
      ∀ σ : ℝ, α < σ → IntegrableOn (fun t : ℝ ↦ psiDefect C α t * t ^ (-(σ + 1))) (Set.Ioi 1) :=
    integrableOn_psiDefect_rpow_of_gt_alpha hα_pos hα_lt_one hg_nonneg
  have h_cont_mellin : ContinuousAt (mellinLogDeriv (psiDefect C α) 0) ρ :=
    (hasDerivAt_mellinLogDeriv hg_nonneg hInt_α 0 hα_lt_ρ).continuousAt
  have h_lhs_tendsto :
      Tendsto (fun z : ℂ ↦ (z - ρ) * mellinLogDeriv (psiDefect C α) 0 z) (𝓝[≠] ρ) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ ↦ (z - ρ) * mellinLogDeriv (psiDefect C α) 0 z) (𝓝 ρ)
        (𝓝 ((ρ - ρ) * mellinLogDeriv (psiDefect C α) 0 ρ)) :=
      (continuousAt_id.tendsto.sub tendsto_const_nhds).mul h_cont_mellin.tendsto
    rw [sub_self, zero_mul] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hρ1 : ρ ≠ 1 := by
    intro h1
    rw [h1, one_re] at hρ_lt
    exact lt_irrefl 1 hρ_lt
  have hρ0 : ρ ≠ 0 := by
    intro h0
    rw [h0, zero_re] at hρ_gt
    linarith
  set m := analyticOrderNatAt riemannZeta ρ
  have hm_ge_one : 1 ≤ m := one_le_analyticOrderNatAt_of_riemannZeta_eq_zero hρ1 hρ_zero
  have hm_ne_zero : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_res := tendsto_sub_mul_deriv_riemannZeta_div_of_eq_zero hρ1 hρ_zero
  have h_zeta_ne : ∀ᶠ z in 𝓝[≠] ρ, riemannZeta z ≠ 0 := by
    filter_upwards [h_res.eventually_ne hm_ne_zero] with z hz h_zero
    apply hz
    simp [h_zero]
  have h_open_nhds : ∀ᶠ z in 𝓝[≠] ρ, α < z.re ∧ z ≠ 1 ∧ z ≠ 0 := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    have h_α_ev : ∀ᶠ z in 𝓝 ρ, α < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hα_lt_ρ
    exact h_α_ev.and ((eventually_ne_nhds hρ1).and (eventually_ne_nhds hρ0))
  have h_congr :
      (fun z : ℂ ↦ (z - ρ) * mellinLogDeriv (psiDefect C α) 0 z) =ᶠ[𝓝[≠] ρ]
        fun z : ℂ ↦ (z - ρ) * ((C : ℂ) / (z - α) + 1 / (z - 1)) +
          ((z - ρ) * (deriv riemannZeta z / riemannZeta z)) / z := by
    filter_upwards [h_zeta_ne, h_open_nhds] with z hz_zeta ⟨hz_α, hz_1, hz_0⟩
    have hG_ne : completedPoleZeta z ≠ 0 := by
      rw [completedPoleZeta_of_ne_one hz_1]
      exact mul_ne_zero (sub_ne_zero.mpr hz_1) hz_zeta
    have h_mellin := mellinLogDeriv_zero_psiDefect_eq_of_completedPoleZeta_ne_zero
      hα_pos le_rfl hα_lt_one.le hg_nonneg hInt_α hz_α hG_ne
    rw [h_mellin, ← mellin_lhs_eq_completedPoleZeta hz_0 hz_1 hz_zeta]
    ring
  have h_ρ_sub_α : ρ - (α : ℂ) ≠ 0 := by
    intro hsub
    have hre := congrArg Complex.re (sub_eq_zero.mp hsub)
    simp only [ofReal_re] at hre
    linarith
  have h_ρ_sub_1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have h_first_tendsto :
      Tendsto (fun z : ℂ ↦ (z - ρ) * ((C : ℂ) / (z - α) + 1 / (z - 1))) (𝓝[≠] ρ) (𝓝 0) := by
    have h_inner : Tendsto (fun z : ℂ ↦ (C : ℂ) / (z - α) + 1 / (z - 1)) (𝓝 ρ)
        (𝓝 ((C : ℂ) / (ρ - α) + 1 / (ρ - 1))) :=
      (tendsto_const_nhds.div (continuousAt_id.tendsto.sub tendsto_const_nhds) h_ρ_sub_α).add
        (tendsto_const_nhds.div (continuousAt_id.tendsto.sub tendsto_const_nhds) h_ρ_sub_1)
    have h1 : Tendsto (fun z : ℂ ↦ (z - ρ) * ((C : ℂ) / (z - α) + 1 / (z - 1))) (𝓝 ρ)
        (𝓝 ((ρ - ρ) * ((C : ℂ) / (ρ - α) + 1 / (ρ - 1)))) :=
      (continuousAt_id.tendsto.sub tendsto_const_nhds).mul h_inner
    rw [sub_self, zero_mul] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have h_second_tendsto :
      Tendsto (fun z : ℂ ↦ ((z - ρ) * (deriv riemannZeta z / riemannZeta z)) / z)
        (𝓝[≠] ρ) (𝓝 ((m : ℂ) / ρ)) :=
    h_res.div (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds) hρ0
  have h_rhs_tendsto :
      Tendsto (fun z : ℂ ↦ (z - ρ) * ((C : ℂ) / (z - α) + 1 / (z - 1)) +
          ((z - ρ) * (deriv riemannZeta z / riemannZeta z)) / z)
        (𝓝[≠] ρ) (𝓝 ((m : ℂ) / ρ)) := by
    simpa using h_first_tendsto.add h_second_tendsto
  have h_lhs_tendsto' :
      Tendsto (fun z : ℂ ↦ (z - ρ) * mellinLogDeriv (psiDefect C α) 0 z)
        (𝓝[≠] ρ) (𝓝 ((m : ℂ) / ρ)) :=
    h_rhs_tendsto.congr' h_congr.symm
  have h_eq_lim : (0 : ℂ) = (m : ℂ) / ρ :=
    tendsto_nhds_unique h_lhs_tendsto h_lhs_tendsto'
  exact div_ne_zero hm_ne_zero hρ0 h_eq_lim.symm

end RiemannSchmidt

