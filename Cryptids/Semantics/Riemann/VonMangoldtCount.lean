/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Fourth-Order Euler–Maclaurin Zero-Free Region, Local Jensen Bounds, and Zero Counting

This file proves (with **zero `sorry`s**):

1. **Fourth-Order Euler–Maclaurin Identity (`quarticKernel`) and Zero-Free Region `|ρ.im| > 6`**:
   - Defines `quarticKernel t = (t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2` on `(1, ∞)`.
   - Proves a general Dirichlet–Mellin summation identity (`integral_floor_poly_mul_cpow_eq` and
     `integrableOn_floor_poly_mul_cpow`) for arbitrary degree-`m` power sums
     `∑ k ∈ Icc 1 n, a * k ^ m = P n`.
   - Proves the exact fourth-order identity valid for all `s : ℂ` with `0 < s.re` and `s ≠ 1`:
     $$\operatorname{mellin}\;\text{quarticKernel}\;(-(s + 3))
       = \frac{2}{(s - 1) s (s + 1)} - \frac{24}{s (s + 1) (s + 2) (s + 3)} \zeta(s).$$
   - Evaluates the exact real integral on `(1, 2]`:
     $$\int_1^2 (t - 1)^2 (2 - t)^2 t^{-9/2} \, dt
       = \frac{668 \sqrt{2} - 944}{105} \le \frac{1}{150}$$
     and bounds the tail on `(2, ∞)` by `1 / (448 * √2) ≤ 1 / 600`, yielding for `s.re = 1 / 2`:
     $$\|\operatorname{mellin}\;\text{quarticKernel}\;(-(s + 3))\| \le \frac{1}{120}.$$
   - Deduces that for every zero `ρ` of `riemannZeta` on the critical line `ρ.re = 1 / 2`:
     $$240 \le \|\rho - 1\| \cdot \|\rho\| \cdot \|\rho + 1\|, \qquad
       37 < \rho.\text{im}^2, \qquad 6 < |\rho.\text{im}|.$$
   - Consequently, under `RiemannHypothesis`, `nontrivialZetaZerosUpTo T = ∅` and
     `zeroCountingFunction T = 0` for all `T ≤ 6`.

2. **Local Jensen Multiplicity & Zero-Counting Bounds (`divisor riemannZeta₁`)**:
   - Proves that for every `c : ℂ`, `r : ℝ`, and `ρ ∈ closedBall c |r|` with `ρ ≠ 1`,
     `divisor riemannZeta₁ (closedBall c |r|) ρ = (analyticOrderNatAt riemannZeta ρ : ℤ)`.
   - Proves that under `RiemannHypothesis`, every zero `ρ` with `t - 1 / 2 ≤ ρ.im ≤ t + 1 / 2`
     lies in `closedBall (2 + t * I) (7 / 4)` (`r = 7 / 4 < R = 15 / 8 < 2`), giving an explicit
     Jensen upper bound on the sum of multiplicities of zeros in `[t - 1 / 2, t + 1 / 2]`.

3. **Low-Frequency Stieltjes Integration by Parts (`g(t) = 1 / t`) and Discharge of `h_low`**:
   - Proves that whenever `zeroCountingFunction t₀ = 0` (`0 < t₀ ≤ T`, e.g. `t₀ = 6` under
     `RiemannHypothesis`), Stieltjes integration by parts on `[t₀, T]` gives:
     $$\sum_{\rho \in \text{nontrivialZetaZerosUpTo } T} \frac{1}{|\rho.\text{im}|}
       = \frac{N(T)}{T} + \int_{t_0}^T \frac{N(t)}{t^2} \, dt.$$
   - Proves that if `zeroCountingFunction t ≤ a * t * Real.log t + C * t + D` on `[t₀, T]` with
     `0 ≤ D`, then the `± D / T` terms cancel, yielding:
     $$\sum_{\rho \in \text{nontrivialZetaZerosUpTo } T} \frac{1}{\|\rho\|}
       \le \frac{a}{2} (\log T)^2 + (a + C) \log T + C + \frac{D}{t_0}
           - \frac{a}{2} (\log t_0)^2 - C \log t_0.$$

4. **Global Multiplicity-Weighted Zero-Counting Bound (`N_w(t) ≤ (16 / 5) t log t + (11 / 5) t`)**:
   - Proves `weightedZeroCountingFunction_le_sixteen_fifths` and
     `zeroCountingFunction_le_sixteen_fifths` for all `6 ≤ t` under `RiemannHypothesis`.
-/

@[expose] public section

namespace ConjectureMachines.Riemann543.Semantics.VonMangoldtCount

open Complex Finset Filter MeasureTheory Set Asymptotics Metric MeromorphicOn
open scoped Real Topology ArithmeticFunction LSeries.notation

/-!
## Section 1: Fourth-Order Euler–Maclaurin Identity & Low-Lying Zero-Free Region `|ρ.im| > 6`
-/

/-- For `t ≥ 0`, `0 ≤ t - ⌊t⌋₊` and `t - ⌊t⌋₊ ≤ 1`. -/
theorem sub_floor_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t - (⌊t⌋₊ : ℝ) ∧ t - (⌊t⌋₊ : ℝ) ≤ 1 := by
  refine ⟨sub_nonneg.mpr (Nat.floor_le ht), ?_⟩
  linarith [Nat.lt_floor_add_one t]

/-- For `t ≥ 0`, `0 ≤ (t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2 ≤ 1 / 16`. -/
theorem quartic_floor_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ (t - (⌊t⌋₊ : ℝ)) ^ 2 * (1 - (t - (⌊t⌋₊ : ℝ))) ^ 2 ∧
      (t - (⌊t⌋₊ : ℝ)) ^ 2 * (1 - (t - (⌊t⌋₊ : ℝ))) ^ 2 ≤ 1 / 16 := by
  obtain ⟨h0, h1⟩ := sub_floor_bounds ht
  refine ⟨by positivity, ?_⟩
  set u := t - (⌊t⌋₊ : ℝ)
  have hu_nonneg : 0 ≤ u * (1 - u) := mul_nonneg h0 (sub_nonneg.mpr h1)
  have hu_le : u * (1 - u) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (u - 1 / 2)]
  calc
    u ^ 2 * (1 - u) ^ 2 = (u * (1 - u)) * (u * (1 - u)) := by ring
    _ ≤ (1 / 4) * (1 / 4) := mul_le_mul hu_le hu_le hu_nonneg (by positivity)
    _ = 1 / 16 := by norm_num

/-- The fourth-order Euler–Maclaurin kernel on `(1, ∞)`:
`quarticKernel t = (t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2` for `t > 1`, and `0` for `t ≤ 1`. -/
noncomputable def quarticKernel : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator
    (fun t : ℝ ↦ (((t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2 : ℝ) : ℂ))

/-- `‖quarticKernel t‖ ≤ 1 / 16` for all `t : ℝ`. -/
theorem norm_quarticKernel_le_one_sixteenth (t : ℝ) : ‖quarticKernel t‖ ≤ 1 / 16 := by
  unfold quarticKernel
  by_cases ht : t ∈ Ioi (1 : ℝ)
  · rw [indicator_of_mem ht, norm_real, Real.norm_eq_abs]
    have ht0 : 0 ≤ t := by linarith [mem_Ioi.mp ht]
    obtain ⟨h0, h1⟩ := quartic_floor_bounds ht0
    rw [abs_of_nonneg h0]
    exact h1
  · rw [indicator_of_notMem ht, norm_zero]
    norm_num

/-- `quarticKernel` is measurable. -/
theorem measurable_quarticKernel : Measurable quarticKernel := by
  unfold quarticKernel
  refine Measurable.indicator ?_ measurableSet_Ioi
  have hm : Measurable (fun t : ℝ ↦ t - (⌊t⌋₊ : ℝ)) :=
    measurable_id.sub (measurable_from_nat.comp Nat.measurable_floor)
  exact Complex.measurable_ofReal.comp
    ((hm.pow_const 2).mul ((measurable_const.sub hm).pow_const 2))

/-- `quarticKernel` is locally integrable on `Ioi 0`. -/
theorem locallyIntegrableOn_quarticKernel : LocallyIntegrableOn quarticKernel (Ioi 0) := by
  intro x _
  refine ⟨Metric.closedBall x 1, nhdsWithin_le_nhds (Metric.closedBall_mem_nhds x zero_lt_one), ?_⟩
  refine (integrableOn_const (C := (1 / 16 : ℝ))
    (hs := (isCompact_closedBall x 1).measure_lt_top.ne)).mono'
    measurable_quarticKernel.aestronglyMeasurable ?_
  exact Eventually.of_forall norm_quarticKernel_le_one_sixteenth

/-- `quarticKernel` is `O(t ^ (-(0 : ℝ)))` as `t → ∞`. -/
theorem isBigO_quarticKernel_atTop :
    quarticKernel =O[atTop] (fun t : ℝ ↦ t ^ (-(0 : ℝ))) := by
  refine IsBigO.of_bound (1 / 16) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t _
  simpa using norm_quarticKernel_le_one_sixteenth t

/-- `quarticKernel` vanishes on `Ioo 0 1`, so it is `O(t ^ (-b))` at `𝓝[>] 0` for every `b : ℝ`. -/
theorem isBigO_quarticKernel_nhdsGT_zero (b : ℝ) :
    quarticKernel =O[𝓝[>] 0] (fun t : ℝ ↦ t ^ (-b)) := by
  refine IsBigO.of_bound 0 ?_
  have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT zero_lt_one
  filter_upwards [hmem] with t ht
  have hnot : t ∉ Ioi (1 : ℝ) := notMem_Ioi.mpr ht.2.le
  simp [quarticKernel, indicator_of_notMem hnot]

/-- For every `z : ℂ` with `z.re < 0`, `MellinConvergent quarticKernel z` holds. -/
theorem mellinConvergent_quarticKernel {z : ℂ} (hz : z.re < 0) :
    MellinConvergent quarticKernel z :=
  mellinConvergent_of_isBigO_rpow locallyIntegrableOn_quarticKernel
    isBigO_quarticKernel_atTop hz (isBigO_quarticKernel_nhdsGT_zero (z.re - 1)) (by linarith)

/-- For every `z : ℂ` with `z.re < 0`, `mellin quarticKernel` is complex-differentiable at `z`. -/
theorem differentiableAt_mellin_quarticKernel {z : ℂ} (hz : z.re < 0) :
    DifferentiableAt ℂ (mellin quarticKernel) z :=
  mellin_differentiableAt_of_isBigO_rpow locallyIntegrableOn_quarticKernel
    isBigO_quarticKernel_atTop hz (isBigO_quarticKernel_nhdsGT_zero (z.re - 1)) (by linarith)

/-- Rewriting `mellin quarticKernel (-(s + 3))` as an integral over `Ioi 1`. -/
theorem mellin_quarticKernel_neg_add_three_eq (s : ℂ) :
    mellin quarticKernel (-(s + 3)) =
      ∫ t in Ioi (1 : ℝ),
        (((t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 4)) := by
  unfold mellin quarticKernel
  simp_rw [← indicator_smul]
  rw [setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [smul_eq_mul, mul_comm, show -(s + 3) - 1 = -(s + 4) by ring]

/-- General bound on power sums: for `0 ≤ a` and `m, n : ℕ`,
`0 ≤ ∑ k ∈ Icc 1 n, a * (k : ℝ) ^ m` and
`∑ k ∈ Icc 1 n, a * (k : ℝ) ^ m ≤ a * (n : ℝ) ^ (m + 1 : ℝ)`. -/
theorem sum_Icc_const_mul_pow_bounds {a : ℝ} (ha : 0 ≤ a) (m n : ℕ) :
    0 ≤ ∑ k ∈ Finset.Icc 1 n, a * (k : ℝ) ^ m ∧
      ∑ k ∈ Finset.Icc 1 n, a * (k : ℝ) ^ m ≤ a * (n : ℝ) ^ (m + 1 : ℝ) := by
  refine ⟨Finset.sum_nonneg fun k _ ↦ by positivity, ?_⟩
  have hle : ∑ k ∈ Finset.Icc 1 n, a * (k : ℝ) ^ m ≤
      ∑ _k ∈ Finset.Icc 1 n, a * (n : ℝ) ^ m := by
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hk).2
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg k) hkn m) ha
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hle
  have hrpow : (n : ℝ) * (a * (n : ℝ) ^ m) = a * (n : ℝ) ^ (m + 1 : ℝ) := by
    have h1 : (n : ℝ) ^ (m + 1 : ℝ) = (n : ℝ) ^ (m + 1 : ℕ) := by norm_cast
    rw [h1, pow_succ]
    ring
  linarith

/-- Shifting `LSeries` by `m : ℕ` for `a * k ^ m` yields `a * riemannZeta s` when `1 < s.re`. -/
theorem LSeries_const_mul_pow_add_nat_eq {s : ℂ} (hs : 1 < s.re) (a : ℝ) (m : ℕ) :
    LSeries (fun k : ℕ ↦ ((a * (k : ℝ) ^ m : ℝ) : ℂ)) (s + m) = (a : ℂ) * riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs, LSeries, LSeries, ← tsum_mul_left]
  refine tsum_congr fun k ↦ ?_
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · rw [LSeries.term_of_ne_zero hk, LSeries.term_of_ne_zero hk, Pi.one_apply]
    have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    rw [cpow_add _ _ hk0, cpow_natCast]
    have hpow0 : (k : ℂ) ^ m ≠ 0 := pow_ne_zero m hk0
    push_cast
    field_simp [hpow0]

/-- General `IntegrableOn` for floor power-sum polynomials `(P ⌊t⌋₊ : ℂ) * t ^ (-(s + m + 1))`
on `Ioi 1` when `1 < s.re`. -/
theorem integrableOn_floor_poly_mul_cpow {s : ℂ} (hs : 1 < s.re) {a : ℝ} (ha : 0 ≤ a)
    (m : ℕ) {P : ℕ → ℝ} (hP : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, a * (k : ℝ) ^ m = P n) :
    IntegrableOn (fun t : ℝ ↦ (P ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + m + 1))) (Ioi (1 : ℝ)) := by
  have hrpow : IntegrableOn (fun t : ℝ ↦ a * t ^ (-s.re)) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul a
  refine hrpow.mono' ?_ ?_
  · refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.measurable_ofReal.comp
        (measurable_from_nat.comp Nat.measurable_floor)).aestronglyMeasurable
    · refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).aestronglyMeasurable
        measurableSet_Ioi
      exact continuousAt_ofReal_cpow_const _ _ (Or.inr (zero_lt_one.trans ht).ne')
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := zero_lt_one.trans ht
    obtain ⟨h0, h1⟩ := sum_Icc_const_mul_pow_bounds ha m ⌊t⌋₊
    rw [hP ⌊t⌋₊] at h0 h1
    rw [norm_mul, norm_real, Real.norm_of_nonneg h0, norm_cpow_eq_rpow_re_of_pos ht_pos]
    have hre : (-(s + (m : ℂ) + 1)).re = -s.re - (m + 1 : ℝ) := by simp; ring
    rw [hre]
    have hfloor_le : (⌊t⌋₊ : ℝ) ^ (m + 1 : ℝ) ≤ t ^ (m + 1 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le ht_pos.le) (by positivity)
    calc
      P ⌊t⌋₊ * t ^ (-s.re - (m + 1 : ℝ))
        ≤ a * (⌊t⌋₊ : ℝ) ^ (m + 1 : ℝ) * t ^ (-s.re - (m + 1 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht_pos.le _)
      _ ≤ a * t ^ (m + 1 : ℝ) * t ^ (-s.re - (m + 1 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfloor_le ha)
            (Real.rpow_nonneg ht_pos.le _)
      _ = a * (t ^ (m + 1 : ℝ) * t ^ (-s.re - (m + 1 : ℝ))) := by ring
      _ = a * t ^ (-s.re) := by
          rw [← Real.rpow_add ht_pos]
          ring_nf

/-- General Mellin–Dirichlet evaluation for floor power-sum polynomials:
for `1 < s.re`, `∫ t in Ioi 1, (P ⌊t⌋₊ : ℂ) * t ^ (-(s + m + 1)) = a * riemannZeta s / (s + m)`. -/
theorem integral_floor_poly_mul_cpow_eq {s : ℂ} (hs : 1 < s.re) {a : ℝ} (ha : 0 ≤ a)
    (m : ℕ) {P : ℕ → ℝ} (hP : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, a * (k : ℝ) ^ m = P n) :
    ∫ t in Ioi (1 : ℝ), (P ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + m + 1)) =
      (a : ℂ) * riemannZeta s / (s + m) := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, a * (k : ℝ) ^ m) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ (m + 1 : ℝ) := by
    refine IsBigO.of_bound a ?_
    filter_upwards [eventually_ge_atTop 0] with n _
    obtain ⟨h0, h1⟩ := sum_Icc_const_mul_pow_bounds ha m n
    rw [Real.norm_of_nonneg h0,
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
    exact h1
  have hs_add : (m + 1 : ℝ) < (s + m).re := by simp; linarith
  have h := LSeries_eq_mul_integral_of_nonneg (fun k : ℕ ↦ a * (k : ℝ) ^ m)
    (by positivity : (0 : ℝ) ≤ m + 1) hs_add hO (fun k ↦ by positivity)
  rw [LSeries_const_mul_pow_add_nat_eq hs a m] at h
  have hsm_ne : s + (m : ℂ) ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have h_int_congr :
      (∫ t in Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (a * (k : ℝ) ^ m : ℝ) : ℂ) *
        (t : ℂ) ^ (-(s + (m : ℂ) + 1))) =
      ∫ t in Ioi (1 : ℝ), (P ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + (m : ℂ) + 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    rw [← ofReal_sum, hP ⌊t⌋₊]
  rw [← h_int_congr, h, mul_div_cancel_left₀ _ hsm_ne]

theorem sum_Icc_pow_zero (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) * (k : ℝ) ^ 0 = (n : ℝ) := by
  simp

theorem sum_Icc_two_mul_pow_one (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (2 : ℝ) * (k : ℝ) ^ 1 = (n : ℝ) * ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    push_cast
    ring

theorem sum_Icc_six_mul_pow_two (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (6 : ℝ) * (k : ℝ) ^ 2 =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    push_cast
    ring

theorem sum_Icc_four_mul_pow_three (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, (4 : ℝ) * (k : ℝ) ^ 3 =
      (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    push_cast
    ring

/-- For `0 < z.re`, `∫ t in Ioi 1, (t : ℂ) ^ (-(z + 1)) = 1 / z`. -/
theorem integral_Ioi_one_cpow_neg_add_one {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-(z + 1)) = 1 / z := by
  have hlt : (-(z + 1)).re < -1 := by simp only [neg_re, add_re, one_re]; linarith
  rw [integral_Ioi_cpow_of_lt hlt zero_lt_one]
  have h1 : -(z + 1) + 1 = -z := by ring
  rw [ofReal_one, one_cpow, h1, div_neg, neg_div, neg_neg]

/-- **Fourth-Order Euler–Maclaurin Identity for `mellin quarticKernel (-(s + 3))` on `1 < s.re`**:
For every `s : ℂ` with `1 < s.re`,
$$\operatorname{mellin}\;\text{quarticKernel}\;(-(s + 3))
  = \frac{2}{(s - 1) s (s + 1)} - \frac{24}{s (s + 1) (s + 2) (s + 3)} \zeta(s).$$ -/
theorem mellin_quarticKernel_neg_add_three_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    mellin quarticKernel (-(s + 3)) =
      2 / ((s - 1) * s * (s + 1)) -
        24 / (s * (s + 1) * (s + 2) * (s + 3)) * riemannZeta s := by
  let g0 : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-s)
  let g1 : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-(s + 1))
  let g2 : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (-(s + 2))
  let p0 : ℝ → ℂ := fun t ↦ ((⌊t⌋₊ : ℝ) : ℂ) * (t : ℂ) ^ (-(s + (0 : ℕ) + 1))
  let p1 : ℝ → ℂ := fun t ↦ (((⌊t⌋₊ : ℝ) * ((⌊t⌋₊ : ℝ) + 1) : ℝ) : ℂ) *
    (t : ℂ) ^ (-(s + (1 : ℕ) + 1))
  let p2 : ℝ → ℂ := fun t ↦ (((⌊t⌋₊ : ℝ) * ((⌊t⌋₊ : ℝ) + 1) * (2 * (⌊t⌋₊ : ℝ) + 1) : ℝ) : ℂ) *
    (t : ℂ) ^ (-(s + (2 : ℕ) + 1))
  let p3 : ℝ → ℂ := fun t ↦ (((⌊t⌋₊ : ℝ) ^ 2 * ((⌊t⌋₊ : ℝ) + 1) ^ 2 : ℝ) : ℂ) *
    (t : ℂ) ^ (-(s + (3 : ℕ) + 1))
  have hint_g0 : IntegrableOn g0 (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hint_g1 : IntegrableOn g1 (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hint_g2 : IntegrableOn g2 (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hint_p0 : IntegrableOn p0 (Ioi (1 : ℝ)) :=
    integrableOn_floor_poly_mul_cpow hs zero_le_one 0 sum_Icc_pow_zero
  have hint_p1 : IntegrableOn p1 (Ioi (1 : ℝ)) :=
    integrableOn_floor_poly_mul_cpow hs (by norm_num) 1 sum_Icc_two_mul_pow_one
  have hint_p2 : IntegrableOn p2 (Ioi (1 : ℝ)) :=
    integrableOn_floor_poly_mul_cpow hs (by norm_num) 2 sum_Icc_six_mul_pow_two
  have hint_p3 : IntegrableOn p3 (Ioi (1 : ℝ)) :=
    integrableOn_floor_poly_mul_cpow hs (by norm_num) 3 sum_Icc_four_mul_pow_three
  have hcongr : EqOn
      (fun t : ℝ ↦ (((t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 4)))
      (fun t : ℝ ↦ g0 t - 2 * g1 t + g2 t - 4 * p0 t + 6 * p1 t - 2 * p2 t + p3 t)
      (Ioi (1 : ℝ)) := by
    intro t ht
    dsimp only [g0, g1, g2, p0, p1, p2, p3]
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
    have hp0 : (t : ℂ) ^ (-s) = (t : ℂ) ^ (4 : ℕ) * (t : ℂ) ^ (-(s + 4)) := by
      rw [← cpow_natCast, ← cpow_add _ _ ht0]
      ring_nf
    have hp1 : (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (3 : ℕ) * (t : ℂ) ^ (-(s + 4)) := by
      rw [← cpow_natCast, ← cpow_add _ _ ht0]
      ring_nf
    have hp2 : (t : ℂ) ^ (-(s + 2)) = (t : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (-(s + 4)) := by
      rw [← cpow_natCast, ← cpow_add _ _ ht0]
      ring_nf
    have hp3 : (t : ℂ) ^ (-(s + (2 : ℕ) + 1)) = (t : ℂ) * (t : ℂ) ^ (-(s + 4)) := by
      rw [show (t : ℂ) * (t : ℂ) ^ (-(s + 4)) = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 4)) by
        rw [cpow_one], ← cpow_add _ _ ht0]
      push_cast
      ring_nf
    have hp0' : (t : ℂ) ^ (-(s + (0 : ℕ) + 1)) = (t : ℂ) ^ (3 : ℕ) * (t : ℂ) ^ (-(s + 4)) := by
      rw [← cpow_natCast, ← cpow_add _ _ ht0]
      push_cast
      ring_nf
    have hp1' : (t : ℂ) ^ (-(s + (1 : ℕ) + 1)) = (t : ℂ) ^ (2 : ℕ) * (t : ℂ) ^ (-(s + 4)) := by
      rw [← cpow_natCast, ← cpow_add _ _ ht0]
      push_cast
      ring_nf
    have hp3' : (t : ℂ) ^ (-(s + (3 : ℕ) + 1)) = (t : ℂ) ^ (-(s + 4)) := by
      push_cast
      ring_nf
    rw [hp0, hp1, hp2, hp0', hp1', hp3, hp3']
    push_cast
    ring
  rw [mellin_quarticKernel_neg_add_three_eq, setIntegral_congr_fun measurableSet_Ioi hcongr]
  have h1 : IntegrableOn (fun x ↦ g0 x - 2 * g1 x) (Ioi (1 : ℝ)) :=
    hint_g0.sub (hint_g1.const_mul 2)
  have h2 : IntegrableOn (fun x ↦ g0 x - 2 * g1 x + g2 x) (Ioi (1 : ℝ)) :=
    h1.add hint_g2
  have h3 : IntegrableOn (fun x ↦ g0 x - 2 * g1 x + g2 x - 4 * p0 x) (Ioi (1 : ℝ)) :=
    h2.sub (hint_p0.const_mul 4)
  have h4 : IntegrableOn (fun x ↦ g0 x - 2 * g1 x + g2 x - 4 * p0 x + 6 * p1 x) (Ioi (1 : ℝ)) :=
    h3.add (hint_p1.const_mul 6)
  have h5 : IntegrableOn (fun x ↦ g0 x - 2 * g1 x + g2 x - 4 * p0 x + 6 * p1 x - 2 * p2 x)
      (Ioi (1 : ℝ)) :=
    h4.sub (hint_p2.const_mul 2)
  rw [integral_add h5 hint_p3,
    integral_sub h4 (hint_p2.const_mul 2),
    integral_add h3 (hint_p1.const_mul 6),
    integral_sub h2 (hint_p0.const_mul 4),
    integral_add h1 hint_g2,
    integral_sub hint_g0 (hint_g1.const_mul 2),
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  have hg0_eq : ∫ t in Ioi (1 : ℝ), g0 t = 1 / (s - 1) := by
    dsimp only [g0]
    have h := integral_Ioi_one_cpow_neg_add_one (z := s - 1) (by simp; linarith)
    simpa [sub_add_cancel] using h
  have hg1_eq : ∫ t in Ioi (1 : ℝ), g1 t = 1 / s :=
    integral_Ioi_one_cpow_neg_add_one (by linarith)
  have hg2_eq : ∫ t in Ioi (1 : ℝ), g2 t = 1 / (s + 1) := by
    dsimp only [g2]
    have h := integral_Ioi_one_cpow_neg_add_one (z := s + 1)
      (by simp only [add_re, one_re]; linarith)
    simpa [show s + 1 + 1 = s + 2 by ring] using h
  have hp0_eq := integral_floor_poly_mul_cpow_eq hs zero_le_one 0 sum_Icc_pow_zero
  have hp1_eq := integral_floor_poly_mul_cpow_eq hs (by norm_num) 1 sum_Icc_two_mul_pow_one
  have hp2_eq := integral_floor_poly_mul_cpow_eq hs (by norm_num) 2 sum_Icc_six_mul_pow_two
  have hp3_eq := integral_floor_poly_mul_cpow_eq hs (by norm_num) 3 sum_Icc_four_mul_pow_three
  change _ = _
  rw [hg0_eq, hg1_eq, hg2_eq, hp0_eq, hp1_eq, hp2_eq, hp3_eq]
  have hs1_ne : s - 1 ≠ 0 := sub_ne_zero.mpr (by
    intro h; have := congrArg Complex.re h; norm_num at this; linarith)
  have hs0_ne : s ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num at this; linarith
  have hsa1_ne : s + 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num [Complex.add_re] at this; linarith
  have hsa2_ne : s + 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num [Complex.add_re] at this; linarith
  have hsa3_ne : s + 3 ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num [Complex.add_re] at this; linarith
  push_cast
  field_simp [hs1_ne, hs0_ne, hsa1_ne, hsa2_ne, hsa3_ne]
  ring

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

/-- **Analytic Continuation of the Fourth-Order Euler–Maclaurin Identity to `0 < s.re`**:
For every `s : ℂ` with `0 < s.re` and `s ≠ 1`,
$$(s - 1) \operatorname{mellin}\;\text{quarticKernel}\;(-(s + 3))
  = \frac{2}{s (s + 1)} - \frac{24}{s (s + 1) (s + 2) (s + 3)} \text{riemannZeta}_1(s).$$ -/
theorem sub_one_mul_mellin_quarticKernel_eq_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    (s - 1) * mellin quarticKernel (-(s + 3)) =
      2 / (s * (s + 1)) -
        24 / (s * (s + 1) * (s + 2) * (s + 3)) * riemannZeta₁ s := by
  have hOpen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hAn1 : AnalyticOnNhd ℂ (fun z : ℂ ↦ (z - 1) * mellin quarticKernel (-(z + 3)))
      {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hOpen
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.mul ?_ ?_)
    · exact differentiableAt_id.sub_const 1
    · exact (differentiableAt_mellin_quarticKernel
        (by simp only [neg_re, add_re]; norm_num; linarith [show 0 < z.re from hz])).comp z
        (differentiableAt_id.add_const 3).neg
  have hAn2 : AnalyticOnNhd ℂ
      (fun z : ℂ ↦ 2 / (z * (z + 1)) -
        24 / (z * (z + 1) * (z + 2) * (z + 3)) * riemannZeta₁ z)
      {z : ℂ | 0 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hOpen
    have hz0 : z ≠ 0 := by intro h; subst h; simp at hz
    have hz1 : z + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h
      norm_num [Complex.add_re] at this; linarith [show 0 < z.re from hz]
    have hz2 : z + 2 ≠ 0 := by
      intro h; have := congrArg Complex.re h
      norm_num [Complex.add_re] at this; linarith [show 0 < z.re from hz]
    have hz3 : z + 3 ≠ 0 := by
      intro h; have := congrArg Complex.re h
      norm_num [Complex.add_re] at this; linarith [show 0 < z.re from hz]
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.sub ?_ ?_)
    · exact (differentiableAt_const 2).div
        (differentiableAt_id.mul (differentiableAt_id.add_const 1)) (mul_ne_zero hz0 hz1)
    · refine DifferentiableAt.mul ?_ (differentiable_riemannZeta₁ z)
      exact (differentiableAt_const 24).div
        (((differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul
          (differentiableAt_id.add_const 2)).mul (differentiableAt_id.add_const 3))
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hz0 hz1) hz2) hz3)
  have hEv : (fun z : ℂ ↦ (z - 1) * mellin quarticKernel (-(z + 3))) =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ ↦ 2 / (z * (z + 1)) -
        24 / (z * (z + 1) * (z + 2) * (z + 3)) * riemannZeta₁ z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz1 : z ≠ 1 := by intro h; subst h; simp at hz
    have hz1_sub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hzeta1 : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hz1, ← mul_assoc, mul_inv_cancel₀ hz1_sub, one_mul]
    rw [mellin_quarticKernel_neg_add_three_eq_of_one_lt_re hz, hzeta1]
    field_simp [hz1_sub]
  exact hAn1.eqOn_of_preconnected_of_eventuallyEq hAn2 isPreconnected_re_pos
    (by norm_num : (2 : ℂ) ∈ _) hEv hs

/-- At any zero `ρ` of `riemannZeta` with `0 < ρ.re`,
`mellin quarticKernel (-(ρ + 3)) = 2 / ((ρ - 1) * ρ * (ρ + 1))`. -/
theorem mellin_quarticKernel_eq_of_riemannZeta_eq_zero {ρ : ℂ}
    (hρ : 0 < ρ.re) (hζ : riemannZeta ρ = 0) :
    mellin quarticKernel (-(ρ + 3)) = 2 / ((ρ - 1) * ρ * (ρ + 1)) := by
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    exact riemannZeta_one_ne_zero hζ
  have hρ1_sub : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hζ₁ : riemannZeta₁ ρ = 0 := by
    have h := riemannZeta_eq_inv_sub_mul hρ1
    rw [hζ] at h
    rcases mul_eq_zero.mp h.symm with hinv | h1
    · exact absurd hinv (inv_ne_zero hρ1_sub)
    · exact h1
  have hid := sub_one_mul_mellin_quarticKernel_eq_of_re_pos hρ
  rw [hζ₁, mul_zero, sub_zero] at hid
  apply mul_left_cancel₀ hρ1_sub
  rw [hid]
  field_simp [hρ1_sub]

/-- Explicit antiderivative of `(t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ)` on `(0, ∞)`. -/
noncomputable def quarticIocAntideriv (t : ℝ) : ℝ :=
  2 * t ^ (1 / 2 : ℝ) + 12 * t ^ (-1 / 2 : ℝ) - (26 / 3) * t ^ (-3 / 2 : ℝ) +
    (24 / 5) * t ^ (-5 / 2 : ℝ) - (8 / 7) * t ^ (-7 / 2 : ℝ)

/-- For `0 < t`,
`HasDerivAt quarticIocAntideriv ((t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ)) t`. -/
theorem hasDerivAt_quarticIocAntideriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt quarticIocAntideriv ((t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ)) t := by
  unfold quarticIocAntideriv
  have h1 := (Real.hasDerivAt_rpow_const (p := (1 / 2 : ℝ)) (Or.inl ht.ne')).const_mul 2
  have h2 := (Real.hasDerivAt_rpow_const (p := (-1 / 2 : ℝ)) (Or.inl ht.ne')).const_mul 12
  have h3 := (Real.hasDerivAt_rpow_const (p := (-3 / 2 : ℝ)) (Or.inl ht.ne')).const_mul (26 / 3)
  have h4 := (Real.hasDerivAt_rpow_const (p := (-5 / 2 : ℝ)) (Or.inl ht.ne')).const_mul (24 / 5)
  have h5 := (Real.hasDerivAt_rpow_const (p := (-7 / 2 : ℝ)) (Or.inl ht.ne')).const_mul (8 / 7)
  refine ((((h1.add h2).sub h3).add h4).sub h5).congr_deriv ?_
  have p1 : t ^ ((1 / 2 : ℝ) - 1) = t ^ (4 : ℕ) * t ^ (-9 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    norm_num
  have p2 : t ^ ((-1 / 2 : ℝ) - 1) = t ^ (3 : ℕ) * t ^ (-9 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    norm_num
  have p3 : t ^ ((-3 / 2 : ℝ) - 1) = t ^ (2 : ℕ) * t ^ (-9 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht]
    norm_num
  have p4 : t ^ ((-5 / 2 : ℝ) - 1) = t * t ^ (-9 / 2 : ℝ) := by
    have h := (Real.rpow_add ht (1 : ℝ) (-9 / 2 : ℝ)).symm
    rw [Real.rpow_one] at h
    rw [h]
    norm_num
  have p5 : t ^ ((-7 / 2 : ℝ) - 1) = t ^ (-9 / 2 : ℝ) := by norm_num
  rw [p1, p2, p3, p4, p5]
  ring

/-- Exact evaluation of `∫ t in Ioc 1 2, (t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ)`
and the rational upper bound `≤ 1 / 150`. -/
theorem integral_Ioc_one_two_quartic_le :
    (∫ t in Ioc (1 : ℝ) 2, (t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ)) ≤ 1 / 150 := by
  have hle : (1 : ℝ) ≤ 2 := by norm_num
  rw [← intervalIntegral.integral_of_le hle]
  have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) 2,
      HasDerivAt quarticIocAntideriv ((t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ)) t := by
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    exact hasDerivAt_quarticIocAntideriv (zero_lt_one.trans_le ht.1)
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ (t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ)) volume 1 2 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hle]
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).integrableOn_Icc
    have ht_pos : 0 < t := zero_lt_one.trans_le ht.1
    refine ContinuousAt.mul ?_ (Real.continuousAt_rpow_const _ _ (Or.inl ht_pos.ne'))
    exact ((continuousAt_id.sub continuousAt_const).pow 2).mul
      ((continuousAt_const.sub continuousAt_id).pow 2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold quarticIocAntideriv
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have r1 : (2 : ℝ) ^ (-1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℤ) * (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add h2_pos]
    norm_num
  have r2 : (2 : ℝ) ^ (-3 / 2 : ℝ) = (2 : ℝ) ^ (-2 : ℤ) * (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add h2_pos]
    norm_num
  have r3 : (2 : ℝ) ^ (-5 / 2 : ℝ) = (2 : ℝ) ^ (-3 : ℤ) * (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add h2_pos]
    norm_num
  have r4 : (2 : ℝ) ^ (-7 / 2 : ℝ) = (2 : ℝ) ^ (-4 : ℤ) * (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add h2_pos]
    norm_num
  rw [r1, r2, r3, r4, ← Real.sqrt_eq_rpow]
  simp only [Real.one_rpow]
  have hsqrt2 : 6680 * Real.sqrt 2 ≤ 9447 := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ 6680 * Real.sqrt 2),
      ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9447), ← sq_le_sq,
      mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  linarith

/-- Explicit tail bound on `Ioi 2`:
`∫ t in Ioi 2, (1 / 16 : ℝ) * t ^ (-9 / 2 : ℝ) ≤ 1 / 600`. -/
theorem integral_Ioi_two_quartic_tail_le :
    (∫ t in Ioi (2 : ℝ), (1 / 16 : ℝ) * t ^ (-9 / 2 : ℝ)) ≤ 1 / 600 := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) (by norm_num)]
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have hrpow : (2 : ℝ) ^ ((-9 / 2 : ℝ) + 1) = (1 / 16 : ℝ) * Real.sqrt 2 := by
    have h16 : (1 / 16 : ℝ) = (2 : ℝ) ^ (-4 : ℤ) := by norm_num
    rw [h16, Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_add h2_pos]
    norm_num
  rw [hrpow]
  have h_eq : (1 / 16 : ℝ) * (-((1 / 16 : ℝ) * Real.sqrt 2) / ((-9 / 2 : ℝ) + 1)) =
      (1 / 896) * Real.sqrt 2 := by ring
  rw [h_eq]
  have hsqrt2 : 75 * Real.sqrt 2 ≤ 112 := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ 75 * Real.sqrt 2),
      ← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 112), ← sq_le_sq,
      mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  linarith

/-- **Critical-Line Norm Bound on `mellin quarticKernel (-(s + 3))`**:
For any `s : ℂ` with `s.re = 1 / 2`,
`‖mellin quarticKernel (-(s + 3))‖ ≤ 1 / 120`. -/
theorem norm_mellin_quarticKernel_le_of_re_eq_half {s : ℂ} (hre : s.re = 1 / 2) :
    ‖mellin quarticKernel (-(s + 3))‖ ≤ 1 / 120 := by
  rw [mellin_quarticKernel_neg_add_three_eq]
  let f : ℝ → ℝ := fun t ↦ (t - (⌊t⌋₊ : ℝ)) ^ 2 * (1 - (t - (⌊t⌋₊ : ℝ))) ^ 2 * t ^ (-9 / 2 : ℝ)
  have hf_meas : AEStronglyMeasurable f (volume.restrict (Ioi (1 : ℝ))) := by
    have hm1 : Measurable (fun t : ℝ ↦ t - (⌊t⌋₊ : ℝ)) :=
      measurable_id.sub (measurable_from_nat.comp Nat.measurable_floor)
    have hm2 : Measurable (fun t : ℝ ↦ (t - (⌊t⌋₊ : ℝ)) ^ 2 * (1 - (t - (⌊t⌋₊ : ℝ))) ^ 2) :=
      (hm1.pow_const 2).mul ((measurable_const.sub hm1).pow_const 2)
    refine AEStronglyMeasurable.mul hm2.aestronglyMeasurable ?_
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).aestronglyMeasurable
      measurableSet_Ioi
    exact Real.continuousAt_rpow_const _ _ (Or.inl (zero_lt_one.trans ht).ne')
  have hf_int : IntegrableOn f (Ioi (1 : ℝ)) := by
    refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-9 / 2 : ℝ) < -1) zero_lt_one).const_mul
      (1 / 16)).mono' hf_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := zero_lt_one.trans ht
    obtain ⟨h0, h1⟩ := quartic_floor_bounds ht_pos.le
    dsimp only [f]
    rw [Real.norm_of_nonneg (mul_nonneg h0 (Real.rpow_nonneg ht_pos.le _))]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht_pos.le _)
  have hnorm_le :
      ‖∫ t in Ioi (1 : ℝ),
        (((t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 4))‖ ≤
      ∫ t in Ioi (1 : ℝ), f t := by
    refine norm_integral_le_of_norm_le hf_int ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := zero_lt_one.trans ht
    obtain ⟨h0, _⟩ := quartic_floor_bounds ht_pos.le
    rw [norm_mul, norm_real, Real.norm_of_nonneg h0, norm_cpow_eq_rpow_re_of_pos ht_pos]
    have hexp : (-(s + 4)).re = -9 / 2 := by simp [hre]; ring
    rw [hexp]
  have hunion : Ioi (1 : ℝ) = Ioc (1 : ℝ) 2 ∪ Ioi (2 : ℝ) :=
    (Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 2)).symm
  have hdisj : Disjoint (Ioc (1 : ℝ) 2) (Ioi (2 : ℝ)) := Ioc_disjoint_Ioi le_rfl
  have hsplit : ∫ t in Ioi (1 : ℝ), f t =
      (∫ t in Ioc (1 : ℝ) 2, f t) + ∫ t in Ioi (2 : ℝ), f t := by
    rw [hunion, setIntegral_union hdisj measurableSet_Ioi
      (hf_int.mono_set (by rw [hunion]; exact subset_union_left))
      (hf_int.mono_set (by rw [hunion]; exact subset_union_right))]
  have h_ioc : ∫ t in Ioc (1 : ℝ) 2, f t ≤ 1 / 150 := by
    have h_ae : f =ᵐ[volume.restrict (Ioc (1 : ℝ) 2)]
        fun t : ℝ ↦ (t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ) := by
      have h_eq_ioo : EqOn f (fun t : ℝ ↦ (t - 1) ^ 2 * (2 - t) ^ 2 * t ^ (-9 / 2 : ℝ))
          (Ioo (1 : ℝ) 2) := by
        intro t ht
        dsimp only [f]
        have hfl : ⌊t⌋₊ = 1 :=
          Nat.floor_eq_iff (zero_lt_one.trans ht.1).le |>.mpr
            ⟨by exact_mod_cast ht.1.le, by norm_num; exact ht.2⟩
        rw [hfl, Nat.cast_one]
        ring
      exact (ae_restrict_iff' measurableSet_Ioc).mpr
        (ae_of_all _ fun t ht ↦ by
          rcases eq_or_lt_of_le ht.2 with rfl | hlt
          · simp [f]
          · exact h_eq_ioo ⟨ht.1, hlt⟩)
    rw [integral_congr_ae h_ae]
    exact integral_Ioc_one_two_quartic_le
  have h_ioi : ∫ t in Ioi (2 : ℝ), f t ≤ 1 / 600 := by
    refine ( setIntegral_mono_on (hf_int.mono_set (Ioi_subset_Ioi (by norm_num)))
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)).const_mul (1 / 16))
      measurableSet_Ioi fun t ht ↦ ?_ ).trans integral_Ioi_two_quartic_tail_le
    have ht_pos : 0 < t := by linarith [mem_Ioi.mp ht]
    obtain ⟨_, h1⟩ := quartic_floor_bounds ht_pos.le
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht_pos.le _)
  linarith

/-- **Fourth-Order Critical-Line Product Bound (`240 ≤ ‖ρ - 1‖ * ‖ρ‖ * ‖ρ + 1‖`)**:
For every zero `ρ` of `riemannZeta` with `ρ.re = 1 / 2`,
`240 ≤ ‖ρ - 1‖ * ‖ρ‖ * ‖ρ + 1‖`. -/
theorem two_hundred_forty_le_norm_prod_of_riemannZeta_eq_zero_of_re_eq_half {ρ : ℂ}
    (hre : ρ.re = 1 / 2) (hζ : riemannZeta ρ = 0) :
    240 ≤ ‖ρ - 1‖ * ‖ρ‖ * ‖ρ + 1‖ := by
  have hρ_pos : 0 < ρ.re := by linarith
  have h_eq := mellin_quarticKernel_eq_of_riemannZeta_eq_zero hρ_pos hζ
  have h_le := norm_mellin_quarticKernel_le_of_re_eq_half hre
  rw [h_eq, norm_div, norm_ofNat, norm_mul, norm_mul] at h_le
  have h1 : 0 < ‖ρ - 1‖ := norm_pos_iff.mpr (by
    intro h; have := congrArg Complex.re (sub_eq_zero.mp h); simp [hre] at this)
  have h2 : 0 < ‖ρ‖ := norm_pos_iff.mpr (by
    intro h; rw [h] at hre; simp at hre)
  have h3 : 0 < ‖ρ + 1‖ := norm_pos_iff.mpr (by
    intro h; have := congrArg Complex.re h; simp [hre] at this; linarith)
  have hprod_pos : 0 < ‖ρ - 1‖ * ‖ρ‖ * ‖ρ + 1‖ := mul_pos (mul_pos h1 h2) h3
  rw [div_le_iff₀ hprod_pos] at h_le
  linarith

/-- **Low-Lying Zero-Free Region on the Critical Line (`37 < ρ.im ^ 2`)**:
For every zero `ρ` of `riemannZeta` with `ρ.re = 1 / 2`, `37 < ρ.im ^ 2`. -/
theorem thirty_seven_lt_im_sq_of_riemannZeta_eq_zero_of_re_eq_half {ρ : ℂ}
    (hre : ρ.re = 1 / 2) (hζ : riemannZeta ρ = 0) :
    37 < ρ.im ^ 2 := by
  have hprod := two_hundred_forty_le_norm_prod_of_riemannZeta_eq_zero_of_re_eq_half hre hζ
  have h_norm_sq : ‖ρ‖ ^ 2 = 1 / 4 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre]
    ring
  have h_norm_sub_eq : ‖ρ - 1‖ = ‖ρ‖ := by
    apply sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [sub_re, one_re, sub_im, one_im, hre]
    ring
  have h_norm_add_sq : ‖ρ + 1‖ ^ 2 = 9 / 4 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [add_re, one_re, add_im, one_im, hre]
    ring
  rw [h_norm_sub_eq, ← sq, h_norm_sq] at hprod
  have hsq : 240 ^ 2 ≤ ((1 / 4 + ρ.im ^ 2) * ‖ρ + 1‖) ^ 2 := by
    nlinarith [norm_nonneg (ρ + 1)]
  rw [mul_pow, h_norm_add_sq] at hsq
  by_contra! hle
  have hnonneg : 0 ≤ ρ.im ^ 2 := sq_nonneg ρ.im
  nlinarith

/-- **Low-Lying Zero-Free Region on the Critical Line (`6 < |ρ.im|`)**:
For every zero `ρ` of `riemannZeta` with `ρ.re = 1 / 2`, `6 < |ρ.im|`. -/
theorem six_lt_abs_im_of_riemannZeta_eq_zero_of_re_eq_half {ρ : ℂ}
    (hre : ρ.re = 1 / 2) (hζ : riemannZeta ρ = 0) :
    6 < |ρ.im| := by
  have h := thirty_seven_lt_im_sq_of_riemannZeta_eq_zero_of_re_eq_half hre hζ
  rw [← sq_abs] at h
  by_contra! hle
  have hnonneg : 0 ≤ |ρ.im| := abs_nonneg ρ.im
  nlinarith

/-- A complex number `s` is a nontrivial zero of `riemannZeta` if `riemannZeta s = 0`,
`s` is not a trivial zero `-2 * (n + 1)` (`n : ℕ`), and `s ≠ 1`. -/
def IsNontrivialZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

/-- No nontrivial zero of `riemannZeta` equals `0`. -/
theorem isNontrivialZetaZero_ne_zero {s : ℂ} (hs : IsNontrivialZetaZero s) : s ≠ 0 := by
  rintro rfl
  have h0 := hs.1
  rw [riemannZeta_zero] at h0
  norm_num at h0

/-- Every nontrivial zero `s` of `riemannZeta` has `s.re < 1`. -/
theorem re_lt_one_of_isNontrivialZetaZero {s : ℂ} (hs : IsNontrivialZetaZero s) : s.re < 1 := by
  by_contra! hle
  exact riemannZeta_ne_zero_of_one_le_re hle hs.1

/-- Every nontrivial zero `s` of `riemannZeta` has `0 < s.re`. -/
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
  have hGamma : Gamma (1 - s) ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hZeta : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1s_re
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
    simp only [Int.cast_zero, mul_zero] at hs_eq
    exact hs0 hs_eq
  refine hs.2.1 ⟨(k - 1).toNat, ?_⟩
  have hk_nat : ((k - 1).toNat : ℂ) + 1 = (k : ℂ) := by
    have : ((k - 1).toNat : ℤ) + 1 = k := by omega
    exact_mod_cast this
  rw [hk_nat, hs_eq]

/-- Every nontrivial zero of `riemannZeta` satisfies `0 < s.re ∧ s.re < 1`. -/
theorem mem_criticalStrip_of_isNontrivialZetaZero {s : ℂ} (hs : IsNontrivialZetaZero s) :
    0 < s.re ∧ s.re < 1 :=
  ⟨zero_lt_re_of_isNontrivialZetaZero hs, re_lt_one_of_isNontrivialZetaZero hs⟩

/-- Finiteness of nontrivial zeros up to height `T`. -/
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

/-- **Zero-Counting Function `N(T)`**:
The number of nontrivial zeros `ρ` of `riemannZeta` with `|ρ.im| ≤ T`. -/
noncomputable def zeroCountingFunction (T : ℝ) : ℕ :=
  (nontrivialZetaZerosUpTo T).card

/-- Under `RiemannHypothesis`, every nontrivial zero `ρ` of `riemannZeta` satisfies
`37 < ρ.im ^ 2`. -/
theorem thirty_seven_lt_im_sq_of_riemannHypothesis (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : IsNontrivialZetaZero ρ) :
    37 < ρ.im ^ 2 :=
  thirty_seven_lt_im_sq_of_riemannZeta_eq_zero_of_re_eq_half (hRH ρ hρ.1 hρ.2.1 hρ.2.2) hρ.1

/-- Under `RiemannHypothesis`, every nontrivial zero `ρ` of `riemannZeta` satisfies
`6 < |ρ.im|`. -/
theorem six_lt_abs_im_of_riemannHypothesis (hRH : RiemannHypothesis) {ρ : ℂ}
    (hρ : IsNontrivialZetaZero ρ) :
    6 < |ρ.im| :=
  six_lt_abs_im_of_riemannZeta_eq_zero_of_re_eq_half (hRH ρ hρ.1 hρ.2.1 hρ.2.2) hρ.1

/-- Under `RiemannHypothesis`, `nontrivialZetaZerosUpTo T = ∅` for all `T ≤ 6`. -/
theorem nontrivialZetaZerosUpTo_eq_empty_of_le_six (hRH : RiemannHypothesis) {T : ℝ}
    (hT : T ≤ 6) :
    nontrivialZetaZerosUpTo T = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro ρ hρ
  rw [mem_nontrivialZetaZerosUpTo] at hρ
  have h6 := six_lt_abs_im_of_riemannHypothesis hRH hρ.1
  linarith [hρ.2]

/-- Under `RiemannHypothesis`, `zeroCountingFunction T = 0` for all `T ≤ 6`. -/
theorem zeroCountingFunction_eq_zero_of_le_six (hRH : RiemannHypothesis) {T : ℝ}
    (hT : T ≤ 6) :
    zeroCountingFunction T = 0 := by
  unfold zeroCountingFunction
  rw [nontrivialZetaZerosUpTo_eq_empty_of_le_six hRH hT, Finset.card_empty]

/-- In particular, under `RiemannHypothesis`, `zeroCountingFunction 6 = 0`. -/
theorem zeroCountingFunction_six_eq_zero (hRH : RiemannHypothesis) :
    zeroCountingFunction 6 = 0 :=
  zeroCountingFunction_eq_zero_of_le_six hRH le_rfl

/-!
## Section 2: Local Jensen Multiplicity & Zero-Counting Bounds (`divisor riemannZeta₁`)
-/

/-- `riemannZeta₁` is analytic on a neighborhood of every set `U : Set ℂ`. -/
theorem analyticOnNhd_riemannZeta₁ (U : Set ℂ) : AnalyticOnNhd ℂ riemannZeta₁ U :=
  (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ).mono (subset_univ U)

/-- `riemannZeta₁` is analytic at every point `s : ℂ`. -/
theorem analyticAt_riemannZeta₁ (s : ℂ) : AnalyticAt ℂ riemannZeta₁ s :=
  analyticOnNhd_riemannZeta₁ univ s (mem_univ s)

/-- On the punctured plane `{1}ᶜ`, `riemannZeta` and `(s - 1)⁻¹ * riemannZeta₁ s` agree in a
neighborhood of any `s₀ ≠ 1`. -/
theorem riemannZeta_eventuallyEq_inv_sub_mul_riemannZeta₁ {s₀ : ℂ} (hs₀ : s₀ ≠ 1) :
    riemannZeta =ᶠ[𝓝 s₀] fun s ↦ (s - 1)⁻¹ * riemannZeta₁ s := by
  filter_upwards [isOpen_ne.mem_nhds hs₀] with s hs
  exact riemannZeta_eq_inv_sub_mul hs

/-- **Equality of Analytic Orders Away from `s = 1`**:
For every `s₀ ≠ 1`, `analyticOrderAt riemannZeta s₀ = analyticOrderAt riemannZeta₁ s₀`. -/
theorem analyticOrderAt_riemannZeta_eq_analyticOrderAt_riemannZeta₁ {s₀ : ℂ} (hs₀ : s₀ ≠ 1) :
    analyticOrderAt riemannZeta s₀ = analyticOrderAt riemannZeta₁ s₀ := by
  have h_inv_an : AnalyticAt ℂ (fun s : ℂ ↦ (s - 1)⁻¹) s₀ :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hs₀)
  have h_inv_ne : (s₀ - 1)⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hs₀)
  have h_ord_inv : analyticOrderAt (fun s : ℂ ↦ (s - 1)⁻¹) s₀ = 0 :=
    h_inv_an.analyticOrderAt_eq_zero.mpr h_inv_ne
  rw [analyticOrderAt_congr (riemannZeta_eventuallyEq_inv_sub_mul_riemannZeta₁ hs₀)]
  change analyticOrderAt ((fun s : ℂ ↦ (s - 1)⁻¹) * riemannZeta₁) s₀ =
    analyticOrderAt riemannZeta₁ s₀
  rw [analyticOrderAt_mul h_inv_an (analyticAt_riemannZeta₁ s₀), h_ord_inv, zero_add]

/-- For every `s₀ ≠ 1`, `analyticOrderNatAt riemannZeta s₀ = analyticOrderNatAt riemannZeta₁ s₀`. -/
theorem analyticOrderNatAt_riemannZeta_eq_analyticOrderNatAt_riemannZeta₁ {s₀ : ℂ}
    (hs₀ : s₀ ≠ 1) :
    analyticOrderNatAt riemannZeta s₀ = analyticOrderNatAt riemannZeta₁ s₀ := by
  unfold analyticOrderNatAt
  rw [analyticOrderAt_riemannZeta_eq_analyticOrderAt_riemannZeta₁ hs₀]

/-- Helper lemma: for any `o : ℕ∞`, `(ENat.map (Nat.cast : ℕ → ℤ) o).untop₀ = (o.toNat : ℤ)`. -/
theorem enat_map_natCast_untop₀ (o : ℕ∞) :
    (ENat.map (Nat.cast : ℕ → ℤ) o).untop₀ = (o.toNat : ℤ) := by
  cases o <;> rfl

/-- **Divisor of `riemannZeta₁` Equals `analyticOrderNatAt riemannZeta`**:
For any set `U : Set ℂ` and any `ρ ∈ U` with `ρ ≠ 1`,
`divisor riemannZeta₁ U ρ = (analyticOrderNatAt riemannZeta ρ : ℤ)`. -/
theorem divisor_riemannZeta₁_eq_analyticOrderNatAt_riemannZeta (U : Set ℂ) {ρ : ℂ}
    (hρU : ρ ∈ U) (hρ1 : ρ ≠ 1) :
    divisor riemannZeta₁ U ρ = (analyticOrderNatAt riemannZeta ρ : ℤ) := by
  rw [(analyticOnNhd_riemannZeta₁ U).divisor_apply hρU, enat_map_natCast_untop₀]
  unfold analyticOrderNatAt
  rw [analyticOrderAt_riemannZeta_eq_analyticOrderAt_riemannZeta₁ hρ1]

/-- `analyticOrderAt riemannZeta₁ s ≠ ⊤` for every `s : ℂ` (since `riemannZeta₁ 1 = 1 ≠ 0`). -/
theorem analyticOrderAt_riemannZeta₁_ne_top (s : ℂ) :
    analyticOrderAt riemannZeta₁ s ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have h_zero : EqOn riemannZeta₁ 0 univ :=
    (analyticOnNhd_riemannZeta₁ univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ s) htop
  have h1 : riemannZeta₁ 1 = 0 := h_zero (mem_univ 1)
  rw [riemannZeta₁_one] at h1
  exact one_ne_zero h1

/-- Every nontrivial zero `ρ` of `riemannZeta` has multiplicity
`1 ≤ analyticOrderNatAt riemannZeta ρ`. -/
theorem one_le_analyticOrderNatAt_of_isNontrivialZetaZero {ρ : ℂ}
    (hρ : IsNontrivialZetaZero ρ) :
    1 ≤ analyticOrderNatAt riemannZeta ρ := by
  rw [analyticOrderNatAt_riemannZeta_eq_analyticOrderNatAt_riemannZeta₁ hρ.2.2]
  have hζ₁ : riemannZeta₁ ρ = 0 := by
    have h := riemannZeta_eq_inv_sub_mul hρ.2.2
    rw [hρ.1] at h
    rcases mul_eq_zero.mp h.symm with hinv | h1
    · exact absurd hinv (inv_ne_zero (sub_ne_zero.mpr hρ.2.2))
    · exact h1
  have h_ne_zero : analyticOrderAt riemannZeta₁ ρ ≠ 0 :=
    (analyticAt_riemannZeta₁ ρ).analyticOrderAt_ne_zero.mpr hζ₁
  have h_ne_top : analyticOrderAt riemannZeta₁ ρ ≠ ⊤ :=
    analyticOrderAt_riemannZeta₁_ne_top ρ
  unfold analyticOrderNatAt
  cases h_ord : analyticOrderAt riemannZeta₁ ρ with
  | top => exact absurd h_ord h_ne_top
  | coe n =>
    rw [h_ord] at h_ne_zero
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h_ne_zero)

/-- At any nontrivial zero `ρ ∈ U`, `1 ≤ divisor riemannZeta₁ U ρ`. -/
theorem one_le_divisor_riemannZeta₁_of_isNontrivialZetaZero (U : Set ℂ) {ρ : ℂ}
    (hρU : ρ ∈ U) (hρ : IsNontrivialZetaZero ρ) :
    1 ≤ divisor riemannZeta₁ U ρ := by
  rw [divisor_riemannZeta₁_eq_analyticOrderNatAt_riemannZeta U hρU hρ.2.2]
  exact_mod_cast one_le_analyticOrderNatAt_of_isNontrivialZetaZero hρ

/-- For any finite set `S : Finset ℂ` and any nonnegative finitely-supported function `f : ℂ → ℤ`,
`∑ z ∈ S, f z ≤ ∑ᶠ u, f u`. -/
theorem sum_le_finsum_of_nonneg (S : Finset ℂ) {f : ℂ → ℤ}
    (hf : (Function.support f).Finite) (h0 : ∀ z, 0 ≤ f z) :
    ∑ z ∈ S, f z ≤ ∑ᶠ u, f u := by
  classical
  rw [finsum_eq_sum_of_support_toFinset_subset f hf (Finset.subset_union_right (s₁ := S))]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun z _ _ ↦ h0 z)

/-- **Multiplicity-Weighted Sum Bound via `divisor riemannZeta₁`**:
For any `S : Finset ℂ`, center `c : ℂ`, and radius `r : ℝ`, if every `ρ ∈ S` satisfies
`ρ ∈ closedBall c |r|` and `ρ ≠ 1`, then
`((∑ ρ ∈ S, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤`
`((∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u : ℤ) : ℝ)`. -/
theorem sum_analyticOrderNatAt_le_finsum_divisor_riemannZeta₁ (S : Finset ℂ) (c : ℂ) (r : ℝ)
    (hS : ∀ ρ ∈ S, ρ ∈ closedBall c |r| ∧ ρ ≠ 1) :
    ((∑ ρ ∈ S, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
      ((∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u : ℤ) : ℝ) := by
  have h_int :
      (∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℤ)) ≤
        ∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u := by
    have h_eq :
        ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℤ) =
          ∑ ρ ∈ S, divisor riemannZeta₁ (closedBall c |r|) ρ := by
      refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
      exact (divisor_riemannZeta₁_eq_analyticOrderNatAt_riemannZeta
        (closedBall c |r|) (hS ρ hρ).1 (hS ρ hρ).2).symm
    rw [h_eq]
    exact sum_le_finsum_of_nonneg S
      ((divisor riemannZeta₁ (closedBall c |r|)).finiteSupport (isCompact_closedBall c |r|))
      ((analyticOnNhd_riemannZeta₁ (closedBall c |r|)).divisor_nonneg)
  exact_mod_cast h_int

/-- For any `S : Finset ℂ` of nontrivial zeros of `riemannZeta`, its cardinality is bounded by
the sum of multiplicities `∑ ρ ∈ S, analyticOrderNatAt riemannZeta ρ`. -/
theorem card_le_sum_analyticOrderNatAt_of_isNontrivialZetaZero (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, IsNontrivialZetaZero ρ) :
    S.card ≤ ∑ ρ ∈ S, analyticOrderNatAt riemannZeta ρ := by
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun ρ hρ ↦ one_le_analyticOrderNatAt_of_isNontrivialZetaZero (hS ρ hρ)

/-- **Unweighted Cardinality Bound via `divisor riemannZeta₁`**:
For any `S : Finset ℂ` of nontrivial zeros of `riemannZeta` contained in `closedBall c |r|`,
`(S.card : ℝ) ≤ ((∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u : ℤ) : ℝ)`. -/
theorem card_le_finsum_divisor_riemannZeta₁ (S : Finset ℂ) (c : ℂ) (r : ℝ)
    (hS : ∀ ρ ∈ S, IsNontrivialZetaZero ρ ∧ ρ ∈ closedBall c |r|) :
    (S.card : ℝ) ≤ ((∑ᶠ u, divisor riemannZeta₁ (closedBall c |r|) u : ℤ) : ℝ) := by
  have h1 : (S.card : ℝ) ≤ ((∑ ρ ∈ S, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) := by
    exact_mod_cast card_le_sum_analyticOrderNatAt_of_isNontrivialZetaZero S (fun ρ hρ ↦ (hS ρ hρ).1)
  exact h1.trans (sum_analyticOrderNatAt_le_finsum_divisor_riemannZeta₁ S c r
    (fun ρ hρ ↦ ⟨(hS ρ hρ).2, (hS ρ hρ).1.2.2⟩))

/-- **Nontrivial Zeros in the Unit Height Window `[t - 1 / 2, t + 1 / 2]`**:
The `Finset ℂ` of nontrivial zeros `ρ` of `riemannZeta` with `t - 1 / 2 ≤ ρ.im ≤ t + 1 / 2`. -/
noncomputable def nontrivialZetaZerosInUnitWindow (t : ℝ) : Finset ℂ :=
  (nontrivialZetaZerosUpTo (|t| + 1 / 2)).filter
    (fun ρ ↦ t - 1 / 2 ≤ ρ.im ∧ ρ.im ≤ t + 1 / 2)

@[simp]
theorem mem_nontrivialZetaZerosInUnitWindow {t : ℝ} {ρ : ℂ} :
    ρ ∈ nontrivialZetaZerosInUnitWindow t ↔
      IsNontrivialZetaZero ρ ∧ t - 1 / 2 ≤ ρ.im ∧ ρ.im ≤ t + 1 / 2 := by
  simp only [nontrivialZetaZerosInUnitWindow, mem_filter, mem_nontrivialZetaZerosUpTo]
  refine ⟨fun ⟨⟨h1, _⟩, h3, h4⟩ ↦ ⟨h1, h3, h4⟩, fun ⟨h1, h3, h4⟩ ↦ ⟨⟨h1, ?_⟩, h3, h4⟩⟩
  rw [abs_le]
  have ht := le_abs_self t
  have hnt := neg_le_abs t
  constructor <;> linarith

/-- Under `RiemannHypothesis`, every nontrivial zero `ρ ∈ nontrivialZetaZerosInUnitWindow t`
lies in `closedBall (2 + (t : ℂ) * I) |(7 / 4 : ℝ)|`. -/
theorem mem_closedBall_two_add_mul_I_seven_fourths_of_riemannHypothesis
    (hRH : RiemannHypothesis) (t : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ nontrivialZetaZerosInUnitWindow t) :
    ρ ∈ closedBall (2 + (t : ℂ) * I) |(7 / 4 : ℝ)| := by
  rw [mem_nontrivialZetaZerosInUnitWindow] at hρ
  obtain ⟨h_nt, h_lo, h_hi⟩ := hρ
  have hre : ρ.re = 1 / 2 := hRH ρ h_nt.1 h_nt.2.1 h_nt.2.2
  rw [mem_closedBall, dist_eq_norm, abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)]
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply]
  have h_re_sub : (ρ - (2 + (t : ℂ) * I)).re = -3 / 2 := by simp [hre]; ring
  have h_im_sub : (ρ - (2 + (t : ℂ) * I)).im = ρ.im - t := by simp
  rw [h_re_sub, h_im_sub]
  have him_sq : (ρ.im - t) ^ 2 ≤ (1 / 2) ^ 2 := by
    nlinarith
  nlinarith

/-- **Multiplicity-Weighted Local Zero-Counting Bound via Jensen's Inequality**:
Under `RiemannHypothesis`, for every `t : ℝ`, the sum of multiplicities of nontrivial zeros of
`riemannZeta` in the unit height window `[t - 1 / 2, t + 1 / 2]` is bounded by the Jensen divisor
sum on `closedBall (2 + t * I) |(7 / 4 : ℝ)|`. -/
theorem sum_analyticOrderNatAt_unitWindow_le_finsum_divisor_of_riemannHypothesis
    (hRH : RiemannHypothesis) (t : ℝ) :
    ((∑ ρ ∈ nontrivialZetaZerosInUnitWindow t, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
      ((∑ᶠ u, divisor riemannZeta₁ (closedBall (2 + (t : ℂ) * I) |(7 / 4 : ℝ)|) u : ℤ) : ℝ) := by
  refine sum_analyticOrderNatAt_le_finsum_divisor_riemannZeta₁
    (nontrivialZetaZerosInUnitWindow t) (2 + (t : ℂ) * I) (7 / 4) fun ρ hρ ↦ ?_
  refine ⟨mem_closedBall_two_add_mul_I_seven_fourths_of_riemannHypothesis hRH t hρ, ?_⟩
  exact (mem_nontrivialZetaZerosInUnitWindow.mp hρ).1.2.2

/-- **Unweighted Local Zero-Counting Bound via Jensen's Inequality**:
Under `RiemannHypothesis`, for every `t : ℝ`, the number of nontrivial zeros of `riemannZeta`
in the unit height window `[t - 1 / 2, t + 1 / 2]` is bounded by the Jensen divisor sum on
`closedBall (2 + t * I) |(7 / 4 : ℝ)|`. -/
theorem card_unitWindow_le_finsum_divisor_of_riemannHypothesis
    (hRH : RiemannHypothesis) (t : ℝ) :
    ((nontrivialZetaZerosInUnitWindow t).card : ℝ) ≤
      ((∑ᶠ u, divisor riemannZeta₁ (closedBall (2 + (t : ℂ) * I) |(7 / 4 : ℝ)|) u : ℤ) : ℝ) := by
  refine card_le_finsum_divisor_riemannZeta₁
    (nontrivialZetaZerosInUnitWindow t) (2 + (t : ℂ) * I) (7 / 4) fun ρ hρ ↦ ?_
  exact ⟨(mem_nontrivialZetaZerosInUnitWindow.mp hρ).1,
    mem_closedBall_two_add_mul_I_seven_fourths_of_riemannHypothesis hRH t hρ⟩

/-- Combining `sum_analyticOrderNatAt_unitWindow_le_finsum_divisor_of_riemannHypothesis` with
`AnalyticOnNhd.sum_divisor_le` gives an explicit upper bound on the multiplicity-weighted zero
count in `[t - 1 / 2, t + 1 / 2]` for any outer radius `7 / 4 < |R|` and sphere upper bound
`1 ≤ M`. -/
theorem sum_analyticOrderNatAt_unitWindow_le_jensen_of_riemannHypothesis
    (hRH : RiemannHypothesis) (t : ℝ) {R M : ℝ}
    (hR : 7 / 4 < |R|) (hM : 1 ≤ M)
    (hc : riemannZeta₁ (2 + (t : ℂ) * I) ≠ 0)
    (f_bound : ∀ z ∈ sphere (2 + (t : ℂ) * I) |R|, ‖riemannZeta₁ z‖ ≤ M) :
    ((∑ ρ ∈ nontrivialZetaZerosInUnitWindow t, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
      Real.log (M / ‖riemannZeta₁ (2 + (t : ℂ) * I)‖) / Real.log (R / (7 / 4)) := by
  refine (sum_analyticOrderNatAt_unitWindow_le_finsum_divisor_of_riemannHypothesis hRH t).trans ?_
  exact (analyticOnNhd_riemannZeta₁ (closedBall (2 + (t : ℂ) * I) |R|)).sum_divisor_le
    (r := 7 / 4) (by norm_num) (by simpa [abs_of_pos (by norm_num : (0 : ℝ) < 7 / 4)] using hR)
    hM hc f_bound

/-!
## Section 3: Low-Frequency Stieltjes Integration by Parts (`g(t) = 1 / t`) and Discharge of `h_low`
-/

theorem nontrivialZetaZerosUpTo_subset_of_le {t T : ℝ} (htT : t ≤ T) :
    nontrivialZetaZerosUpTo t ⊆ nontrivialZetaZerosUpTo T := by
  intro ρ hρ
  rw [mem_nontrivialZetaZerosUpTo] at hρ ⊢
  exact ⟨hρ.1, hρ.2.trans htT⟩

theorem zeroCountingFunction_mono : Monotone zeroCountingFunction :=
  fun _ _ htT ↦ card_le_card (nontrivialZetaZerosUpTo_subset_of_le htT)

/-- **Nontrivial Zeros Between Heights `T` and `U`**:
The `Finset ℂ` of nontrivial zeros `ρ` of `riemannZeta` with `T < |ρ.im| ≤ U`. -/
noncomputable def nontrivialZetaZerosBetween (T U : ℝ) : Finset ℂ :=
  (nontrivialZetaZerosUpTo U).filter (fun ρ ↦ T < |ρ.im|)

@[simp]
theorem mem_nontrivialZetaZerosBetween {T U : ℝ} {ρ : ℂ} :
    ρ ∈ nontrivialZetaZerosBetween T U ↔
      IsNontrivialZetaZero ρ ∧ |ρ.im| ≤ U ∧ T < |ρ.im| := by
  simp [nontrivialZetaZerosBetween, and_assoc]

/-- Whenever `zeroCountingFunction t₀ = 0`, `nontrivialZetaZerosUpTo T` coincides with
`nontrivialZetaZerosBetween t₀ T`! -/
theorem nontrivialZetaZerosUpTo_eq_nontrivialZetaZerosBetween_of_zeroCountingFunction_eq_zero
    {t₀ T : ℝ} (h0 : zeroCountingFunction t₀ = 0) :
    nontrivialZetaZerosUpTo T = nontrivialZetaZerosBetween t₀ T := by
  have hempty : nontrivialZetaZerosUpTo t₀ = ∅ := Finset.card_eq_zero.mp h0
  ext ρ
  simp only [mem_nontrivialZetaZerosUpTo, mem_nontrivialZetaZerosBetween]
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, h2, ?_⟩, fun ⟨h1, h2, _⟩ ↦ ⟨h1, h2⟩⟩
  by_contra! hle
  have hmem : ρ ∈ nontrivialZetaZerosUpTo t₀ := mem_nontrivialZetaZerosUpTo.mpr ⟨h1, hle⟩
  rw [hempty] at hmem
  exact Finset.notMem_empty ρ hmem

/-- Under `RiemannHypothesis`, `nontrivialZetaZerosUpTo T = nontrivialZetaZerosBetween 6 T`
for every `T : ℝ`. -/
theorem nontrivialZetaZerosUpTo_eq_nontrivialZetaZerosBetween_six_of_riemannHypothesis
    (hRH : RiemannHypothesis) (T : ℝ) :
    nontrivialZetaZerosUpTo T = nontrivialZetaZerosBetween 6 T :=
  nontrivialZetaZerosUpTo_eq_nontrivialZetaZerosBetween_of_zeroCountingFunction_eq_zero
    (zeroCountingFunction_six_eq_zero hRH)

/-- Complementary filter characterization: for `T ≤ U`, filtering `nontrivialZetaZerosUpTo U`
by `¬ (T < |ρ.im|)` recovers `nontrivialZetaZerosUpTo T`. -/
theorem filter_not_lt_abs_im_nontrivialZetaZerosUpTo {T U : ℝ} (hTU : T ≤ U) :
    (nontrivialZetaZerosUpTo U).filter (fun ρ ↦ ¬ T < |ρ.im|) =
      nontrivialZetaZerosUpTo T := by
  ext ρ
  simp only [mem_filter, mem_nontrivialZetaZerosUpTo, not_lt]
  exact ⟨fun ⟨⟨h1, _⟩, h3⟩ ↦ ⟨h1, h3⟩, fun ⟨h1, h2⟩ ↦ ⟨⟨h1, h2.trans hTU⟩, h2⟩⟩

/-- For `T ≤ U`, the cardinality of `nontrivialZetaZerosBetween T U` plus `zeroCountingFunction T`
equals `zeroCountingFunction U`. -/
theorem card_nontrivialZetaZerosBetween_add_eq {T U : ℝ} (hTU : T ≤ U) :
    (nontrivialZetaZerosBetween T U).card + zeroCountingFunction T =
      zeroCountingFunction U := by
  unfold nontrivialZetaZerosBetween zeroCountingFunction
  rw [← filter_not_lt_abs_im_nontrivialZetaZerosUpTo hTU]
  exact card_filter_add_card_filter_not (fun ρ : ℂ ↦ T < |ρ.im|)

/-- For `T ≤ U`, the cardinality of `nontrivialZetaZerosBetween T U` over `ℝ` is
`(zeroCountingFunction U : ℝ) - (zeroCountingFunction T : ℝ)`. -/
theorem card_nontrivialZetaZerosBetween_real {T U : ℝ} (hTU : T ≤ U) :
    ((nontrivialZetaZerosBetween T U).card : ℝ) =
      (zeroCountingFunction U : ℝ) - (zeroCountingFunction T : ℝ) := by
  have h :
      ((nontrivialZetaZerosBetween T U).card : ℝ) + (zeroCountingFunction T : ℝ) =
        (zeroCountingFunction U : ℝ) := by
    exact_mod_cast card_nontrivialZetaZerosBetween_add_eq hTU
  linarith

/-- Filtering `nontrivialZetaZerosBetween T U` by `|ρ.im| ≤ t` for `t ≤ U` recovers
`nontrivialZetaZerosBetween T t`. -/
theorem filter_abs_im_le_nontrivialZetaZerosBetween {T t U : ℝ} (htU : t ≤ U) :
    (nontrivialZetaZerosBetween T U).filter (fun ρ ↦ |ρ.im| ≤ t) =
      nontrivialZetaZerosBetween T t := by
  ext ρ
  simp only [mem_filter, mem_nontrivialZetaZerosBetween]
  exact ⟨fun ⟨⟨h1, _, h3⟩, h4⟩ ↦ ⟨h1, h4, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨⟨h1, h2.trans htU, h3⟩, h2⟩⟩

/-- For `T ≤ t ≤ U`, the indicator sum `∑_{ρ ∈ Z(T, U)} (if |ρ.im| ≤ t then 1 else 0)` equals
`(zeroCountingFunction t : ℝ) - (zeroCountingFunction T : ℝ)`. -/
theorem sum_ite_abs_im_le_nontrivialZetaZerosBetween {T t U : ℝ} (hTt : T ≤ t) (htU : t ≤ U) :
    (∑ ρ ∈ nontrivialZetaZerosBetween T U, if |ρ.im| ≤ t then (1 : ℝ) else 0) =
      (zeroCountingFunction t : ℝ) - (zeroCountingFunction T : ℝ) := by
  rw [sum_boole, filter_abs_im_le_nontrivialZetaZerosBetween htU,
    card_nontrivialZetaZerosBetween_real hTt]

/-- For `T < γ ≤ U` and any function `g, g' : ℝ → ℝ` with `HasDerivAt g (g' t) t` on `[T, U]`
and `ContinuousOn g' (Set.Icc T U)`, the set integral of `(Set.Ici γ).indicator g'` over
`Set.Ioc T U` equals `g U - g γ`. -/
theorem setIntegral_indicator_deriv_eq_sub {T γ U : ℝ} (hγ : T < γ) (hγU : γ ≤ U)
    {g g' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc T U, HasDerivAt g (g' t) t)
    (hcont : ContinuousOn g' (Set.Icc T U)) :
    (∫ t in Set.Ioc T U, (Set.Ici γ).indicator g' t) = g U - g γ := by
  rw [setIntegral_indicator measurableSet_Ici]
  have hinter : Set.Ioc T U ∩ Set.Ici γ = Set.Icc γ U := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
    exact ⟨fun ⟨⟨_, h2⟩, h3⟩ ↦ ⟨h3, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨⟨hγ.trans_le h1, h2⟩, h1⟩⟩
  rw [hinter, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hγU]
  have hsub : Set.Icc γ U ⊆ Set.Icc T U := Set.Icc_subset_Icc_left hγ.le
  have hd_sub : ∀ t ∈ Set.uIcc γ U, HasDerivAt g (g' t) t := by
    intro t ht
    rw [Set.uIcc_of_le hγU] at ht
    exact hderiv t (hsub ht)
  have hint_sub : IntervalIntegrable g' volume γ U := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hγU]
    exact (hcont.mono hsub).integrableOn_Icc
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd_sub hint_sub

/-- Integrability of `(Set.Ici γ).indicator g'` on `Set.Ioc T U` for `T < γ` when `g'` is
continuous on `Set.Icc T U`. -/
theorem integrableOn_indicator_of_continuousOn {T γ U : ℝ} (hγ : T < γ)
    {g' : ℝ → ℝ} (hcont : ContinuousOn g' (Set.Icc T U)) :
    IntegrableOn ((Set.Ici γ).indicator g') (Set.Ioc T U) := by
  rw [integrableOn_indicator_iff measurableSet_Ici]
  have hinter : Set.Ici γ ∩ Set.Ioc T U = Set.Icc γ U := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
    exact ⟨fun ⟨h1, _, h3⟩ ↦ ⟨h1, h3⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, hγ.trans_le h1, h2⟩⟩
  rw [hinter]
  exact (hcont.mono (Set.Icc_subset_Icc_left hγ.le)).integrableOn_Icc

/-- Pointwise decomposition of
`((zeroCountingFunction t : ℝ) - (zeroCountingFunction T : ℝ)) * g' t`
on `Set.Ioc T U` as a finite sum of indicator functions over `nontrivialZetaZerosBetween T U`. -/
theorem eqOn_sub_zeroCountingFunction_mul_sum_indicator {T U : ℝ} (g' : ℝ → ℝ) :
    Set.EqOn
      (fun t : ℝ ↦ ((zeroCountingFunction t : ℝ) - (zeroCountingFunction T : ℝ)) * g' t)
      (fun t : ℝ ↦ ∑ ρ ∈ nontrivialZetaZerosBetween T U, (Set.Ici |ρ.im|).indicator g' t)
      (Set.Ioc T U) := by
  intro t ht
  dsimp only
  rw [← sum_ite_abs_im_le_nontrivialZetaZerosBetween ht.1.le ht.2, sum_mul]
  refine sum_congr rfl fun ρ _ ↦ ?_
  simp only [Set.indicator, Set.mem_Ici]
  split_ifs <;> ring

/-- If `g'` is continuous on `Set.Icc T U` (`T ≤ U`), then
`fun t ↦ (zeroCountingFunction t : ℝ) * g' t` is `IntervalIntegrable` on `T..U`. -/
theorem intervalIntegrable_zeroCountingFunction_mul {T U : ℝ} (hTU : T ≤ U)
    {g' : ℝ → ℝ} (hcont : ContinuousOn g' (Set.Icc T U)) :
    IntervalIntegrable (fun t : ℝ ↦ (zeroCountingFunction t : ℝ) * g' t) volume T U := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hTU]
  have h_sub_int :
      IntegrableOn
        (fun t : ℝ ↦ ((zeroCountingFunction t : ℝ) - (zeroCountingFunction T : ℝ)) * g' t)
        (Set.Ioc T U) := by
    refine IntegrableOn.congr_fun ?_ (eqOn_sub_zeroCountingFunction_mul_sum_indicator g').symm
      measurableSet_Ioc
    exact integrable_finsetSum (nontrivialZetaZerosBetween T U) fun ρ hρ ↦
      integrableOn_indicator_of_continuousOn
        (mem_nontrivialZetaZerosBetween.mp hρ).2.2
        hcont
  have h_const_int :
      IntegrableOn (fun t : ℝ ↦ (zeroCountingFunction T : ℝ) * g' t) (Set.Ioc T U) :=
    (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).const_mul _
  have h_add := h_sub_int.add h_const_int
  refine h_add.congr_fun (fun t _ ↦ ?_) measurableSet_Ioc
  simp only [Pi.add_apply]
  ring

/-- **General Stieltjes Integration-by-Parts Identity for `nontrivialZetaZerosBetween T U`**:
For any `T ≤ U` and any `g, g' : ℝ → ℝ` with `HasDerivAt g (g' t) t` on `Set.Icc T U` and
`ContinuousOn g' (Set.Icc T U)`,
$$\sum_{\rho \in \mathcal{Z}(T, U)} g(|\operatorname{Im} \rho|)
  = N(U) g(U) - N(T) g(T) - \int_T^U N(t) g'(t) \, dt.$$ -/
theorem sum_nontrivialZetaZerosBetween_eq_stieltjes {T U : ℝ} (hTU : T ≤ U)
    {g g' : ℝ → ℝ}
    (hderiv : ∀ t ∈ Set.Icc T U, HasDerivAt g (g' t) t)
    (hcont : ContinuousOn g' (Set.Icc T U)) :
    (∑ ρ ∈ nontrivialZetaZerosBetween T U, g |ρ.im|) =
      (zeroCountingFunction U : ℝ) * g U - (zeroCountingFunction T : ℝ) * g T -
        ∫ t in T..U, (zeroCountingFunction t : ℝ) * g' t := by
  have h_ind_int :
      (∫ t in Set.Ioc T U,
          ((zeroCountingFunction t : ℝ) - (zeroCountingFunction T : ℝ)) * g' t) =
        ((zeroCountingFunction U : ℝ) - (zeroCountingFunction T : ℝ)) * g U -
          ∑ ρ ∈ nontrivialZetaZerosBetween T U, g |ρ.im| := by
    rw [setIntegral_congr_fun measurableSet_Ioc
        (eqOn_sub_zeroCountingFunction_mul_sum_indicator g'),
      integral_finsetSum (nontrivialZetaZerosBetween T U) fun ρ hρ ↦
        integrableOn_indicator_of_continuousOn
          (mem_nontrivialZetaZerosBetween.mp hρ).2.2
          hcont]
    calc
      (∑ ρ ∈ nontrivialZetaZerosBetween T U,
          ∫ t in Set.Ioc T U, (Set.Ici |ρ.im|).indicator g' t)
        = ∑ ρ ∈ nontrivialZetaZerosBetween T U, (g U - g |ρ.im|) := by
          refine sum_congr rfl fun ρ hρ ↦ ?_
          exact setIntegral_indicator_deriv_eq_sub
            (mem_nontrivialZetaZerosBetween.mp hρ).2.2
            (mem_nontrivialZetaZerosBetween.mp hρ).2.1
            hderiv hcont
      _ = ((zeroCountingFunction U : ℝ) - (zeroCountingFunction T : ℝ)) * g U -
            ∑ ρ ∈ nontrivialZetaZerosBetween T U, g |ρ.im| := by
          rw [sum_sub_distrib, sum_const, nsmul_eq_mul, card_nontrivialZetaZerosBetween_real hTU]
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
  have h_int_N : IntervalIntegrable (fun t : ℝ ↦ (zeroCountingFunction t : ℝ) * g' t) volume T U :=
    intervalIntegrable_zeroCountingFunction_mul hTU hcont
  have h_split :
      (∫ t in Set.Ioc T U,
          ((zeroCountingFunction t : ℝ) - (zeroCountingFunction T : ℝ)) * g' t) =
        (∫ t in T..U, (zeroCountingFunction t : ℝ) * g' t) -
          (zeroCountingFunction T : ℝ) * (g U - g T) := by
    rw [← intervalIntegral.integral_of_le hTU]
    have h_sub_fn :
        (fun t : ℝ ↦ ((zeroCountingFunction t : ℝ) - (zeroCountingFunction T : ℝ)) * g' t) =
          fun t : ℝ ↦
            (zeroCountingFunction t : ℝ) * g' t - (zeroCountingFunction T : ℝ) * g' t := by
      ext t; ring
    rw [h_sub_fn, intervalIntegral.integral_sub h_int_N (h_int_g'.const_mul _),
      intervalIntegral.integral_const_mul, h_ftc]
  linarith

/-- Derivative of `1 / t` at `t ≠ 0` is `-1 / t ^ 2`. -/
theorem hasDerivAt_one_div {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ 1 / x) (-1 / t ^ 2) t := by
  simp only [one_div]
  exact (hasDerivAt_inv ht).congr_deriv (by ring)

/-- **Stieltjes Identity for the Low-Frequency Reciprocal Sum**
`∑_{t₀ < |γ| ≤ T} 1 / |γ|`:
For `0 < t₀ ≤ T`,
$$\sum_{\rho \in \mathcal{Z}(t_0, T)} \frac{1}{|\operatorname{Im} \rho|}
  = \frac{N(T)}{T} - \frac{N(t_0)}{t_0} + \int_{t_0}^T \frac{N(t)}{t^2} \, dt.$$ -/
theorem sum_inv_abs_im_nontrivialZetaZerosBetween_eq {t₀ T : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) :
    (∑ ρ ∈ nontrivialZetaZerosBetween t₀ T, 1 / |ρ.im|) =
      (zeroCountingFunction T : ℝ) / T - (zeroCountingFunction t₀ : ℝ) / t₀ +
        ∫ t in t₀..T, (zeroCountingFunction t : ℝ) / t ^ 2 := by
  have hderiv : ∀ t ∈ Set.Icc t₀ T, HasDerivAt (fun x : ℝ ↦ 1 / x) (-1 / t ^ 2) t :=
    fun t ht ↦ hasDerivAt_one_div (ht₀.trans_le ht.1).ne'
  have hcont : ContinuousOn (fun t : ℝ ↦ -1 / t ^ 2) (Set.Icc t₀ T) := by
    refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    exact continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 ht_pos.ne')
  rw [sum_nontrivialZetaZerosBetween_eq_stieltjes ht₀T hderiv hcont]
  have h_pull :
      (∫ t in t₀..T, (zeroCountingFunction t : ℝ) * (-1 / t ^ 2)) =
        -(∫ t in t₀..T, (zeroCountingFunction t : ℝ) / t ^ 2) := by
    have h_fn :
        (fun t : ℝ ↦ (zeroCountingFunction t : ℝ) * (-1 / t ^ 2)) =
          fun t : ℝ ↦ -((zeroCountingFunction t : ℝ) / t ^ 2) := by
      ext t; ring
    rw [h_fn, intervalIntegral.integral_neg]
  rw [h_pull]
  ring

/-- **Exact Low-Frequency Stieltjes Identity for `nontrivialZetaZerosUpTo T`**:
Whenever `0 < t₀ ≤ T` and `zeroCountingFunction t₀ = 0` (e.g. `t₀ = 6` under `RiemannHypothesis`),
$$\sum_{\rho \in \text{nontrivialZetaZerosUpTo } T} \frac{1}{|\operatorname{Im} \rho|}
  = \frac{N(T)}{T} + \int_{t_0}^T \frac{N(t)}{t^2} \, dt.$$ -/
theorem sum_inv_abs_im_nontrivialZetaZerosUpTo_eq {t₀ T : ℝ}
    (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (h0 : zeroCountingFunction t₀ = 0) :
    (∑ ρ ∈ nontrivialZetaZerosUpTo T, 1 / |ρ.im|) =
      (zeroCountingFunction T : ℝ) / T +
        ∫ t in t₀..T, (zeroCountingFunction t : ℝ) / t ^ 2 := by
  rw [nontrivialZetaZerosUpTo_eq_nontrivialZetaZerosBetween_of_zeroCountingFunction_eq_zero h0,
    sum_inv_abs_im_nontrivialZetaZerosBetween_eq ht₀ ht₀T, h0]
  simp

/-- `(fun t : ℝ ↦ (zeroCountingFunction t : ℝ) / t ^ 2)` is `IntervalIntegrable` on `t₀..T` for
`0 < t₀ ≤ T`. -/
theorem intervalIntegrable_zeroCountingFunction_div_sq {t₀ T : ℝ}
    (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) :
    IntervalIntegrable (fun t : ℝ ↦ (zeroCountingFunction t : ℝ) / t ^ 2) volume t₀ T := by
  have hcont : ContinuousOn (fun t : ℝ ↦ 1 / t ^ 2) (Set.Icc t₀ T) := by
    refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    exact continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 ht_pos.ne')
  have h := intervalIntegrable_zeroCountingFunction_mul ht₀T hcont
  simpa only [mul_one_div] using h

/-- **Closed-Form Evaluation of the Quadratic Riemann–von Mangoldt Stieltjes Integral**:
For `0 < t₀ ≤ T` and any constants `a, C, D : ℝ`,
$$\int_{t_0}^T \frac{a t \log t + C t + D}{t^2} \, dt
  = \left(\frac{a}{2} (\log T)^2 + C \log T - \frac{D}{T}\right)
    - \left(\frac{a}{2} (\log t_0)^2 + C \log t_0 - \frac{D}{t_0}\right).$$ -/
theorem intervalIntegral_riemannVonMangoldt_div_sq {t₀ T : ℝ} (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T)
    (a C D : ℝ) :
    (∫ t : ℝ in t₀..T, (a * t * Real.log t + C * t + D) / t ^ 2) =
      (a / 2 * (Real.log T) ^ 2 + C * Real.log T - D / T) -
        (a / 2 * (Real.log t₀) ^ 2 + C * Real.log t₀ - D / t₀) := by
  have hderiv : ∀ t ∈ Set.uIcc t₀ T,
      HasDerivAt (fun x : ℝ ↦ a / 2 * (Real.log x) ^ 2 + C * Real.log x - D * x⁻¹)
        ((a * t * Real.log t + C * t + D) / t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le ht₀T] at ht
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    have ht_ne : t ≠ 0 := ht_pos.ne'
    have hd_log_sq :
        HasDerivAt (fun x : ℝ ↦ (Real.log x) ^ 2) (2 * (Real.log t) ^ (2 - 1) * t⁻¹) t :=
      (Real.hasDerivAt_log ht_ne).pow 2
    have hd1 : HasDerivAt (fun x : ℝ ↦ a / 2 * (Real.log x) ^ 2)
        (a / 2 * (2 * (Real.log t) ^ (2 - 1) * t⁻¹)) t :=
      hd_log_sq.const_mul (a / 2)
    have hd2 : HasDerivAt (fun x : ℝ ↦ C * Real.log x) (C * t⁻¹) t :=
      (Real.hasDerivAt_log ht_ne).const_mul C
    have hd3 : HasDerivAt (fun x : ℝ ↦ D * x⁻¹) (D * -(t ^ 2)⁻¹) t :=
      (hasDerivAt_inv ht_ne).const_mul D
    refine ((hd1.add hd2).sub hd3).congr_deriv ?_
    field_simp [ht_ne]
    ring
  have hint :
      IntervalIntegrable (fun t : ℝ ↦ (a * t * Real.log t + C * t + D) / t ^ 2) volume t₀ T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht₀T]
    refine (continuousOn_of_forall_continuousAt fun t ht ↦ ?_).integrableOn_Icc
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    have ht_ne : t ≠ 0 := ht_pos.ne'
    refine ContinuousAt.div ?_ (continuousAt_id.pow 2) (pow_ne_zero 2 ht_ne)
    exact (((continuousAt_const.mul continuousAt_id).mul (Real.continuousAt_log ht_ne)).add
      (continuousAt_const.mul continuousAt_id)).add continuousAt_const
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- Whenever `0 < t₀` and `zeroCountingFunction t₀ = 0`, every `ρ ∈ nontrivialZetaZerosUpTo T`
satisfies `1 / ‖ρ‖ ≤ 1 / |ρ.im|`. -/
theorem sum_inv_norm_le_sum_inv_abs_im_nontrivialZetaZerosUpTo {t₀ T : ℝ}
    (ht₀ : 0 < t₀) (h0 : zeroCountingFunction t₀ = 0) :
    (∑ ρ ∈ nontrivialZetaZerosUpTo T, 1 / ‖ρ‖) ≤
      ∑ ρ ∈ nontrivialZetaZerosUpTo T, 1 / |ρ.im| := by
  rw [nontrivialZetaZerosUpTo_eq_nontrivialZetaZerosBetween_of_zeroCountingFunction_eq_zero h0]
  refine Finset.sum_le_sum fun ρ hρ ↦ ?_
  have him_gt : t₀ < |ρ.im| := (mem_nontrivialZetaZerosBetween.mp hρ).2.2
  have him_pos : 0 < |ρ.im| := ht₀.trans him_gt
  exact one_div_le_one_div_of_le him_pos (abs_im_le_norm ρ)

/-- **General Low-Frequency Stieltjes Bound on** `∑_{ρ ∈ Z(T)} 1 / ‖ρ‖`:
If `0 < t₀ ≤ T`, `zeroCountingFunction t₀ = 0`, and
`(zeroCountingFunction t : ℝ) ≤ a * t * Real.log t + C * t + D` for all `t ∈ Set.Icc t₀ T`,
then the `± D / T` boundary and integral terms cancel identically, yielding:
$$\sum_{\rho \in \text{nontrivialZetaZerosUpTo } T} \frac{1}{\|\rho\|}
  \le \frac{a}{2} (\log T)^2 + (a + C) \log T + C + \frac{D}{t_0}
      - \frac{a}{2} (\log t_0)^2 - C \log t_0.$$ -/
theorem sum_inv_norm_nontrivialZetaZerosUpTo_le_of_riemannVonMangoldt {t₀ T a C D : ℝ}
    (ht₀ : 0 < t₀) (ht₀T : t₀ ≤ T) (h0 : zeroCountingFunction t₀ = 0)
    (hN_bound : ∀ t ∈ Set.Icc t₀ T,
      (zeroCountingFunction t : ℝ) ≤ a * t * Real.log t + C * t + D) :
    (∑ ρ ∈ nontrivialZetaZerosUpTo T, 1 / ‖ρ‖) ≤
      a / 2 * (Real.log T) ^ 2 + (a + C) * Real.log T + C + D / t₀ -
        a / 2 * (Real.log t₀) ^ 2 - C * Real.log t₀ := by
  have hT_pos : 0 < T := ht₀.trans_le ht₀T
  have hT_ne : T ≠ 0 := hT_pos.ne'
  refine (sum_inv_norm_le_sum_inv_abs_im_nontrivialZetaZerosUpTo ht₀ h0).trans ?_
  rw [sum_inv_abs_im_nontrivialZetaZerosUpTo_eq ht₀ ht₀T h0]
  have hNT_le : (zeroCountingFunction T : ℝ) / T ≤ a * Real.log T + C + D / T := by
    have hT_in : T ∈ Set.Icc t₀ T := ⟨ht₀T, le_rfl⟩
    have h1 : (zeroCountingFunction T : ℝ) / T ≤ (a * T * Real.log T + C * T + D) / T :=
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
      (∫ t in t₀..T, (zeroCountingFunction t : ℝ) / t ^ 2) ≤
        (a / 2 * (Real.log T) ^ 2 + C * Real.log T - D / T) -
          (a / 2 * (Real.log t₀) ^ 2 + C * Real.log t₀ - D / t₀) := by
    rw [← intervalIntegral_riemannVonMangoldt_div_sq ht₀ ht₀T a C D]
    refine intervalIntegral.integral_mono_on ht₀T
      (intervalIntegrable_zeroCountingFunction_div_sq ht₀ ht₀T) hint_B fun t ht ↦ ?_
    have ht_pos : 0 < t := ht₀.trans_le ht.1
    exact div_le_div_of_nonneg_right (hN_bound t ht) (by positivity)
  linarith

/-- **Complete Discharge of the Low-Frequency Zero-Sum Hypothesis `h_low` (`t₀ = 6`, `T = √x`)**:
Under `RiemannHypothesis`, for all `36 ≤ x` (in particular for `253 < x`), if
`(zeroCountingFunction t : ℝ) ≤ 1 / Real.pi * t * Real.log t + C * t` on `[6, √x]`, then
$$\sum_{\rho \in \text{nontrivialZetaZerosUpTo } \sqrt{x}} \frac{1}{\|\rho\|}
  \le \frac{1}{2\pi} (\log \sqrt{x})^2 + \left(\frac{1}{\pi} + C\right) \log \sqrt{x} + C
      - \frac{1}{2\pi} (\log 6)^2 - C \log 6.$$ -/
theorem sum_inv_norm_nontrivialZetaZerosUpTo_sqrt_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) {x C : ℝ} (hx : 36 ≤ x)
    (hN_low : ∀ t ∈ Set.Icc 6 (Real.sqrt x),
      (zeroCountingFunction t : ℝ) ≤ 1 / Real.pi * t * Real.log t + C * t) :
    (∑ ρ ∈ nontrivialZetaZerosUpTo (Real.sqrt x), 1 / ‖ρ‖) ≤
      1 / (2 * Real.pi) * (Real.log (Real.sqrt x)) ^ 2 +
        (1 / Real.pi + C) * Real.log (Real.sqrt x) + C
        - 1 / (2 * Real.pi) * (Real.log 6) ^ 2 - C * Real.log 6 := by
  have h6_le_sqrt : (6 : ℝ) ≤ Real.sqrt x := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 6)]
    exact Real.sqrt_le_sqrt (by linarith)
  have h := sum_inv_norm_nontrivialZetaZerosUpTo_le_of_riemannVonMangoldt
    (t₀ := 6) (T := Real.sqrt x) (a := 1 / Real.pi) (C := C) (D := 0)
    (by norm_num) h6_le_sqrt (zeroCountingFunction_six_eq_zero hRH)
    (fun t ht ↦ by simpa using hN_low t ht)
  refine h.trans_eq ?_
  ring

/-!
## Section 4: Global Multiplicity-Weighted Bound `N_w(t) ≤ (16 / 5) * t * log t + (11 / 5) * t`
-/

/-- **Multiplicity-Weighted Zero-Counting Function `N_w(U)`**:
The sum of the analytic multiplicities `analyticOrderNatAt riemannZeta ρ` over all nontrivial
zeros `ρ` of `riemannZeta` with `|ρ.im| ≤ U`. -/
noncomputable def weightedZeroCountingFunction (U : ℝ) : ℕ :=
  ∑ ρ ∈ nontrivialZetaZerosUpTo U, analyticOrderNatAt riemannZeta ρ

/-- Every nontrivial zero has multiplicity `≥ 1`, so
`zeroCountingFunction U ≤ weightedZeroCountingFunction U`. -/
theorem zeroCountingFunction_le_weightedZeroCountingFunction (U : ℝ) :
    zeroCountingFunction U ≤ weightedZeroCountingFunction U := by
  unfold zeroCountingFunction weightedZeroCountingFunction
  exact card_le_sum_analyticOrderNatAt_of_isNontrivialZetaZero (nontrivialZetaZerosUpTo U)
    fun ρ hρ ↦ (mem_nontrivialZetaZerosUpTo.mp hρ).1

/-- The open half-plane `{z : ℂ | -3 < z.re}` is preconnected. -/
theorem isPreconnected_neg_three_lt_re : IsPreconnected {z : ℂ | -3 < z.re} := by
  have hConv : Convex ℝ {z : ℂ | -3 < z.re} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, add_re, smul_re, smul_eq_mul] at hx hy ⊢
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · simp only [zero_mul, zero_add] at hab ⊢
      subst hab
      simpa using hy
    · rcases eq_or_lt_of_le hb with rfl | hb_pos
      · simp only [zero_mul, add_zero] at hab ⊢
        subst hab
        simpa using hx
      · have h1 : a * (-3) < a * x.re := mul_lt_mul_of_pos_left hx ha_pos
        have h2 : b * (-3) < b * y.re := mul_lt_mul_of_pos_left hy hb_pos
        linarith
  exact hConv.isPreconnected

/-- **Cleared-Denominator Quartic Euler–Maclaurin Identity on `-3 < s.re`**:
For every `s : ℂ` with `-3 < s.re`,
$$24\,\operatorname{riemannZeta}_1(s)
  = 2 (s + 2) (s + 3) - (s - 1) s (s + 1) (s + 2) (s + 3)
      \operatorname{mellin}\;\text{quarticKernel}\;(-(s + 3)).$$ -/
theorem twenty_four_mul_riemannZeta₁_eq_of_neg_three_lt_re {s : ℂ} (hs : -3 < s.re) :
    24 * riemannZeta₁ s =
      2 * (s + 2) * (s + 3) -
        (s - 1) * s * (s + 1) * (s + 2) * (s + 3) * mellin quarticKernel (-(s + 3)) := by
  have hOpen : IsOpen {z : ℂ | -3 < z.re} := isOpen_lt continuous_const continuous_re
  have hAn1 : AnalyticOnNhd ℂ (fun z : ℂ ↦ 24 * riemannZeta₁ z) {z : ℂ | -3 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z _ ↦ ?_) hOpen
    exact ((differentiableAt_const 24).mul (differentiable_riemannZeta₁ z)).differentiableWithinAt
  have hAn2 : AnalyticOnNhd ℂ
      (fun z : ℂ ↦ 2 * (z + 2) * (z + 3) -
        (z - 1) * z * (z + 1) * (z + 2) * (z + 3) * mellin quarticKernel (-(z + 3)))
      {z : ℂ | -3 < z.re} := by
    refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) hOpen
    refine DifferentiableAt.differentiableWithinAt (DifferentiableAt.sub ?_ ?_)
    · exact (((differentiableAt_const 2).mul (differentiableAt_id.add_const 2)).mul
        (differentiableAt_id.add_const 3))
    · refine DifferentiableAt.mul ?_ ?_
      · exact (((((differentiableAt_id.sub_const 1).mul differentiableAt_id).mul
          (differentiableAt_id.add_const 1)).mul (differentiableAt_id.add_const 2)).mul
          (differentiableAt_id.add_const 3))
      · exact (differentiableAt_mellin_quarticKernel
          (by simp only [neg_re, add_re]; norm_num; linarith [show -3 < z.re from hz])).comp z
          (differentiableAt_id.add_const 3).neg
  have hEv : (fun z : ℂ ↦ 24 * riemannZeta₁ z) =ᶠ[𝓝 (2 : ℂ)]
      (fun z : ℂ ↦ 2 * (z + 2) * (z + 3) -
        (z - 1) * z * (z + 1) * (z + 2) * (z + 3) * mellin quarticKernel (-(z + 3))) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz1 : z ≠ 1 := by intro h; subst h; simp at hz
    have hz1_sub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hz0 : z ≠ 0 := by intro h; subst h; norm_num at hz
    have hza1 : z + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h
      norm_num [Complex.add_re] at this; linarith [show 1 < z.re from hz]
    have hza2 : z + 2 ≠ 0 := by
      intro h; have := congrArg Complex.re h
      norm_num [Complex.add_re] at this; linarith [show 1 < z.re from hz]
    have hza3 : z + 3 ≠ 0 := by
      intro h; have := congrArg Complex.re h
      norm_num [Complex.add_re] at this; linarith [show 1 < z.re from hz]
    have hzeta1 : riemannZeta₁ z = (z - 1) * riemannZeta z := by
      rw [riemannZeta_eq_inv_sub_mul hz1, ← mul_assoc, mul_inv_cancel₀ hz1_sub, one_mul]
    rw [mellin_quarticKernel_neg_add_three_eq_of_one_lt_re hz, hzeta1]
    field_simp [hz1_sub, hz0, hza1, hza2, hza3]
    ring
  exact hAn1.eqOn_of_preconnected_of_eventuallyEq hAn2 isPreconnected_neg_three_lt_re
    (by norm_num : (2 : ℂ) ∈ {z : ℂ | -3 < z.re}) hEv hs

/-- **Uniform Norm Bound on `mellin quarticKernel (-(s + 3))` for `-3 < s.re`**:
For every `s : ℂ` with `-3 < s.re`,
`‖mellin quarticKernel (-(s + 3))‖ ≤ 1 / (16 * (s.re + 3))`. -/
theorem norm_mellin_quarticKernel_neg_add_three_le_of_neg_three_lt_re {s : ℂ} (hs : -3 < s.re) :
    ‖mellin quarticKernel (-(s + 3))‖ ≤ 1 / (16 * (s.re + 3)) := by
  rw [mellin_quarticKernel_neg_add_three_eq]
  have hexp_lt : -(s.re + 4) < -1 := by linarith
  have hint : IntegrableOn (fun t : ℝ ↦ (1 / 16 : ℝ) * t ^ (-(s.re + 4))) (Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt hexp_lt zero_lt_one).const_mul (1 / 16)
  have hnorm_le :
      ‖∫ t in Ioi (1 : ℝ),
        (((t - ⌊t⌋₊) ^ 2 * (1 - (t - ⌊t⌋₊)) ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 4))‖ ≤
      ∫ t in Ioi (1 : ℝ), (1 / 16 : ℝ) * t ^ (-(s.re + 4)) := by
    refine norm_integral_le_of_norm_le hint ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_pos : 0 < t := zero_lt_one.trans ht
    obtain ⟨h0, h1⟩ := quartic_floor_bounds ht_pos.le
    rw [norm_mul, norm_real, Real.norm_of_nonneg h0, norm_cpow_eq_rpow_re_of_pos ht_pos]
    have hre : (-(s + 4)).re = -(s.re + 4) := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht_pos.le _)
  refine hnorm_le.trans_eq ?_
  rw [integral_const_mul, integral_Ioi_rpow_of_lt hexp_lt zero_lt_one, Real.one_rpow]
  have hs3 : s.re + 3 ≠ 0 := by linarith
  have h_exp_add : -(s.re + 4) + 1 = -(s.re + 3) := by ring
  rw [h_exp_add]
  field_simp [hs3]

/-- For every `s : ℂ` with `-14 / 5 ≤ s.re`,
`‖mellin quarticKernel (-(s + 3))‖ ≤ 5 / 16`. -/
theorem norm_mellin_quarticKernel_neg_add_three_le_five_sixteenths {s : ℂ} (hs : -14 / 5 ≤ s.re) :
    ‖mellin quarticKernel (-(s + 3))‖ ≤ 5 / 16 := by
  have hs3 : -3 < s.re := by linarith
  refine (norm_mellin_quarticKernel_neg_add_three_le_of_neg_three_lt_re hs3).trans ?_
  have h_pos : (0 : ℝ) < 16 / 5 := by norm_num
  have h_le : (16 / 5 : ℝ) ≤ 16 * (s.re + 3) := by linarith
  have h_div := one_div_le_one_div_of_le h_pos h_le
  exact h_div.trans_eq (by norm_num)

/-- Summability of `n ↦ 1 / (n + 1 : ℝ) ^ 2` with sum `π ^ 2 / 6`. -/
theorem hasSum_one_div_nat_add_one_sq :
    HasSum (fun n : ℕ ↦ 1 / (n + 1 : ℝ) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

/-- Summability of `n ↦ 1 / (n + 2 : ℝ) ^ 2` with sum `π ^ 2 / 6 - 1`. -/
theorem hasSum_one_div_nat_add_two_sq :
    HasSum (fun n : ℕ ↦ 1 / (n + 2 : ℝ) ^ 2) (Real.pi ^ 2 / 6 - 1) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_one_div_nat_add_one_sq
  convert h using 1
  · ext n
    push_cast
    ring
  · norm_num

/-- Explicit numerical bound `π ^ 2 / 6 - 1 ≤ 3 / 4` (using `Real.pi_lt_d2 : π < 3.15`). -/
theorem pi_sq_div_six_sub_one_le_three_fourths :
    Real.pi ^ 2 / 6 - 1 ≤ 3 / 4 := by
  have hpi_pos : 0 ≤ Real.pi := Real.pi_pos.le
  have hpi_lt : Real.pi < 3.15 := Real.pi_lt_d2
  nlinarith

/-- For `1 < s.re`, `riemannZeta s - 1 = ∑' n : ℕ, 1 / (n + 2 : ℂ) ^ s`. -/
theorem riemannZeta_sub_one_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s - 1 = ∑' n : ℕ, 1 / (n + 2 : ℂ) ^ s := by
  have h_sum : Summable (fun n : ℕ ↦ 1 / (n + 1 : ℂ) ^ s) := by
    have h0 : Summable (fun n : ℕ ↦ 1 / (n : ℂ) ^ s) :=
      Complex.summable_one_div_nat_cpow.mpr hs
    simpa using (summable_nat_add_iff 1).mpr h0
  have h_zeta := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  rw [h_zeta, h_sum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_add, one_cpow, div_one, add_sub_cancel_left]
  refine tsum_congr fun n ↦ ?_
  push_cast
  ring_nf

/-- For every `s : ℂ` with `2 ≤ s.re` and every `n : ℕ`,
`‖1 / (n + 2 : ℂ) ^ s‖ ≤ 1 / (n + 2 : ℝ) ^ 2`. -/
theorem norm_one_div_nat_add_two_cpow_le {s : ℂ} (hs : 2 ≤ s.re) (n : ℕ) :
    ‖1 / (n + 2 : ℂ) ^ s‖ ≤ 1 / (n + 2 : ℝ) ^ 2 := by
  have hn_pos : (0 : ℝ) < n + 2 := by positivity
  have hn_ge_one : (1 : ℝ) ≤ n + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have h_cast : (n + 2 : ℂ) = ((n + 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [norm_div, norm_one, h_cast, norm_cpow_eq_rpow_re_of_pos hn_pos]
  have hrpow : (n + 2 : ℝ) ^ (2 : ℝ) ≤ (n + 2 : ℝ) ^ s.re :=
    Real.rpow_le_rpow_of_exponent_le hn_ge_one hs
  have hrpow_sq : (n + 2 : ℝ) ^ (2 : ℝ) = (n + 2 : ℝ) ^ 2 := Real.rpow_two (n + 2 : ℝ)
  rw [← hrpow_sq]
  exact one_div_le_one_div_of_le (by positivity) hrpow

/-- For every `s : ℂ` with `2 ≤ s.re`, `‖riemannZeta s - 1‖ ≤ 3 / 4`. -/
theorem norm_riemannZeta_sub_one_le_three_fourths {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ 3 / 4 := by
  have hs1 : 1 < s.re := by linarith
  rw [riemannZeta_sub_one_eq_tsum hs1]
  have h_sum_real : Summable (fun n : ℕ ↦ 1 / (n + 2 : ℝ) ^ 2) :=
    hasSum_one_div_nat_add_two_sq.summable
  have h_sum_norm : Summable (fun n : ℕ ↦ ‖1 / (n + 2 : ℂ) ^ s‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      (norm_one_div_nat_add_two_cpow_le hs) h_sum_real
  calc
    ‖∑' n : ℕ, 1 / (n + 2 : ℂ) ^ s‖
      ≤ ∑' n : ℕ, ‖1 / (n + 2 : ℂ) ^ s‖ := norm_tsum_le_tsum_norm h_sum_norm
    _ ≤ ∑' n : ℕ, 1 / (n + 2 : ℝ) ^ 2 :=
        h_sum_norm.tsum_le_tsum (norm_one_div_nat_add_two_cpow_le hs) h_sum_real
    _ = Real.pi ^ 2 / 6 - 1 := hasSum_one_div_nat_add_two_sq.tsum_eq
    _ ≤ 3 / 4 := pi_sq_div_six_sub_one_le_three_fourths

/-- For every `s : ℂ` with `2 ≤ s.re`, `1 / 4 ≤ ‖riemannZeta s‖`. -/
theorem one_fourth_le_norm_riemannZeta_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    1 / 4 ≤ ‖riemannZeta s‖ := by
  have h_norm := norm_riemannZeta_sub_one_le_three_fourths hs
  have h_tri : ‖(1 : ℂ)‖ ≤ ‖riemannZeta s‖ + ‖riemannZeta s - 1‖ := by
    have h := norm_sub_le (riemannZeta s) (riemannZeta s - 1)
    simpa using h
  rw [norm_one] at h_tri
  linarith

/-- For every `y : ℝ`,
`1 / 4 * ‖(1 : ℂ) + (y : ℂ) * I‖ ≤ ‖riemannZeta₁ (2 + (y : ℂ) * I)‖`. -/
theorem one_fourth_mul_norm_le_norm_riemannZeta₁_two_add_mul_I (y : ℝ) :
    1 / 4 * ‖(1 : ℂ) + (y : ℂ) * I‖ ≤ ‖riemannZeta₁ (2 + (y : ℂ) * I)‖ := by
  have hc_ne_one : (2 : ℂ) + (y : ℂ) * I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hc_sub : (2 : ℂ) + (y : ℂ) * I - 1 = (1 : ℂ) + (y : ℂ) * I := by ring
  have hc_sub_ne : (2 : ℂ) + (y : ℂ) * I - 1 ≠ 0 := sub_ne_zero.mpr hc_ne_one
  have hzeta1 : riemannZeta₁ (2 + (y : ℂ) * I) =
      ((1 : ℂ) + (y : ℂ) * I) * riemannZeta (2 + (y : ℂ) * I) := by
    rw [riemannZeta_eq_inv_sub_mul hc_ne_one, ← hc_sub, ← mul_assoc,
      mul_inv_cancel₀ hc_sub_ne, one_mul]
  rw [hzeta1, norm_mul, mul_comm (1 / 4)]
  exact mul_le_mul_of_nonneg_left
    (one_fourth_le_norm_riemannZeta_of_two_le_re (by simp))
    (norm_nonneg _)

/-- For every `y : ℝ`, `1 ≤ ‖(1 : ℂ) + (y : ℂ) * I‖` and `|y| ≤ ‖(1 : ℂ) + (y : ℂ) * I‖`. -/
theorem one_and_abs_le_norm_one_add_mul_I (y : ℝ) :
    1 ≤ ‖(1 : ℂ) + (y : ℂ) * I‖ ∧ |y| ≤ ‖(1 : ℂ) + (y : ℂ) * I‖ := by
  refine ⟨?_, ?_⟩
  · have h := abs_re_le_norm ((1 : ℂ) + (y : ℂ) * I)
    simpa using h
  · have h := abs_im_le_norm ((1 : ℂ) + (y : ℂ) * I)
    simpa using h

/-- For every `y : ℝ`, `riemannZeta₁ (2 + (y : ℂ) * I) ≠ 0`. -/
theorem riemannZeta₁_two_add_mul_I_ne_zero (y : ℝ) :
    riemannZeta₁ (2 + (y : ℂ) * I) ≠ 0 := by
  have h1 := (one_and_abs_le_norm_one_add_mul_I y).1
  have h2 := one_fourth_mul_norm_le_norm_riemannZeta₁_two_add_mul_I y
  exact norm_pos_iff.mp (by linarith)

/-- For `8 ≤ |y|` and `z ∈ closedBall (2 + (y : ℂ) * I) (24 / 5)`,
`-14 / 5 ≤ z.re`, `‖z - 1‖ ≤ (8 / 5) * ‖(1 : ℂ) + (y : ℂ) * I‖`, and for `0 ≤ a ≤ 3`,
`‖z + (a : ℂ)‖ ≤ (3 / 2) * (|y| + 4)`. -/
theorem closedBall_two_add_mul_I_bounds {y : ℝ} (hy : 8 ≤ |y|) {z : ℂ}
    (hz : z ∈ closedBall (2 + (y : ℂ) * I) (24 / 5)) :
    -14 / 5 ≤ z.re ∧
      ‖z - 1‖ ≤ (8 / 5) * ‖(1 : ℂ) + (y : ℂ) * I‖ ∧
      ∀ a : ℝ, 0 ≤ a → a ≤ 3 → ‖z + (a : ℂ)‖ ≤ (3 / 2) * (|y| + 4) := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hy_norm : 8 ≤ ‖(1 : ℂ) + (y : ℂ) * I‖ :=
    hy.trans (one_and_abs_le_norm_one_add_mul_I y).2
  refine ⟨?_, ?_, ?_⟩
  · have hre_diff : |(z - (2 + (y : ℂ) * I)).re| ≤ 24 / 5 :=
      (abs_re_le_norm _).trans hz
    have hre_eq : (z - (2 + (y : ℂ) * I)).re = z.re - 2 := by simp
    rw [hre_eq] at hre_diff
    linarith [(abs_le.mp hre_diff).1]
  · have h_decomp : z - 1 = (z - (2 + (y : ℂ) * I)) + ((1 : ℂ) + (y : ℂ) * I) := by ring
    have h_tri : ‖z - 1‖ ≤ ‖z - (2 + (y : ℂ) * I)‖ + ‖(1 : ℂ) + (y : ℂ) * I‖ := by
      rw [h_decomp]
      exact norm_add_le _ _
    linarith
  · intro a ha0 ha3
    have h_decomp : z + (a : ℂ) =
        (z - (2 + (y : ℂ) * I)) + (((2 + a : ℝ) : ℂ) + (y : ℂ) * I) := by
      push_cast
      ring
    have h_tri1 : ‖z + (a : ℂ)‖ ≤
        ‖z - (2 + (y : ℂ) * I)‖ + ‖((2 + a : ℝ) : ℂ) + (y : ℂ) * I‖ := by
      rw [h_decomp]
      exact norm_add_le _ _
    have h_tri2 : ‖((2 + a : ℝ) : ℂ) + (y : ℂ) * I‖ ≤ (2 + a) + |y| := by
      refine (norm_add_le _ _).trans ?_
      have h1 : ‖((2 + a : ℝ) : ℂ)‖ = 2 + a := by
        rw [norm_real, Real.norm_of_nonneg (by linarith)]
      have h2 : ‖(y : ℂ) * I‖ = |y| := by
        rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
      linarith
    linarith

/-- **Key Ratio Bound on `closedBall (2 + (y : ℂ) * I) (24 / 5)` for `8 ≤ |y|`**:
For every `y : ℝ` with `8 ≤ |y|` and every `z ∈ closedBall (2 + (y : ℂ) * I) (24 / 5)`,
`‖riemannZeta₁ z‖ ≤ ‖riemannZeta₁ (2 + (y : ℂ) * I)‖ * (|y| + 4) ^ 4`. -/
theorem norm_riemannZeta₁_le_on_closedBall_two_add_mul_I {y : ℝ} (hy : 8 ≤ |y|) {z : ℂ}
    (hz : z ∈ closedBall (2 + (y : ℂ) * I) (24 / 5)) :
    ‖riemannZeta₁ z‖ ≤ ‖riemannZeta₁ (2 + (y : ℂ) * I)‖ * (|y| + 4) ^ 4 := by
  obtain ⟨hz_re, hz1, hza⟩ := closedBall_two_add_mul_I_bounds hy hz
  have hz0 : ‖z‖ ≤ (3 / 2) * (|y| + 4) := by simpa using hza 0 le_rfl (by norm_num)
  have hza1 : ‖z + 1‖ ≤ (3 / 2) * (|y| + 4) := by simpa using hza 1 (by norm_num) (by norm_num)
  have hza2 : ‖z + 2‖ ≤ (3 / 2) * (|y| + 4) := by simpa using hza 2 (by norm_num) (by norm_num)
  have hza3 : ‖z + 3‖ ≤ (3 / 2) * (|y| + 4) := by simpa using hza 3 (by norm_num) le_rfl
  have hmellin : ‖mellin quarticKernel (-(z + 3))‖ ≤ 5 / 16 :=
    norm_mellin_quarticKernel_neg_add_three_le_five_sixteenths hz_re
  have hid := congrArg norm (twenty_four_mul_riemannZeta₁_eq_of_neg_three_lt_re
    (by linarith : -3 < z.re))
  rw [norm_mul, norm_ofNat] at hid
  have h_rhs :
      ‖2 * (z + 2) * (z + 3) -
        (z - 1) * z * (z + 1) * (z + 2) * (z + 3) * mellin quarticKernel (-(z + 3))‖ ≤
        2 * ‖z + 2‖ * ‖z + 3‖ +
          ‖z - 1‖ * ‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖ * ‖mellin quarticKernel (-(z + 3))‖ := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · simp only [norm_mul, norm_ofNat, le_rfl]
    · simp only [norm_mul, le_rfl]
  let B : ℝ := (3 / 2) * (|y| + 4)
  let K : ℝ := ‖(1 : ℂ) + (y : ℂ) * I‖
  have hB_nonneg : 0 ≤ B := by positivity
  have hK_ge : 8 ≤ K := hy.trans (one_and_abs_le_norm_one_add_mul_I y).2
  have h_prod2 : ‖z + 2‖ * ‖z + 3‖ ≤ B ^ 2 := by
    rw [sq]
    exact mul_le_mul hza2 hza3 (norm_nonneg _) hB_nonneg
  have h_prod4 : ‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖ ≤ B ^ 4 := by
    have hp12 : ‖z‖ * ‖z + 1‖ ≤ B ^ 2 := by
      rw [sq]
      exact mul_le_mul hz0 hza1 (norm_nonneg _) hB_nonneg
    calc
      ‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖
        = (‖z‖ * ‖z + 1‖) * (‖z + 2‖ * ‖z + 3‖) := by ring
      _ ≤ B ^ 2 * B ^ 2 := mul_le_mul hp12 h_prod2 (by positivity) (by positivity)
      _ = B ^ 4 := by ring
  have h_prod6 :
      ‖z - 1‖ * ‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖ * ‖mellin quarticKernel (-(z + 3))‖ ≤
        (8 / 5) * K * B ^ 4 * (5 / 16) := by
    have hp5 : ‖z - 1‖ * (‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖) ≤ (8 / 5) * K * B ^ 4 :=
      mul_le_mul hz1 h_prod4 (by positivity) (by positivity)
    calc
      ‖z - 1‖ * ‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖ * ‖mellin quarticKernel (-(z + 3))‖
        = (‖z - 1‖ * (‖z‖ * ‖z + 1‖ * ‖z + 2‖ * ‖z + 3‖)) * ‖mellin quarticKernel (-(z + 3))‖ := by
          ring
      _ ≤ ((8 / 5) * K * B ^ 4) * (5 / 16) :=
          mul_le_mul hp5 hmellin (norm_nonneg _) (by positivity)
  have h_y4_sq : 144 ≤ (|y| + 4) ^ 2 := by nlinarith
  have h_B2_le : 2 * B ^ 2 ≤ (1 / 2) * K * (|y| + 4) ^ 4 := by
    have hB2_eq : 2 * B ^ 2 = (9 / 2) * (|y| + 4) ^ 2 := by
      dsimp only [B]
      ring
    rw [hB2_eq]
    have h1 : (9 / 2) * (|y| + 4) ^ 2 * 144 ≤ (9 / 2) * (|y| + 4) ^ 2 * (|y| + 4) ^ 2 :=
      mul_le_mul_of_nonneg_left h_y4_sq (by positivity)
    have h2 : (|y| + 4) ^ 4 ≤ (1 / 8) * K * (|y| + 4) ^ 4 := by
      have hK8 : 1 ≤ (1 / 8) * K := by linarith
      nlinarith [pow_nonneg (by positivity : 0 ≤ |y| + 4) 4]
    nlinarith
  have h_B4_eq : (8 / 5) * K * B ^ 4 * (5 / 16) = (81 / 32) * K * (|y| + 4) ^ 4 := by
    dsimp only [B]
    ring
  have h24_le : 24 * ‖riemannZeta₁ z‖ ≤ 6 * K * (|y| + 4) ^ 4 := by
    have h_K_y4 : 0 ≤ K * (|y| + 4) ^ 4 := by positivity
    linarith
  have h_zeta1_c := one_fourth_mul_norm_le_norm_riemannZeta₁_two_add_mul_I y
  have h_y4_nonneg : 0 ≤ (|y| + 4) ^ 4 := by positivity
  have h_c_mul :
      (1 / 4 * K) * (|y| + 4) ^ 4 ≤ ‖riemannZeta₁ (2 + (y : ℂ) * I)‖ * (|y| + 4) ^ 4 :=
    mul_le_mul_of_nonneg_right h_zeta1_c h_y4_nonneg
  linarith

/-- **Nontrivial Zeros in the Height-4 Window `[y - 2, y + 2]`**:
The `Finset ℂ` of nontrivial zeros `ρ` of `riemannZeta` with `y - 2 ≤ ρ.im ≤ y + 2`. -/
noncomputable def nontrivialZetaZerosInFourWindow (y : ℝ) : Finset ℂ :=
  (nontrivialZetaZerosUpTo (|y| + 2)).filter (fun ρ ↦ y - 2 ≤ ρ.im ∧ ρ.im ≤ y + 2)

@[simp]
theorem mem_nontrivialZetaZerosInFourWindow {y : ℝ} {ρ : ℂ} :
    ρ ∈ nontrivialZetaZerosInFourWindow y ↔
      IsNontrivialZetaZero ρ ∧ y - 2 ≤ ρ.im ∧ ρ.im ≤ y + 2 := by
  simp only [nontrivialZetaZerosInFourWindow, mem_filter, mem_nontrivialZetaZerosUpTo]
  refine ⟨fun ⟨⟨h1, _⟩, h3, h4⟩ ↦ ⟨h1, h3, h4⟩, fun ⟨h1, h3, h4⟩ ↦ ⟨⟨h1, ?_⟩, h3, h4⟩⟩
  rw [abs_le]
  have hy := le_abs_self y
  have hny := neg_le_abs y
  constructor <;> linarith

/-- Under `RiemannHypothesis`, every nontrivial zero `ρ ∈ nontrivialZetaZerosInFourWindow y`
lies in `closedBall (2 + (y : ℂ) * I) |(5 / 2 : ℝ)|`. -/
theorem mem_closedBall_two_add_mul_I_five_halves_of_riemannHypothesis
    (hRH : RiemannHypothesis) (y : ℝ) {ρ : ℂ}
    (hρ : ρ ∈ nontrivialZetaZerosInFourWindow y) :
    ρ ∈ closedBall (2 + (y : ℂ) * I) |(5 / 2 : ℝ)| := by
  rw [mem_nontrivialZetaZerosInFourWindow] at hρ
  obtain ⟨h_nt, h_lo, h_hi⟩ := hρ
  have hre : ρ.re = 1 / 2 := hRH ρ h_nt.1 h_nt.2.1 h_nt.2.2
  rw [mem_closedBall, dist_eq_norm, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2)]
  rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply]
  have h_re_sub : (ρ - (2 + (y : ℂ) * I)).re = -3 / 2 := by simp [hre]; ring
  have h_im_sub : (ρ - (2 + (y : ℂ) * I)).im = ρ.im - y := by simp
  rw [h_re_sub, h_im_sub]
  have him_sq : (ρ.im - y) ^ 2 ≤ 2 ^ 2 := by nlinarith
  nlinarith

/-- Explicit rational lower bound `41 / 64 ≤ Real.log (48 / 25)` proved via
`((64 / 63 : ℝ) ^ 41) ≤ 48 / 25` and `Real.one_sub_inv_le_log_of_pos`. -/
theorem forty_one_div_sixty_four_le_log_forty_eight_div_twenty_five :
    (41 / 64 : ℝ) ≤ Real.log (48 / 25) := by
  have h_step : (1 / 64 : ℝ) ≤ Real.log (64 / 63) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 64 / 63)
    norm_num at h
    exact h
  have h_pow : ((64 / 63 : ℝ) ^ 41) ≤ 48 / 25 := by norm_num
  have h_log_pow : Real.log ((64 / 63 : ℝ) ^ 41) ≤ Real.log (48 / 25) :=
    Real.log_le_log (by positivity) h_pow
  rw [Real.log_pow] at h_log_pow
  linarith

/-- Explicit rational upper bound `Real.log 2 ≤ 31 / 44` proved via
`2 ≤ (45 / 44 : ℝ) ^ 31` and `Real.log_le_sub_one_of_pos`. -/
theorem log_two_le_forty_four_div_sixty_three :
    Real.log 2 ≤ 31 / 44 := by
  have h_step : Real.log (45 / 44) ≤ 1 / 44 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 45 / 44)
    linarith
  have h_pow : (2 : ℝ) ≤ (45 / 44 : ℝ) ^ 31 := by norm_num
  have h_log_pow : Real.log 2 ≤ Real.log ((45 / 44 : ℝ) ^ 31) :=
    Real.log_le_log (by norm_num) h_pow
  rw [Real.log_pow] at h_log_pow
  linarith

/-- **Local Height-4 Window Multiplicity Bound via Jensen's Formula (`r = 5 / 2`, `R = 24 / 5`)**:
Under `RiemannHypothesis`, for every `y : ℝ` with `8 ≤ |y|`,
$$\sum_{\rho \in \text{nontrivialZetaZerosInFourWindow } y}
  \operatorname{analyticOrderNatAt}\;\zeta\;\rho \le \frac{256}{41} \log(|y| + 4).$$ -/
theorem sum_analyticOrderNatAt_fourWindow_le_of_riemannHypothesis
    (hRH : RiemannHypothesis) {y : ℝ} (hy : 8 ≤ |y|) :
    ((∑ ρ ∈ nontrivialZetaZerosInFourWindow y, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
      (256 / 41) * Real.log (|y| + 4) := by
  let c : ℂ := 2 + (y : ℂ) * I
  let M : ℝ := ‖riemannZeta₁ c‖ * (|y| + 4) ^ 4
  have hc_norm_ge : 2 ≤ ‖riemannZeta₁ c‖ := by
    have h1 := (one_and_abs_le_norm_one_add_mul_I y).2
    have h2 := one_fourth_mul_norm_le_norm_riemannZeta₁_two_add_mul_I y
    linarith
  have hc_pos : 0 < ‖riemannZeta₁ c‖ := by linarith
  have hy4_ge : 12 ≤ |y| + 4 := by linarith
  have hy4_pos : 0 < |y| + 4 := by linarith
  have hM_ge_one : 1 ≤ M := by
    dsimp only [M]
    have hp : (1 : ℝ) ≤ (|y| + 4) ^ 4 := one_le_pow₀ (by linarith)
    nlinarith
  have hf_bound : ∀ z ∈ sphere c |(24 / 5 : ℝ)|, ‖riemannZeta₁ z‖ ≤ M := by
    intro z hz
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 24 / 5)] at hz
    exact norm_riemannZeta₁_le_on_closedBall_two_add_mul_I hy (sphere_subset_closedBall hz)
  have h_div :
      ((∑ ρ ∈ nontrivialZetaZerosInFourWindow y, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
        ((∑ᶠ u, divisor riemannZeta₁ (closedBall c |(5 / 2 : ℝ)|) u : ℤ) : ℝ) := by
    refine sum_analyticOrderNatAt_le_finsum_divisor_riemannZeta₁
      (nontrivialZetaZerosInFourWindow y) c (5 / 2) fun ρ hρ ↦ ?_
    exact ⟨mem_closedBall_two_add_mul_I_five_halves_of_riemannHypothesis hRH y hρ,
      (mem_nontrivialZetaZerosInFourWindow.mp hρ).1.2.2⟩
  have h_jensen :=
    (analyticOnNhd_riemannZeta₁ (closedBall c |(24 / 5 : ℝ)|)).sum_divisor_le
      (r := 5 / 2) (by norm_num) (by norm_num) hM_ge_one (riemannZeta₁_two_add_mul_I_ne_zero y)
      hf_bound
  refine (h_div.trans h_jensen).trans ?_
  have h_log_num : Real.log (M / ‖riemannZeta₁ c‖) = 4 * Real.log (|y| + 4) := by
    dsimp only [M]
    rw [mul_div_cancel_left₀ _ hc_pos.ne', Real.log_pow]
    ring
  have h_ratio : (24 / 5 : ℝ) / (5 / 2) = 48 / 25 := by norm_num
  rw [h_log_num, h_ratio]
  have h_log_nonneg : 0 ≤ 4 * Real.log (|y| + 4) := by
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))
  have h_den := forty_one_div_sixty_four_le_log_forty_eight_div_twenty_five
  have h_div_le :
      4 * Real.log (|y| + 4) / Real.log (48 / 25) ≤ 4 * Real.log (|y| + 4) / (41 / 64) :=
    div_le_div_of_nonneg_left h_log_nonneg (by norm_num) h_den
  refine h_div_le.trans_eq ?_
  ring

/-- Subadditivity of `ℕ`-valued `Finset.sum` over binary union. -/
theorem sum_union_le_nat {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α) (f : α → ℕ) :
    ∑ x ∈ s₁ ∪ s₂, f x ≤ ∑ x ∈ s₁, f x + ∑ x ∈ s₂, f x := by
  have h := Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := f)
  omega

/-- Subadditivity of `ℕ`-valued `Finset.sum` over `Finset.biUnion` on `Finset.range n`. -/
theorem sum_biUnion_range_le_nat {α : Type*} [DecidableEq α] (n : ℕ) (g : ℕ → Finset α)
    (f : α → ℕ) :
    ∑ x ∈ (Finset.range n).biUnion g, f x ≤ ∑ k ∈ Finset.range n, ∑ x ∈ g k, f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert, Finset.sum_insert Finset.notMem_range_self]
    have h_u := sum_union_le_nat (g n) ((Finset.range n).biUnion g) f
    omega

/-- Under `RiemannHypothesis`, for any `t : ℝ`, every `ρ ∈ nontrivialZetaZerosUpTo t` belongs to one
of the `2 * (⌊(t - 6) / 4⌋₊ + 1)` height-4 windows centered at `±(8 + 4 * k)` for
`k < ⌊(t - 6) / 4⌋₊ + 1`. -/
theorem nontrivialZetaZerosUpTo_subset_biUnion_fourWindows
    (hRH : RiemannHypothesis) (t : ℝ) :
    nontrivialZetaZerosUpTo t ⊆
      (Finset.range (⌊(t - 6) / 4⌋₊ + 1)).biUnion
        (fun k ↦ nontrivialZetaZerosInFourWindow (8 + 4 * (k : ℝ)) ∪
          nontrivialZetaZerosInFourWindow (-(8 + 4 * (k : ℝ)))) := by
  intro ρ hρ
  rw [mem_nontrivialZetaZerosUpTo] at hρ
  obtain ⟨h_nt, him_le⟩ := hρ
  have him_gt : 6 < |ρ.im| := six_lt_abs_im_of_riemannHypothesis hRH h_nt
  let k : ℕ := ⌊(|ρ.im| - 6) / 4⌋₊
  have hk_nonneg : 0 ≤ (|ρ.im| - 6) / 4 := by linarith
  have hk_le_floor : k ≤ ⌊(t - 6) / 4⌋₊ :=
    Nat.floor_le_floor (by linarith)
  have hk_lt : k < ⌊(t - 6) / 4⌋₊ + 1 := Nat.lt_succ_of_le hk_le_floor
  have hk_lo : (k : ℝ) ≤ (|ρ.im| - 6) / 4 := Nat.floor_le hk_nonneg
  have hk_hi : (|ρ.im| - 6) / 4 < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [Finset.mem_biUnion]
  refine ⟨k, Finset.mem_range.mpr hk_lt, ?_⟩
  rw [Finset.mem_union, mem_nontrivialZetaZerosInFourWindow, mem_nontrivialZetaZerosInFourWindow]
  rcases le_or_gt 0 ρ.im with him_nonneg | him_neg
  · left
    rw [abs_of_nonneg him_nonneg] at hk_lo hk_hi
    refine ⟨h_nt, by linarith, by linarith⟩
  · right
    rw [abs_of_neg him_neg] at hk_lo hk_hi
    refine ⟨h_nt, by linarith, by linarith⟩

/-- **Global Multiplicity-Weighted Riemann–von Mangoldt Upper Bound Under `RiemannHypothesis`**:
Under `RiemannHypothesis`, for all `6 ≤ t`,
`(weightedZeroCountingFunction t : ℝ) ≤ (16 / 5) * t * Real.log t + (11 / 5) * t`. -/
theorem weightedZeroCountingFunction_le_sixteen_fifths
    (hRH : RiemannHypothesis) {t : ℝ} (ht : 6 ≤ t) :
    (weightedZeroCountingFunction t : ℝ) ≤ (16 / 5) * t * Real.log t + (11 / 5) * t := by
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
  have h_log_t_pos : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have h_log_two_pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h_wk_bound : ∀ k ∈ Finset.range K,
      ((∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) ≤
        (512 / 41) * (Real.log t + Real.log 2) := by
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
    have hb1 := sum_analyticOrderNatAt_fourWindow_le_of_riemannHypothesis hRH hy1
    have hb2 := sum_analyticOrderNatAt_fourWindow_le_of_riemannHypothesis hRH hy2
    rw [abs_neg] at hb2
    have h_abs_add : |8 + 4 * (k : ℝ)| + 4 ≤ 2 * t := by
      rw [abs_of_nonneg (by positivity)]
      linarith
    have h_log_le : Real.log (|8 + 4 * (k : ℝ)| + 4) ≤ Real.log t + Real.log 2 := by
      have h1 : Real.log (|8 + 4 * (k : ℝ)| + 4) ≤ Real.log (2 * t) :=
        Real.log_le_log (by positivity) h_abs_add
      rw [Real.log_mul (by norm_num) ht_pos.ne'] at h1
      linarith
    linarith
  have h_sum_le :
      (∑ k ∈ Finset.range K, ((∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ)) ≤
        (K : ℝ) * ((512 / 41) * (Real.log t + Real.log 2)) := by
    calc
      (∑ k ∈ Finset.range K, ((∑ ρ ∈ W k, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ))
        ≤ ∑ _k ∈ Finset.range K, (512 / 41) * (Real.log t + Real.log 2) :=
          Finset.sum_le_sum h_wk_bound
      _ = (K : ℝ) * ((512 / 41) * (Real.log t + Real.log 2)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hK_le : (K : ℝ) ≤ t / 4 := by
    dsimp only [K]
    push_cast
    have hfl : (⌊(t - 6) / 4⌋₊ : ℝ) ≤ (t - 6) / 4 := Nat.floor_le (by linarith)
    linarith
  have h_prod_le :
      (K : ℝ) * ((512 / 41) * (Real.log t + Real.log 2)) ≤
        (t / 4) * ((512 / 41) * (Real.log t + Real.log 2)) :=
    mul_le_mul_of_nonneg_right hK_le (by positivity)
  have h_log2 := log_two_le_forty_four_div_sixty_three
  nlinarith

/-- **Global Unweighted Riemann–von Mangoldt Upper Bound Under `RiemannHypothesis`**:
Under `RiemannHypothesis`, for all `6 ≤ t`,
`(zeroCountingFunction t : ℝ) ≤ (16 / 5) * t * Real.log t + (11 / 5) * t`. -/
theorem zeroCountingFunction_le_sixteen_fifths
    (hRH : RiemannHypothesis) {t : ℝ} (ht : 6 ≤ t) :
    (zeroCountingFunction t : ℝ) ≤ (16 / 5) * t * Real.log t + (11 / 5) * t := by
  have h1 : (zeroCountingFunction t : ℝ) ≤ (weightedZeroCountingFunction t : ℝ) := by
    exact_mod_cast zeroCountingFunction_le_weightedZeroCountingFunction t
  exact h1.trans (weightedZeroCountingFunction_le_sixteen_fifths hRH ht)

/-- Under `RiemannHypothesis`, `weightedZeroCountingFunction T = 0` for all `T ≤ 6`. -/
theorem weightedZeroCountingFunction_eq_zero_of_le_six (hRH : RiemannHypothesis) {T : ℝ}
    (hT : T ≤ 6) :
    weightedZeroCountingFunction T = 0 := by
  unfold weightedZeroCountingFunction
  rw [nontrivialZetaZerosUpTo_eq_empty_of_le_six hRH hT, Finset.sum_empty]

/-- **Unconditional-under-RH Low-Frequency Zero-Sum Bound (`6 ≤ T`)**:
Combining `zeroCountingFunction_le_sixteen_fifths` with Stieltjes integration by parts
(`sum_inv_norm_nontrivialZetaZerosUpTo_le_of_riemannVonMangoldt`) gives for all `6 ≤ T`:
$$\sum_{\rho \in \text{nontrivialZetaZerosUpTo } T} \frac{1}{\|\rho\|}
  \le \frac{8}{5} (\log T)^2 + \frac{27}{5} \log T + \frac{11}{5}
      - \frac{8}{5} (\log 6)^2 - \frac{11}{5} \log 6.$$ -/
theorem sum_inv_norm_nontrivialZetaZerosUpTo_le_sixteen_fifths_of_riemannHypothesis
    (hRH : RiemannHypothesis) {T : ℝ} (hT : 6 ≤ T) :
    (∑ ρ ∈ nontrivialZetaZerosUpTo T, 1 / ‖ρ‖) ≤
      (8 / 5) * (Real.log T) ^ 2 + (27 / 5) * Real.log T + 11 / 5 -
        (8 / 5) * (Real.log 6) ^ 2 - (11 / 5) * Real.log 6 := by
  have h := sum_inv_norm_nontrivialZetaZerosUpTo_le_of_riemannVonMangoldt
    (t₀ := 6) (T := T) (a := 16 / 5) (C := 11 / 5) (D := 0)
    (by norm_num) hT (zeroCountingFunction_six_eq_zero hRH)
    (fun t ht ↦ by simpa using zeroCountingFunction_le_sixteen_fifths hRH ht.1)
  refine h.trans_eq ?_
  ring

end ConjectureMachines.Riemann543.Semantics.VonMangoldtCount
