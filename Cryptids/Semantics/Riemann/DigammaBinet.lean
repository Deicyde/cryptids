/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZetaLogDeriv
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Binet / Euler–Maclaurin Formula for `Complex.digamma` & Left-Vertical `logDeriv riemannZeta` Bound

This standalone file proves **with zero `sorry`s** the complete 1D calculus and complex-analytic
chain for the Binet / Euler–Maclaurin representation of `Complex.digamma`, explicit bounds on
`‖Complex.digamma s - Complex.log s‖` across the right half-plane `0 < s.re`, and the resulting
explicit vertical-growth bound on `‖logDeriv riemannZeta (-1 / 4 + t * I)‖` for all `t : ℝ`:

1. **Real `digamma` Sandwich from `Real.convexOn_log_Gamma` (Bohr–Mollerup Convexity)**:
   - For all real `x > 0`, `Complex.digamma (x : ℂ) = (deriv (Real.log ∘ Real.Gamma) x : ℂ)`.
   - Applying `ConvexOn.slope_le_deriv` and `ConvexOn.deriv_le_slope` to
     `Real.convexOn_log_Gamma : ConvexOn ℝ (Ioi 0) (Real.log ∘ Real.Gamma)` yields for all `x > 0`:
     $$\log x \le \operatorname{Re}\psi(x + 1) \le \log(x + 1), \qquad
       \log x - \frac{1}{x} \le \operatorname{Re}\psi(x) \le \log x,$$
     and therefore $\|\psi(x) - \log x\| \le \frac{1}{x}$ and
     $$\lim_{n \to \infty} \bigl(\psi(x + n) - \log(x + n)\bigr) = 0.$$

2. **Euler–Maclaurin / Binet Integral Representation of `Complex.digamma s` (`0 < s.re`)**:
   - On each unit interval $[k, k + 1]$, exact integration by parts with antiderivative
     $\operatorname{log}(s + t) - \frac{t - k - 1/2}{s + t}$ gives:
     $$\int_k^{k+1} \frac{t - k - 1/2}{(s + t)^2} \, dt
       = \log(s + k + 1) - \log(s + k) - \frac{1}{2(s + k + 1)} - \frac{1}{2(s + k)}.$$
   - Summing over $k \in \operatorname{Finset.range} n$ telescopes to:
     $$\int_0^n \frac{t - \lfloor t \rfloor - 1/2}{(s + t)^2} \, dt
       = \log(s + n) - \log s + \frac{1}{2s} - \frac{1}{2(s + n)} - \sum_{k=0}^{n-1} (s + k)^{-1}.$$
   - Combining with `Complex.digamma_apply_add_nat`, taking $n \to \infty$ for real $x > 0$, and
     extending from $(0, \infty)$ to the right half-plane
     $\{s \in \mathbb{C} \mid 0 < \operatorname{Re} s\}$
     by analytic continuation (`AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) proves for all
     $s \in \mathbb{C}$ with $0 < \operatorname{Re} s$:
     $$\psi(s) = \log s - \frac{1}{2s}
       - \int_{t \in \operatorname{Ioi} 0} \frac{t - \lfloor t \rfloor - 1/2}{(s + t)^2} \, dt.$$

3. **Explicit Right-Half-Plane `digamma` Bounds & Left-Vertical `logDeriv riemannZeta` Bound**:
   - For all $s \in \mathbb{C}$ with $0 < \operatorname{Re} s$:
     $$\|\psi(s) - \log s + \tfrac{1}{2s}\| \le \frac{1}{2 \operatorname{Re} s}, \qquad
       \|\psi(s) - \log s\| \le \frac{1}{2\|s\|} + \frac{1}{2 \operatorname{Re} s},$$
     and using $\|s + t\|^2 = \|s\|^2 + 2 t \operatorname{Re} s + t^2 \ge \|s\|^2 + t^2$
     for $t \ge 0$ together with $\int_0^\infty \frac{1}{\|s\|^2 + t^2} \, dt = \frac{\pi}{2\|s\|}$:
     $$\|\psi(s) - \log s + \tfrac{1}{2s}\| \le \frac{\pi}{4\|s\|}, \qquad
       \|\psi(s) - \log s\| \le \frac{2 + \pi}{4\|s\|} \le \frac{2}{\|s\|}.$$
   - Combining with `Complex.digamma_apply_add_one` and `logDeriv_riemannZeta_one_sub` along the
     left vertical line $s = -1/4 + t i$ ($t \in \mathbb{R}$) yields the explicit vertical bound:
     $$\left\|\frac{\zeta'}{\zeta}\!\left(-\frac{1}{4} + t i\right)\right\|
       \le \log(|t| + 2) + C_{\text{left}}.$$
-/

namespace ConjectureMachines.Riemann543.Semantics.DigammaBinet

open Complex Finset Filter MeasureTheory Set
open scoped Real Topology Interval ArithmeticFunction.vonMangoldt LSeries.notation

/-!
## Section 1: Real `digamma` Sandwich from `Real.convexOn_log_Gamma`
-/

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

/-- For `x : ℝ` with `0 < x`, `(Complex.digamma (x : ℂ)).im = 0`. -/
theorem digamma_ofReal_im {x : ℝ} (hx : 0 < x) :
    (Complex.digamma (x : ℂ)).im = 0 := by
  rw [digamma_ofReal_eq_deriv_log_Gamma hx, Complex.ofReal_im]

/-- **Bohr–Mollerup Convexity Sandwich for `Complex.digamma (x + 1)`**:
For all real `x > 0`,
$$\log x \le \operatorname{Re}\psi(x + 1) \le \log(x + 1).$$ -/
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
For all real `x > 0`,
$$\log x - \frac{1}{x} \le \operatorname{Re}\psi(x) \le \log x.$$ -/
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
    rw [digamma_ofReal_eq_deriv_log_Gamma hx, ← Complex.ofReal_log hx.le, ← Complex.ofReal_sub]
  rw [h_eq, Complex.norm_real, Real.norm_eq_abs, ← digamma_ofReal_re hx, abs_le]
  have h_sand := digamma_ofReal_re_sandwich hx
  have hx_inv : 0 ≤ 1 / x := by positivity
  constructor <;> linarith

/-- **Asymptotic Vanishing of `ψ(x + n) - log(x + n)` as `n → ∞`**:
For all real `x > 0`,
$$\lim_{n \to \infty} \bigl(\psi(x + n) - \log(x + n)\bigr) = 0.$$ -/
theorem tendsto_digamma_add_nat_sub_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ ↦ Complex.digamma ((x : ℂ) + n) - Complex.log ((x : ℂ) + n))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h_le : ∀ n : ℕ,
      ‖Complex.digamma ((x : ℂ) + n) - Complex.log ((x : ℂ) + n)‖ ≤ 1 / (x + (n : ℝ)) := by
    intro n
    have hxn_pos : 0 < x + (n : ℝ) := by positivity
    have h_cast : (x : ℂ) + (n : ℂ) = ((x + n : ℝ) : ℂ) := by push_cast; ring
    rw [h_cast]
    exact norm_digamma_ofReal_sub_log_le hxn_pos
  have h_lim : Tendsto (fun n : ℕ ↦ 1 / (x + (n : ℝ))) atTop (𝓝 0) := by
    have h_tendsto : Tendsto (fun n : ℕ ↦ x + (n : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp h_tendsto
  exact squeeze_zero (fun _ ↦ norm_nonneg _) h_le h_lim

/-- Real-log spelling of `tendsto_digamma_add_nat_sub_log`: for all `x > 0`,
`Tendsto (fun n : ℕ ↦ Complex.digamma (x + n) - (Real.log (x + n) : ℂ)) atTop (𝓝 0)`. -/
theorem tendsto_digamma_add_nat_sub_real_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ ↦ Complex.digamma ((x : ℂ) + n) - (Real.log (x + n) : ℂ))
      atTop (𝓝 0) := by
  refine (tendsto_digamma_add_nat_sub_log hx).congr fun n ↦ ?_
  have hxn : 0 ≤ x + (n : ℝ) := by positivity
  have h_cast : (x : ℂ) + (n : ℂ) = ((x + n : ℝ) : ℂ) := by push_cast; rfl
  rw [h_cast, Complex.ofReal_log hxn]

/-!
## Section 2: Finite & Infinite Euler–Maclaurin / Binet Identity for `Complex.digamma`
-/

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
  exact (measurable_id.sub
    (measurable_from_top.comp Nat.floor_mono.measurable)).sub measurable_const

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
    simp only [id_eq]
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
    simp only [id_eq]
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
  exact ((measurable_const.add Complex.measurable_ofReal).pow_const 2)

/-- `binetIntegrand s` is `IntegrableOn` `Ioi (0 : ℝ)` for every `s : ℂ` with `0 < s.re`. -/
theorem integrableOn_Ioi_binetIntegrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (binetIntegrand s) (Ioi 0) := by
  have h_dom : IntegrableOn (fun t : ℝ ↦ (1 / 2) * (1 / (s.re + t) ^ 2)) (Ioi 0) :=
    (integrableOn_Ioi_one_div_add_sq hs).const_mul (1 / 2)
  refine h_dom.mono' (measurable_binetIntegrand s).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (norm_binetIntegrand_le hs (mem_Ioi.mp ht).le).trans_eq (by ring)

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

/-- Exact derivative of `eulerMaclaurinAntideriv s k` for `0 < s.re` and `0 ≤ t`:
`HasDerivAt (eulerMaclaurinAntideriv s k) (((t : ℂ) - k - 1 / 2) / (s + t) ^ 2) t`. -/
theorem hasDerivAt_eulerMaclaurinAntideriv {s : ℂ} (hs : 0 < s.re) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (eulerMaclaurinAntideriv s k) (((t : ℂ) - k - 1 / 2) / (s + t) ^ 2) t := by
  unfold eulerMaclaurinAntideriv
  have h_slit : s + (t : ℂ) ∈ Complex.slitPlane := add_ofReal_mem_slitPlane hs ht
  have h_ne : s + (t : ℂ) ≠ 0 := Complex.slitPlane_ne_zero h_slit
  have hd_ofReal : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hd_st : HasDerivAt (fun u : ℝ ↦ s + (u : ℂ)) 1 t := by
    simpa using hd_ofReal.const_add s
  have hd_log : HasDerivAt (fun u : ℝ ↦ Complex.log (s + u)) (1 / (s + t)) t :=
    hd_st.clog_real h_slit
  have hd_num : HasDerivAt (fun u : ℝ ↦ (u : ℂ) - k - 1 / 2) 1 t := by
    simpa using (hd_ofReal.sub_const (k : ℂ)).sub_const (1 / 2 : ℂ)
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
$$\int_k^{k+1} \frac{t - k - 1/2}{(s + t)^2} \, dt
  = \log(s + k + 1) - \log(s + k) - \frac{1}{2(s + k + 1)} - \frac{1}{2(s + k)}.$$ -/
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

/-- Replacing `k` by `⌊t⌋₊` on `(k : ℝ)..(k + 1 : ℝ)` in `intervalIntegral_eulerMaclaurin_unit`,
written in telescoping form with `H(z) := log z - 1 / (2 * z)`. -/
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
$$\int_0^n \frac{t - \lfloor t \rfloor - 1/2}{(s + t)^2} \, dt
  = \log(s + n) - \log s + \frac{1}{2s} - \frac{1}{2(s + n)}
    - \sum_{k \in \operatorname{range} n} (s + k)^{-1}.$$ -/
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
    refine sum_congr rfl fun k _ ↦ ?_
    push_cast
    simpa [Nat.cast_add, Nat.cast_one] using intervalIntegral_binetIntegrand_unit hs k
  rw [h_sum_eq, sum_sub_distrib,
    sum_range_sub (fun k : ℕ ↦ Complex.log (s + (k : ℕ)) - 1 / (2 * (s + (k : ℕ)))) n]
  simp only [Nat.cast_zero, add_zero]
  ring

/-- **Finite Euler–Maclaurin Formula for `Complex.digamma s`**:
For all `s : ℂ` with `0 < s.re` and all `n : ℕ`,
$$\psi(s) = \log s - \frac{1}{2s} + \int_0^n \frac{t - \lfloor t \rfloor - 1/2}{(s + t)^2} \, dt
  + \psi(s + n) - \log(s + n) + \frac{1}{2(s + n)}.$$ -/
theorem digamma_eq_log_sub_half_inv_sub_intervalIntegral_add_rem {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Complex.digamma s =
      Complex.log s - 1 / (2 * s) + (∫ t : ℝ in (0 : ℝ)..(n : ℝ), binetIntegrand s t) +
        (Complex.digamma (s + n) - Complex.log (s + n)) + 1 / (2 * (s + n)) := by
  have h_rec := Complex.digamma_apply_add_nat (ne_neg_natCast_of_re_pos hs) n
  have h_int := intervalIntegral_binetIntegrand_range hs n
  linear_combination -h_rec - h_int

/-- **Euler–Maclaurin / Binet Integral Representation for Real `x > 0`**:
For all real `x > 0`,
$$\psi(x) = \log x - \frac{1}{2x}
  + \int_{t \in \operatorname{Ioi} 0} \frac{t - \lfloor t \rfloor - 1/2}{(x + t)^2} \, dt.$$ -/
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
    have h_le : ∀ n : ℕ, ‖(1 : ℂ) / (2 * ((x : ℂ) + n))‖ ≤ 1 / (2 * (x + (n : ℝ))) := by
      intro n
      have hxn_pos : 0 < x + (n : ℝ) := by positivity
      have h_norm : x + (n : ℝ) ≤ ‖(x : ℂ) + (n : ℂ)‖ := by
        simpa using re_add_le_norm_add_ofReal (s := (x : ℂ)) (t := (n : ℝ))
      rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat]
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    have h_lim : Tendsto (fun n : ℕ ↦ 1 / (2 * (x + (n : ℝ)))) atTop (𝓝 0) := by
      have h_tend : Tendsto (fun n : ℕ ↦ 2 * (x + (n : ℝ))) atTop atTop :=
        (tendsto_atTop_add_const_left atTop x tendsto_natCast_atTop_atTop).const_mul_atTop
          (by norm_num)
      simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp h_tend
    exact squeeze_zero (fun _ ↦ norm_nonneg _) h_le h_lim
  have h_c :
      Tendsto (fun _ : ℕ ↦ Complex.log (x : ℂ) - 1 / (2 * (x : ℂ)))
        atTop (𝓝 (Complex.log (x : ℂ) - 1 / (2 * (x : ℂ)))) :=
    tendsto_const_nhds
  have h_rhs := ((h_c.add h_int_tendsto).add h_rem1).add h_rem2
  simp only [add_zero] at h_rhs
  have h_const :
      Tendsto (fun _ : ℕ ↦ Complex.digamma (x : ℂ)) atTop (𝓝 (Complex.digamma (x : ℂ))) :=
    tendsto_const_nhds
  refine tendsto_nhds_unique h_const (h_rhs.congr fun n ↦ ?_)
  exact (digamma_eq_log_sub_half_inv_sub_intervalIntegral_add_rem hx_re n).symm

/-- Convexity of the open right half-plane `{s : ℂ | 0 < s.re}`. -/
theorem convex_rightHalfPlane : Convex ℝ {s : ℂ | 0 < s.re} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq, add_re, smul_re, smul_eq_mul] at hx hy ⊢
  rcases lt_or_eq_of_le ha with ha' | rfl
  · have : 0 < a * x.re := mul_pos ha' hx
    have : 0 ≤ b * y.re := mul_nonneg hb hy.le
    linarith
  · have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hy

/-- Complex differentiability of `s ↦ ∫ t in Ioi 0, binetIntegrand s t` on `{s : ℂ | 0 < s.re}`. -/
theorem differentiableOn_integral_binetIntegrand :
    DifferentiableOn ℂ (fun s : ℂ ↦ ∫ t : ℝ in Ioi 0, binetIntegrand s t)
      {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  simp only [mem_ofPred_eq] at hs₀
  set c : ℝ := s₀.re / 2
  have hc : 0 < c := half_pos hs₀
  let V : Set ℂ := {z : ℂ | c < z.re}
  have hV_open : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hs₀_V : s₀ ∈ V := by simp [V, c, half_lt_self hs₀]
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
      (integrableOn_Ioi_binetIntegrand hs₀)
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
      field_simp [h_ne]
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
  exact ((hGamma' s hs).div (hGamma s hs) (Complex.Gamma_ne_zero_of_re_pos hs))

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
  have hU_preconn : IsPreconnected U := convex_rightHalfPlane.isPreconnected
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
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq h_an1 h_an2 hU_preconn h1_mem h_freq hs

/-!
## Section 3: Explicit Right-Half-Plane Bounds on `digamma` & Left-Vertical `logDeriv riemannZeta`
-/

/-- **First Binet Remainder Bound (`1 / (2 * s.re)`)**:
For all `s : ℂ` with `0 < s.re`,
$$\|\psi(s) - \log s + \tfrac{1}{2s}\| \le \frac{1}{2 \operatorname{Re} s}.$$ -/
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
    exact (norm_binetIntegrand_le hs (mem_Ioi.mp ht).le).trans_eq (by ring)
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

/-- For `s : ℂ` with `0 ≤ s.re` and `t ≥ 0`, `‖s‖ ^ 2 + t ^ 2 ≤ ‖s + (t : ℂ)‖ ^ 2`. -/
theorem norm_sq_add_sq_le_norm_add_ofReal_sq {s : ℂ} (hs : 0 ≤ s.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖s‖ ^ 2 + t ^ 2 ≤ ‖s + (t : ℂ)‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
  have h_nonneg : 0 ≤ 2 * s.re * t := by positivity
  nlinarith

/-- Exact improper integral `∫ t in Ioi (0 : ℝ), 1 / (R ^ 2 + t ^ 2) = π / (2 * R)` for `R > 0`. -/
theorem integral_Ioi_one_div_sq_add_sq {R : ℝ} (hR : 0 < R) :
    (∫ t : ℝ in Ioi 0, 1 / (R ^ 2 + t ^ 2)) = Real.pi / (2 * R) := by
  have hR_ne : R ≠ 0 := hR.ne'
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun u : ℝ ↦ (1 / R) * Real.arctan (u / R)) (1 / (R ^ 2 + t ^ 2)) t := by
    intro t _
    have hpos : R ^ 2 + t ^ 2 ≠ 0 := by positivity
    have hd := (((hasDerivAt_id t).div_const R).arctan).const_mul (1 / R)
    refine hd.congr_deriv ?_
    simp only [id_eq]
    field_simp [hR_ne, hpos]
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / (R ^ 2 + t ^ 2) := fun t _ ↦ by positivity
  have htend :
      Tendsto (fun u : ℝ ↦ (1 / R) * Real.arctan (u / R)) atTop (𝓝 (Real.pi / (2 * R))) := by
    have h_div : Tendsto (fun u : ℝ ↦ u / R) atTop atTop := tendsto_id.atTop_div_const hR
    have h_atan : Tendsto (fun u : ℝ ↦ Real.arctan (u / R)) atTop (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h_div
    have h_mul := h_atan.const_mul (1 / R)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using h_mul
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos htend]
  simp

/-- Integrability of `t ↦ 1 / (R ^ 2 + t ^ 2)` on `Ioi (0 : ℝ)` for `R > 0`. -/
theorem integrableOn_Ioi_one_div_sq_add_sq {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ ↦ 1 / (R ^ 2 + t ^ 2)) (Ioi 0) := by
  have hR_ne : R ≠ 0 := hR.ne'
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun u : ℝ ↦ (1 / R) * Real.arctan (u / R)) (1 / (R ^ 2 + t ^ 2)) t := by
    intro t _
    have hpos : R ^ 2 + t ^ 2 ≠ 0 := by positivity
    have hd := (((hasDerivAt_id t).div_const R).arctan).const_mul (1 / R)
    refine hd.congr_deriv ?_
    simp only [id_eq]
    field_simp [hR_ne, hpos]
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / (R ^ 2 + t ^ 2) := fun t _ ↦ by positivity
  have htend :
      Tendsto (fun u : ℝ ↦ (1 / R) * Real.arctan (u / R)) atTop (𝓝 (Real.pi / (2 * R))) := by
    have h_div : Tendsto (fun u : ℝ ↦ u / R) atTop atTop := tendsto_id.atTop_div_const hR
    have h_atan : Tendsto (fun u : ℝ ↦ Real.arctan (u / R)) atTop (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h_div
    have h_mul := h_atan.const_mul (1 / R)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using h_mul
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend

/-- **Sharp Right-Half-Plane Binet Remainder Bound (`π / (4 * ‖s‖)`)**:
For all `s : ℂ` with `0 < s.re`,
$$\|\psi(s) - \log s + \tfrac{1}{2s}\| \le \frac{\pi}{4 \|s\|}.$$ -/
theorem norm_digamma_sub_log_add_half_inv_le_norm {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.digamma s - Complex.log s + 1 / (2 * s)‖ ≤ Real.pi / (4 * ‖s‖) := by
  have hs_norm : 0 < ‖s‖ := hs.trans_le (Complex.re_le_norm s)
  have h_eq :
      Complex.digamma s - Complex.log s + 1 / (2 * s) =
        ∫ t : ℝ in Ioi 0, binetIntegrand s t := by
    have h := digamma_eq_log_sub_half_inv_sub_integral hs
    unfold binetIntegrand
    linear_combination h
  rw [h_eq]
  have h_bound :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
        ‖binetIntegrand s t‖ ≤ (1 / 2) * (1 / (‖s‖ ^ 2 + t ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_nonneg : 0 ≤ t := (mem_Ioi.mp ht).le
    rw [binetIntegrand_eq_sawtoothB1, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow,
      ← div_eq_mul_one_div]
    exact div_le_div₀ (by norm_num) (abs_sawtoothB1_le_half ht_nonneg)
      (by positivity) (norm_sq_add_sq_le_norm_add_ofReal_sq hs.le ht_nonneg)
  have h_int_le :=
    norm_integral_le_of_norm_le ((integrableOn_Ioi_one_div_sq_add_sq hs_norm).const_mul (1 / 2))
      h_bound
  rw [MeasureTheory.integral_const_mul, integral_Ioi_one_div_sq_add_sq hs_norm] at h_int_le
  refine h_int_le.trans (le_of_eq ?_)
  ring

/-- **Uniform Right-Half-Plane Bound on `‖Complex.digamma s - Complex.log s‖`**:
For all `s : ℂ` with `0 < s.re`,
$$\|\psi(s) - \log s\| \le \frac{2 + \pi}{4 \|s\|} \le \frac{2}{\|s\|}.$$ -/
theorem norm_digamma_sub_log_le_two_add_pi_div_four_norm {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.digamma s - Complex.log s‖ ≤ (2 + Real.pi) / (4 * ‖s‖) := by
  have h_decomp :
      Complex.digamma s - Complex.log s =
        (-1 / (2 * s)) + (Complex.digamma s - Complex.log s + 1 / (2 * s)) := by ring
  rw [h_decomp]
  have h1 : ‖-1 / (2 * s)‖ = 1 / (2 * ‖s‖) := by
    rw [norm_div, norm_neg, norm_one, norm_mul, Complex.norm_ofNat]
  have h2 := norm_digamma_sub_log_add_half_inv_le_norm hs
  calc
    ‖(-1 / (2 * s)) + (Complex.digamma s - Complex.log s + 1 / (2 * s))‖
      ≤ ‖-1 / (2 * s)‖ + ‖Complex.digamma s - Complex.log s + 1 / (2 * s)‖ := norm_add_le _ _
    _ ≤ 1 / (2 * ‖s‖) + Real.pi / (4 * ‖s‖) := by linarith
    _ = (2 + Real.pi) / (4 * ‖s‖) := by ring

theorem norm_digamma_sub_log_le_two_div_norm {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.digamma s - Complex.log s‖ ≤ 2 / ‖s‖ := by
  have hs_norm : 0 < ‖s‖ := hs.trans_le (Complex.re_le_norm s)
  refine (norm_digamma_sub_log_le_two_add_pi_div_four_norm hs).trans ?_
  rw [div_le_iff₀ (by positivity)]
  have h_rhs : 2 / ‖s‖ * (4 * ‖s‖) = 8 := by field_simp [hs_norm.ne']; ring
  rw [h_rhs]
  linarith [Real.pi_lt_four]

/-!
### Section 3B: Second-Order `quadKernel` Binet Formula & $O(1 / |s|^2)$ Remainder Bounds
-/

/-- The nonnegative second-order Bernoulli quadratic kernel on `[0, ∞)`:
`quadKernel t := (t - ⌊t⌋₊) * (1 - (t - ⌊t⌋₊))`. -/
noncomputable def quadKernel (t : ℝ) : ℝ :=
  (t - ⌊t⌋₊) * (1 - (t - ⌊t⌋₊))

/-- Measurability of `quadKernel`. -/
theorem measurable_quadKernel : Measurable quadKernel := by
  have h_eq : quadKernel = fun t : ℝ ↦ (sawtoothB1 t + 1 / 2) * (1 / 2 - sawtoothB1 t) := by
    ext t
    unfold quadKernel sawtoothB1
    ring
  rw [h_eq]
  exact (measurable_sawtoothB1.add measurable_const).mul
    (measurable_const.sub measurable_sawtoothB1)

/-- For all `t ≥ 0`, `0 ≤ quadKernel t ∧ quadKernel t ≤ 1 / 4`, hence `|quadKernel t| ≤ 1 / 4`. -/
theorem quadKernel_nonneg_and_le_quarter {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ quadKernel t ∧ quadKernel t ≤ 1 / 4 := by
  unfold quadKernel
  have h_le : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
  have h_lt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hu0 : 0 ≤ t - ⌊t⌋₊ := by linarith
  have hu1 : 0 ≤ 1 - (t - ⌊t⌋₊) := by linarith
  refine ⟨mul_nonneg hu0 hu1, ?_⟩
  have h_sq : 0 ≤ (t - ⌊t⌋₊ - 1 / 2) ^ 2 := sq_nonneg _
  linarith

theorem abs_quadKernel_le_quarter {t : ℝ} (ht : 0 ≤ t) :
    |quadKernel t| ≤ 1 / 4 := by
  rw [abs_of_nonneg (quadKernel_nonneg_and_le_quarter ht).1]
  exact (quadKernel_nonneg_and_le_quarter ht).2

/-- The second-order Binet integrand
`quadBinetIntegrand s t := (quadKernel t : ℂ) / (s + t) ^ 3`. -/
noncomputable def quadBinetIntegrand (s : ℂ) (t : ℝ) : ℂ :=
  (quadKernel t : ℂ) / (s + t) ^ 3

theorem measurable_quadBinetIntegrand (s : ℂ) : Measurable (quadBinetIntegrand s) := by
  unfold quadBinetIntegrand
  refine (Complex.measurable_ofReal.comp measurable_quadKernel).div ?_
  exact (measurable_const.add Complex.measurable_ofReal).pow_const 3

theorem norm_quadBinetIntegrand_le {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖quadBinetIntegrand s t‖ ≤ (1 / 4) / (s.re + t) ^ 3 := by
  have hst_pos : 0 < s.re + t := by linarith
  unfold quadBinetIntegrand
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow]
  exact div_le_div₀ (by norm_num) (abs_quadKernel_le_quarter ht)
    (by positivity) (pow_le_pow_left₀ hst_pos.le re_add_le_norm_add_ofReal 3)

/-- Exact improper integral `∫ t in Ioi (0 : ℝ), 1 / (a + t) ^ 3 = 1 / (2 * a ^ 2)` for `a > 0`. -/
theorem integral_Ioi_one_div_add_cube {a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in Ioi 0, 1 / (a + t) ^ 3) = 1 / (2 * a ^ 2) := by
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun u : ℝ ↦ -(1 / 2) * ((a + u) ^ 2)⁻¹) (1 / (a + t) ^ 3) t := by
    intro t ht
    have hat : a + t ≠ 0 := by linarith [mem_Ici.mp ht]
    have hd_pow : HasDerivAt (fun u : ℝ ↦ (a + u) ^ 2) (2 * (a + t)) t := by
      simpa [Pi.pow_def, pow_one] using ((hasDerivAt_id t).const_add a).pow 2
    have hd := (hd_pow.inv (pow_ne_zero 2 hat)).const_mul (-(1 / 2 : ℝ))
    refine hd.congr_deriv ?_
    field_simp [hat]
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / (a + t) ^ 3 := fun t ht ↦ by
    have : 0 < a + t := by linarith [mem_Ioi.mp ht]
    positivity
  have htend : Tendsto (fun u : ℝ ↦ -(1 / 2) * ((a + u) ^ 2)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ ↦ a + u) atTop atTop :=
      tendsto_atTop_add_const_left atTop a tendsto_id
    have h2 : Tendsto (fun u : ℝ ↦ (a + u) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp h1
    have h3 := (tendsto_inv_atTop_zero.comp h2).const_mul (-(1 / 2 : ℝ))
    simpa only [Function.comp_def, mul_zero] using h3
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos htend]
  have ha_ne : a ≠ 0 := ha.ne'
  field_simp [ha_ne]
  ring

/-- Integrability of `t ↦ 1 / (a + t) ^ 3` on `Ioi (0 : ℝ)` for `a > 0`. -/
theorem integrableOn_Ioi_one_div_add_cube {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ ↦ 1 / (a + t) ^ 3) (Ioi 0) := by
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun u : ℝ ↦ -(1 / 2) * ((a + u) ^ 2)⁻¹) (1 / (a + t) ^ 3) t := by
    intro t ht
    have hat : a + t ≠ 0 := by linarith [mem_Ici.mp ht]
    have hd_pow : HasDerivAt (fun u : ℝ ↦ (a + u) ^ 2) (2 * (a + t)) t := by
      simpa [Pi.pow_def, pow_one] using ((hasDerivAt_id t).const_add a).pow 2
    have hd := (hd_pow.inv (pow_ne_zero 2 hat)).const_mul (-(1 / 2 : ℝ))
    refine hd.congr_deriv ?_
    field_simp [hat]
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / (a + t) ^ 3 := fun t ht ↦ by
    have : 0 < a + t := by linarith [mem_Ioi.mp ht]
    positivity
  have htend : Tendsto (fun u : ℝ ↦ -(1 / 2) * ((a + u) ^ 2)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ ↦ a + u) atTop atTop :=
      tendsto_atTop_add_const_left atTop a tendsto_id
    have h2 : Tendsto (fun u : ℝ ↦ (a + u) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp h1
    have h3 := (tendsto_inv_atTop_zero.comp h2).const_mul (-(1 / 2 : ℝ))
    simpa only [Function.comp_def, mul_zero] using h3
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hderiv hpos htend

theorem integrableOn_Ioi_quadBinetIntegrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (quadBinetIntegrand s) (Ioi 0) := by
  have h_dom : IntegrableOn (fun t : ℝ ↦ (1 / 4) * (1 / (s.re + t) ^ 3)) (Ioi 0) :=
    (integrableOn_Ioi_one_div_add_cube hs).const_mul (1 / 4)
  refine h_dom.mono' (measurable_quadBinetIntegrand s).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (norm_quadBinetIntegrand_le hs (mem_Ioi.mp ht).le).trans_eq (by ring)

theorem intervalIntegrable_quadBinetIntegrand {s : ℂ} (hs : 0 < s.re) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (quadBinetIntegrand s) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine (integrableOn_Ioi_quadBinetIntegrand hs).mono_set ?_
  intro t ht
  exact mem_Ioi.mpr (ha.trans_lt ht.1)

/-- The quadratic boundary-vanishing correction on `[k, k + 1]`:
`quadCorrection s k t := -(((t : ℂ) - k) * (1 - ((t : ℂ) - k))) / (2 * (s + t) ^ 2)`. -/
noncomputable def quadCorrection (s : ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  -(((t : ℂ) - k) * (1 - ((t : ℂ) - k))) / (2 * (s + t) ^ 2)

theorem hasDerivAt_quadCorrection {s : ℂ} (hs : 0 < s.re) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (quadCorrection s k)
      ((((t : ℂ) - k - 1 / 2) / (s + t) ^ 2) +
        (((t : ℂ) - k) * (1 - ((t : ℂ) - k))) / (s + t) ^ 3) t := by
  have h_ne : s + (t : ℂ) ≠ 0 := add_ofReal_ne_zero hs ht
  have hd_t : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 t := hasDerivAt_id t |>.ofReal_comp
  have hd_u : HasDerivAt (fun u : ℝ ↦ (u : ℂ) - k) 1 t := by
    simpa using hd_t.sub_const (k : ℂ)
  have hd_1mu : HasDerivAt (fun u : ℝ ↦ 1 - ((u : ℂ) - k)) (-1) t := by
    simpa using hd_u.const_sub (1 : ℂ)
  have hd_num : HasDerivAt (fun u : ℝ ↦ -(((u : ℂ) - k) * (1 - ((u : ℂ) - k))))
      (-(1 * (1 - ((t : ℂ) - k)) + ((t : ℂ) - k) * (-1))) t :=
    (hd_u.mul hd_1mu).neg
  have hd_st : HasDerivAt (fun u : ℝ ↦ s + (u : ℂ)) 1 t := by
    simpa using hd_t.const_add s
  have hd_st2 : HasDerivAt (fun u : ℝ ↦ (s + (u : ℂ)) ^ 2) (2 * (s + (t : ℂ))) t := by
    simpa [Pi.pow_def, pow_one] using hd_st.pow 2
  have hd_den : HasDerivAt (fun u : ℝ ↦ 2 * (s + (u : ℂ)) ^ 2) (2 * (2 * (s + (t : ℂ)))) t :=
    hd_st2.const_mul 2
  have h_den_ne : 2 * (s + (t : ℂ)) ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 h_ne)
  have hd_quot := hd_num.div hd_den h_den_ne
  unfold quadCorrection
  refine hd_quot.congr_deriv ?_
  field_simp [h_ne]
  ring

theorem intervalIntegral_binetIntegrand_add_quadBinetIntegrand_unit
    {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    (∫ t : ℝ in (k : ℝ)..(k + 1 : ℝ), (binetIntegrand s t + quadBinetIntegrand s t)) = 0 := by
  have hk_le : (k : ℝ) ≤ k + 1 := by linarith
  have h_congr :
      (∫ t : ℝ in (k : ℝ)..(k + 1 : ℝ), (binetIntegrand s t + quadBinetIntegrand s t)) =
        ∫ t : ℝ in (k : ℝ)..(k + 1 : ℝ),
          ((((t : ℂ) - k - 1 / 2) / (s + t) ^ 2) +
            (((t : ℂ) - k) * (1 - ((t : ℂ) - k))) / (s + t) ^ 3) := by
    refine intervalIntegral.integral_congr_Ioo_of_le hk_le fun t ht ↦ ?_
    unfold binetIntegrand quadBinetIntegrand quadKernel
    have ht_nonneg : 0 ≤ t := (Nat.cast_nonneg k).trans ht.1.le
    have h_floor : ⌊t⌋₊ = k := Nat.floor_eq_iff ht_nonneg |>.mpr ⟨ht.1.le, ht.2⟩
    rw [h_floor]
    push_cast
    rfl
  rw [h_congr]
  have hderiv : ∀ t ∈ uIcc (k : ℝ) (k + 1 : ℝ),
      HasDerivAt (quadCorrection s k)
        ((((t : ℂ) - k - 1 / 2) / (s + t) ^ 2) +
          (((t : ℂ) - k) * (1 - ((t : ℂ) - k))) / (s + t) ^ 3) t := by
    intro t ht
    rw [uIcc_of_le hk_le] at ht
    exact hasDerivAt_quadCorrection hs k ((Nat.cast_nonneg k).trans ht.1)
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ ((((t : ℂ) - k - 1 / 2) / (s + t) ^ 2) +
        (((t : ℂ) - k) * (1 - ((t : ℂ) - k))) / (s + t) ^ 3))
      volume (k : ℝ) (k + 1 : ℝ) := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hk_le]
    intro t ht
    have ht_nonneg : 0 ≤ t := (Nat.cast_nonneg k).trans ht.1
    have h_ne2 : (s + (t : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (add_ofReal_ne_zero hs ht_nonneg)
    have h_ne3 : (s + (t : ℂ)) ^ 3 ≠ 0 := pow_ne_zero 3 (add_ofReal_ne_zero hs ht_nonneg)
    refine ContinuousWithinAt.add
      (ContinuousAt.continuousWithinAt (ContinuousAt.div (by fun_prop) (by fun_prop) h_ne2))
      (ContinuousAt.continuousWithinAt (ContinuousAt.div (by fun_prop) (by fun_prop) h_ne3))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  unfold quadCorrection
  push_cast
  have h1 : (k : ℂ) + 1 - (k : ℂ) = 1 := by ring
  have h2 : (k : ℂ) - (k : ℂ) = 0 := by ring
  rw [h1, h2]
  ring

theorem intervalIntegral_binetIntegrand_eq_neg_quadBinetIntegrand_unit
    {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    (∫ t : ℝ in (k : ℝ)..(k + 1 : ℝ), binetIntegrand s t) =
      -(∫ t : ℝ in (k : ℝ)..(k + 1 : ℝ), quadBinetIntegrand s t) := by
  have hk_le : (k : ℝ) ≤ k + 1 := by linarith
  have h_int1 := intervalIntegrable_binetIntegrand hs (Nat.cast_nonneg k) hk_le
  have h_int2 := intervalIntegrable_quadBinetIntegrand hs (Nat.cast_nonneg k) hk_le
  have h_sum := intervalIntegral_binetIntegrand_add_quadBinetIntegrand_unit hs k
  rw [intervalIntegral.integral_add h_int1 h_int2] at h_sum
  linear_combination h_sum

theorem integral_Ioi_binetIntegrand_eq_neg_quadBinetIntegrand {s : ℂ} (hs : 0 < s.re) :
    (∫ t : ℝ in Ioi 0, binetIntegrand s t) =
      -(∫ t : ℝ in Ioi 0, quadBinetIntegrand s t) := by
  have h_range : ∀ n : ℕ,
      (∫ t : ℝ in (0 : ℝ)..(n : ℝ), binetIntegrand s t) =
        -(∫ t : ℝ in (0 : ℝ)..(n : ℝ), quadBinetIntegrand s t) := by
    intro n
    have h_adj1 :
        (∑ k ∈ Finset.range n, ∫ t : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), binetIntegrand s t) =
          ∫ t : ℝ in ((0 : ℕ) : ℝ)..(n : ℝ), binetIntegrand s t := by
      refine intervalIntegral.sum_integral_adjacent_intervals fun k _ ↦ ?_
      push_cast
      exact intervalIntegrable_binetIntegrand hs (Nat.cast_nonneg k) (by linarith)
    have h_adj2 :
        (∑ k ∈ Finset.range n, ∫ t : ℝ in (k : ℝ)..((k + 1 : ℕ) : ℝ), quadBinetIntegrand s t) =
          ∫ t : ℝ in ((0 : ℕ) : ℝ)..(n : ℝ), quadBinetIntegrand s t := by
      refine intervalIntegral.sum_integral_adjacent_intervals fun k _ ↦ ?_
      push_cast
      exact intervalIntegrable_quadBinetIntegrand hs (Nat.cast_nonneg k) (by linarith)
    simp only [Nat.cast_zero] at h_adj1 h_adj2
    rw [← h_adj1, ← h_adj2, ← sum_neg_distrib]
    refine sum_congr rfl fun k _ ↦ ?_
    push_cast
    exact intervalIntegral_binetIntegrand_eq_neg_quadBinetIntegrand_unit hs k
  have h_tend1 := MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_Ioi_binetIntegrand hs) tendsto_natCast_atTop_atTop
  have h_tend2 := (MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_Ioi_quadBinetIntegrand hs) tendsto_natCast_atTop_atTop).neg
  exact tendsto_nhds_unique h_tend1 (h_tend2.congr fun n ↦ (h_range n).symm)

/-- **Second-Order Binet Integral Formula for `Complex.digamma s` (`0 < s.re`)**:
For all `s : ℂ` with `0 < s.re`,
$$\psi(s) = \log s - \frac{1}{2s}
  - \int_{t \in \operatorname{Ioi} 0}
    \frac{(\text{quadKernel } t : \mathbb{C})}{(s + t)^3} \, dt.$$ -/
theorem digamma_eq_log_sub_half_inv_sub_quadIntegral {s : ℂ} (hs : 0 < s.re) :
    Complex.digamma s =
      Complex.log s - 1 / (2 * s) -
        ∫ t : ℝ in Ioi 0, ((quadKernel t : ℂ) / (s + t) ^ 3) := by
  have h1 := digamma_eq_log_sub_half_inv_sub_integral hs
  have h2 := integral_Ioi_binetIntegrand_eq_neg_quadBinetIntegrand hs
  unfold binetIntegrand quadBinetIntegrand at h2
  linear_combination h1 + h2

/-- **Second-Order Binet Remainder Bound (`1 / (8 * s.re ^ 2)`)**:
For all `s : ℂ` with `0 < s.re`,
$$\|\psi(s) - \log s + \tfrac{1}{2s}\| \le \frac{1}{8 (\operatorname{Re} s)^2}.$$ -/
theorem norm_digamma_sub_log_add_half_inv_le_re_sq {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.digamma s - Complex.log s + 1 / (2 * s)‖ ≤ 1 / (8 * s.re ^ 2) := by
  have h_eq :
      Complex.digamma s - Complex.log s + 1 / (2 * s) =
        -∫ t : ℝ in Ioi 0, quadBinetIntegrand s t := by
    have h := digamma_eq_log_sub_half_inv_sub_quadIntegral hs
    unfold quadBinetIntegrand
    linear_combination h
  rw [h_eq, norm_neg]
  have h_bound :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
        ‖quadBinetIntegrand s t‖ ≤ (1 / 4) * (1 / (s.re + t) ^ 3) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (norm_quadBinetIntegrand_le hs (mem_Ioi.mp ht).le).trans_eq (by ring)
  have h_int_le :=
    norm_integral_le_of_norm_le ((integrableOn_Ioi_one_div_add_cube hs).const_mul (1 / 4)) h_bound
  rw [MeasureTheory.integral_const_mul, integral_Ioi_one_div_add_cube hs] at h_int_le
  refine h_int_le.trans (le_of_eq ?_)
  ring

/-- **Mixed Second-Order Binet Remainder Bound (`1 / (4 * s.re * ‖s‖)`)**:
For all `s : ℂ` with `0 < s.re`,
$$\|\psi(s) - \log s + \tfrac{1}{2s}\| \le \frac{1}{4 (\operatorname{Re} s) \|s\|}.$$ -/
theorem norm_digamma_sub_log_add_half_inv_le_re_mul_norm {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.digamma s - Complex.log s + 1 / (2 * s)‖ ≤ 1 / (4 * s.re * ‖s‖) := by
  have hs_norm : 0 < ‖s‖ := hs.trans_le (Complex.re_le_norm s)
  have h_eq :
      Complex.digamma s - Complex.log s + 1 / (2 * s) =
        -∫ t : ℝ in Ioi 0, quadBinetIntegrand s t := by
    have h := digamma_eq_log_sub_half_inv_sub_quadIntegral hs
    unfold quadBinetIntegrand
    linear_combination h
  rw [h_eq, norm_neg]
  have h_bound :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
        ‖quadBinetIntegrand s t‖ ≤ (1 / (4 * ‖s‖)) * (1 / (s.re + t) ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_nonneg : 0 ≤ t := (mem_Ioi.mp ht).le
    have hst_pos : 0 < s.re + t := by linarith
    have h_norm_ge : ‖s‖ ≤ ‖s + (t : ℂ)‖ := by
      have h_sq := norm_sq_add_sq_le_norm_add_ofReal_sq hs.le ht_nonneg
      have h_sq2 : ‖s‖ ^ 2 ≤ ‖s + (t : ℂ)‖ ^ 2 := by nlinarith
      nlinarith [norm_nonneg (s + (t : ℂ))]
    have h_re_ge : (s.re + t) ^ 2 ≤ ‖s + (t : ℂ)‖ ^ 2 :=
      pow_le_pow_left₀ hst_pos.le re_add_le_norm_add_ofReal 2
    have h_den : ‖s‖ * (s.re + t) ^ 2 ≤ ‖s + (t : ℂ)‖ ^ 3 := by
      calc
        ‖s‖ * (s.re + t) ^ 2 ≤ ‖s + (t : ℂ)‖ * ‖s + (t : ℂ)‖ ^ 2 :=
          mul_le_mul h_norm_ge h_re_ge (by positivity) (norm_nonneg _)
        _ = ‖s + (t : ℂ)‖ ^ 3 := by ring
    unfold quadBinetIntegrand
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow, one_div_mul_one_div,
      show 4 * ‖s‖ * (s.re + t) ^ 2 = 4 * (‖s‖ * (s.re + t) ^ 2) by ring, ← div_div]
    exact div_le_div₀ (by positivity) (abs_quadKernel_le_quarter ht_nonneg) (by positivity) h_den
  have h_int_le :=
    norm_integral_le_of_norm_le
      ((integrableOn_Ioi_one_div_add_sq hs).const_mul (1 / (4 * ‖s‖))) h_bound
  rw [MeasureTheory.integral_const_mul, integral_Ioi_one_div_add_sq hs] at h_int_le
  refine h_int_le.trans (le_of_eq ?_)
  ring

/-- **Uniform $O(1 / \|s\|^2)$ Second-Order Binet Remainder Bound (`1 / (2 * ‖s‖ ^ 2)`)**:
For all `s : ℂ` with `0 < s.re`,
$$\|\psi(s) - \log s + \tfrac{1}{2s}\| \le \frac{1}{2 \|s\|^2}.$$ -/
theorem norm_digamma_sub_log_add_half_inv_le_norm_sq {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.digamma s - Complex.log s + 1 / (2 * s)‖ ≤ 1 / (2 * ‖s‖ ^ 2) := by
  have hs_norm : 0 < ‖s‖ := hs.trans_le (Complex.re_le_norm s)
  have h_eq :
      Complex.digamma s - Complex.log s + 1 / (2 * s) =
        -∫ t : ℝ in Ioi 0, quadBinetIntegrand s t := by
    have h := digamma_eq_log_sub_half_inv_sub_quadIntegral hs
    unfold quadBinetIntegrand
    linear_combination h
  rw [h_eq, norm_neg]
  have h_bound :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
        ‖quadBinetIntegrand s t‖ ≤ 1 / (‖s‖ + t) ^ 3 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht_nonneg : 0 ≤ t := (mem_Ioi.mp ht).le
    have hA_pos : 0 < ‖s‖ + t := by linarith
    have hB_nonneg : 0 ≤ ‖s + (t : ℂ)‖ := norm_nonneg _
    have h_sq : (‖s‖ + t) ^ 2 ≤ 2 * ‖s + (t : ℂ)‖ ^ 2 := by
      have h1 : (‖s‖ + t) ^ 2 ≤ 2 * (‖s‖ ^ 2 + t ^ 2) := by
        have : 0 ≤ (‖s‖ - t) ^ 2 := sq_nonneg _
        linarith
      have h2 := norm_sq_add_sq_le_norm_add_ofReal_sq hs.le ht_nonneg
      linarith
    have h_cube : (‖s‖ + t) ^ 3 ≤ 4 * ‖s + (t : ℂ)‖ ^ 3 := by
      have h_pow6 : ((‖s‖ + t) ^ 3) ^ 2 ≤ (4 * ‖s + (t : ℂ)‖ ^ 3) ^ 2 := by
        calc
          ((‖s‖ + t) ^ 3) ^ 2 = ((‖s‖ + t) ^ 2) ^ 3 := by ring
          _ ≤ (2 * ‖s + (t : ℂ)‖ ^ 2) ^ 3 := pow_le_pow_left₀ (by positivity) h_sq 3
          _ = 8 * ‖s + (t : ℂ)‖ ^ 6 := by ring
          _ ≤ 16 * ‖s + (t : ℂ)‖ ^ 6 := by nlinarith [pow_nonneg hB_nonneg 6]
          _ = (4 * ‖s + (t : ℂ)‖ ^ 3) ^ 2 := by ring
      nlinarith [pow_nonneg hA_pos.le 3, pow_nonneg hB_nonneg 3]
    unfold quadBinetIntegrand
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, norm_pow]
    have h_num : |quadKernel t| * 4 ≤ 1 := by linarith [abs_quadKernel_le_quarter ht_nonneg]
    have hB_pos : 0 < ‖s + (t : ℂ)‖ :=
      (by linarith : 0 < s.re + t).trans_le re_add_le_norm_add_ofReal
    rw [div_le_div_iff₀ (pow_pos hB_pos 3) (pow_pos hA_pos 3)]
    nlinarith [pow_nonneg hA_pos.le 3, abs_nonneg (quadKernel t)]
  have h_int_le :=
    norm_integral_le_of_norm_le (integrableOn_Ioi_one_div_add_cube hs_norm) h_bound
  rwa [integral_Ioi_one_div_add_cube hs_norm] at h_int_le

/-!
## Section 4: Explicit Bound on `‖logDeriv riemannZeta (-1 / 4 + t * I)‖`
-/

/-- For any `z : ℂ` with `1 < z.re`, `‖logDeriv riemannZeta z‖ ≤ ‖logDeriv riemannZeta (z.re : ℂ)‖`
via the absolute convergence of the von Mangoldt L-series `L ↗Λ`. -/
theorem norm_logDeriv_riemannZeta_le_of_one_lt_re {z : ℂ} (hz : 1 < z.re) :
    ‖logDeriv riemannZeta z‖ ≤ ‖logDeriv riemannZeta (z.re : ℂ)‖ := by
  have hz_re : 1 < (z.re : ℂ).re := by simpa using hz
  have h1 : logDeriv riemannZeta z = -L ↗Λ z := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz, logDeriv_apply,
      neg_div, neg_neg]
  have h2 : logDeriv riemannZeta (z.re : ℂ) = -L ↗Λ (z.re : ℂ) := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hz_re, logDeriv_apply,
      neg_div, neg_neg]
  rw [h1, h2, norm_neg, norm_neg]
  have h_sum : Summable fun n : ℕ ↦ ‖LSeries.term ↗Λ z n‖ :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hz).norm
  have h_term : ∀ n : ℕ, LSeries.term ↗Λ (z.re : ℂ) n = ((‖LSeries.term ↗Λ z n‖ : ℝ) : ℂ) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, LSeries.norm_term_eq]
      simp only [hn, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.ofReal_div,
        Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  have h_tsum_re : L ↗Λ (z.re : ℂ) = ((∑' n : ℕ, ‖LSeries.term ↗Λ z n‖ : ℝ) : ℂ) := by
    unfold LSeries
    rw [tsum_congr h_term, Complex.ofReal_tsum]
  rw [h_tsum_re, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _)]
  exact norm_tsum_le_tsum_norm h_sum

/-- Exact identity for
`Complex.normSq (Complex.cos (x + y * I)) - Complex.normSq (Complex.sin (x + y * I))`:
for all `x, y : ℝ`,
$$\operatorname{normSq}(\cos(x + y i)) - \operatorname{normSq}(\sin(x + y i)) = \cos(2x).$$ -/
theorem normSq_cos_sub_normSq_sin (x y : ℝ) :
    Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * I)) -
      Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * I)) = Real.cos (2 * x) := by
  rw [Complex.cos_add_mul_I, Complex.sin_add_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
  rw [Complex.normSq_apply, Complex.normSq_apply]
  simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, I_re, zero_mul,
    add_zero, I_im, mul_one, sub_self, sub_im, mul_im, add_im]
  calc
    _ = (Real.cos x ^ 2 - Real.sin x ^ 2) * (Real.cosh y ^ 2 - Real.sinh y ^ 2) := by ring
    _ = Real.cos (2 * x) := by rw [Real.cosh_sq_sub_sinh_sq y, mul_one, ← Real.cos_two_mul']

/-- For all `t : ℝ`, `Complex.cos (π * (-1 / 4 + (t : ℂ) * I) / 2) ≠ 0` and
`‖Complex.tan (π * (-1 / 4 + (t : ℂ) * I) / 2)‖ ≤ 1`. -/
theorem cos_ne_zero_and_norm_tan_le_one_leftVertical (t : ℝ) :
    Complex.cos (π * ((-1 / 4 : ℂ) + (t : ℂ) * I) / 2) ≠ 0 ∧
      ‖Complex.tan (π * ((-1 / 4 : ℂ) + (t : ℂ) * I) / 2)‖ ≤ 1 := by
  set x : ℝ := -Real.pi / 8
  set y : ℝ := Real.pi * t / 2
  have h_arg : π * ((-1 / 4 : ℂ) + (t : ℂ) * I) / 2 = (x : ℂ) + (y : ℂ) * I := by
    dsimp [x, y]
    push_cast
    ring
  rw [h_arg]
  have h_diff := normSq_cos_sub_normSq_sin x y
  have h_cos2x : Real.cos (2 * x) = Real.sqrt 2 / 2 := by
    have h2x : 2 * x = -(Real.pi / 4) := by dsimp [x]; ring
    rw [h2x, Real.cos_neg, Real.cos_pi_div_four]
  rw [h_cos2x] at h_diff
  have h_sqrt2_pos : 0 < Real.sqrt 2 / 2 := by positivity
  have h_sin_nonneg : 0 ≤ Complex.normSq (Complex.sin ((x : ℂ) + (y : ℂ) * I)) :=
    Complex.normSq_nonneg _
  have h_cos_pos : 0 < Complex.normSq (Complex.cos ((x : ℂ) + (y : ℂ) * I)) := by linarith
  have h_cos_ne : Complex.cos ((x : ℂ) + (y : ℂ) * I) ≠ 0 :=
    Complex.normSq_pos.mp h_cos_pos
  refine ⟨h_cos_ne, ?_⟩
  rw [Complex.tan_eq_sin_div_cos, norm_div]
  have h_norm_cos_pos : 0 < ‖Complex.cos ((x : ℂ) + (y : ℂ) * I)‖ := norm_pos_iff.mpr h_cos_ne
  rw [div_le_one₀ h_norm_cos_pos]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  linarith

/-- For all `t : ℝ`, `(-1 / 4 : ℂ) + (t : ℂ) * I` is not an integer `(n : ℂ)`. -/
theorem leftVertical_ne_intCast (t : ℝ) (n : ℤ) :
    (-1 / 4 : ℂ) + (t : ℂ) * I ≠ (n : ℂ) := by
  intro h
  have hre := congrArg Complex.re h
  simp only [add_re, neg_re, div_ofNat_re, one_re, mul_re, ofReal_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, sub_self, add_zero, intCast_re] at hre
  have h4_real : (-1 : ℝ) = ((4 * n : ℤ) : ℝ) := by push_cast; linarith
  have h4 : (-1 : ℤ) = 4 * n := by exact_mod_cast h4_real
  omega

/-- For all `t : ℝ`, `riemannZeta ((-1 / 4 : ℂ) + (t : ℂ) * I) ≠ 0`. -/
theorem riemannZeta_leftVertical_ne_zero (t : ℝ) :
    riemannZeta ((-1 / 4 : ℂ) + (t : ℂ) * I) ≠ 0 := by
  set s : ℂ := (-1 / 4 : ℂ) + (t : ℂ) * I
  have h1s_re : 1 < (1 - s).re := by simp [s]; norm_num
  have h1s_nat : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hre
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1s_one : 1 - s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [one_re] at hre
    linarith
  have h_fe := riemannZeta_one_sub h1s_nat h1s_one
  rw [sub_sub_cancel] at h_fe
  rw [h_fe]
  have h1 : (2 : ℂ) ≠ 0 := two_ne_zero
  have h2 : (2 * π : ℂ) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    left
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have h3 : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have h4 : Complex.cos (π * (1 - s) / 2) ≠ 0 := by
    intro hcos
    rw [Complex.cos_eq_zero_iff] at hcos
    obtain ⟨k, hk⟩ := hcos
    have hpi_ne : (π : ℂ) ≠ 0 := mod_cast Real.pi_ne_zero
    have h1s_eq : 1 - s = 2 * k + 1 := by
      apply mul_right_cancel₀ hpi_ne
      calc
        (1 - s) * π = (π * (1 - s) / 2) * 2 := by ring
        _ = ((2 * k + 1) * π / 2) * 2 := by rw [hk]
        _ = (2 * k + 1) * π := by ring
    exact leftVertical_ne_intCast t (-2 * k) (by push_cast; linear_combination -h1s_eq)
  have h5 : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h1s_re
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4) h5

/-- Bound on `‖Complex.log ((3 / 4 : ℂ) + (t : ℂ) * I)‖` for all `t : ℝ`:
`‖Complex.log ((3 / 4 : ℂ) + (t : ℂ) * I)‖ ≤ Real.log (|t| + 2) + Real.pi`. -/
theorem norm_log_three_fourths_add_mul_I_le (t : ℝ) :
    ‖Complex.log ((3 / 4 : ℂ) + (t : ℂ) * I)‖ ≤ Real.log (|t| + 2) + Real.pi := by
  set w : ℂ := (3 / 4 : ℂ) + (t : ℂ) * I
  have hw_re : w.re = 3 / 4 := by simp [w]
  have hw_im : w.im = t := by simp [w]
  have hw_norm_ge : 3 / 4 ≤ ‖w‖ := by
    have h := Complex.re_le_norm w
    linarith
  have hw_norm_le : ‖w‖ ≤ |t| + 2 := by
    have h := Complex.norm_le_abs_re_add_abs_im w
    rw [hw_re, hw_im, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)] at h
    linarith
  have ht2_pos : 0 < |t| + 2 := by positivity
  have hw_norm_pos : 0 < ‖w‖ := by linarith
  have h_inv_le : (|t| + 2)⁻¹ ≤ ‖w‖ := by
    have h1 : (|t| + 2)⁻¹ ≤ (2 : ℝ)⁻¹ :=
      inv_anti₀ (by norm_num) (by linarith [abs_nonneg t])
    linarith
  have h_abs_log : |Real.log ‖w‖| ≤ Real.log (|t| + 2) := by
    rw [abs_le]
    refine ⟨?_, Real.log_le_log hw_norm_pos hw_norm_le⟩
    rw [← Real.log_inv]
    exact Real.log_le_log (by positivity) h_inv_le
  rw [← Complex.re_add_im (Complex.log w), Complex.log_re, Complex.log_im]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_I, mul_one]
  exact add_le_add h_abs_log (Complex.abs_arg_le_pi w)

/-- Bound on `‖Complex.digamma ((-1 / 4 : ℂ) + (t : ℂ) * I)‖` for all `t : ℝ`:
$$\left\|\psi\!\left(-\frac{1}{4} + t i\right)\right\|
  \le \log(|t| + 2) + \pi + \frac{2 + \pi}{3} + 4.$$ -/
theorem norm_digamma_leftVertical_le (t : ℝ) :
    ‖Complex.digamma ((-1 / 4 : ℂ) + (t : ℂ) * I)‖ ≤
      Real.log (|t| + 2) + Real.pi + (2 + Real.pi) / 3 + 4 := by
  set s : ℂ := (-1 / 4 : ℂ) + (t : ℂ) * I
  set w : ℂ := (3 / 4 : ℂ) + (t : ℂ) * I
  have h_sw : s + 1 = w := by dsimp [s, w]; ring
  have hs_nat : ∀ m : ℕ, s ≠ -(m : ℂ) :=
    fun m ↦ by simpa using leftVertical_ne_intCast t (-m)
  have h_step : Complex.digamma s = (Complex.digamma w - Complex.log w) + Complex.log w - s⁻¹ := by
    have h := Complex.digamma_apply_add_one s hs_nat
    rw [h_sw] at h
    linear_combination -h
  have hw_re : 0 < w.re := by simp [w]
  have hw_norm : 3 / 4 ≤ ‖w‖ := by
    have h := Complex.re_le_norm w
    simp [w] at h
    linarith
  have hs_norm : 1 / 4 ≤ ‖s‖ := by
    have h := Complex.abs_re_le_norm s
    have hre : s.re = -1 / 4 := by simp [s]
    rw [hre] at h
    norm_num at h
    exact h
  have h1 : ‖Complex.digamma w - Complex.log w‖ ≤ (2 + Real.pi) / 3 := by
    refine (norm_digamma_sub_log_le_two_add_pi_div_four_norm hw_re).trans ?_
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have h2 : ‖Complex.log w‖ ≤ Real.log (|t| + 2) + Real.pi :=
    norm_log_three_fourths_add_mul_I_le t
  have h3 : ‖s⁻¹‖ ≤ 4 := by
    rw [norm_inv]
    simpa using inv_anti₀ (by norm_num) hs_norm
  change ‖Complex.digamma s‖ ≤ _
  rw [h_step]
  have h_tri1 := norm_sub_le ((Complex.digamma w - Complex.log w) + Complex.log w) s⁻¹
  have h_tri2 := norm_add_le (Complex.digamma w - Complex.log w) (Complex.log w)
  linarith

/-- The explicit additive constant in the vertical growth bound for
`‖logDeriv riemannZeta (-1 / 4 + t * I)‖`. -/
noncomputable def leftVerticalLogDerivConst : ℝ :=
  ‖logDeriv riemannZeta (5 / 4 : ℂ)‖ + Real.log (2 * Real.pi) +
    Real.pi + (2 + Real.pi) / 3 + 4 + Real.pi / 2

theorem leftVerticalLogDerivConst_pos : 0 < leftVerticalLogDerivConst := by
  unfold leftVerticalLogDerivConst
  have h_norm : 0 ≤ ‖logDeriv riemannZeta (5 / 4 : ℂ)‖ := norm_nonneg _
  have h_pi : 0 < Real.pi := Real.pi_pos
  have h_log : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  positivity

/-- **Explicit Vertical Growth Bound for `logDeriv riemannZeta` on `s.re = -1 / 4`**:
For all `t : ℝ`,
$$\left\|\frac{\zeta'}{\zeta}\!\left(-\frac{1}{4} + t i\right)\right\|
  \le \log(|t| + 2) + C_{\text{left}}.$$ -/
theorem norm_logDeriv_riemannZeta_leftVertical_le (t : ℝ) :
    ‖logDeriv riemannZeta ((-1 / 4 : ℂ) + (t : ℂ) * I)‖ ≤
      Real.log (|t| + 2) + leftVerticalLogDerivConst := by
  set s : ℂ := (-1 / 4 : ℂ) + (t : ℂ) * I
  have h_fe :
      logDeriv riemannZeta s =
        -logDeriv riemannZeta (1 - s) + Complex.log (2 * π) - Complex.digamma s +
          π / 2 * Complex.tan (π * s / 2) :=
    logDeriv_riemannZeta_one_sub (leftVertical_ne_intCast t) (riemannZeta_leftVertical_ne_zero t)
  have h1s_re : (1 - s).re = 5 / 4 := by simp [s]; ring
  have h1 : ‖-logDeriv riemannZeta (1 - s)‖ ≤ ‖logDeriv riemannZeta (5 / 4 : ℂ)‖ := by
    rw [norm_neg]
    have h := norm_logDeriv_riemannZeta_le_of_one_lt_re (z := 1 - s) (by rw [h1s_re]; norm_num)
    rwa [h1s_re, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_ofNat] at h
  have h2 : ‖Complex.log (2 * π)‖ = Real.log (2 * Real.pi) := by
    have h_pos : (0 : ℝ) < 2 * Real.pi := by positivity
    rw [show (2 * π : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log h_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.log_pos (by linarith [Real.pi_gt_three]))]
  have h3 : ‖Complex.digamma s‖ ≤ Real.log (|t| + 2) + Real.pi + (2 + Real.pi) / 3 + 4 :=
    norm_digamma_leftVertical_le t
  have h4 : ‖(π : ℂ) / 2 * Complex.tan (π * s / 2)‖ ≤ Real.pi / 2 := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_ofNat]
    have h_tan : ‖Complex.tan (π * s / 2)‖ ≤ 1 :=
      (cos_ne_zero_and_norm_tan_le_one_leftVertical t).2
    nlinarith [Real.pi_pos]
  change ‖logDeriv riemannZeta s‖ ≤ _
  rw [h_fe]
  have h_tri1 :=
    norm_add_le (-logDeriv riemannZeta (1 - s) + Complex.log (2 * π) - Complex.digamma s)
      (π / 2 * Complex.tan (π * s / 2))
  have h_tri2 :=
    norm_sub_le (-logDeriv riemannZeta (1 - s) + Complex.log (2 * π)) (Complex.digamma s)
  have h_tri3 := norm_add_le (-logDeriv riemannZeta (1 - s)) (Complex.log (2 * π))
  unfold leftVerticalLogDerivConst
  linarith

/-- Existential summary of `norm_logDeriv_riemannZeta_leftVertical_le`:
there exists `C > 0` such that for all `t : ℝ`,
`‖logDeriv riemannZeta (-1 / 4 + (t : ℂ) * I)‖ ≤ Real.log (|t| + 2) + C`. -/
theorem exists_norm_logDeriv_riemannZeta_leftVertical_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖logDeriv riemannZeta ((-1 / 4 : ℂ) + (t : ℂ) * I)‖ ≤ Real.log (|t| + 2) + C :=
  ⟨leftVerticalLogDerivConst, leftVerticalLogDerivConst_pos,
    norm_logDeriv_riemannZeta_leftVertical_le⟩

/-!
## Section 5: Pure-Constant Left-Vertical Zeta Bound &
  Vertical Integral of `Re(digamma (a + t * I))`
-/

/-- Telescoping majorant `64 / n ^ (1 / 8)` for `log n / n ^ (5 / 4)`. -/
noncomputable def rpowTelescope (n : ℕ) : ℝ :=
  if n = 0 then 0 else 64 / (n : ℝ) ^ (1 / 8 : ℝ)

theorem rpowTelescope_zero : rpowTelescope 0 = 0 := rfl

theorem rpowTelescope_one : rpowTelescope 1 = 64 := by
  simp [rpowTelescope]

theorem rpowTelescope_nonneg (n : ℕ) : 0 ≤ rpowTelescope n := by
  unfold rpowTelescope
  split_ifs with hn
  · exact le_rfl
  · positivity

/-- For every `n ≥ 2`,
`Real.log (n : ℝ) / (n : ℝ) ^ (5 / 4 : ℝ) ≤ rpowTelescope (n - 1) - rpowTelescope n`. -/
theorem log_nat_div_rpow_five_fourths_le_rpowTelescope_sub {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n : ℝ) / (n : ℝ) ^ (5 / 4 : ℝ) ≤ rpowTelescope (n - 1) - rpowTelescope n := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n - 1 ≠ 0 := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by positivity
  set a : ℝ := ((n - 1 : ℕ) : ℝ) ^ (1 / 8 : ℝ)
  set b : ℝ := (n : ℝ) ^ (1 / 8 : ℝ)
  have ha_pos : 0 < a := Real.rpow_pos_of_pos hn1_pos _
  have hb_pos : 0 < b := Real.rpow_pos_of_pos hn_pos _
  have hab : a ≤ b := by
    refine Real.rpow_le_rpow hn1_pos.le ?_ (by positivity)
    exact_mod_cast Nat.sub_le n 1
  have ha8 : a ^ 8 = ((n - 1 : ℕ) : ℝ) := by
    dsimp [a]
    rw [← Real.rpow_natCast _ 8, ← Real.rpow_mul hn1_pos.le]
    norm_num
  have hb8 : b ^ 8 = (n : ℝ) := by
    dsimp [b]
    rw [← Real.rpow_natCast _ 8, ← Real.rpow_mul hn_pos.le]
    norm_num
  have hb10 : b ^ 10 = (n : ℝ) ^ (5 / 4 : ℝ) := by
    dsimp [b]
    rw [← Real.rpow_natCast _ 10, ← Real.rpow_mul hn_pos.le]
    norm_num
  have hlog_le : Real.log (n : ℝ) ≤ 8 * b := by
    have hlog_b8 : Real.log (n : ℝ) = 8 * Real.log b := by
      rw [← hb8, Real.log_pow, Nat.cast_ofNat]
    have hlog_b : Real.log b ≤ b - 1 := Real.log_le_sub_one_of_pos hb_pos
    linarith
  have h_b8_sub_a8 : b ^ 8 - a ^ 8 = 1 := by
    rw [hb8, ha8, Nat.cast_sub (by omega), Nat.cast_one]
    ring
  have h_diff_ge : 1 ≤ 8 * b ^ 7 * (b - a) := by
    have h_ba : 0 ≤ b - a := sub_nonneg.mpr hab
    have h_ba1 : b + a ≤ 2 * b := by linarith
    have h_ba2 : b ^ 2 + a ^ 2 ≤ 2 * b ^ 2 := by
      have : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha_pos.le hab 2
      linarith
    have h_ba4 : b ^ 4 + a ^ 4 ≤ 2 * b ^ 4 := by
      have : a ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ ha_pos.le hab 4
      linarith
    calc
      (1 : ℝ) = b ^ 8 - a ^ 8 := h_b8_sub_a8.symm
      _ = (b ^ 4 + a ^ 4) * (b ^ 2 + a ^ 2) * (b + a) * (b - a) := by ring
      _ ≤ (2 * b ^ 4) * (2 * b ^ 2) * (2 * b) * (b - a) := by
          gcongr
      _ = 8 * b ^ 7 * (b - a) := by ring
  have h_tele_eq : rpowTelescope (n - 1) - rpowTelescope n = 64 * (b - a) / (a * b) := by
    simp only [rpowTelescope, hn0, hn1, ↓reduceIte]
    change 64 / a - 64 / b = 64 * (b - a) / (a * b)
    have ha_ne : a ≠ 0 := ha_pos.ne'
    have hb_ne : b ≠ 0 := hb_pos.ne'
    field_simp
  rw [ ← hb10, h_tele_eq]
  calc
    Real.log (n : ℝ) / b ^ 10
      ≤ (8 * b) / b ^ 10 := by gcongr
    _ = 8 / b ^ 9 := by
        have hb_ne : b ≠ 0 := hb_pos.ne'
        field_simp [hb_ne]
    _ ≤ 64 * (b - a) / (a * b) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h_mul : a * b ≤ b ^ 2 * (8 * b ^ 7 * (b - a)) := by
          calc
            a * b ≤ b * b := by gcongr
            _ = b ^ 2 * 1 := by ring
            _ ≤ b ^ 2 * (8 * b ^ 7 * (b - a)) := by gcongr
        linarith

/-- For every `n ≥ 2`,
`‖LSeries.term ↗Λ (5 / 4 : ℂ) n‖ ≤ rpowTelescope (n - 1) - rpowTelescope n`. -/
theorem norm_term_vonMangoldt_five_fourths_le {n : ℕ} (hn : 2 ≤ n) :
    ‖LSeries.term (↗Λ) (5 / 4 : ℂ) n‖ ≤ rpowTelescope (n - 1) - rpowTelescope n := by
  rw [LSeries.norm_term_eq]
  have hn0 : n ≠ 0 := by omega
  simp only [hn0, ↓reduceIte, Complex.norm_real]
  rw [Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hre : (5 / 4 : ℂ).re = 5 / 4 := by norm_num
  rw [hre]
  refine (div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (by positivity)).trans ?_
  exact log_nat_div_rpow_five_fourths_le_rpowTelescope_sub hn

theorem sum_range_norm_term_vonMangoldt_five_fourths_le_sub :
    ∀ N : ℕ, 2 ≤ N →
      ∑ n ∈ Finset.range N, ‖LSeries.term (↗Λ) (5 / 4 : ℂ) n‖ ≤
        64 - rpowTelescope (N - 1) := by
  intro N hN
  induction N with
  | zero => omega
  | succ N ih =>
    rcases eq_or_lt_of_le hN with h_eq | h_lt
    · have hN1 : N = 1 := by omega
      subst hN1
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp [LSeries.term, rpowTelescope_one]
    · have hN2 : 2 ≤ N := by omega
      rw [Finset.sum_range_succ]
      have h1 := ih hN2
      have h2 := norm_term_vonMangoldt_five_fourths_le hN2
      rw [Nat.add_sub_cancel]
      linarith

theorem sum_range_norm_term_vonMangoldt_five_fourths_le (N : ℕ) :
    ∑ n ∈ Finset.range N, ‖LSeries.term (↗Λ) (5 / 4 : ℂ) n‖ ≤ 64 := by
  rcases lt_or_ge N 2 with hlt | hge
  · interval_cases N
    · simp
    · rw [Finset.sum_range_one, LSeries.term_zero, norm_zero]
      norm_num
  · have h := sum_range_norm_term_vonMangoldt_five_fourths_le_sub N hge
    have h_nonneg := rpowTelescope_nonneg (N - 1)
    linarith

/-- **Explicit Pure-Constant Bound on `‖logDeriv riemannZeta (5 / 4 : ℂ)‖`**:
$$\left\|\frac{\zeta'}{\zeta}\!\left(\frac{5}{4}\right)\right\| \le 64.$$ -/
theorem norm_logDeriv_riemannZeta_five_fourths_le :
    ‖logDeriv riemannZeta (5 / 4 : ℂ)‖ ≤ 64 := by
  have h_re : 1 < (5 / 4 : ℂ).re := by norm_num
  have h_eq : logDeriv riemannZeta (5 / 4 : ℂ) = -L (↗Λ) (5 / 4 : ℂ) := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h_re, logDeriv_apply,
      neg_div, neg_neg]
  rw [h_eq, norm_neg]
  unfold LSeries
  have h_sum : Summable (fun n : ℕ ↦ ‖LSeries.term (↗Λ) (5 / 4 : ℂ) n‖) :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt h_re).norm
  refine (norm_tsum_le_tsum_norm h_sum).trans ?_
  exact h_sum.tsum_le_of_sum_range_le sum_range_norm_term_vonMangoldt_five_fourths_le

/-- Explicit upper bound `leftVerticalLogDerivConst ≤ 85`. -/
theorem leftVerticalLogDerivConst_le :
    leftVerticalLogDerivConst ≤ 85 := by
  unfold leftVerticalLogDerivConst
  have h1 := norm_logDeriv_riemannZeta_five_fourths_le
  have h_pi : Real.pi < 4 := Real.pi_lt_four
  have h_2pi_pos : 0 < 2 * Real.pi := by positivity
  have h_log : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 :=
    Real.log_le_sub_one_of_pos h_2pi_pos
  linarith

/-- **Explicit Pure-Constant Bound on `‖logDeriv riemannZeta (-1 / 4 + t * I)‖`**:
For all `t : ℝ`,
$$\left\|\frac{\zeta'}{\zeta}\!\left(-\frac{1}{4} + t i\right)\right\| \le \log(|t| + 2) + 85.$$ -/
theorem norm_logDeriv_riemannZeta_leftVertical_le_eighty_five (t : ℝ) :
    ‖logDeriv riemannZeta ((-1 / 4 : ℂ) + (t : ℂ) * I)‖ ≤ Real.log (|t| + 2) + 85 := by
  refine (norm_logDeriv_riemannZeta_leftVertical_le t).trans ?_
  linarith [leftVerticalLogDerivConst_le]

/-!
### Section 5B: Exact Vertical Integral of `Re(Complex.digamma (a + t * I))` on `[-U, U]`
-/

/-- Norm squared of `(a : ℂ) + (t : ℂ) * I` is `a ^ 2 + t ^ 2`. -/
theorem norm_sq_ofReal_add_mul_I (a t : ℝ) :
    ‖(a : ℂ) + (t : ℂ) * I‖ ^ 2 = a ^ 2 + t ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [sq]

/-- For any `a, t : ℝ`,
`(Complex.log ((a : ℂ) + (t : ℂ) * I)).re = 1 / 2 * Real.log (a ^ 2 + t ^ 2)`. -/
theorem re_log_ofReal_add_mul_I (a t : ℝ) :
    (Complex.log ((a : ℂ) + (t : ℂ) * I)).re = 1 / 2 * Real.log (a ^ 2 + t ^ 2) := by
  rw [Complex.log_re, ← norm_sq_ofReal_add_mul_I a t, Real.log_pow, Nat.cast_ofNat]
  ring

/-- For any `a, t : ℝ`,
`(1 / (2 * ((a : ℂ) + (t : ℂ) * I))).re = a / (2 * (a ^ 2 + t ^ 2))`. -/
theorem re_half_inv_ofReal_add_mul_I (a t : ℝ) :
    ((1 : ℂ) / (2 * ((a : ℂ) + (t : ℂ) * I))).re = a / (2 * (a ^ 2 + t ^ 2)) := by
  simp only [mul_inv, mul_re, inv_re, re_ofNat, normSq_ofNat, inv_im, im_ofNat, neg_zero,
    one_re, one_im, add_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add, zero_mul, sub_zero, Complex.normSq_eq_norm_sq,
    norm_sq_ofReal_add_mul_I, div_eq_mul_inv]
  ring

/-- Exact derivative of
`t ↦ t / 2 * Real.log (a ^ 2 + t ^ 2) - t + a * Real.arctan (t / a)` for `0 < a`. -/
theorem hasDerivAt_vertical_re_log_antideriv {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ u / 2 * Real.log (a ^ 2 + u ^ 2) - u + a * Real.arctan (u / a))
      (1 / 2 * Real.log (a ^ 2 + t ^ 2)) t := by
  have ha_ne : a ≠ 0 := ha.ne'
  have hpos : 0 < a ^ 2 + t ^ 2 := by positivity
  have hpos_ne : a ^ 2 + t ^ 2 ≠ 0 := hpos.ne'
  have hd_u2 : HasDerivAt (fun u : ℝ ↦ u / 2) (1 / 2) t := by
    simpa using (hasDerivAt_id t).div_const 2
  have hd_sq : HasDerivAt (fun u : ℝ ↦ a ^ 2 + u ^ 2) (2 * t) t := by
    simpa [Pi.pow_def, pow_one] using ((hasDerivAt_id t).pow 2).const_add (a ^ 2)
  have hd_log : HasDerivAt (fun u : ℝ ↦ Real.log (a ^ 2 + u ^ 2)) (2 * t / (a ^ 2 + t ^ 2)) t := by
    have hd := (Real.hasDerivAt_log hpos_ne).comp t hd_sq
    refine hd.congr_deriv ?_
    ring
  have hd_prod := hd_u2.mul hd_log
  have hd_atan : HasDerivAt (fun u : ℝ ↦ a * Real.arctan (u / a)) (a ^ 2 / (a ^ 2 + t ^ 2)) t := by
    have hd := (((hasDerivAt_id t).div_const a).arctan).const_mul a
    refine hd.congr_deriv ?_
    simp only [id_eq]
    field_simp [ha_ne, hpos_ne]
  have hd_total := (hd_prod.sub (hasDerivAt_id t)).add hd_atan
  refine hd_total.congr_deriv ?_
  field_simp [hpos_ne]
  ring

/-- Exact derivative of the combined vertical main-term antiderivative
`t ↦ t / 2 * Real.log (a ^ 2 + t ^ 2) - t + (a - 1 / 2) * Real.arctan (t / a)` for `0 < a`. -/
theorem hasDerivAt_vertical_main_antideriv {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦ u / 2 * Real.log (a ^ 2 + u ^ 2) - u + (a - 1 / 2) * Real.arctan (u / a))
      (1 / 2 * Real.log (a ^ 2 + t ^ 2) - a / (2 * (a ^ 2 + t ^ 2))) t := by
  have ha_ne : a ≠ 0 := ha.ne'
  have hpos : 0 < a ^ 2 + t ^ 2 := by positivity
  have hpos_ne : a ^ 2 + t ^ 2 ≠ 0 := hpos.ne'
  have hd1 := hasDerivAt_vertical_re_log_antideriv ha t
  have hd2 : HasDerivAt (fun u : ℝ ↦ (1 / 2 : ℝ) * Real.arctan (u / a))
      (a / (2 * (a ^ 2 + t ^ 2))) t := by
    have hd := (((hasDerivAt_id t).div_const a).arctan).const_mul (1 / 2 : ℝ)
    refine hd.congr_deriv ?_
    simp only [id_eq]
    field_simp [ha_ne, hpos_ne]
  have h_fun_eq :
      (fun u : ℝ ↦ u / 2 * Real.log (a ^ 2 + u ^ 2) - u + (a - 1 / 2) * Real.arctan (u / a)) =
        fun u : ℝ ↦ (u / 2 * Real.log (a ^ 2 + u ^ 2) - u + a * Real.arctan (u / a)) -
          (1 / 2 : ℝ) * Real.arctan (u / a) := by
    ext u
    ring
  rw [h_fun_eq]
  exact hd1.sub hd2

/-- **Exact Closed-Form Vertical Integral of `Re(log (a + t * I) - 1 / (2 * (a + t * I)))`**:
For all `0 < a` and `U : ℝ`,
$$\int_{-U}^U \operatorname{Re}\left(\log(a + t i) - \frac{1}{2(a + t i)}\right) dt
  = U \log(a^2 + U^2) - 2 U + (2 a - 1) \arctan\left(\frac{U}{a}\right).$$ -/
theorem intervalIntegral_re_log_sub_half_inv_vertical {a U : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in (-U)..U,
      (Complex.log ((a : ℂ) + (t : ℂ) * I) - 1 / (2 * ((a : ℂ) + (t : ℂ) * I))).re) =
      U * Real.log (a ^ 2 + U ^ 2) - 2 * U + (2 * a - 1) * Real.arctan (U / a) := by
  have h_congr :
      (fun t : ℝ ↦ (Complex.log ((a : ℂ) + (t : ℂ) * I) - 1 / (2 * ((a : ℂ) + (t : ℂ) * I))).re) =
        fun t : ℝ ↦ 1 / 2 * Real.log (a ^ 2 + t ^ 2) - a / (2 * (a ^ 2 + t ^ 2)) := by
    ext t
    rw [sub_re, re_log_ofReal_add_mul_I a t, re_half_inv_ofReal_add_mul_I a t]
  rw [h_congr]
  have hderiv : ∀ t ∈ uIcc (-U) U,
      HasDerivAt
        (fun u : ℝ ↦ u / 2 * Real.log (a ^ 2 + u ^ 2) - u + (a - 1 / 2) * Real.arctan (u / a))
        (1 / 2 * Real.log (a ^ 2 + t ^ 2) - a / (2 * (a ^ 2 + t ^ 2))) t :=
    fun t _ ↦ hasDerivAt_vertical_main_antideriv ha t
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ 1 / 2 * Real.log (a ^ 2 + t ^ 2) - a / (2 * (a ^ 2 + t ^ 2)))
      volume (-U) U := by
    refine Continuous.intervalIntegrable ?_ (-U) U
    have h_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 := fun t ↦ by positivity
    have h_ne2 : ∀ t : ℝ, 2 * (a ^ 2 + t ^ 2) ≠ 0 := fun t ↦ by positivity
    refine Continuous.sub
      (continuous_const.mul (Continuous.log (by fun_prop) h_ne))
      (Continuous.div continuous_const (by fun_prop) h_ne2)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h_neg_div : (-U) / a = -(U / a) := neg_div a U
  rw [neg_sq, h_neg_div, Real.arctan_neg]
  ring

/-- Exact interval integral
`∫ t in (-U)..U, 1 / (2 * (a ^ 2 + t ^ 2)) = (1 / a) * Real.arctan (U / a)`
for `0 < a`. -/
theorem intervalIntegral_one_div_two_add_sq_vertical {a U : ℝ} (ha : 0 < a) :
    (∫ t : ℝ in (-U)..U, 1 / (2 * (a ^ 2 + t ^ 2))) = (1 / a) * Real.arctan (U / a) := by
  have ha_ne : a ≠ 0 := ha.ne'
  have hderiv : ∀ t ∈ uIcc (-U) U,
      HasDerivAt (fun u : ℝ ↦ (1 / (2 * a)) * Real.arctan (u / a))
        (1 / (2 * (a ^ 2 + t ^ 2))) t := by
    intro t _
    have hpos : a ^ 2 + t ^ 2 ≠ 0 := by positivity
    have hd := (((hasDerivAt_id t).div_const a).arctan).const_mul (1 / (2 * a))
    refine hd.congr_deriv ?_
    simp only [id_eq]
    field_simp [ha_ne, hpos]
  have hint : IntervalIntegrable (fun t : ℝ ↦ 1 / (2 * (a ^ 2 + t ^ 2))) volume (-U) U := by
    refine Continuous.intervalIntegrable ?_ (-U) U
    have h_ne : ∀ t : ℝ, 2 * (a ^ 2 + t ^ 2) ≠ 0 := fun t ↦ by positivity
    exact Continuous.div continuous_const (by fun_prop) h_ne
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h_neg_div : (-U) / a = -(U / a) := neg_div a U
  rw [h_neg_div, Real.arctan_neg]
  ring

/-- Pointwise bound on the vertical line `s = a + t * I` (`0 < a`):
`|(Complex.digamma (a + t * I)).re - (Complex.log (a + t * I) - 1 / (2 * (a + t * I))).re| ≤`
`1 / (2 * (a ^ 2 + t ^ 2))`. -/
theorem abs_re_digamma_sub_main_vertical_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |(Complex.digamma ((a : ℂ) + (t : ℂ) * I)).re -
        (Complex.log ((a : ℂ) + (t : ℂ) * I) - 1 / (2 * ((a : ℂ) + (t : ℂ) * I))).re| ≤
      1 / (2 * (a ^ 2 + t ^ 2)) := by
  set s : ℂ := (a : ℂ) + (t : ℂ) * I
  have hs_re : 0 < s.re := by simp [s, ha]
  have h_re_sub :
      (Complex.digamma s).re - (Complex.log s - 1 / (2 * s)).re =
        (Complex.digamma s - Complex.log s + 1 / (2 * s)).re := by
    simp only [sub_re, add_re]
    ring
  rw [h_re_sub]
  refine (Complex.abs_re_le_norm _).trans ?_
  have h_norm := norm_digamma_sub_log_add_half_inv_le_norm_sq hs_re
  rwa [norm_sq_ofReal_add_mul_I a t] at h_norm

/-- Continuity of `t ↦ (Complex.digamma ((a : ℂ) + (t : ℂ) * I)).re` for `0 < a`. -/
theorem continuous_re_digamma_vertical {a : ℝ} (ha : 0 < a) :
    Continuous (fun t : ℝ ↦ (Complex.digamma ((a : ℂ) + (t : ℂ) * I)).re) := by
  have h_cont_line : Continuous (fun t : ℝ ↦ (a : ℂ) + (t : ℂ) * I) := by fun_prop
  have h_maps : MapsTo (fun t : ℝ ↦ (a : ℂ) + (t : ℂ) * I) univ {s : ℂ | 0 < s.re} := by
    intro t _
    simp [ha]
  have h_cont_digamma : Continuous (fun t : ℝ ↦ Complex.digamma ((a : ℂ) + (t : ℂ) * I)) :=
    differentiableOn_digamma_rightHalfPlane.continuousOn.comp_continuous h_cont_line
      (fun t ↦ h_maps (mem_univ t))
  exact Complex.continuous_re.comp h_cont_digamma

/-- **Vertical Integral Approximation for `Re(Complex.digamma (a + t * I))` on `[-U, U]`**:
For all `0 < a` and `0 ≤ U`,
$$\left|\int_{-U}^U \operatorname{Re}\big(\psi(a + t i)\big) \, dt
  - \left(U \log(a^2 + U^2) - 2 U + (2 a - 1) \arctan\left(\frac{U}{a}\right)\right)\right|
  \le \frac{\pi}{2 a}.$$ -/
theorem abs_intervalIntegral_re_digamma_vertical_sub_le {a U : ℝ} (ha : 0 < a) (hU : 0 ≤ U) :
    |(∫ t : ℝ in (-U)..U, (Complex.digamma ((a : ℂ) + (t : ℂ) * I)).re) -
        (U * Real.log (a ^ 2 + U ^ 2) - 2 * U + (2 * a - 1) * Real.arctan (U / a))| ≤
      Real.pi / (2 * a) := by
  have hU_le : -U ≤ U := by linarith
  rw [← intervalIntegral_re_log_sub_half_inv_vertical ha]
  have h_int1 : IntervalIntegrable
      (fun t : ℝ ↦ (Complex.digamma ((a : ℂ) + (t : ℂ) * I)).re) volume (-U) U :=
    (continuous_re_digamma_vertical ha).intervalIntegrable (-U) U
  have h_int2 : IntervalIntegrable
      (fun t : ℝ ↦ (Complex.log ((a : ℂ) + (t : ℂ) * I) - 1 / (2 * ((a : ℂ) + (t : ℂ) * I))).re)
      volume (-U) U := by
    have h_eq :
        (fun t : ℝ ↦ (Complex.log ((a : ℂ) + (t : ℂ) * I) - 1 / (2 * ((a : ℂ) + (t : ℂ) * I))).re) =
          fun t : ℝ ↦ 1 / 2 * Real.log (a ^ 2 + t ^ 2) - a / (2 * (a ^ 2 + t ^ 2)) := by
      ext t
      rw [sub_re, re_log_ofReal_add_mul_I a t, re_half_inv_ofReal_add_mul_I a t]
    rw [h_eq]
    refine Continuous.intervalIntegrable ?_ (-U) U
    have h_ne : ∀ t : ℝ, a ^ 2 + t ^ 2 ≠ 0 := fun t ↦ by positivity
    have h_ne2 : ∀ t : ℝ, 2 * (a ^ 2 + t ^ 2) ≠ 0 := fun t ↦ by positivity
    exact Continuous.sub
      (continuous_const.mul (Continuous.log (by fun_prop) h_ne))
      (Continuous.div continuous_const (by fun_prop) h_ne2)
  have h_int_maj : IntervalIntegrable (fun t : ℝ ↦ 1 / (2 * (a ^ 2 + t ^ 2))) volume (-U) U := by
    refine Continuous.intervalIntegrable ?_ (-U) U
    have h_ne : ∀ t : ℝ, 2 * (a ^ 2 + t ^ 2) ≠ 0 := fun t ↦ by positivity
    exact Continuous.div continuous_const (by fun_prop) h_ne
  rw [← intervalIntegral.integral_sub h_int1 h_int2, ← Real.norm_eq_abs]
  have h_le := intervalIntegral.norm_integral_le_of_norm_le hU_le
    (f := fun t : ℝ ↦ (Complex.digamma ((a : ℂ) + (t : ℂ) * I)).re -
      (Complex.log ((a : ℂ) + (t : ℂ) * I) - 1 / (2 * ((a : ℂ) + (t : ℂ) * I))).re)
    (g := fun t : ℝ ↦ 1 / (2 * (a ^ 2 + t ^ 2)))
    (by
      filter_upwards with t _
      rw [Real.norm_eq_abs]
      exact abs_re_digamma_sub_main_vertical_le ha t)
    h_int_maj
  rw [intervalIntegral_one_div_two_add_sq_vertical ha] at h_le
  refine h_le.trans ?_
  have h_atan : Real.arctan (U / a) ≤ Real.pi / 2 := (Real.arctan_lt_pi_div_two (U / a)).le
  calc
    (1 / a) * Real.arctan (U / a) ≤ (1 / a) * (Real.pi / 2) :=
      mul_le_mul_of_nonneg_left h_atan (by positivity)
    _ = Real.pi / (2 * a) := by ring

/-- **Explicit Upper Bound on `∫ t in (-U)..U, Re(Complex.digamma (a + t * I))`
for `0 < a` and `1 ≤ U`**:
$$\int_{-U}^U \operatorname{Re}\big(\psi(a + t i)\big) \, dt
  \le 2 U \log U - 2 U + \pi a + \frac{a^2}{U} + \frac{\pi}{2 a}.$$ -/
theorem intervalIntegral_re_digamma_vertical_le {a U : ℝ} (ha : 0 < a) (hU : 1 ≤ U) :
    (∫ t : ℝ in (-U)..U, (Complex.digamma ((a : ℂ) + (t : ℂ) * I)).re) ≤
      2 * U * Real.log U - 2 * U + Real.pi * a + a ^ 2 / U + Real.pi / (2 * a) := by
  have hU_pos : 0 < U := zero_lt_one.trans_le hU
  have h_approx := (abs_le.mp (abs_intervalIntegral_re_digamma_vertical_sub_le ha hU_pos.le)).2
  have h_log_split : Real.log (a ^ 2 + U ^ 2) ≤ 2 * Real.log U + a ^ 2 / U ^ 2 := by
    have h_eq : a ^ 2 + U ^ 2 = U ^ 2 * (1 + a ^ 2 / U ^ 2) := by
      have hU2_ne : U ^ 2 ≠ 0 := by positivity
      field_simp [hU2_ne]
      ring
    rw [h_eq, Real.log_mul (by positivity) (by positivity), Real.log_pow, Nat.cast_ofNat]
    have h_one_add : Real.log (1 + a ^ 2 / U ^ 2) ≤ a ^ 2 / U ^ 2 := by
      have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + a ^ 2 / U ^ 2)
      linarith
    linarith
  have h_U_log : U * Real.log (a ^ 2 + U ^ 2) ≤ 2 * U * Real.log U + a ^ 2 / U := by
    have h1 := mul_le_mul_of_nonneg_left h_log_split hU_pos.le
    have h2 : U * (2 * Real.log U + a ^ 2 / U ^ 2) = 2 * U * Real.log U + a ^ 2 / U := by
      have hU_ne : U ≠ 0 := hU_pos.ne'
      field_simp [hU_ne]
    linarith
  have h_atan_nonneg : 0 ≤ Real.arctan (U / a) :=
    Real.arctan_nonneg.mpr (by positivity)
  have h_atan_le : Real.arctan (U / a) ≤ Real.pi / 2 :=
    (Real.arctan_lt_pi_div_two (U / a)).le
  have h_atan_term : (2 * a - 1) * Real.arctan (U / a) ≤ Real.pi * a := by
    have h1 : 2 * a * Real.arctan (U / a) ≤ 2 * a * (Real.pi / 2) :=
      mul_le_mul_of_nonneg_left h_atan_le (by positivity)
    linarith
  linarith

end ConjectureMachines.Riemann543.Semantics.DigammaBinet
