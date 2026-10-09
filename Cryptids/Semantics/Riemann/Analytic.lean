/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Harmonic.Defs
public import Cryptids.Semantics.Riemann.RegisterMachine
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.Int
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Cryptids.Semantics.Riemann.Schmidt
public import Cryptids.Semantics.Riemann.DigammaBinet
public import Cryptids.Semantics.Riemann.HorizontalBounds
public import Cryptids.Semantics.Riemann.WeightedStieltjes
public import Cryptids.Semantics.Riemann.VonMangoldtCount
public import Cryptids.Semantics.Riemann.ExplicitLarge

/-!
# Part II: Number-Theoretic & Analytic Bridge for `riemann_744` and `riemann_543`

This file develops the number-theoretic and real-analytic bridge between the elementary
Matiyasevich–Aaronson counterexample predicate `MatiyasevichRiemannCounterexample` (computed by
`riemann.nql`) and Mathlib's `RiemannHypothesis`.

## Mathematical Overview

For each integer $x > 253$ and $L_x = \operatorname{lcm}(1, \dots, x)$, the NQL program tests
whether
$$H_{L_x} > x \quad\text{and}\quad (H_{L_x} - x)^2 > x \cdot H_x^4.$$
We decompose the equivalence
$$\left(\exists x : \mathbb{N},\; \text{MatiyasevichRiemannCounterexample } x\right) \iff
  \neg \text{RiemannHypothesis}$$
into the following steps, proving all elementary, harmonic, Euler–Mascheroni, and Chebyshev-$\psi$
reductions completely in Lean 4 and isolating the classical complex-analytic number theory results
of Schoenfeld (1976) and Schmidt (1903):

1. **Rational and Real Reformulations**:
   - `matiyasevichRiemannCounterexample_iff_harmonic`: equivalence with the $\mathbb{Q}$-inequality.
   - `matiyasevichRiemannCounterexample_iff_real`: equivalence with the $\mathbb{R}$-inequality.
   - `matiyasevichRiemannCounterexample_iff_sqrt_lt`: single real inequality
     $253 < x \;\wedge\; \sqrt{x} \cdot H_x^2 < H_{\operatorname{lcm}(1,\dots,x)} - x$.
   - `matiyasevichRiemannCounterexample_iff_abs_and_sqrt_lt`: formulation with
     $|H_{\operatorname{lcm}(1,\dots,x)} - x| = H_{\operatorname{lcm}(1,\dots,x)} - x$.
2. **Identity $\psi(x) = \log \operatorname{lcm}(1, \dots, x)$ and Positivity of `lcmUpTo`**:
   - `lcmUpTo_pos`, `one_le_lcmUpTo`, `dvd_lcmUpTo`, `self_le_lcmUpTo`, `lcmUpTo_mono`.
   - `psi_eq_log_lcmUpTo : Chebyshev.psi x = Real.log (lcmUpTo x)` and
     `exp_psi_eq_lcmUpTo : Real.exp (Chebyshev.psi x) = lcmUpTo x`.
3. **Euler–Mascheroni & Harmonic-to-Chebyshev-$\psi$ Bounds**:
   - $\psi(x) + \gamma < H_{\operatorname{lcm}(1,\dots,x)} \le \psi(x) + 1$
     (`psi_add_eulerMascheroniConstant_lt_harmonic_lcmUpTo`, `harmonic_lcmUpTo_le_psi_add_one`).
   - $\log x \le H_x \le 1 + \log x$ and $(\log x)^2 \le H_x^2 \le (1 + \log x)^2$.
4. **Elementary Reduction Between $\psi(x)$ Bounds and `MatiyasevichRiemannCounterexample`**:
   - `not_matiyasevichRiemannCounterexample_of_psi_sub_le`: proves that Schoenfeld's explicit bound
     $\psi(x) - x \le \frac{1}{8\pi}\sqrt{x}(\log x)^2$ implies
     $\neg \text{MatiyasevichRiemannCounterexample } x$ (absorbing the $+1$ harmonic slack via
     $\pi > 3$ and $x > 253$).
   - `matiyasevichRiemannCounterexample_of_sqrt_mul_harmonic_sq_le_psi_sub` and
     `matiyasevichRiemannCounterexample_of_sqrt_mul_one_add_log_sq_le_psi_sub`: proves that a
     sufficiently large positive excursion of $\psi(x) - x$ yields
     `MatiyasevichRiemannCounterexample x`.
5. **Classical Analytic Number Theory Ingredients (Schoenfeld 1976 & Schmidt 1903)**:
   - `riemannHypothesis_imp_schoenfeld_psi_bound`: under `RiemannHypothesis`,
     $|\psi(x) - x| \le \frac{1}{8\pi} \sqrt{x} (\log x)^2$ for $x > 253$.
   - `not_riemannHypothesis_imp_exists_psi_oscillation`: under `¬ RiemannHypothesis`,
     there exists $x > 253$ with $\sqrt{x} H_x^2 \le \psi(x) - x + \gamma$.
-/

@[expose] public section

namespace ConjectureMachines.Riemann543.Semantics

/-!
## 1. The Matiyasevich–Aaronson Elementary Counterexample Predicate
-/

/-- Over `ℚ`, `harmNum n` is `n! * harmonic n`. -/
theorem harmNum_eq_factorial_mul_harmonic (n : ℕ) :
    (harmNum n : ℚ) = (n.factorial : ℚ) * harmonic n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [harmNum_succ, Nat.factorial_succ, harmonic_succ]
    push_cast
    rw [ih]
    have hpos : (n + 1 : ℚ) ≠ 0 := by positivity
    linear_combination (n.factorial : ℚ) * (mul_inv_cancel₀ hpos).symm

/-- Over `ℚ`, `harmNum n / n!` equals Mathlib's `harmonic n`. -/
theorem harmNum_div_factorial (n : ℕ) :
    (harmNum n : ℚ) / (n.factorial : ℚ) = harmonic n := by
  rw [harmNum_eq_factorial_mul_harmonic, mul_div_cancel_left₀]
  positivity


/-- Equivalence between the integer cross-multiplied test in `MatiyasevichRiemannCounterexample`
and the rational harmonic number inequality $(H_{\operatorname{lcm}(1,\dots,x)} - x)^2 > x H_x^4$
with $H_{\operatorname{lcm}(1,\dots,x)} > x$. -/
theorem matiyasevichRiemannCounterexample_iff_harmonic (x : ℕ) :
    MatiyasevichRiemannCounterexample x ↔
      253 < x ∧
      let lcm := (Finset.Icc 1 x).lcm id
      (x : ℚ) < harmonic lcm ∧
      (x : ℚ) * harmonic x ^ 4 < (harmonic lcm - x) ^ 2 := by
  unfold MatiyasevichRiemannCounterexample
  dsimp only
  set lcm := (Finset.Icc 1 x).lcm id
  have hlcm_fac_pos : (0 : ℚ) < lcm.factorial := by positivity
  have hx_fac_pos : (0 : ℚ) < x.factorial := by positivity
  have hden_pos : (0 : ℚ) < (lcm.factorial : ℚ) ^ 2 * (x.factorial : ℚ) ^ 4 := by positivity
  constructor
  · rintro ⟨hx, hlt⟩
    refine ⟨hx, ?_⟩
    have hsub_pos : lcm.factorial * x < harmNum lcm := by
      by_contra hle
      rw [not_lt, ← Nat.sub_eq_zero_iff_le] at hle
      simp [hle] at hlt
    have hlt_q :
        ((lcm.factorial ^ 2 * (harmNum x ^ 4 * x) : ℕ) : ℚ) <
          (((harmNum lcm - lcm.factorial * x) ^ 2 * x.factorial ^ 4 : ℕ) : ℚ) := by
      exact_mod_cast hlt
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub (le_of_lt hsub_pos), Nat.cast_mul, Nat.cast_pow] at hlt_q
    rw [harmNum_eq_factorial_mul_harmonic lcm, harmNum_eq_factorial_mul_harmonic x] at hlt_q
    have hsub_q : (lcm.factorial : ℚ) * (x : ℚ) < (lcm.factorial : ℚ) * harmonic lcm := by
      rw [← harmNum_eq_factorial_mul_harmonic lcm]
      exact_mod_cast hsub_pos
    refine ⟨lt_of_mul_lt_mul_left hsub_q (le_of_lt hlcm_fac_pos), ?_⟩
    have hring1 :
        (lcm.factorial : ℚ) ^ 2 * (((x.factorial : ℚ) * harmonic x) ^ 4 * (x : ℚ)) =
          ((lcm.factorial : ℚ) ^ 2 * (x.factorial : ℚ) ^ 4) * ((x : ℚ) * harmonic x ^ 4) := by
      ring
    have hring2 :
        ((lcm.factorial : ℚ) * harmonic lcm - (lcm.factorial : ℚ) * (x : ℚ)) ^ 2 *
            (x.factorial : ℚ) ^ 4 =
          ((lcm.factorial : ℚ) ^ 2 * (x.factorial : ℚ) ^ 4) * (harmonic lcm - (x : ℚ)) ^ 2 := by
      ring
    rw [hring1, hring2] at hlt_q
    exact lt_of_mul_lt_mul_left hlt_q (le_of_lt hden_pos)
  · rintro ⟨hx, hxlcm, hineq⟩
    refine ⟨hx, ?_⟩
    have hsub_q : (lcm.factorial : ℚ) * (x : ℚ) < (harmNum lcm : ℚ) := by
      rw [harmNum_eq_factorial_mul_harmonic lcm]
      exact mul_lt_mul_of_pos_left hxlcm hlcm_fac_pos
    have hsub_nat : lcm.factorial * x ≤ harmNum lcm := by
      exact_mod_cast le_of_lt hsub_q
    have hmul_q :
        ((lcm.factorial : ℚ) ^ 2 * (x.factorial : ℚ) ^ 4) * ((x : ℚ) * harmonic x ^ 4) <
          ((lcm.factorial : ℚ) ^ 2 * (x.factorial : ℚ) ^ 4) * (harmonic lcm - (x : ℚ)) ^ 2 :=
      mul_lt_mul_of_pos_left hineq hden_pos
    have hlt_q :
        ((lcm.factorial ^ 2 * (harmNum x ^ 4 * x) : ℕ) : ℚ) <
          (((harmNum lcm - lcm.factorial * x) ^ 2 * x.factorial ^ 4 : ℕ) : ℚ) := by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_sub hsub_nat, Nat.cast_mul, Nat.cast_pow,
        harmNum_eq_factorial_mul_harmonic lcm, harmNum_eq_factorial_mul_harmonic x]
      calc
        (lcm.factorial : ℚ) ^ 2 * (((x.factorial : ℚ) * harmonic x) ^ 4 * (x : ℚ))
          = ((lcm.factorial : ℚ) ^ 2 * (x.factorial : ℚ) ^ 4) * ((x : ℚ) * harmonic x ^ 4) := by
            ring
        _ < ((lcm.factorial : ℚ) ^ 2 * (x.factorial : ℚ) ^ 4) * (harmonic lcm - (x : ℚ)) ^ 2 :=
            hmul_q
        _ = ((lcm.factorial : ℚ) * harmonic lcm - (lcm.factorial : ℚ) * (x : ℚ)) ^ 2 *
              (x.factorial : ℚ) ^ 4 := by
            ring
    exact_mod_cast hlt_q

/-!
## 2. Least Common Multiple `lcmUpTo x` and Chebyshev's $\psi(x)$
-/

@[simp]
theorem lcmUpTo_eq_lcmUpto (x : ℕ) : lcmUpTo x = Nat.lcmUpto x := rfl

@[simp]
theorem lcmUpTo_one : lcmUpTo 1 = 1 := rfl

theorem lcmUpTo_ne_zero (x : ℕ) : lcmUpTo x ≠ 0 :=
  Nat.lcmUpto_ne_zero x

theorem one_le_lcmUpTo (x : ℕ) : 1 ≤ lcmUpTo x :=
  Nat.succ_le_of_lt (lcmUpTo_pos x)

theorem dvd_lcmUpTo {x k : ℕ} (hk1 : 1 ≤ k) (hkx : k ≤ x) : k ∣ lcmUpTo x :=
  Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hk1, hkx⟩)

theorem self_le_lcmUpTo {x : ℕ} (hx : 1 ≤ x) : x ≤ lcmUpTo x :=
  Nat.le_of_dvd (lcmUpTo_pos x) (dvd_lcmUpTo hx le_rfl)

theorem lcmUpTo_dvd_of_le {x y : ℕ} (hxy : x ≤ y) : lcmUpTo x ∣ lcmUpTo y :=
  Finset.lcm_dvd fun _ hk => Finset.dvd_lcm (Finset.Icc_subset_Icc_right hxy hk)

theorem lcmUpTo_mono : Monotone lcmUpTo :=
  fun _ _ hxy => Nat.le_of_dvd (lcmUpTo_pos _) (lcmUpTo_dvd_of_le hxy)

theorem lcmUpTo_dvd_factorial (x : ℕ) : lcmUpTo x ∣ x.factorial :=
  Nat.lcmUpto_dvd_factorial x

theorem two_pow_le_mul_lcmUpTo (x : ℕ) : 2 ^ x ≤ (x + 1) * lcmUpTo x :=
  Chebyshev.two_pow_le_mul_lcmUpto x

/-- Chebyshev's $\psi(x) = \sum_{n \le x} \Lambda(n)$ equals $\log \operatorname{lcm}(1, \dots, x)$
for every natural number $x$. -/
theorem psi_eq_log_lcmUpTo (x : ℕ) : Chebyshev.psi x = Real.log (lcmUpTo x) :=
  Chebyshev.psi_eq_log_lcmUpto x

/-- Exponentiating Chebyshev's $\psi(x)$ recovers $\operatorname{lcm}(1, \dots, x)$. -/
theorem exp_psi_eq_lcmUpTo (x : ℕ) : Real.exp (Chebyshev.psi x) = lcmUpTo x := by
  rw [psi_eq_log_lcmUpTo, Real.exp_log (by exact_mod_cast lcmUpTo_pos x)]

/-!
## 3. Positivity and Monotonicity of Harmonic Numbers & Real-Analytic Reformulations
-/

theorem harmonic_nonneg (n : ℕ) : (0 : ℚ) ≤ harmonic n := by
  unfold harmonic
  positivity

theorem harmonic_mono : Monotone harmonic := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [harmonic_succ]
  have : (0 : ℚ) ≤ ((n + 1 : ℕ) : ℚ)⁻¹ := by positivity
  linarith

@[simp]
theorem harmonic_one : harmonic 1 = 1 := by
  simp [harmonic]

theorem one_le_harmonic {n : ℕ} (hn : 1 ≤ n) : (1 : ℚ) ≤ harmonic n := by
  simpa using harmonic_mono hn

theorem one_le_harmonic_real {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ (harmonic n : ℝ) := by
  exact_mod_cast one_le_harmonic hn

theorem harmonic_real_nonneg (n : ℕ) : (0 : ℝ) ≤ (harmonic n : ℝ) := by
  exact_mod_cast harmonic_nonneg n

/-- Real-analytic reformulation of `MatiyasevichRiemannCounterexample x` over `ℝ`. -/
theorem matiyasevichRiemannCounterexample_iff_real (x : ℕ) :
    MatiyasevichRiemannCounterexample x ↔
      253 < x ∧
      (x : ℝ) < (harmonic (lcmUpTo x) : ℝ) ∧
      (x : ℝ) * (harmonic x : ℝ) ^ 4 < ((harmonic (lcmUpTo x) : ℝ) - x) ^ 2 := by
  rw [matiyasevichRiemannCounterexample_iff_harmonic]
  refine and_congr_right fun _ => ?_
  dsimp only
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by exact_mod_cast h1, ?_⟩
    exact_mod_cast h2
  · rintro ⟨h1, h2⟩
    refine ⟨by exact_mod_cast h1, ?_⟩
    exact_mod_cast h2

/-- Single-inequality real reformulation of `MatiyasevichRiemannCounterexample x`:
for $x > 253$, the cross-multiplied test holds if and only if
$$\sqrt{x} \cdot H_x^2 < H_{\operatorname{lcm}(1, \dots, x)} - x.$$ -/
theorem matiyasevichRiemannCounterexample_iff_sqrt_lt (x : ℕ) :
    MatiyasevichRiemannCounterexample x ↔
      253 < x ∧
      Real.sqrt x * (harmonic x : ℝ) ^ 2 < (harmonic (lcmUpTo x) : ℝ) - x := by
  rw [matiyasevichRiemannCounterexample_iff_real]
  refine and_congr_right fun _ => ?_
  have hx_nonneg : (0 : ℝ) ≤ x := by positivity
  have hlhs_nonneg : 0 ≤ Real.sqrt x * (harmonic x : ℝ) ^ 2 := by positivity
  have hsq : (Real.sqrt x * (harmonic x : ℝ) ^ 2) ^ 2 = (x : ℝ) * (harmonic x : ℝ) ^ 4 := by
    calc
      (Real.sqrt x * (harmonic x : ℝ) ^ 2) ^ 2
        = Real.sqrt x ^ 2 * ((harmonic x : ℝ) ^ 2) ^ 2 := by ring
      _ = (x : ℝ) * (harmonic x : ℝ) ^ 4 := by
        rw [Real.sq_sqrt hx_nonneg]
        ring
  constructor
  · rintro ⟨hxlcm, hineq⟩
    have hrhs_pos : 0 < (harmonic (lcmUpTo x) : ℝ) - x := sub_pos.mpr hxlcm
    rw [← hsq] at hineq
    exact lt_of_pow_lt_pow_left₀ 2 hrhs_pos.le hineq
  · intro hlt
    have hrhs_pos : 0 < (harmonic (lcmUpTo x) : ℝ) - x := lt_of_le_of_lt hlhs_nonneg hlt
    refine ⟨sub_pos.mp hrhs_pos, ?_⟩
    rw [← hsq]
    exact pow_lt_pow_left₀ hlt hlhs_nonneg (by decide)

/-- Formulation of `MatiyasevichRiemannCounterexample x` making explicit that
$H_{\operatorname{lcm}(1,\dots,x)} - x$ is positive and exceeds $\sqrt{x} H_x^2$. -/
theorem matiyasevichRiemannCounterexample_iff_abs_and_sqrt_lt (x : ℕ) :
    MatiyasevichRiemannCounterexample x ↔
      253 < x ∧
      |(harmonic (lcmUpTo x) : ℝ) - x| = (harmonic (lcmUpTo x) : ℝ) - x ∧
      Real.sqrt x * (harmonic x : ℝ) ^ 2 < (harmonic (lcmUpTo x) : ℝ) - x := by
  rw [matiyasevichRiemannCounterexample_iff_sqrt_lt]
  refine and_congr_right fun _ => ⟨fun h => ⟨abs_of_pos ?_, h⟩, fun h => h.2⟩
  exact lt_of_le_of_lt (by positivity) h

/-!
## 4. Euler–Mascheroni and Harmonic-to-Logarithm Bounds
-/

/-- For every $n \ge 1$, $\log n + \gamma < H_n$. -/
theorem log_add_eulerMascheroniConstant_lt_harmonic {n : ℕ} (hn : n ≠ 0) :
    Real.log n + Real.eulerMascheroniConstant < (harmonic n : ℝ) := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  simp only [Real.eulerMascheroniSeq', hn, ↓reduceIte] at h
  linarith

/-- For every $n \in \mathbb{N}$, $H_n < \log(n + 1) + \gamma$. -/
theorem harmonic_lt_log_add_one_add_eulerMascheroniConstant (n : ℕ) :
    (harmonic n : ℝ) < Real.log (n + 1) + Real.eulerMascheroniConstant := by
  have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  unfold Real.eulerMascheroniSeq at h
  linarith

/-- For every $n \ge 6$, $H_n < \log n + 2 / 3$. -/
theorem harmonic_lt_log_add_two_thirds {n : ℕ} (hn : 6 ≤ n) :
    (harmonic n : ℝ) < Real.log n + 2 / 3 := by
  have hn0 : n ≠ 0 := by omega
  have h1 : Real.eulerMascheroniSeq' n < 2 / 3 :=
    (Real.strictAnti_eulerMascheroniSeq'.antitone hn).trans_lt
      Real.eulerMascheroniSeq'_six_lt_two_thirds
  simp only [Real.eulerMascheroniSeq', hn0, ↓reduceIte] at h1
  linarith

/-- Lower bound connecting $H_{\operatorname{lcm}(1,\dots,x)}$ to Chebyshev's $\psi(x)$:
$$\psi(x) + \gamma < H_{\operatorname{lcm}(1,\dots,x)}.$$ -/
theorem psi_add_eulerMascheroniConstant_lt_harmonic_lcmUpTo (x : ℕ) :
    Chebyshev.psi x + Real.eulerMascheroniConstant < (harmonic (lcmUpTo x) : ℝ) := by
  rw [psi_eq_log_lcmUpTo]
  exact log_add_eulerMascheroniConstant_lt_harmonic (lcmUpTo_ne_zero x)

/-- Since $\gamma > 1/2 > 0$, Chebyshev's $\psi(x)$ is strictly bounded above by
$H_{\operatorname{lcm}(1,\dots,x)} - 1/2$, so $\psi(x) < H_{\operatorname{lcm}(1,\dots,x)}$. -/
theorem psi_add_one_half_lt_harmonic_lcmUpTo (x : ℕ) :
    Chebyshev.psi x + 1 / 2 < (harmonic (lcmUpTo x) : ℝ) := by
  linarith [psi_add_eulerMascheroniConstant_lt_harmonic_lcmUpTo x,
    Real.one_half_lt_eulerMascheroniConstant]

theorem psi_lt_harmonic_lcmUpTo (x : ℕ) :
    Chebyshev.psi x < (harmonic (lcmUpTo x) : ℝ) := by
  linarith [psi_add_one_half_lt_harmonic_lcmUpTo x]

/-- Upper bound connecting $H_{\operatorname{lcm}(1,\dots,x)}$ to Chebyshev's $\psi(x)$:
$$H_{\operatorname{lcm}(1,\dots,x)} \le \psi(x) + 1.$$ -/
theorem harmonic_lcmUpTo_le_psi_add_one (x : ℕ) :
    (harmonic (lcmUpTo x) : ℝ) ≤ Chebyshev.psi x + 1 := by
  rw [psi_eq_log_lcmUpTo, add_comm]
  exact harmonic_le_one_add_log (lcmUpTo x)

/-- Sharper upper bound for $x \ge 6$:
$$H_{\operatorname{lcm}(1,\dots,x)} < \psi(x) + \frac{2}{3}.$$ -/
theorem harmonic_lcmUpTo_lt_psi_add_two_thirds {x : ℕ} (hx : 6 ≤ x) :
    (harmonic (lcmUpTo x) : ℝ) < Chebyshev.psi x + 2 / 3 := by
  rw [psi_eq_log_lcmUpTo]
  have h6 : 6 ≤ lcmUpTo x := hx.trans (self_le_lcmUpTo (by omega))
  exact harmonic_lt_log_add_two_thirds h6

/-- For every natural number $x$, $\log x \le H_x$. -/
theorem log_le_harmonic (x : ℕ) : Real.log x ≤ (harmonic x : ℝ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx_pos : (0 : ℝ) < x := by positivity
    have h1 : Real.log x ≤ Real.log (x + 1 : ℕ) := by
      push_cast
      exact Real.log_le_log hx_pos (by linarith)
    exact h1.trans (log_add_one_le_harmonic x)

theorem log_sq_le_harmonic_sq (x : ℕ) :
    (Real.log x) ^ 2 ≤ (harmonic x : ℝ) ^ 2 := by
  have hlog : 0 ≤ Real.log x := Real.log_natCast_nonneg x
  exact pow_le_pow_left₀ hlog (log_le_harmonic x) 2

theorem harmonic_sq_le_one_add_log_sq (x : ℕ) :
    (harmonic x : ℝ) ^ 2 ≤ (1 + Real.log x) ^ 2 := by
  exact pow_le_pow_left₀ (harmonic_real_nonneg x) (harmonic_le_one_add_log x) 2

/-!
## 5. Elementary Reductions Between $\psi(x)$ Inequalities and `MatiyasevichRiemannCounterexample`
-/

/-- Upper bound `Real.log 4 - 1 ≤ 3863 / 10000` from `Real.log_two_lt_d9`. -/
theorem log_four_sub_one_le : Real.log 4 - 1 ≤ 3863 / 10000 := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, Real.log_pow, Nat.cast_ofNat]
  linarith [Real.log_two_lt_d9]

/-- Upper bound `1 - Real.log 2 ≤ 3863 / 10000` from `Real.log_two_gt_d9`. -/
theorem one_sub_log_two_le : 1 - Real.log 2 ≤ 3863 / 10000 := by
  linarith [Real.log_two_gt_d9]

/-- For all `y ≥ 254`, `519 / 100 ≤ Real.log y` (since `254 ^ 2 = 64516 ≥ 32768 = 2 ^ 15`). -/
theorem log_ge_of_ge_254 {y : ℝ} (hy : 254 ≤ y) : 519 / 100 ≤ Real.log y := by
  have hy_pos : 0 < y := by linarith
  have h_pow : (2 : ℝ) ^ 15 ≤ y ^ 2 := by nlinarith
  have h_log : Real.log ((2 : ℝ) ^ 15) ≤ Real.log (y ^ 2) :=
    Real.log_le_log (by positivity) h_pow
  rw [Real.log_pow, Real.log_pow, Nat.cast_ofNat, Nat.cast_ofNat] at h_log
  linarith [Real.log_two_gt_d9]

/-- For all `y ≥ 900`, `623 / 100 ≤ Real.log y` (since `900 ≥ 512 = 2 ^ 9`). -/
theorem log_ge_of_ge_900 {y : ℝ} (hy : 900 ≤ y) : 623 / 100 ≤ Real.log y := by
  have h_pow : (2 : ℝ) ^ 9 ≤ y := by linarith
  have h_log : Real.log ((2 : ℝ) ^ 9) ≤ Real.log y :=
    Real.log_le_log (by positivity) h_pow
  rw [Real.log_pow, Nat.cast_ofNat] at h_log
  linarith [Real.log_two_gt_d9]

/-- For all `y ≥ 2500`, `762 / 100 ≤ Real.log y` (since `2500 ≥ 2048 = 2 ^ 11`). -/
theorem log_ge_of_ge_2500 {y : ℝ} (hy : 2500 ≤ y) : 762 / 100 ≤ Real.log y := by
  have h_pow : (2 : ℝ) ^ 11 ≤ y := by linarith
  have h_log : Real.log ((2 : ℝ) ^ 11) ≤ Real.log y :=
    Real.log_le_log (by positivity) h_pow
  rw [Real.log_pow, Nat.cast_ofNat] at h_log
  linarith [Real.log_two_gt_d9]

/-- Monotonicity of `t ↦ (7 / 8) * t ^ 2 - 2 * t = t * ((7 / 8) * t - 2)` for `t ≥ c ≥ 16 / 7`. -/
theorem seven_eighths_sq_sub_two_mul_ge {c t : ℝ} (hc : 16 / 7 ≤ c) (hct : c ≤ t) :
    c * ((7 / 8 : ℝ) * c - 2) ≤ (7 / 8 : ℝ) * t ^ 2 - 2 * t := by
  have h_eq : (7 / 8 : ℝ) * t ^ 2 - 2 * t = t * ((7 / 8 : ℝ) * t - 2) := by ring
  rw [h_eq]
  exact mul_le_mul hct (by linarith) (by linarith) (by linarith)

/-- For all `y ∈ [254, 6000]`,
`(3863 / 10000) * Real.sqrt y + 2 * Real.log y ≤ (7 / 8) * (Real.log y) ^ 2`. -/
theorem chebyshev_factor_le_seven_eighths_log_sq {y : ℝ} (hy_low : 254 ≤ y) (hy_high : y ≤ 6000) :
    (3863 / 10000 : ℝ) * Real.sqrt y + 2 * Real.log y ≤ (7 / 8 : ℝ) * (Real.log y) ^ 2 := by
  rcases le_total y 900 with hy900 | hy900
  · have h_sqrt : Real.sqrt y ≤ 30 := by
      rw [Real.sqrt_le_left (by norm_num)]
      linarith
    have h_log : 519 / 100 ≤ Real.log y := log_ge_of_ge_254 hy_low
    have h_quad := seven_eighths_sq_sub_two_mul_ge (by norm_num : (16 / 7 : ℝ) ≤ 519 / 100) h_log
    linarith
  · rcases le_total y 2500 with hy2500 | hy2500
    · have h_sqrt : Real.sqrt y ≤ 50 := by
        rw [Real.sqrt_le_left (by norm_num)]
        linarith
      have h_log : 623 / 100 ≤ Real.log y := log_ge_of_ge_900 hy900
      have h_quad := seven_eighths_sq_sub_two_mul_ge (by norm_num : (16 / 7 : ℝ) ≤ 623 / 100) h_log
      linarith
    · have h_sqrt : Real.sqrt y ≤ 78 := by
        rw [Real.sqrt_le_left (by norm_num)]
        linarith
      have h_log : 762 / 100 ≤ Real.log y := log_ge_of_ge_2500 hy2500
      have h_quad := seven_eighths_sq_sub_two_mul_ge (by norm_num : (16 / 7 : ℝ) ≤ 762 / 100) h_log
      linarith

/-- From `Chebyshev.psi_le` and `Chebyshev.psi_ge`, for all `x ≥ 254`,
`|Chebyshev.psi x - x| ≤ Real.sqrt x * ((3863 / 10000) * Real.sqrt x + 2 * Real.log x)`. -/
theorem abs_psi_sub_self_le_linear_add_sqrt_log {x : ℕ} (hx : 254 ≤ x) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x * ((3863 / 10000 : ℝ) * Real.sqrt x + 2 * Real.log x) := by
  have hy_cast : (254 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  set y : ℝ := (x : ℝ)
  have hy : 254 ≤ y := hy_cast
  have hy_pos : 0 < y := by linarith
  have h_sqrt_sq : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy_pos.le
  have h_rhs_eq :
      Real.sqrt y * ((3863 / 10000 : ℝ) * Real.sqrt y + 2 * Real.log y) =
        (3863 / 10000 : ℝ) * y + 2 * Real.sqrt y * Real.log y := by
    calc
      Real.sqrt y * ((3863 / 10000 : ℝ) * Real.sqrt y + 2 * Real.log y)
        = (3863 / 10000 : ℝ) * (Real.sqrt y * Real.sqrt y) + 2 * Real.sqrt y * Real.log y := by
            ring
      _ = (3863 / 10000 : ℝ) * y + 2 * Real.sqrt y * Real.log y := by rw [h_sqrt_sq]
  rw [h_rhs_eq, abs_le]
  constructor
  · have h_ge : y * Real.log 2 - Real.log (y + 1) ≤ Chebyshev.psi y := Chebyshev.psi_ge x
    have h_coeff := one_sub_log_two_le
    have h_log_add_one : Real.log (y + 1) ≤ 2 * Real.log y := by
      have h_le_sq : y + 1 ≤ y ^ 2 := by nlinarith
      have h1 : Real.log (y + 1) ≤ Real.log (y ^ 2) := Real.log_le_log (by positivity) h_le_sq
      rwa [Real.log_pow, Nat.cast_ofNat] at h1
    have h_sqrt_ge_one : 1 ≤ Real.sqrt y := Real.le_sqrt_of_sq_le (by linarith)
    have h_log_nonneg : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
    have h_log_le_sqrt_log : 2 * Real.log y ≤ 2 * Real.sqrt y * Real.log y := by
      nlinarith
    nlinarith
  · have h_le := Chebyshev.psi_le (by linarith : 1 ≤ y)
    have h_coeff := log_four_sub_one_le
    nlinarith

/-- **Unconditional Chebyshev Bound for $253 < x \le 6000$**:
For every natural number $x$ with $253 < x \le 6000$,
$$|\psi(x) - x| \le \frac{7}{8} \sqrt{x} (\log x)^2.$$ -/
theorem abs_psi_sub_self_le_seven_eighths_of_le_six_thousand
    {x : ℕ} (hx_low : 253 < x) (hx_high : x ≤ 6000) :
    |Chebyshev.psi x - x| ≤ (7 / 8 : ℝ) * Real.sqrt x * (Real.log x) ^ 2 := by
  have hx254_nat : 254 ≤ x := by omega
  have hx254 : (254 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx254_nat
  have hx6000 : (x : ℝ) ≤ 6000 := by exact_mod_cast hx_high
  calc
    |Chebyshev.psi x - x|
      ≤ Real.sqrt x * ((3863 / 10000 : ℝ) * Real.sqrt x + 2 * Real.log x) :=
        abs_psi_sub_self_le_linear_add_sqrt_log hx254_nat
    _ ≤ Real.sqrt x * ((7 / 8 : ℝ) * (Real.log x) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (chebyshev_factor_le_seven_eighths_log_sq hx254 hx6000) (Real.sqrt_nonneg x)
    _ = (7 / 8 : ℝ) * Real.sqrt x * (Real.log x) ^ 2 := by ring

/-- Explicit Schoenfeld-type inequality at $x$:
$$|\psi(x) - x| \le \frac{7}{8} \sqrt{x} (\log x)^2.$$ -/
def SchoenfeldPsiBound (x : ℝ) : Prop :=
  |Chebyshev.psi x - x| ≤ (7 / 8 : ℝ) * Real.sqrt x * (Real.log x) ^ 2

/-- **Schoenfeld Bound $\implies$ No Counterexample**:
If Chebyshev's $\psi(x)$ satisfies the explicit upper bound
$$\psi(x) - x \le \frac{7}{8} \sqrt{x} (\log x)^2,$$
then `MatiyasevichRiemannCounterexample x` cannot hold.

The proof is completely elementary: for $x > 253$, we have $\sqrt{x} \ge 15$, $H_x \ge 5$,
$\log x \le H_x$, $\frac{1}{8} \sqrt{x} H_x^2 \ge \frac{375}{8} > 1$, and
$H_{\operatorname{lcm}(1,\dots,x)} \le \psi(x) + 1$, so the $+1$ slack between $H_{L_x}$ and
$\psi(x)$ is absorbed with room to spare. -/
theorem not_matiyasevichRiemannCounterexample_of_psi_sub_le {x : ℕ}
    (hpsi : Chebyshev.psi x - x ≤ (7 / 8 : ℝ) * Real.sqrt x * (Real.log x) ^ 2) :
    ¬ MatiyasevichRiemannCounterexample x := by
  rw [matiyasevichRiemannCounterexample_iff_sqrt_lt]
  rintro ⟨hx, hlt⟩
  have hx254 : (254 : ℝ) ≤ (x : ℝ) := by
    have : 254 ≤ x := by omega
    exact_mod_cast this
  have hsqrt15 : (15 : ℝ) ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le (by linarith)
  have hlog5 : (5 : ℝ) ≤ Real.log x := by
    linarith [log_ge_of_ge_254 hx254]
  have hharm5 : (5 : ℝ) ≤ (harmonic x : ℝ) :=
    hlog5.trans (log_le_harmonic x)
  have hharm_sq25 : (25 : ℝ) ≤ (harmonic x : ℝ) ^ 2 := by nlinarith
  have h_one_eighth : (1 : ℝ) ≤ (1 / 8 : ℝ) * (Real.sqrt x * (harmonic x : ℝ) ^ 2) := by
    nlinarith
  have hlog_harm : (Real.log x) ^ 2 ≤ (harmonic x : ℝ) ^ 2 := log_sq_le_harmonic_sq x
  have h_seven_eighths :
      (7 / 8 : ℝ) * Real.sqrt x * (Real.log x) ^ 2 ≤
        (7 / 8 : ℝ) * (Real.sqrt x * (harmonic x : ℝ) ^ 2) := by
    calc
      (7 / 8 : ℝ) * Real.sqrt x * (Real.log x) ^ 2
        ≤ (7 / 8 : ℝ) * Real.sqrt x * (harmonic x : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hlog_harm (by positivity)
      _ = (7 / 8 : ℝ) * (Real.sqrt x * (harmonic x : ℝ) ^ 2) := by ring
  have hhlcm : (harmonic (lcmUpTo x) : ℝ) - x ≤ Chebyshev.psi x - x + 1 := by
    linarith [harmonic_lcmUpTo_le_psi_add_one x]
  linarith

/-- Variant of `not_matiyasevichRiemannCounterexample_of_psi_sub_le` taking the
two-sided absolute-value bound `SchoenfeldPsiBound x`. -/
theorem not_matiyasevichRiemannCounterexample_of_schoenfeldPsiBound {x : ℕ}
    (hpsi : SchoenfeldPsiBound x) :
    ¬ MatiyasevichRiemannCounterexample x :=
  not_matiyasevichRiemannCounterexample_of_psi_sub_le ((le_abs_self _).trans hpsi)

/-- **$\psi(x)$ Oscillation $\implies$ Counterexample**:
If $x > 253$ and $\sqrt{x} H_x^2 \le \psi(x) - x + \gamma$, then
`MatiyasevichRiemannCounterexample x` holds. -/
theorem matiyasevichRiemannCounterexample_of_sqrt_mul_harmonic_sq_le_psi_sub {x : ℕ}
    (hx : 253 < x)
    (hpsi : Real.sqrt x * (harmonic x : ℝ) ^ 2 ≤
      Chebyshev.psi x - x + Real.eulerMascheroniConstant) :
    MatiyasevichRiemannCounterexample x := by
  rw [matiyasevichRiemannCounterexample_iff_sqrt_lt]
  refine ⟨hx, ?_⟩
  linarith [psi_add_eulerMascheroniConstant_lt_harmonic_lcmUpTo x]

/-- Purely logarithmic sufficient condition for `MatiyasevichRiemannCounterexample x`:
if $x > 253$ and $\sqrt{x} (1 + \log x)^2 \le \psi(x) - x$, then
`MatiyasevichRiemannCounterexample x` holds. -/
theorem matiyasevichRiemannCounterexample_of_sqrt_mul_one_add_log_sq_le_psi_sub {x : ℕ}
    (hx : 253 < x)
    (hpsi : Real.sqrt x * (1 + Real.log x) ^ 2 ≤ Chebyshev.psi x - x) :
    MatiyasevichRiemannCounterexample x := by
  apply matiyasevichRiemannCounterexample_of_sqrt_mul_harmonic_sq_le_psi_sub hx
  have h1 : Real.sqrt x * (harmonic x : ℝ) ^ 2 ≤ Real.sqrt x * (1 + Real.log x) ^ 2 :=
    mul_le_mul_of_nonneg_left (harmonic_sq_le_one_add_log_sq x) (Real.sqrt_nonneg x)
  linarith [Real.one_half_lt_eulerMascheroniConstant]

/-!
## 6. Classical Analytic Number Theory Ingredients (Schoenfeld 1976 & Schmidt 1903)
-/

export RiemannSchmidt
  (not_riemannHypothesis_iff_exists_zero
   not_riemannHypothesis_imp_exists_psi_sub_ge_sqrt_mul_one_add_log_sq)

/-- **Explicit Formula $\psi(x)$ Bound for $x \ge 5000$ under `RiemannHypothesis`**:
Combining the smoothed Perron contour shift and multiplicity-weighted Stieltjes bound
(`WeightedStieltjes`), the quartic Euler–Maclaurin Jensen zero-counting bound (`VonMangoldtCount`),
the Binet/Euler–Maclaurin digamma vertical bound (`DigammaBinet`), the Borel–Carathéodory
horizontal contour bound (`HorizontalBounds`), and the large-`x` real inequality (`ExplicitLarge`)
proves `SchoenfeldPsiBound x` for all `x ≥ 5000`. -/
theorem abs_psi_sub_self_le_seven_eighths_of_five_thousand_le (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 5000 ≤ x) :
    SchoenfeldPsiBound x := by
  unfold SchoenfeldPsiBound
  obtain ⟨⟨hx_sub, hh_pos, h6T⟩, h_rhs⟩ :=
    ExplicitLarge.explicit_rhs_le_seven_eighths_of_five_thousand_le hx
  obtain ⟨C_h, hCh, h_heights_hb⟩ :=
    HorizontalBounds.exists_zero_free_height_with_log_pow_five_bound hRH h6T
  have hN_bound : ∀ t ≥ 6,
      (WeightedStieltjes.weightedZeroCountingFunction t : ℝ) ≤
        (16 / 5 : ℝ) * t * Real.log t + (11 / 5 : ℝ) * t + (0 : ℝ) := by
    intro t ht
    rw [add_zero]
    exact VonMangoldtCount.weightedZeroCountingFunction_le_sixteen_fifths hRH ht
  have h_left_zeta : ∀ t : ℝ,
      ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (1 : ℝ) * Real.log (|t| + 2) + (85 : ℝ) := by
    intro t
    have h_eq : (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        (-1 / 4 : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    rw [h_eq, neg_div, norm_neg, ← logDeriv_apply, one_mul]
    exact DigammaBinet.norm_logDeriv_riemannZeta_leftVertical_le_eighty_five t
  have h_explicit :=
    WeightedStieltjes.abs_psi_sub_self_le_weighted_riemannVonMangoldt_six_neg_one_fourth
      hRH hx_sub hh_pos h6T (by norm_num) (by norm_num) (by norm_num) (by norm_num) hCh
      hN_bound h_left_zeta h_heights_hb
  exact h_explicit.trans h_rhs

/-- **Explicit $\psi(x)$ Bound under RH**:
Assuming `RiemannHypothesis`, for every integer $x > 253$,
$$|\psi(x) - x| \le \frac{7}{8} \sqrt{x} (\log x)^2.$$ -/
theorem riemannHypothesis_imp_schoenfeldPsiBound (hRH : RiemannHypothesis)
    {x : ℕ} (hx : 253 < x) :
    SchoenfeldPsiBound x := by
  rcases le_or_gt x 6000 with hx_le | hx_gt
  · exact abs_psi_sub_self_le_seven_eighths_of_le_six_thousand hx hx_le
  · have hx5000 : (5000 : ℝ) ≤ (x : ℝ) := by
      have : 5000 ≤ x := by omega
      exact_mod_cast this
    exact abs_psi_sub_self_le_seven_eighths_of_five_thousand_le hRH hx5000

/-- Corollary of `not_riemannHypothesis_imp_exists_psi_sub_ge_sqrt_mul_one_add_log_sq` in terms
of harmonic numbers and the Euler–Mascheroni constant $\gamma$. -/
theorem not_riemannHypothesis_imp_exists_psi_oscillation (hNotRH : ¬ RiemannHypothesis) :
    ∃ x : ℕ, 253 < x ∧
      Real.sqrt x * (harmonic x : ℝ) ^ 2 ≤
        Chebyshev.psi x - x + Real.eulerMascheroniConstant := by
  obtain ⟨x, hx, hpsi⟩ :=
    not_riemannHypothesis_imp_exists_psi_sub_ge_sqrt_mul_one_add_log_sq hNotRH
  refine ⟨x, hx, ?_⟩
  have h1 : Real.sqrt x * (harmonic x : ℝ) ^ 2 ≤ Real.sqrt x * (1 + Real.log x) ^ 2 :=
    mul_le_mul_of_nonneg_left (harmonic_sq_le_one_add_log_sq x) (Real.sqrt_nonneg x)
  linarith [Real.one_half_lt_eulerMascheroniConstant]

/-- **Schoenfeld's Explicit Chebyshev-$\psi$ Criterion for RH (1976)**:
The Riemann Hypothesis holds if and only if `SchoenfeldPsiBound x` holds for all $x > 253$. -/
theorem riemannHypothesis_iff_forall_schoenfeldPsiBound :
    RiemannHypothesis ↔ ∀ x : ℕ, 253 < x → SchoenfeldPsiBound x := by
  constructor
  · exact fun hRH _ hx => riemannHypothesis_imp_schoenfeldPsiBound hRH hx
  · intro hBound
    by_contra hNotRH
    obtain ⟨x, hx, hpsi⟩ :=
      not_riemannHypothesis_imp_exists_psi_sub_ge_sqrt_mul_one_add_log_sq hNotRH
    exact not_matiyasevichRiemannCounterexample_of_schoenfeldPsiBound (hBound x hx)
      (matiyasevichRiemannCounterexample_of_sqrt_mul_one_add_log_sq_le_psi_sub hx hpsi)

/-- **Matiyasevich–Aaronson Harmonic-LCM Criterion for RH (2016)**:
The Riemann Hypothesis holds if and only if no natural number $x$ satisfies
`MatiyasevichRiemannCounterexample x`. -/
theorem riemannHypothesis_iff_forall_not_counterexample :
    RiemannHypothesis ↔ ∀ x : ℕ, ¬ MatiyasevichRiemannCounterexample x := by
  constructor
  · intro hRH x hx_ce
    have hx : 253 < x := hx_ce.1
    exact not_matiyasevichRiemannCounterexample_of_schoenfeldPsiBound
      (riemannHypothesis_imp_schoenfeldPsiBound hRH hx) hx_ce
  · intro hNoCE
    by_contra hNotRH
    obtain ⟨x, hx, hpsi⟩ := not_riemannHypothesis_imp_exists_psi_oscillation hNotRH
    exact hNoCE x (matiyasevichRiemannCounterexample_of_sqrt_mul_harmonic_sq_le_psi_sub hx hpsi)

/-- **Part II (Elementary Counterexample ↔ Riemann Hypothesis)**:
There exists an integer `x` satisfying `MatiyasevichRiemannCounterexample x` if and only if
the Riemann Hypothesis (`RiemannHypothesis`) is false. -/
theorem exists_counterexample_iff_not_riemannHypothesis :
    (∃ x : ℕ, MatiyasevichRiemannCounterexample x) ↔ ¬ RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_not_counterexample]
  push Not
  rfl

end ConjectureMachines.Riemann543.Semantics
