/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Sheshadri.Bezout

/-!
# Numerical estimates in the exact determinantal-complexity argument

This file has no geometric assumptions.  Its hypotheses are the explicit
numerical inequalities that the geometric part of the argument must supply.
-/

namespace Sheshadri

/-- The familiar binomial estimate, proved from a term of the exponential series. -/
theorem choose_le_exp_bound (N k : ℕ) (hk : 0 < k) :
    (N.choose k : ℝ) ≤ (Real.exp 1 * N / k) ^ k := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
  have hterm := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
  calc
    (N.choose k : ℝ) ≤ (N : ℝ) ^ k / k.factorial := Nat.choose_le_pow_div k N
    _ = ((N : ℝ) / k) ^ k * ((k : ℝ) ^ k / k.factorial) := by
      rw [div_pow]
      field_simp [hk0, hfac]
    _ ≤ ((N : ℝ) / k) ^ k * Real.exp k :=
      mul_le_mul_of_nonneg_left hterm (by positivity)
    _ = (Real.exp 1 * N / k) ^ k := by
      rw [show Real.exp (k : ℝ) = Real.exp 1 ^ k by
        simpa using Real.exp_nat_mul 1 k]
      rw [← mul_pow]
      congr 1
      ring

/-- Absorb the power of two in the incidence Bezout estimate. -/
theorem scaled_choose_le_exp_bound (N n : ℕ) (hn : 3 ≤ n) :
    (2 : ℝ) ^ (n - 2) * (N.choose (n - 1) : ℝ) ≤
      (2 * Real.exp 1 * N / ((n : ℝ) - 1)) ^ (n - 1) := by
  have hk : 0 < n - 1 := by omega
  have hchoose := choose_le_exp_bound N (n - 1) hk
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hcast] at hchoose
  calc
    (2 : ℝ) ^ (n - 2) * (N.choose (n - 1) : ℝ) ≤
        (2 : ℝ) ^ (n - 1) * (Real.exp 1 * N / ((n : ℝ) - 1)) ^ (n - 1) := by
      apply mul_le_mul
      · exact pow_le_pow_right₀ (by norm_num) (by omega)
      · exact hchoose
      · positivity
      · positivity
    _ = (2 * Real.exp 1 * N / ((n : ℝ) - 1)) ^ (n - 1) := by
      rw [← mul_pow]
      congr 1
      ring

/-- Taking the `(n-1)`-st root produces the quadratic lower bound.

The constant is arbitrary and positive. No analytic asymptotic argument is
needed here, and the natural-number Fermat count is retained in the premise.
-/
theorem quadratic_bound_of_count_bound (n m : ℕ) (hn : 3 ≤ n)
    (C : ℝ) (hC : 0 < C)
    (h : ((n * (n - 1) ^ (n - 2) : ℕ) : ℝ) ≤
      (C * m / ((n : ℝ) - 1)) ^ (n - 1)) :
    ((n : ℝ) - 1) ^ 2 / C ≤ (m : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 0 < (n : ℝ) - 1 := by linarith
  have hexp : n - 1 = (n - 2) + 1 := by omega
  have hsmall : ((n : ℝ) - 1) ^ (n - 1) ≤
      ((n * (n - 1) ^ (n - 2) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hn1]
    rw [hexp, pow_succ]
    nlinarith [pow_nonneg (le_of_lt hx) (n - 2)]
  have hroot : (n : ℝ) - 1 ≤ C * m / ((n : ℝ) - 1) :=
    le_of_pow_le_pow_left₀ (by omega) (by positivity) (hsmall.trans h)
  apply (div_le_iff₀ hC).2
  have hmul := (le_div_iff₀ hx).1 hroot
  nlinarith

/-- The ordinary determinant constant `1/(4e)`. -/
theorem ordinary_quadratic_bound_of_count_bound (n m : ℕ) (hn : 3 ≤ n)
    (h : ((n * (n - 1) ^ (n - 2) : ℕ) : ℝ) ≤
      (4 * Real.exp 1 * m / ((n : ℝ) - 1)) ^ (n - 1)) :
    ((n : ℝ) - 1) ^ 2 / (4 * Real.exp 1) ≤ (m : ℝ) := by
  exact quadratic_bound_of_count_bound n m hn (4 * Real.exp 1) (by positivity) h

/-- The symmetric determinant constant `1/(2e)`. -/
theorem symmetric_quadratic_bound_of_count_bound (n m : ℕ) (hn : 3 ≤ n)
    (h : ((n * (n - 1) ^ (n - 2) : ℕ) : ℝ) ≤
      (2 * Real.exp 1 * m / ((n : ℝ) - 1)) ^ (n - 1)) :
    ((n : ℝ) - 1) ^ 2 / (2 * Real.exp 1) ≤ (m : ℝ) := by
  exact quadratic_bound_of_count_bound n m hn (2 * Real.exp 1) (by positivity) h

/-- The second estimate in Lemma 10.1, with its full constant. -/
theorem ordinaryBezout_le_exp_bound (m n : ℕ) (hn : 3 ≤ n) :
    (ordinaryBezout m n : ℝ) ≤
      (4 * Real.exp 1 * m / ((n : ℝ) - 1)) ^ (n - 1) := by
  have hnreal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) - 1 := by linarith
  calc
    (ordinaryBezout m n : ℝ) ≤
        (2 : ℝ) ^ (n - 2) * ((2 * m - 1).choose (n - 1) : ℝ) := by
      exact_mod_cast ordinaryBezout_le_vandermonde m n
    _ ≤ (2 * Real.exp 1 * (2 * m - 1 : ℕ) / ((n : ℝ) - 1)) ^ (n - 1) :=
      scaled_choose_le_exp_bound (2 * m - 1) n hn
    _ ≤ (4 * Real.exp 1 * m / ((n : ℝ) - 1)) ^ (n - 1) := by
      apply pow_le_pow_left₀ (by positivity)
      apply (div_le_div_iff_of_pos_right hden).2
      have hnat : ((2 * m - 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
        exact_mod_cast (Nat.sub_le (2 * m) 1)
      calc
        2 * Real.exp 1 * (2 * m - 1 : ℕ) ≤ 2 * Real.exp 1 * (2 * (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hnat (by positivity)
        _ = 4 * Real.exp 1 * m := by ring

/-- The full ordinary quadratic consequence of the geometric count comparison. -/
theorem ordinary_quadratic_bound (n m : ℕ) (hn : 3 ≤ n)
    (hcount : fermatCount n ≤ ordinaryBezout m n) :
    ((n : ℝ) - 1) ^ 2 / (4 * Real.exp 1) ≤ (m : ℝ) := by
  apply ordinary_quadratic_bound_of_count_bound n m hn
  exact (by exact_mod_cast hcount : (fermatCount n : ℝ) ≤ (ordinaryBezout m n : ℝ)).trans
    (ordinaryBezout_le_exp_bound m n hn)

/-- The full symmetric quadratic consequence of the geometric count comparison. -/
theorem symmetric_quadratic_bound (n m : ℕ) (hn : 3 ≤ n)
    (hcount : fermatCount n ≤ symmetricBezout m n) :
    ((n : ℝ) - 1) ^ 2 / (2 * Real.exp 1) ≤ (m : ℝ) := by
  apply symmetric_quadratic_bound_of_count_bound n m hn
  have hc : (fermatCount n : ℝ) ≤ (symmetricBezout m n : ℝ) := by exact_mod_cast hcount
  apply hc.trans
  simpa only [symmetricBezout, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
    scaled_choose_le_exp_bound m n hn

end Sheshadri
