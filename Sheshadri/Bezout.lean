/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-!
# The exact combinatorial counts

These are natural-number proofs; this module introduces no axioms.
The identification with an intersection number is a separate geometric input.
-/

namespace Sheshadri

open Finset

/-- The closed-form ordinary Bezout number in Theorem 1.4(i). -/
def ordinaryBezout (m n : ℕ) : ℕ :=
  ∑ i ∈ Icc 1 (n - 1),
    m.choose i * (m - 1).choose (n - 1 - i) * (n - 2).choose (i - 1)

/-- The symmetric Bezout number in Theorem 1.4(ii). -/
def symmetricBezout (m n : ℕ) : ℕ :=
  2 ^ (n - 2) * m.choose (n - 1)

/-- The target count from the Fermat cone. The geometric interpretation is external. -/
def fermatCount (n : ℕ) : ℕ := n * (n - 1) ^ (n - 2)

/-- The ordinary incidence is square. This alone does not establish isolatedness. -/
theorem ordinary_equation_count (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) :
    m + (m - 1) + (n - 2) + 1 = n + 2 * m - 2 := by omega

theorem symmetric_equation_count (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) :
    m + 1 + (n - 2) = n + m - 1 := by omega

/-- The exponent-matching calculation of Section 4.3, Step 6.

The bounds on i,j,k say that they select genuine terms of the three binomial
expansions. Polynomial expansion itself is not being postulated or verified here.
-/
theorem ordinary_exponent_matching (m n i j k : ℕ)
    (hm : 1 ≤ m) (hn : 2 ≤ n)
    (hi : i ≤ m) (hj : j ≤ m - 1) (_hk : k ≤ n - 2) :
    (1 + i + j = n ∧ (m - i) + k = m - 1 ∧
      (m - 1 - j) + (n - 2 - k) = m - 1) ↔
    (1 ≤ i ∧ i ≤ n - 1 ∧ j = n - 1 - i ∧ k = i - 1) := by
  omega

theorem choose_le_two_pow_weak (n k : ℕ) : n.choose k ≤ 2 ^ n := by
  by_cases hn : n = 0
  · subst n
    cases k <;> simp
  · exact (Nat.choose_le_two_pow n k (Nat.pos_of_ne_zero hn)).le

/-- The first inequality of Lemma 10.1, valid even outside the paper's range. -/
theorem ordinaryBezout_le_vandermonde (m n : ℕ) :
    ordinaryBezout m n ≤ 2 ^ (n - 2) * (2 * m - 1).choose (n - 1) := by
  calc
    ordinaryBezout m n ≤
        ∑ i ∈ Icc 1 (n - 1),
          2 ^ (n - 2) * (m.choose i * (m - 1).choose (n - 1 - i)) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        Nat.mul_le_mul_left (m.choose i * (m - 1).choose (n - 1 - i))
          (choose_le_two_pow_weak (n - 2) (i - 1))
    _ ≤ ∑ i ∈ range ((n - 1) + 1),
          2 ^ (n - 2) * (m.choose i * (m - 1).choose (n - 1 - i)) := by
      apply Finset.sum_le_sum_of_subset
      intro i hi
      have h := (Finset.mem_Icc.mp hi).2
      exact Finset.mem_range.mpr (by omega)
    _ = 2 ^ (n - 2) * (m + (m - 1)).choose (n - 1) := by
      rw [← Finset.mul_sum, Nat.add_choose_eq,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => m.choose i * (m - 1).choose j)]
    _ = 2 ^ (n - 2) * (2 * m - 1).choose (n - 1) := by
      congr 2
      omega

/-- The elementary lower comparison used before root extraction. -/
theorem power_le_fermatCount (n : ℕ) (hn : 2 ≤ n) :
    (n - 1) ^ (n - 1) ≤ fermatCount n := by
  have he : n - 1 = (n - 2) + 1 := by omega
  unfold fermatCount
  calc
    (n - 1) ^ (n - 1) = (n - 1) ^ ((n - 2) + 1) := by rw [← he]
    _ = (n - 1) * (n - 1) ^ (n - 2) := by rw [pow_succ']
    _ ≤ n * (n - 1) ^ (n - 2) :=
      Nat.mul_le_mul_right _ (by omega : n - 1 ≤ n)

theorem ordinaryBezout_mono {a b : ℕ} (n : ℕ) (hab : a ≤ b) :
    ordinaryBezout a n ≤ ordinaryBezout b n := by
  unfold ordinaryBezout
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_right _
    (Nat.mul_le_mul (Nat.choose_le_choose _ hab)
      (Nat.choose_le_choose _ (Nat.sub_le_sub_right hab 1)))

theorem symmetricBezout_mono {a b : ℕ} (n : ℕ) (hab : a ≤ b) :
    symmetricBezout a n ≤ symmetricBezout b n := by
  exact Nat.mul_le_mul_left _ (Nat.choose_le_choose _ hab)

/-- A kernel-checked sample; `decide` is reduced by Lean's kernel. -/
theorem ordinaryBezout_5_4 : ordinaryBezout 5 4 = 120 := by
  simp only [ordinaryBezout, Nat.choose_eq_descFactorial_div_factorial]
  decide

theorem symmetricBezout_5_4 : symmetricBezout 5 4 = 40 := by
  simp only [symmetricBezout, Nat.choose_eq_descFactorial_div_factorial]
  decide

theorem fermatCount_4 : fermatCount 4 = 36 := by decide

/-- At n=6, a size-6 ordinary representation fails the enumerative comparison. -/
theorem ordinary_size_six_fails : ordinaryBezout 6 6 < fermatCount 6 := by
  simp only [ordinaryBezout, fermatCount, Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- At n=10, a size-24 symmetric representation fails the comparison. -/
theorem symmetric_size_twentyfour_fails : symmetricBezout 24 10 < fermatCount 10 := by
  simp only [symmetricBezout, fermatCount, Nat.choose_eq_descFactorial_div_factorial]
  decide

/-- The exact finite count forces the stronger integer bound at n=10. -/
theorem ordinary_n10_threshold (m : ℕ)
    (hcount : fermatCount 10 ≤ ordinaryBezout m 10) : 15 ≤ m := by
  by_contra h
  have hmono := ordinaryBezout_mono 10 (show m ≤ 14 by omega)
  have hfail : ordinaryBezout 14 10 < fermatCount 10 := by
    simp only [ordinaryBezout, fermatCount, Nat.choose_eq_descFactorial_div_factorial]
    decide
  omega

theorem symmetric_n10_threshold (m : ℕ)
    (hcount : fermatCount 10 ≤ symmetricBezout m 10) : 25 ≤ m := by
  by_contra h
  have hmono := symmetricBezout_mono 10 (show m ≤ 24 by omega)
  have hfail := symmetric_size_twentyfour_fails
  omega

end Sheshadri
