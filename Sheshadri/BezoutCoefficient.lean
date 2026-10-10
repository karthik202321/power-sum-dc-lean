/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.Bezout
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Coefficient extraction for the actual multihomogeneous Bezout polynomials

The variables are `H = X 0`, `U = X 1`, and `V = X 2`. Coefficients are natural
numbers; no equality with a formal coefficient is postulated as an axiom.
-/

namespace Sheshadri.BezoutCoefficient

noncomputable section

open Finset MvPolynomial
open scoped BigOperators

abbrev ClassPolynomial := MvPolynomial (Fin 3) ℕ

def exponent (h u v : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 h + Finsupp.single 1 u + Finsupp.single 2 v

def H : ClassPolynomial := X 0
def U : ClassPolynomial := X 1
def V : ClassPolynomial := X 2

def ordinaryClass (m n : ℕ) : ClassPolynomial :=
  H * (H + U) ^ m * (H + V) ^ (m - 1) * (U + V) ^ (n - 2)

def symmetricClass (m n : ℕ) : ClassPolynomial :=
  H * (H + U) ^ m * (C 2 * U) ^ (n - 2)

theorem exponent_injective {h u v h' u' v' : ℕ} :
    exponent h u v = exponent h' u' v' ↔ h = h' ∧ u = u' ∧ v = v' := by
  constructor
  · intro e
    have h0 := congrArg (fun f : Fin 3 →₀ ℕ => f 0) e
    have h1 := congrArg (fun f : Fin 3 →₀ ℕ => f 1) e
    have h2 := congrArg (fun f : Fin 3 →₀ ℕ => f 2) e
    simpa [exponent] using And.intro h0 (And.intro h1 h2)
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem binomial_monomial_expansion (x y : Fin 3) (d : ℕ) :
    (X x + X y : ClassPolynomial) ^ d =
      ∑ i ∈ range (d + 1),
        monomial (Finsupp.single x i + Finsupp.single y (d - i)) (d.choose i) := by
  rw [add_pow]
  apply sum_congr rfl
  intro i hi
  rw [X_pow_eq_monomial, X_pow_eq_monomial, ← C_eq_coe_nat]
  simp only [Nat.cast_id, C_apply, monomial_mul, add_zero, one_mul, mul_one]

theorem ordinaryClass_expansion (m n : ℕ) :
    ordinaryClass m n =
      ∑ i ∈ range (m + 1), ∑ j ∈ range ((m - 1) + 1), ∑ k ∈ range ((n - 2) + 1),
        monomial (exponent (1 + i + j) ((m - i) + k) ((m - 1 - j) + (n - 2 - k)))
          (m.choose i * (m - 1).choose j * (n - 2).choose k) := by
  unfold ordinaryClass H U V
  rw [binomial_monomial_expansion, binomial_monomial_expansion,
    binomial_monomial_expansion]
  rw [Finset.mul_sum (s := range (m + 1))]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum (s := range ((m - 1) + 1))]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro k hk
  rw [X]
  simp only [monomial_mul, one_mul]
  apply congrArg (fun e : Fin 3 →₀ ℕ =>
    (monomial e (m.choose i * (m - 1).choose j * (n - 2).choose k) : ClassPolynomial))
  ext t
  fin_cases t <;> simp [exponent]

theorem ordinary_coefficient_triple_sum (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) :
    coeff (exponent n (m - 1) (m - 1)) (ordinaryClass m n) =
      ∑ i ∈ range (m + 1), ∑ j ∈ range ((m - 1) + 1), ∑ k ∈ range ((n - 2) + 1),
        if 1 ≤ i ∧ i ≤ n - 1 ∧ j = n - 1 - i ∧ k = i - 1 then
          m.choose i * (m - 1).choose j * (n - 2).choose k else 0 := by
  rw [ordinaryClass_expansion]
  simp only [coeff_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro k hk
  simp only [coeff_monomial, exponent_injective,
    ordinary_exponent_matching m n i j k hm hn
      (by simpa only [mem_range, Nat.lt_succ_iff] using hi)
      (by simpa only [mem_range, Nat.lt_succ_iff] using hj)
      (by simpa only [mem_range, Nat.lt_succ_iff] using hk)]

theorem ordinary_inner_sum (m n i : ℕ) (hn : 2 ≤ n) :
    (∑ j ∈ range ((m - 1) + 1), ∑ k ∈ range ((n - 2) + 1),
      if 1 ≤ i ∧ i ≤ n - 1 ∧ j = n - 1 - i ∧ k = i - 1 then
        m.choose i * (m - 1).choose j * (n - 2).choose k else 0) =
    if 1 ≤ i ∧ i ≤ n - 1 then
      m.choose i * (m - 1).choose (n - 1 - i) * (n - 2).choose (i - 1) else 0 := by
  classical
  by_cases hlo : 1 ≤ i
  · by_cases hhi : i ≤ n - 1
    · have hk : i - 1 < (n - 2) + 1 := by omega
      by_cases hj : n - 1 - i < (m - 1) + 1
      · simp [hlo, hhi, ite_and, hk, hj]
      · have hz : (m - 1).choose (n - 1 - i) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [hlo, hhi, ite_and, hk, hj, hz]
    · simp [hhi]
  · simp [hlo]

theorem ordinary_outer_sum (m n : ℕ) :
    (∑ i ∈ range (m + 1), if 1 ≤ i ∧ i ≤ n - 1 then
      m.choose i * (m - 1).choose (n - 1 - i) * (n - 2).choose (i - 1) else 0) =
      ordinaryBezout m n := by
  classical
  let f : ℕ → ℕ := fun i =>
    m.choose i * (m - 1).choose (n - 1 - i) * (n - 2).choose (i - 1)
  change (∑ i ∈ range (m + 1), if 1 ≤ i ∧ i ≤ n - 1 then f i else 0) = _
  calc
    (∑ i ∈ range (m + 1), if 1 ≤ i ∧ i ≤ n - 1 then f i else 0) =
        ∑ i ∈ range (m + n + 1), if 1 ≤ i ∧ i ≤ n - 1 then f i else 0 := by
      apply Finset.sum_subset
      · intro i hi
        simp only [mem_range] at hi ⊢
        omega
      · intro i hi hnot
        have hz : m.choose i = 0 := Nat.choose_eq_zero_of_lt (by
          simp only [mem_range] at hnot
          omega)
        simp [f, hz]
    _ = ∑ i ∈ (range (m + n + 1)).filter (fun i => 1 ≤ i ∧ i ≤ n - 1), f i := by
      rw [Finset.sum_filter]
    _ = ordinaryBezout m n := by
      have hs : (range (m + n + 1)).filter (fun i => 1 ≤ i ∧ i ≤ n - 1) =
          Icc 1 (n - 1) := by
        ext i
        simp only [mem_filter, mem_range, mem_Icc]
        omega
      rw [hs]
      rfl

/-- The ordinary Bezout number is the actual multivariate polynomial coefficient. -/
theorem ordinary_coefficient (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) :
    coeff (exponent n (m - 1) (m - 1)) (ordinaryClass m n) = ordinaryBezout m n := by
  rw [ordinary_coefficient_triple_sum m n hm hn]
  simp_rw [ordinary_inner_sum m n _ hn]
  exact ordinary_outer_sum m n

theorem symmetricClass_expansion (m n : ℕ) :
    symmetricClass m n = ∑ i ∈ range (m + 1),
      monomial (exponent (1 + i) ((m - i) + (n - 2)) 0)
        (m.choose i * 2 ^ (n - 2)) := by
  unfold symmetricClass H U
  rw [binomial_monomial_expansion, Finset.mul_sum]
  simp only [Finset.sum_mul]
  apply sum_congr rfl
  intro i hi
  rw [mul_pow, ← map_pow, X_pow_eq_monomial]
  simp only [X, C_apply, monomial_mul, one_mul, mul_one, add_zero]
  apply congrArg (fun e : Fin 3 →₀ ℕ =>
    (monomial e (m.choose i * 2 ^ (n - 2)) : ClassPolynomial))
  ext t
  fin_cases t <;> simp [exponent]

/-- The symmetric Bezout number is the actual coefficient of
`H (H+U)^m (2U)^(n-2)` at `H^n U^(m-1)`. -/
theorem symmetric_coefficient (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) :
    coeff (exponent n (m - 1) 0) (symmetricClass m n) = symmetricBezout m n := by
  classical
  rw [symmetricClass_expansion]
  simp only [coeff_sum, coeff_monomial, exponent_injective]
  calc
    (∑ i ∈ range (m + 1),
        if 1 + i = n ∧ m - i + (n - 2) = m - 1 ∧ True then
          m.choose i * 2 ^ (n - 2) else 0) =
      ∑ i ∈ range (m + 1), if i = n - 1 then m.choose i * 2 ^ (n - 2) else 0 := by
        apply sum_congr rfl
        intro i hi
        have hi' : i ≤ m := by simpa only [mem_range, Nat.lt_succ_iff] using hi
        have he : (1 + i = n ∧ m - i + (n - 2) = m - 1 ∧ True) ↔ i = n - 1 := by
          simp only [and_true]
          omega
        simp only [he]
    _ = symmetricBezout m n := by
      by_cases hi : n - 1 < m + 1
      · simp [hi, symmetricBezout, mul_comm]
      · have hz : m.choose (n - 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [hi, symmetricBezout, hz]

end
end Sheshadri.BezoutCoefficient
