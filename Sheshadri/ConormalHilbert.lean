/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Rat.Cast.Order

/-!
# Recovering multidegrees from the top Hilbert polynomial

For a pure `d`-dimensional cycle in a product of projective spaces, the
homogeneous degree-`d` part of its two-variable Hilbert polynomial has
coefficient `delta k / ((d-k)! * k!)` at `a^(d-k) * b^k`. Setting `a = 1`
retains all these coefficients. The polynomial below records precisely this
one-variable specialization, including the factorial normalization.

This module proves that equality of these polynomials, or equality of their
values, forces equality of every multidegree. This is the algebraic
coefficient-extraction step in the conservation argument of Section 7.4.

The scheme-theoretic input remains separate: properness and flatness must
first yield equality of fibre Hilbert polynomials, and their leading
coefficients must be identified with the fibre cycles' intersection numbers.
Those geometric assertions are not proved or assumed as axioms here.
-/

noncomputable section

namespace Sheshadri.ConormalHilbert

open Polynomial
open scoped BigOperators

/-- The nonzero factorial denominator of the `k`th multidegree coefficient. -/
def coefficientDenominator (d : ℕ) (k : Fin (d + 1)) : ℚ :=
  (Nat.factorial (d - k.val) : ℚ) * (Nat.factorial k.val : ℚ)

theorem coefficientDenominator_ne_zero (d : ℕ) (k : Fin (d + 1)) :
    coefficientDenominator d k ≠ 0 := by
  exact mul_ne_zero
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (d - k.val)))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k.val))

/-- The degree-`d` homogeneous Hilbert part specialized at `(a,b) = (1,T)`. -/
def topHilbertPolynomial (d : ℕ) (delta : Fin (d + 1) → ℚ) : Polynomial ℚ :=
  ∑ k : Fin (d + 1), monomial k.val (delta k / coefficientDenominator d k)

/-- The formal polynomial has the actual factorial-normalized coefficients. -/
@[simp] theorem coeff_topHilbertPolynomial (d : ℕ)
    (delta : Fin (d + 1) → ℚ) (k : Fin (d + 1)) :
    (topHilbertPolynomial d delta).coeff k.val =
      delta k / coefficientDenominator d k := by
  classical
  simp only [topHilbertPolynomial, finset_sum_coeff, coeff_monomial]
  have hinj : ∀ j : Fin (d + 1), j.val = k.val ↔ j = k :=
    fun j => ⟨Fin.ext, fun h => congrArg Fin.val h⟩
  simp only [hinj, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Each multidegree can be recovered from its corresponding coefficient. -/
theorem recover_multidegree (d : ℕ) (delta : Fin (d + 1) → ℚ)
    (k : Fin (d + 1)) :
    (topHilbertPolynomial d delta).coeff k.val * coefficientDenominator d k =
      delta k := by
  rw [coeff_topHilbertPolynomial,
    div_mul_cancel₀ _ (coefficientDenominator_ne_zero d k)]

/-- Equality of the top Hilbert polynomials conserves every multidegree. -/
theorem multidegrees_eq_of_topHilbertPolynomial_eq (d : ℕ)
    {delta epsilon : Fin (d + 1) → ℚ}
    (h : topHilbertPolynomial d delta = topHilbertPolynomial d epsilon) :
    delta = epsilon := by
  funext k
  calc
    delta k = (topHilbertPolynomial d delta).coeff k.val *
        coefficientDenominator d k := (recover_multidegree d delta k).symm
    _ = (topHilbertPolynomial d epsilon).coeff k.val *
        coefficientDenominator d k := by rw [h]
    _ = epsilon k := recover_multidegree d epsilon k

theorem topHilbertPolynomial_injective (d : ℕ) :
    Function.Injective (topHilbertPolynomial d) :=
  fun _ _ h => multidegrees_eq_of_topHilbertPolynomial_eq d h

@[simp] theorem topHilbertPolynomial_eq_iff (d : ℕ)
    (delta epsilon : Fin (d + 1) → ℚ) :
    topHilbertPolynomial d delta = topHilbertPolynomial d epsilon ↔
      delta = epsilon :=
  (topHilbertPolynomial_injective d).eq_iff

/-- Agreement as rational-valued polynomial functions also suffices. -/
theorem multidegrees_eq_of_eval_eq (d : ℕ)
    {delta epsilon : Fin (d + 1) → ℚ}
    (h : ∀ t : ℚ, (topHilbertPolynomial d delta).eval t =
      (topHilbertPolynomial d epsilon).eval t) :
    delta = epsilon := by
  apply multidegrees_eq_of_topHilbertPolynomial_eq d
  exact Polynomial.funext h

/-- It suffices that the polynomial functions agree on an infinite set. -/
theorem multidegrees_eq_of_infinite_eval_eq (d : ℕ)
    {delta epsilon : Fin (d + 1) → ℚ}
    (h : Set.Infinite {t : ℚ | (topHilbertPolynomial d delta).eval t =
      (topHilbertPolynomial d epsilon).eval t}) :
    delta = epsilon := by
  apply multidegrees_eq_of_topHilbertPolynomial_eq d
  exact Polynomial.eq_of_infinite_eval_eq _ _ h

/-- Family form: constancy of the top Hilbert polynomial implies
constancy of each multidegree, with no restrictions on the parameter type. -/
theorem multidegrees_constant_of_topHilbertPolynomial_constant
    {Parameter : Type*} (d : ℕ) (delta : Parameter → Fin (d + 1) → ℚ)
    (base : Parameter)
    (h : ∀ c, topHilbertPolynomial d (delta c) =
      topHilbertPolynomial d (delta base)) :
    ∀ c k, delta c k = delta base k := by
  intro c k
  exact congrFun (multidegrees_eq_of_topHilbertPolynomial_eq d (h c)) k

end Sheshadri.ConormalHilbert
