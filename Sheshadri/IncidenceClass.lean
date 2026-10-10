/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.IncidenceSystem
import Sheshadri.MultiProjectiveBezout
import Sheshadri.BezoutCoefficient

/-! The class product of the actual, indexed incidence equations.

This proves the advertised product from the number and verified multidegrees of
the equations.  No intersection number or coefficient extraction is assumed.
-/

noncomputable section

namespace Sheshadri.Incidence

open MvPolynomial MultiProjective

theorem ordinary_class_product (n m : ℕ) :
    classPolynomial (ordinaryDegree (n := n) (m := m)) =
      X 0 * (X 0 + X 1) ^ m * (X 0 + X 2) ^ (m - 1) *
        (X 1 + X 2) ^ (n - 2) := by
  simp [classPolynomial, OrdinaryEquationIndex, ordinaryDegree,
    Fintype.prod_sum_type, classFactor]
  ac_rfl

/-- Add a zero-degree third block when using the universal three-factor
Bezout formulation for the symmetric two-factor system. -/
def symmetricDegreeThree {n m : ℕ} (e : SymmetricEquationIndex n m) : Degree :=
  ((symmetricDegree e).1, (symmetricDegree e).2, 0)

theorem symmetric_class_product (n m : ℕ) :
    classPolynomial (symmetricDegreeThree (n := n) (m := m)) =
      X 0 * (X 0 + X 1) ^ m * (C 2 * X 1) ^ (n - 2) := by
  simp [classPolynomial, SymmetricEquationIndex, symmetricDegreeThree,
    symmetricDegree, Fintype.prod_sum_type, classFactor]
  ac_rfl

/-- The generic Bezout coefficient budget of the actual ordinary family is
exactly the closed-form sum in Theorem 1.4. -/
theorem ordinary_coefficientBudget (n m : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) :
    coefficientBudget (ordinaryDegree (n := n) (m := m)) n (m - 1) (m - 1) =
      ordinaryBezout m n := by
  unfold coefficientBudget
  rw [ordinary_class_product]
  exact BezoutCoefficient.ordinary_coefficient m n hm hn

theorem symmetric_coefficientBudget (n m : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) :
    coefficientBudget (symmetricDegreeThree (n := n) (m := m)) n (m - 1) 0 =
      symmetricBezout m n := by
  unfold coefficientBudget
  rw [symmetric_class_product]
  exact BezoutCoefficient.symmetric_coefficient m n hm hn

end Sheshadri.Incidence
