/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.MultiProjectiveBezout
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting the branches of a split multiprojective start system

Each equation of multidegree `(d₀,d₁,d₂)` has `dᵢ` labeled linear factors
from block `i`. Expanding the actual class polynomial shows that its target
coefficient is exactly the number of factor selections with the required
block quotas. Empty equations and degree-zero blocks are included.
-/

noncomputable section
namespace Sheshadri.BezoutSplitBudget
open MvPolynomial MultiProjective
open scoped Classical

abbrev Factor (d : Degree) := Fin d.1 ⊕ (Fin d.2.1 ⊕ Fin d.2.2)

def factorBlock {d : Degree} : Factor d → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

theorem classFactor_eq_sum (d : Degree) :
    classFactor d = ∑ j : Factor d, (X (factorBlock j) : MvPolynomial (Fin 3) ℕ) := by
  simp [classFactor, Factor, factorBlock, Fintype.sum_sum_type,
    nsmul_eq_mul, add_assoc]

variable {E : Type*} [Fintype E]

def choiceExponent (degree : E → Degree) (c : ∀ e, Factor (degree e)) : Fin 3 →₀ ℕ :=
  ∑ e, Finsupp.single (factorBlock (c e)) 1

abbrev QuotaChoice (degree : E → Degree) (a b c : ℕ) :=
  {s : ∀ e, Factor (degree e) // choiceExponent degree s = exponent a b c}

theorem classPolynomial_eq_sum (degree : E → Degree) :
    classPolynomial degree = ∑ c : ∀ e, Factor (degree e),
      monomial (choiceExponent degree c) (1 : ℕ) := by
  unfold classPolynomial
  simp_rw [classFactor_eq_sum]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [choiceExponent, monomial_sum_one]
  rfl

/-- The coefficient is an actual finite cardinal, rather than a separately
supplied combinatorial estimate. -/
theorem coefficientBudget_eq_card (degree : E → Degree) (a b c : ℕ) :
    coefficientBudget degree a b c = Fintype.card (QuotaChoice degree a b c) := by
  rw [coefficientBudget, classPolynomial_eq_sum, coeff_sum]
  simp only [coeff_monomial]
  simp [QuotaChoice, Fintype.card_subtype, eq_comm]

theorem coefficientBudget_eq_natCard (degree : E → Degree) (a b c : ℕ) :
    coefficientBudget degree a b c = Nat.card (QuotaChoice degree a b c) := by
  rw [Nat.card_eq_fintype_card, coefficientBudget_eq_card]

theorem sum_quota_indicator (degree : E → Degree) (a b c : ℕ) :
    (∑ s : ∀ e, Factor (degree e),
      if choiceExponent degree s = exponent a b c then 1 else 0) =
        coefficientBudget degree a b c := by
  rw [coefficientBudget_eq_card]
  simp [QuotaChoice, Fintype.card_subtype]

abbrev Selected (degree : E → Degree) (c : ∀ e, Factor (degree e)) (b : Fin 3) :=
  {e : E // factorBlock (c e) = b}

theorem choiceExponent_apply (degree : E → Degree) (c : ∀ e, Factor (degree e))
    (b : Fin 3) : choiceExponent degree c b = Fintype.card (Selected degree c b) := by
  simp [choiceExponent, Finsupp.single_apply, Fintype.card_subtype, Selected, eq_comm]

theorem exponent_apply (a b c : ℕ) (i : Fin 3) :
    exponent a b c i = ![a, b, c] i := by
  fin_cases i <;> simp [exponent]

theorem choiceExponent_eq_iff (degree : E → Degree) (s : ∀ e, Factor (degree e))
    (a b c : ℕ) :
    choiceExponent degree s = exponent a b c ↔
      ∀ i : Fin 3, Fintype.card (Selected degree s i) = ![a,b,c] i := by
  rw [Finsupp.ext_iff]
  simp only [choiceExponent_apply, exponent_apply]

theorem choiceExponent_eq_iff_dim (degree : E → Degree)
    (s : ∀ e, Factor (degree e)) (dim : Fin 3 → ℕ) :
    choiceExponent degree s = exponent (dim 0) (dim 1) (dim 2) ↔
      ∀ i : Fin 3, Fintype.card (Selected degree s i) = dim i := by
  rw [choiceExponent_eq_iff]
  have hdim : ![dim 0, dim 1, dim 2] = dim := by
    funext i
    fin_cases i <;> rfl
  rw [hdim]

end Sheshadri.BezoutSplitBudget
