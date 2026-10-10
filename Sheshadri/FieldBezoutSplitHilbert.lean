/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldSplitBranchHilbert

noncomputable section
open Sheshadri.MultiProjective
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

namespace Sheshadri.FieldBezoutSplitHilbert
variable {k₀ : Type*} [Field k₀] [CharZero k₀]
open MvPolynomial FieldMultiProjective BezoutSplitBudget FieldBezoutSplitSystem
  BezoutProductIteration FieldSplitBranchHilbert FlatMultiGradedHilbert
  ProjectivePointInterpolation
open scoped BigOperators Classical

variable {E : Type*} [Fintype E]

/-- A branch contributes one exactly when its factor choice has the correct
block quotas; every other branch has zero sufficiently positive pieces. -/
theorem branch_eventualBound (dim : Fin 3 → ℕ) (degree : E → MultiProjective.Degree)
    (α : FactorIndex degree → k₀) (hα : Function.Injective α)
    (hN : Fintype.card E = ∑ b, dim b) (s : ∀ e, Factor (degree e)) :
    EventualBound (blockWeight dim) (homogeneousBranchIdeal dim degree α s)
      (if choiceExponent degree s = exponent (dim 0) (dim 1) (dim 2) then 1 else 0) := by
  refine ⟨1, ?_⟩
  intro a b c ha hb hc
  apply branch_piece_finrank_le_quotaIndicator dim degree α hα s hN (a,b,c)
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

/-- Multihomogeneous Bézout's coefficient bounds the actual eventual
multigraded Hilbert function of the explicit split system. -/
theorem splitSystem_eventualBound (dim : Fin 3 → ℕ) (degree : E → MultiProjective.Degree)
    (α : FactorIndex degree → k₀) (hα : Function.Injective α)
    (hN : Fintype.card E = ∑ b, dim b) :
    EventualBound (blockWeight dim)
      (Ideal.span (Set.range (splitEquation dim degree α)))
      (coefficientBudget degree (dim 0) (dim 1) (dim 2)) := by
  let B : (∀ e, Factor (degree e)) → ℕ := fun s =>
    if choiceExponent degree s = exponent (dim 0) (dim 1) (dim 2) then 1 else 0
  have hbot : IsHomogeneous (blockWeight dim)
      (⊥ : Ideal (MvPolynomial (ProjectiveVariables dim) k₀)) := by
    intro d p hp
    have hp : p = 0 := hp
    simp [hp]
  have h := eventualBound_productSystem (blockWeight dim) (fun _ _ => inferInstance)
    ⊥ hbot (homogeneousFactor dim degree α) (fun _ f => blockDegree (factorBlock f)) B
    (homogeneousFactor_homogeneous dim degree α)
    (fun s => by simpa [B] using branch_eventualBound dim degree α hα hN s)
  have hsum : (∑ s : ∀ e, Factor (degree e), B s) =
      coefficientBudget degree (dim 0) (dim 1) (dim 2) := by
    rw [coefficientBudget_eq_card]
    simp [B, QuotaChoice, Fintype.card_subtype]
  simpa only [bot_sup_eq, BezoutExcessProducts.productIdeal, splitEquation, hsum] using h

/-- The canonical start system needs only its square dimension equality.
All generic-position and counting assertions are proved in the construction. -/
theorem canonicalSplitSystem_eventualBound (dim : Fin 3 → ℕ)
    (degree : E → MultiProjective.Degree)
    (hN : Fintype.card E = ∑ b, dim b) :
    EventualBound (blockWeight dim)
      (Ideal.span (Set.range (splitEquation dim degree (fieldParameters (k₀ := k₀) degree))))
      (coefficientBudget degree (dim 0) (dim 1) (dim 2)) :=
  splitSystem_eventualBound dim degree (fieldParameters (k₀ := k₀) degree)
    (fieldParameters_injective degree) hN

end Sheshadri.FieldBezoutSplitHilbert
