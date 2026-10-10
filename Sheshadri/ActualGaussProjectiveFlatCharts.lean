/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalProjectiveCharts
import Sheshadri.ActualGaussCoefficientHomogeneous

/-!
# Flatness of the actual normalized Gauss charts

The literal total Gauss ideal is used here, together with its already proved
bihomogeneity and scalar saturation. Its quotient by the two projective-chart
normalization equations is flat over the parameter ring. No identification,
homogeneity, or flatness certificate for this family is an input.
-/

noncomputable section
namespace Sheshadri.ActualGaussProjectiveFlatCharts

open MvPolynomial ActualGaussCoefficientRing ConormalProjectiveCharts

variable {Z : Type} [Fintype Z]

abbrev TotalChart (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ))
    (i j : Option Z) := NormalizedChart (coefficientIdeal F U) i j

/-- The actual normalized quotient equals its coordinate-ratio subalgebra. -/
def totalChartEquivRatio
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (i j : Option Z) :
    TotalChart F U i j ≃ₐ[Polynomial ℂ] RatioChart (coefficientIdeal F U) i j :=
  normalizedChartEquivRatioChart (coefficientIdeal F U) i j
    (coefficientIdeal_bihomogeneous F U)

/-- Every actual normalized chart of the affine-line Gauss family is flat. -/
theorem totalChart_flat
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U)
    (i j : Option Z) : Module.Flat (Polynomial ℂ) (TotalChart F U i j) := by
  letI := coefficientRing_torsionfree F U hU
  letI : Module.Flat (Polynomial ℂ) (RatioChart (coefficientIdeal F U) i j) :=
    GeneralConormalFlatFamily.ratioChart_flat (Polynomial ℂ) _ _ i j
  exact Module.Flat.of_linearEquiv (totalChartEquivRatio F U i j).toLinearEquiv

/-- The chart map is a flat morphism of actual affine schemes. -/
theorem totalChart_spec_flat
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U)
    (i j : Option Z) :
    AlgebraicGeometry.Flat (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap (Polynomial ℂ) (TotalChart F U i j)))) := by
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
  exact flat_algebraMap_iff.mpr (totalChart_flat F U hU i j)

end Sheshadri.ActualGaussProjectiveFlatCharts
