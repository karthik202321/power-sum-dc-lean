/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.GeneralConormalFlatFamily

/-!
# Concrete equations and presentation of the ratio chart

The ratio chart is the quotient by the kernel of the explicit polynomial
map sending each coordinate to its normalized ratio. This provides actual
coordinate equations and a base-algebra equivalence, including the two
normalizing equations. No abstract chart ring or chart equivalence is assumed.
-/

noncomputable section
namespace Sheshadri.GeneralConormalFlatFamily

open MvPolynomial

variable (R : Type*) [CommRing R]
variable {Q X Y : Type*} [CommRing Q] [Algebra R Q]
variable (x : X → Q) (y : Y → Q) (i : X) (j : Y)

def ratioPolynomialMap : MvPolynomial (X ⊕ Y) R →ₐ[R] OpenChartRing x y i j :=
  MvPolynomial.aeval (Sum.elim (leftRatio x y i j) (rightRatio x y i j))

theorem ratioPolynomialMap_range : (ratioPolynomialMap R x y i j).range = ratioChart R x y i j := by
  unfold ratioPolynomialMap ratioChart
  rw [← Algebra.adjoin_range_eq_range_aeval]
  congr 1
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | inl k => exact Or.inl ⟨k, rfl⟩
    | inr k => exact Or.inr ⟨k, rfl⟩
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨Sum.inl k, rfl⟩
    · exact ⟨Sum.inr k, rfl⟩

/-- The actual kernel ideal of the normalized coordinate map. -/
def ratioIdeal : Ideal (MvPolynomial (X ⊕ Y) R) :=
  RingHom.ker (ratioPolynomialMap R x y i j)

/-- The chart is concretely the quotient by its displayed equations. -/
def ratioChartPresentation :
    (MvPolynomial (X ⊕ Y) R ⧸ ratioIdeal R x y i j) ≃ₐ[R] ratioChart R x y i j :=
  (Ideal.quotientKerEquivRange (ratioPolynomialMap R x y i j)).trans
    (Subalgebra.equivOfEq _ _ (ratioPolynomialMap_range R x y i j))

@[simp] theorem ratioPolynomialMap_left (k : X) :
    ratioPolynomialMap R x y i j (MvPolynomial.X (Sum.inl k)) = leftRatio x y i j k := by
  simp [ratioPolynomialMap]

@[simp] theorem ratioPolynomialMap_right (k : Y) :
    ratioPolynomialMap R x y i j (MvPolynomial.X (Sum.inr k)) = rightRatio x y i j k := by
  simp [ratioPolynomialMap]

/-- The chosen primal coordinate is normalized to one in the chart ideal. -/
theorem left_normalization_mem :
    MvPolynomial.X (Sum.inl i) - 1 ∈ ratioIdeal R x y i j := by
  change ratioPolynomialMap R x y i j _ = 0
  simp

/-- The chosen dual coordinate is normalized to one in the chart ideal. -/
theorem right_normalization_mem :
    MvPolynomial.X (Sum.inr j) - 1 ∈ ratioIdeal R x y i j := by
  change ratioPolynomialMap R x y i j _ = 0
  simp

theorem ratioIdeal_isRadical [IsReduced Q] : (ratioIdeal R x y i j).IsRadical := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mpr
  exact SaturatedFlatFamily.quotient_ker_reduced (ratioPolynomialMap R x y i j)

theorem ratioIdeal_saturated [NoZeroSMulDivisors R Q]
    (r : R) (hr : r ≠ 0) (p : MvPolynomial (X ⊕ Y) R)
    (hp : r • p ∈ ratioIdeal R x y i j) : p ∈ ratioIdeal R x y i j := by
  change ratioPolynomialMap R x y i j p = 0
  change (ratioPolynomialMap R x y i j).toLinearMap (r • p) = 0 at hp
  rw [(ratioPolynomialMap R x y i j).toLinearMap.map_smul] at hp
  exact (smul_eq_zero.mp hp).resolve_left hr

end Sheshadri.GeneralConormalFlatFamily
