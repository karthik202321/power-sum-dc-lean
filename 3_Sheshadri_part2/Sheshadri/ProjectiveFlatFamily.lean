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
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Actual relative Proj is flat over a PID

For a genuinely graded algebra whose underlying module is torsion-free over
a PID, every homogeneous localization is torsion-free.  The standard affine
cover of Mathlib's actual `Proj` scheme then proves its actual structure
morphism flat. This is a theorem about the scheme, not a collection of
assumed chart-flatness certificates.
-/

noncomputable section
namespace Sheshadri.ProjectiveFlatFamily

section HomogeneousLocalization

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (M : Submonoid A)

/-- The actual base map into the degree-zero localization. -/
def homogeneousBaseMap : R →+* HomogeneousLocalization 𝒜 M :=
  (HomogeneousLocalization.fromZeroRingHom 𝒜 M).comp (algebraMap R (𝒜 0))

local instance homogeneousBaseAlgebra : Algebra R (HomogeneousLocalization 𝒜 M) :=
  (homogeneousBaseMap 𝒜 M).toAlgebra

local instance homogeneousBaseSMul : SMul R (HomogeneousLocalization 𝒜 M) :=
  (homogeneousBaseAlgebra 𝒜 M).toSMul

/-- The homogeneous localization embeds linearly in the full localization. -/
def homogeneousVal : HomogeneousLocalization 𝒜 M →ₐ[R] Localization M where
  toRingHom := algebraMap (HomogeneousLocalization 𝒜 M) (Localization M)
  commutes' r := by
    change HomogeneousLocalization.val
      (HomogeneousLocalization.fromZeroRingHom 𝒜 M (algebraMap R (𝒜 0) r)) = _
    simp only [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.val_mk]
    change Localization.mk (algebraMap R A r) (1 : M) = algebraMap R (Localization M) r
    rw [Localization.mk_one_eq_algebraMap]
    rfl

theorem homogeneousVal_injective : Function.Injective (homogeneousVal 𝒜 M) :=
  HomogeneousLocalization.val_injective M

theorem homogeneousLocalization_torsionfree [NoZeroSMulDivisors R A] :
    NoZeroSMulDivisors R (HomogeneousLocalization 𝒜 M) := by
  letI : NoZeroSMulDivisors R (Localization M) :=
    GeneralConormalFlatFamily.localization_torsionfree M
  exact (homogeneousVal_injective 𝒜 M).noZeroSMulDivisors _
    (map_zero _) (fun r z => (homogeneousVal 𝒜 M).toLinearMap.map_smul r z)

/-- Every actual homogeneous-localization base map is flat over a PID. -/
theorem homogeneousBaseMap_flat [IsDomain R] [IsPrincipalIdealRing R]
    [NoZeroSMulDivisors R A] : (homogeneousBaseMap 𝒜 M).Flat := by
  change @Module.Flat R (HomogeneousLocalization 𝒜 M) _ _
    (homogeneousBaseAlgebra 𝒜 M).toModule
  letI := homogeneousLocalization_torsionfree 𝒜 M
  exact ConormalFlatness.flat_of_torsionfree_pid R _

end HomogeneousLocalization

section Proj

open AlgebraicGeometry CategoryTheory

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- The actual structure morphism of relative `Proj` to the original base. -/
def structureToBase : Proj 𝒜 ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))

/-- A torsion-free graded algebra over a PID gives an actually flat Proj
structure morphism, proved on Mathlib's standard affine open cover. -/
theorem structureToBase_flat [IsDomain R] [IsPrincipalIdealRing R]
    [NoZeroSMulDivisors R A] : Flat (structureToBase 𝒜) := by
  apply IsLocalAtSource.of_openCover (P := @Flat) (Proj.affineOpenCover 𝒜).openCover
  intro i
  change Flat (Proj.awayι 𝒜 i.2 i.2.2 i.1.2 ≫ structureToBase 𝒜)
  rw [structureToBase, ← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact homogeneousBaseMap_flat 𝒜 (Submonoid.powers (i.2 : A))

end Proj

end Sheshadri.ProjectiveFlatFamily
