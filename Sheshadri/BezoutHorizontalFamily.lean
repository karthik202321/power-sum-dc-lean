/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SaturatedFlatFamily
import Sheshadri.GeneralHomogeneousBaseChange
import Sheshadri.GeneralGradedBaseChange
import Sheshadri.FlatMultiGradedHilbert
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal

/-!
# The actual horizontal family used for excess Bézout

Contract the generic equation ideal itself. Reduction is unnecessary here:
the quotient embeds in the generic quotient, hence is torsion-free over the
base PID. Homogeneity and inclusion of the original equations are theorems.
In particular no flatness or special-fibre containment certificate is assumed.
-/

noncomputable section
namespace Sheshadri.BezoutHorizontalFamily
open MvPolynomial

variable {σ R K : Type*} [CommRing R] [Field K] [Algebra R K]

def contractedIdeal (I : Ideal (MvPolynomial σ K)) : Ideal (MvPolynomial σ R) :=
  I.comap (MvPolynomial.map (algebraMap R K))

def genericMap (I : Ideal (MvPolynomial σ K)) :
    MvPolynomial σ R →ₐ[R] (MvPolynomial σ K ⧸ I) :=
  (Ideal.Quotient.mkₐ R I).comp (MvPolynomial.mapAlgHom (Algebra.ofId R K))

theorem contractedIdeal_eq_ker (I : Ideal (MvPolynomial σ K)) :
    contractedIdeal (R := R) I = RingHom.ker (genericMap (R := R) I) := by
  ext p
  change MvPolynomial.map (algebraMap R K) p ∈ I ↔
    Ideal.Quotient.mk I (MvPolynomial.map (algebraMap R K) p) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.symm

def genericEmbedding (I : Ideal (MvPolynomial σ K)) :
    (MvPolynomial σ R ⧸ contractedIdeal (R := R) I) →ₐ[R]
      (MvPolynomial σ K ⧸ I) :=
  Ideal.Quotient.liftₐ _ (genericMap I) (by
    intro p hp
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp)

theorem genericEmbedding_injective (I : Ideal (MvPolynomial σ K)) :
    Function.Injective (genericEmbedding (R := R) I) := by
  intro x y h
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨q,rfl⟩ := Ideal.Quotient.mk_surjective y
  apply Ideal.Quotient.eq.mpr
  change genericMap (R := R) I p = genericMap (R := R) I q at h
  change MvPolynomial.map (algebraMap R K) (p-q) ∈ I
  rw [map_sub]
  exact Ideal.Quotient.eq.mp h

instance contractedQuotient_torsionfree [IsDomain R] [IsFractionRing R K]
    (I : Ideal (MvPolynomial σ K)) :
    NoZeroSMulDivisors R (MvPolynomial σ R ⧸ contractedIdeal (R := R) I) := by
  letI : NoZeroSMulDivisors K (MvPolynomial σ K ⧸ I) :=
    GroupWithZero.toNoZeroSMulDivisors
  letI : NoZeroSMulDivisors R (MvPolynomial σ K ⧸ I) :=
    NoZeroSMulDivisors.trans_faithfulSMul R K _
  exact (genericEmbedding_injective I).noZeroSMulDivisors _ (map_zero _)
    (fun r x => (genericEmbedding (R := R) I).toLinearMap.map_smul r x)

instance contractedQuotient_flat [IsDomain R] [IsFractionRing R K]
    [IsPrincipalIdealRing R] (I : Ideal (MvPolynomial σ K)) :
    Module.Flat R (MvPolynomial σ R ⧸ contractedIdeal (R := R) I) :=
  ConormalFlatness.flat_of_torsionfree_pid R _

theorem originalIdeal_le_contraction (I : Ideal (MvPolynomial σ R)) :
    I ≤ contractedIdeal (R := R)
      (GeneralGradedBaseChange.extendedIdeal (K := K) I) := by
  intro p hp
  exact Ideal.mem_map_of_mem _ hp

theorem extended_contractedIdeal [IsDomain R] [IsFractionRing R K]
    (I : Ideal (MvPolynomial σ K)) :
    GeneralGradedBaseChange.extendedIdeal (K := K) (contractedIdeal (R := R) I) = I := by
  letI := MvPolynomial.algebraMvPolynomial (σ := σ) (R := R) (S := K)
  exact IsLocalization.map_comap ((nonZeroDivisors R).map (MvPolynomial.C (σ := σ)))
    (MvPolynomial σ K) I

theorem mem_contracted_extension_iff [IsDomain R] [IsFractionRing R K]
    (I : Ideal (MvPolynomial σ R)) (p : MvPolynomial σ R) :
    p ∈ contractedIdeal (R := R) (GeneralGradedBaseChange.extendedIdeal (K := K) I) ↔
      ∃ r : R, r ≠ 0 ∧ MvPolynomial.C r * p ∈ I := by
  letI := MvPolynomial.algebraMvPolynomial (σ := σ) (R := R) (S := K)
  change algebraMap (MvPolynomial σ R) (MvPolynomial σ K) p ∈
    I.map (algebraMap (MvPolynomial σ R) (MvPolynomial σ K)) ↔ _
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((nonZeroDivisors R).map (MvPolynomial.C (σ := σ)))]
  constructor
  · rintro ⟨s,⟨r,hr,rfl⟩,hs⟩
    exact ⟨r,mem_nonZeroDivisors_iff_ne_zero.mp hr,hs⟩
  · rintro ⟨r,hr,hp⟩
    exact ⟨C r,⟨r,mem_nonZeroDivisors_iff_ne_zero.mpr hr,rfl⟩,hp⟩

section Homogeneity
variable {Γ : Type*} [AddCommMonoid Γ] [DecidableEq Γ]

theorem contractedIdeal_homogeneous (w : σ → Γ) (I : Ideal (MvPolynomial σ K))
    (hI : ∀ d p, p ∈ I → weightedHomogeneousComponent w d p ∈ I) :
    ∀ d p, p ∈ contractedIdeal (R := R) I →
      weightedHomogeneousComponent w d p ∈ contractedIdeal (R := R) I := by
  intro d p hp
  change MvPolynomial.map (algebraMap R K) (weightedHomogeneousComponent w d p) ∈ I
  rw [← GeneralHomogeneousBaseChange.weightedComponent_map]
  exact hI d _ hp

theorem span_homogeneous {E : Type*} (w : σ → Γ)
    (f : E → MvPolynomial σ R) (degree : E → Γ)
    (hf : ∀ e, (f e).IsWeightedHomogeneous w (degree e)) :
    ∀ d p, p ∈ Ideal.span (Set.range f) →
      weightedHomogeneousComponent w d p ∈ Ideal.span (Set.range f) := by
  letI : GradedAlgebra (weightedHomogeneousSubmodule R w) := weightedGradedAlgebra R w
  have h : (Ideal.span (Set.range f)).IsHomogeneous (weightedHomogeneousSubmodule R w) :=
    Ideal.homogeneous_span _ _ (by rintro _ ⟨e,rfl⟩; exact ⟨degree e,hf e⟩)
  intro d p hp
  have hd := h d hp
  change (MvPolynomial.decompose' R w p d : MvPolynomial σ R) ∈ _ at hd
  rwa [MvPolynomial.decompose'_apply] at hd

end Homogeneity

section FibreComparison
open ProjectivePointInterpolation FlatMultiGradedHilbert GeneralGradedBaseChange
variable {Γ L : Type*} [AddCommMonoid Γ] [DecidableEq Γ]
variable [IsDomain R] [IsFractionRing R K] [IsPrincipalIdealRing R] [Field L]

/-- Compare two actual coefficient specializations even when they have the
same target field. The common generic fibre supplies the intervening equality. -/
theorem specialized_dimensions_equal (w : σ → Γ) (I : Ideal (MvPolynomial σ K))
    (hI : FlatMultiGradedHilbert.IsHomogeneous w I)
    (φ ψ : R →+* L) (d : Γ)
    [Module.Finite R (coordinatePiece w (contractedIdeal (R := R) I) d)] :
    Module.finrank L (coordinatePiece w
      ((contractedIdeal (R := R) I).map (MvPolynomial.map φ)) d) =
    Module.finrank L (coordinatePiece w
      ((contractedIdeal (R := R) I).map (MvPolynomial.map ψ)) d) := by
  have hJ : FlatMultiGradedHilbert.IsHomogeneous w (contractedIdeal (R := R) I) :=
    contractedIdeal_homogeneous w I hI
  have hφ : Module.finrank L (coordinatePiece w
      ((contractedIdeal (R := R) I).map (MvPolynomial.map φ)) d) =
      Module.finrank K (coordinatePiece w I d) := by
    letI : Algebra R L := φ.toAlgebra
    have h := literal_fibre_dimensions_equal w (contractedIdeal (R := R) I) hJ L K d
    rw [extended_contractedIdeal] at h
    exact h
  have hψ : Module.finrank L (coordinatePiece w
      ((contractedIdeal (R := R) I).map (MvPolynomial.map ψ)) d) =
      Module.finrank K (coordinatePiece w I d) := by
    letI : Algebra R L := ψ.toAlgebra
    have h := literal_fibre_dimensions_equal w (contractedIdeal (R := R) I) hJ L K d
    rw [extended_contractedIdeal] at h
    exact h
  exact hφ.trans hψ.symm

end FibreComparison
end Sheshadri.BezoutHorizontalFamily
