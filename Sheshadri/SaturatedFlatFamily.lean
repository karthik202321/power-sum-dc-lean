/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalFlatness
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Canonical reduced horizontal affine families

For an ideal `I` over the fraction field `K` of a PID `R`, we construct the
affine `R`-algebra obtained by contracting `radical I` to `R[variables]`.
Unlike a flatness certificate, the ideal and quotient are explicit.  The
quotient embeds in the reduced generic algebra, so it is reduced and is
torsion-free over `R`; consequently its actual spectrum morphism is flat.

This gives the local algebra for the reduced horizontal closure in Section
7.2.  Identifying and gluing the affine charts of a particular projective
Gauss graph is a separate geometric obligation.
-/

noncomputable section

namespace Sheshadri.SaturatedFlatFamily

section Kernel

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] (f : S →ₐ[R] T)

/-- A kernel quotient is reduced when its target is reduced. -/
theorem quotient_ker_reduced [IsReduced T] : IsReduced (S ⧸ RingHom.ker f) :=
  isReduced_of_injective (Ideal.kerLiftAlg f) (Ideal.kerLiftAlg_injective f)

/-- Torsion-freeness descends to the explicitly constructed kernel quotient. -/
theorem quotient_ker_torsionfree [NoZeroSMulDivisors R T] :
    NoZeroSMulDivisors R (S ⧸ RingHom.ker f) :=
  (Ideal.kerLiftAlg_injective f).noZeroSMulDivisors _
    (map_zero _) (fun r x => (Ideal.kerLiftAlg f).toLinearMap.map_smul r x)

end Kernel

section Saturation

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Scalar saturation of a concrete ideal suffices for torsion-freeness of
its actual quotient; this interface also applies to vanishing ideals of
Gauss graphs when saturation is proved by smooth-point persistence. -/
theorem quotient_torsionfree_of_saturated (I : Ideal S)
    (hsat : ∀ (r : R), r ≠ 0 → ∀ x : S, r • x ∈ I → x ∈ I) :
    NoZeroSMulDivisors R (S ⧸ I) := by
  constructor
  intro r x hrx
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply hsat r hr s
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mkₐ R I).toLinearMap (r • s) = 0
    rw [(Ideal.Quotient.mkₐ R I).toLinearMap.map_smul]
    exact hrx

/-- Saturation constructs a flat affine quotient over a PID. -/
theorem quotient_flat_of_saturated [IsDomain R] [IsPrincipalIdealRing R]
    (I : Ideal S)
    (hsat : ∀ (r : R), r ≠ 0 → ∀ x : S, r • x ∈ I → x ∈ I) :
    Module.Flat R (S ⧸ I) := by
  letI := quotient_torsionfree_of_saturated I hsat
  exact ConormalFlatness.flat_of_torsionfree_pid R (S ⧸ I)

end Saturation

section Polynomial

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
variable {σ : Type*} (I : Ideal (MvPolynomial σ K))

/-- The reduced generic-fibre coordinate algebra. -/
abbrev GenericReducedRing := MvPolynomial σ K ⧸ I.radical

instance genericReducedRing_reduced : IsReduced (GenericReducedRing K I) :=
  (Ideal.isRadical_iff_quotient_reduced I.radical).mp I.radical_isRadical

/-- Send a polynomial over the base to the reduced generic fibre. -/
def genericMap : MvPolynomial σ R →ₐ[R] GenericReducedRing K I :=
  (Ideal.Quotient.mkₐ R I.radical).comp
    (MvPolynomial.mapAlgHom (Algebra.ofId R K))

/-- The contracted radical ideal, defining the reduced horizontal closure. -/
def horizontalIdeal : Ideal (MvPolynomial σ R) := RingHom.ker (genericMap R K I)

/-- The actual affine coordinate ring, rather than an abstract certificate. -/
abbrev HorizontalRing := MvPolynomial σ R ⧸ horizontalIdeal R K I

/-- The construction is literally contraction of the generic radical. -/
theorem horizontalIdeal_eq_comap :
    horizontalIdeal R K I = I.radical.comap (MvPolynomial.map (algebraMap R K)) := by
  ext p
  change Ideal.Quotient.mk I.radical (MvPolynomial.map (algebraMap R K) p) = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The support is exactly the Zariski closure of the generic zero locus.
Thus this is a construction of the affine horizontal closure, not merely a
flat quotient unrelated to the starting generic scheme. -/
theorem horizontal_zeroLocus_eq_closure :
    PrimeSpectrum.zeroLocus (horizontalIdeal R K I) =
      closure (PrimeSpectrum.comap (MvPolynomial.map (algebraMap R K)) ''
        PrimeSpectrum.zeroLocus (I : Set (MvPolynomial σ K))) := by
  rw [horizontalIdeal_eq_comap]
  simpa only [PrimeSpectrum.zeroLocus_radical] using
    (PrimeSpectrum.closure_image_comap_zeroLocus
      (MvPolynomial.map (algebraMap R K)) I.radical).symm

/-- A canonical injection into the reduced generic coordinate ring. -/
def genericEmbedding : HorizontalRing R K I →ₐ[R] GenericReducedRing K I :=
  Ideal.kerLiftAlg (genericMap R K I)

theorem genericEmbedding_injective : Function.Injective (genericEmbedding R K I) :=
  Ideal.kerLiftAlg_injective (genericMap R K I)

instance horizontalRing_reduced : IsReduced (HorizontalRing R K I) :=
  quotient_ker_reduced (genericMap R K I)

variable [IsDomain R] [IsFractionRing R K]

instance genericReducedRing_torsionfree : NoZeroSMulDivisors R (GenericReducedRing K I) := by
  letI : NoZeroSMulDivisors K (GenericReducedRing K I) :=
    GroupWithZero.toNoZeroSMulDivisors
  exact NoZeroSMulDivisors.trans_faithfulSMul R K (GenericReducedRing K I)

instance horizontalRing_torsionfree : NoZeroSMulDivisors R (HorizontalRing R K I) :=
  quotient_ker_torsionfree (genericMap R K I)

/-- Saturation by every nonzero base scalar is a theorem of the construction. -/
theorem horizontalIdeal_saturated (r : R) (hr : r ≠ 0) (p : MvPolynomial σ R)
    (hp : r • p ∈ horizontalIdeal R K I) : p ∈ horizontalIdeal R K I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h : r • (Ideal.Quotient.mk (horizontalIdeal R K I) p) = 0 := by
    change r • ((Ideal.Quotient.mkₐ R (horizontalIdeal R K I)).toLinearMap p) = 0
    rw [← (Ideal.Quotient.mkₐ R (horizontalIdeal R K I)).toLinearMap.map_smul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
  exact (smul_eq_zero.mp h).resolve_left hr

variable [IsPrincipalIdealRing R]

instance horizontalRing_flat : Module.Flat R (HorizontalRing R K I) :=
  ConormalFlatness.flat_of_torsionfree_pid R (HorizontalRing R K I)

/-- Flatness of the actual structure ring homomorphism. -/
theorem horizontal_algebraMap_flat : (algebraMap R (HorizontalRing R K I)).Flat :=
  flat_algebraMap_iff.mpr (horizontalRing_flat R K I)

end Polynomial

section Scheme

universe u
variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsFractionRing R K] [IsPrincipalIdealRing R]
variable {σ : Type u} (I : Ideal (MvPolynomial σ K))

/-- The affine horizontal family is an actual scheme with an actually flat
structure morphism.  No assumption of flatness or componentwise dominance
occurs in this theorem. -/
theorem horizontal_spec_flat :
    AlgebraicGeometry.Flat
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap R (HorizontalRing R K I)))) := by
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
  exact horizontal_algebraMap_flat R K I

end Scheme

end Sheshadri.SaturatedFlatFamily
