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
# Componentwise dominance of the constructed charts

An injective map into an algebra over the fraction field gives dense generic
image on spectra. Every minimal prime lifts to the generic algebra, where
nonzero base scalars are units. Hence the base embeds in each minimal-prime
quotient. This supplies the exact componentwise-dominance statement used in
Section 7.2 from the actual chart construction.
-/

noncomputable section
namespace Sheshadri.GeneralConormalFlatFamily

section GenericDominance

variable {R K S B : Type*} [CommRing R] [Field K] [CommRing S] [CommRing B]
variable [Algebra R K] [IsFractionRing R K]
variable [Algebra R S] [Algebra R B] [Algebra K B] [IsScalarTower R K B]

include K

/-- Componentwise dominance is derived from a genuine generic embedding. -/
theorem componentwiseDominant_of_generic_embedding
    (f : S →ₐ[R] B) (hf : Function.Injective f) :
    ConormalFlatness.ComponentwiseDominant (R := R) (S := S) := by
  have hdense : DenseRange (PrimeSpectrum.comap f.toRingHom) := by
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
    rw [(RingHom.injective_iff_ker_eq_bot f.toRingHom).mp hf]
    exact bot_le
  intro p hp
  rw [RingHom.injective_iff_ker_eq_bot]
  apply bot_unique
  intro r hr
  change r = 0
  by_contra hne
  have hmem : algebraMap R S r ∈ p := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact hr
  obtain ⟨q, hq⟩ := (PrimeSpectrum.denseRange_comap_iff_minimalPrimes f.toRingHom).mp hdense p hp
  have hqp : q.asIdeal.comap f.toRingHom = p := congrArg PrimeSpectrum.asIdeal hq
  have hbr : algebraMap R B r ∈ q.asIdeal := by
    rw [← hqp] at hmem
    change f (algebraMap R S r) ∈ q.asIdeal at hmem
    rwa [f.commutes] at hmem
  have hu : IsUnit (algebraMap R B r) := by
    rw [IsScalarTower.algebraMap_eq R K B]
    apply IsUnit.map (algebraMap K B)
    apply isUnit_iff_ne_zero.mpr
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hne
  exact q.isPrime.ne_top (q.asIdeal.eq_top_of_isUnit_mem hbr hu)

end GenericDominance

section Horizontal

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
variable [IsDomain R] [IsFractionRing R K] [IsPrincipalIdealRing R]
variable {X Y : Type*} (I : Ideal (MvPolynomial (X ⊕ Y) K))

/-- Every minimal component of every constructed ratio chart dominates
the arbitrary PID/DVR base. This is a theorem, not a family hypothesis. -/
theorem horizontalRatioChart_componentwiseDominant (i : X) (j : Y) :
    ConormalFlatness.ComponentwiseDominant
      (R := R) (S := HorizontalRatioChart R K I i j) :=
  componentwiseDominant_of_generic_embedding (K := K)
    (horizontalRatioGenericMap R K I i j) (horizontalRatioGenericMap_injective R K I i j)

end Horizontal

end Sheshadri.GeneralConormalFlatFamily
