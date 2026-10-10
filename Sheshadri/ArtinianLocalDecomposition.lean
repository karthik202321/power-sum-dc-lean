/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.LocalLengthDimension
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Actual Artinian local decomposition and the sum of local lengths

The canonical map to the localizations at all maximal ideals is proved
bijective, including for nonreduced rings. Over an algebraically closed field,
the residue-field identifications and the equality with total vector-space
dimension are derived rather than assumed.
-/

noncomputable section
namespace Sheshadri.ArtinianLocalDecomposition

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

section Rings
variable (R : Type*) [CommRing R] [IsArtinianRing R]

theorem maximal_power_le_localization_kernel (p : MaximalSpectrum R) :
    ∃ N : ℕ, p.asIdeal ^ N ≤ RingHom.ker (algebraMap R (Localization.AtPrime p.asIdeal)) := by
  let A := Localization.AtPrime p.asIdeal
  have hn : IsNilpotent (IsLocalRing.maximalIdeal A) := by
    simpa only [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] using
      (IsArtinianRing.isNilpotent_jacobson_bot (R := A))
  obtain ⟨N, hN⟩ := hn
  refine ⟨N, ?_⟩
  calc
    p.asIdeal ^ N = ((IsLocalRing.maximalIdeal A).comap (algebraMap R A)) ^ N :=
      congrArg (fun J : Ideal R => J ^ N)
        (Localization.AtPrime.comap_maximalIdeal (I := p.asIdeal)).symm
    _ ≤ (IsLocalRing.maximalIdeal A ^ N).comap (algebraMap R A) :=
      Ideal.le_comap_pow (algebraMap R A) N
    _ = RingHom.ker (algebraMap R A) := by rw [hN]; rfl

/-- The actual canonical product map is surjective for an Artinian ring.
Its kernel remains zero even when the ring has nilpotents. -/
theorem toPiLocalization_surjective :
    Function.Surjective (MaximalSpectrum.toPiLocalization R) := by
  classical
  letI := Fintype.ofFinite (MaximalSpectrum R)
  choose N hN using maximal_power_le_localization_kernel R
  have hcop : Pairwise (fun p q : MaximalSpectrum R =>
      IsCoprime (p.asIdeal ^ N p) (q.asIdeal ^ N q)) := by
    intro p q hpq
    exact (Ideal.isCoprime_of_isMaximal (fun h => hpq (MaximalSpectrum.ext h))).pow
  intro y
  choose f hf using fun p : MaximalSpectrum R =>
    IsArtinianRing.localization_surjective p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (y p)
  obtain ⟨g, hg⟩ := Ideal.exists_forall_sub_mem_ideal hcop f
  refine ⟨g, funext fun p => ?_⟩
  have h : algebraMap R (Localization.AtPrime p.asIdeal) (g - f p) = 0 := hN p (hg p)
  simpa only [map_sub, hf, sub_eq_zero] using h

theorem toPiLocalization_bijective :
    Function.Bijective (MaximalSpectrum.toPiLocalization R) :=
  ⟨MaximalSpectrum.toPiLocalization_injective R, toPiLocalization_surjective R⟩

end Rings

section FiniteAlgebras
variable (K R : Type*) [Field K] [CommRing R] [Algebra K R] [Module.Finite K R]

instance localAlgebra_finite (p : MaximalSpectrum R) :
    Module.Finite K (Localization.AtPrime p.asIdeal) := by
  letI : IsArtinianRing R := IsArtinianRing.of_finite K R
  exact Module.Finite.of_surjective
    (IsScalarTower.toAlgHom K R (Localization.AtPrime p.asIdeal)).toLinearMap
    (IsArtinianRing.localization_surjective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))

def piLocalizationAlgHom : R →ₐ[K] MaximalSpectrum.PiLocalization R :=
  Pi.algHom K _ (fun p => IsScalarTower.toAlgHom K R (Localization.AtPrime p.asIdeal))

def piLocalizationAlgEquiv : R ≃ₐ[K] MaximalSpectrum.PiLocalization R := by
  letI : IsArtinianRing R := IsArtinianRing.of_finite K R
  exact AlgEquiv.ofBijective (piLocalizationAlgHom K R) (toPiLocalization_bijective R)

theorem finrank_eq_sum_local_finrank [Fintype (MaximalSpectrum R)] :
    Module.finrank K R = ∑ p : MaximalSpectrum R, Module.finrank K (Localization.AtPrime p.asIdeal) := by
  rw [(piLocalizationAlgEquiv K R).toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

end FiniteAlgebras

section ClosedResidueFields
variable (K A : Type*) [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A]
  [IsLocalRing A] [Module.Finite K A]

/-- The residue field of a finite local algebra over an algebraically closed
field is that field, proved from integrality of the actual finite quotient. -/
def finiteLocalResidue : A →ₐ[K] K :=
  (AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ IsLocalRing.maximalIdeal A))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K))).symm.toAlgHom.comp
      (Ideal.Quotient.mkₐ K (IsLocalRing.maximalIdeal A))

theorem finiteLocal_length_eq_finrank : Module.length A A = (Module.finrank K A : ℕ∞) :=
  LocalLengthDimension.length_eq_finrank (finiteLocalResidue K A) A

end ClosedResidueFields

section SumLengths
variable (K R : Type*) [Field K] [IsAlgClosed K] [CommRing R] [Algebra K R]
  [Module.Finite K R] [Fintype (MaximalSpectrum R)]

/-- Total dimension equals the sum of the lengths of ALL actual maximal
local rings. No choice of reduced points or multiplicity certificate occurs. -/
theorem finrank_eq_sum_local_length :
    (Module.finrank K R : ℕ∞) =
      ∑ p : MaximalSpectrum R,
        Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) := by
  simp_rw [finiteLocal_length_eq_finrank K]
  rw [finrank_eq_sum_local_finrank K R, Nat.cast_sum]

end SumLengths
end Sheshadri.ArtinianLocalDecomposition
