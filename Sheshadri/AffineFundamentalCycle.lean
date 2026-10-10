/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalCycles
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Actual generic lengths and the fundamental cycle of an affine ring

For a Noetherian ring, this file constructs the finite cycle of its actual
minimal primes, weighted by lengths of their actual localizations. Positivity,
full spectrum support, and coefficient one for a reduced ring are proved.
This does not assert purity or define projective intersection degrees, and
does not yet glue these affine cycles to the project's projective family.
-/

noncomputable section
namespace Sheshadri.AffineFundamentalCycle

variable (R : Type*) [CommRing R]

abbrev Component := {p : Ideal R // p ∈ minimalPrimes R}

instance component_isPrime (p : Component R) : p.val.IsPrime := p.property.1.1

abbrev GenericLocalRing (p : Component R) := Localization.AtPrime p.val

instance genericLocalRing_zeroDim (p : Component R) :
    Ring.KrullDimLE 0 (GenericLocalRing R p) :=
  Ring.KrullDimLE.of_isLocalization p.val p.property (GenericLocalRing R p)

/-- Multiplicity is the length of an actual local ring, not a chosen weight. -/
def multiplicity (p : Component R) : ℕ :=
  (Module.length (GenericLocalRing R p) (GenericLocalRing R p)).toNat

variable [IsNoetherianRing R]

instance component_finite : Finite (Component R) :=
  (minimalPrimes.finite_of_isNoetherianRing R).to_subtype

instance genericLocalRing_noetherian (p : Component R) :
    IsNoetherianRing (GenericLocalRing R p) :=
  IsLocalization.isNoetherianRing p.val.primeCompl (GenericLocalRing R p) inferInstance

instance genericLocalRing_artinian (p : Component R) :
    IsArtinianRing (GenericLocalRing R p) :=
  IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

theorem generic_length_finite (p : Component R) :
    Module.length (GenericLocalRing R p) (GenericLocalRing R p) ≠ ⊤ :=
  Module.length_ne_top

theorem multiplicity_pos (p : Component R) : 0 < multiplicity R p := by
  have h := Module.length_pos (R := GenericLocalRing R p) (M := GenericLocalRing R p)
  rw [← ENat.coe_toNat (generic_length_finite R p)] at h
  exact_mod_cast h

/-- The affine fundamental cycle, with every minimal-prime generic length. -/
def cycle : ConormalCycles.EffectiveCycle (Component R) :=
  Finsupp.equivFunOnFinite.symm (multiplicity R)

@[simp] theorem cycle_apply (p : Component R) : cycle R p = multiplicity R p := rfl

@[simp] theorem mem_cycle_support (p : Component R) : p ∈ (cycle R).support :=
  Finsupp.mem_support_iff.mpr (Nat.ne_of_gt (multiplicity_pos R p))

def componentSet (p : Component R) : Set (PrimeSpectrum R) :=
  PrimeSpectrum.zeroLocus (p.val : Set R)

theorem componentSet_closed (p : Component R) : IsClosed (componentSet R p) :=
  PrimeSpectrum.isClosed_zeroLocus _

theorem componentSet_is_component (p : Component R) :
    componentSet R p ∈ irreducibleComponents (PrimeSpectrum R) := by
  apply PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents.mpr
  simpa only [Ideal.IsPrime.radical] using p.property

/-- The constructed cycle has exactly the whole support of the affine scheme. -/
theorem supportSet_eq_univ :
    ConormalCycles.supportSet (componentSet R) (cycle R) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨p, hp, hpx⟩ := Ideal.exists_minimalPrimes_le (J := x.asIdeal) bot_le
  apply Set.mem_iUnion.mpr
  refine ⟨⟨p, hp⟩, Set.mem_iUnion.mpr ⟨mem_cycle_support R _, ?_⟩⟩
  exact hpx

/-- Reduced total rings have actual generic multiplicity one. Their
specialized fibre rings need not be reduced, so this is not applied to them
without a separate proof of reducedness. -/
theorem multiplicity_eq_one [IsReduced R] (p : Component R) :
    multiplicity R p = 1 := by
  letI : Field (GenericLocalRing R p) :=
    (Ring.KrullDimLE.isField_of_isReduced (R := GenericLocalRing R p)).toField
  simp [multiplicity, Module.length_eq_finrank]

theorem cycle_apply_eq_one [IsReduced R] (p : Component R) : cycle R p = 1 :=
  multiplicity_eq_one R p

end Sheshadri.AffineFundamentalCycle
