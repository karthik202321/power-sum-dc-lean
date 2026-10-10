/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.AffineFundamentalCycle
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Generic multiplicities survive restriction to a coordinate open

These are statements about actual local rings and their module lengths.
Restricting the affine cone to the open locus where a product of homogeneous
coordinates is invertible preserves every surviving component multiplicity.
A later projective chart comparison still has to account for the two scaling
torus directions; this module does not silently identify them with a quotient.
-/

noncomputable section
namespace Sheshadri.ProjectiveCycleLengths

/-- A ring isomorphism preserves length over the respective rings. -/
theorem ringEquiv_length {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Module.length R R = Module.length S S := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e.toSemilinearEquiv)

variable {R : Type*} [CommRing R] (M : Submonoid R)

/-- The local ring of a localization at an actual prime is canonically
isomorphic to the original local ring at its contracted prime. -/
def localRingEquiv (p : Ideal (Localization M)) [p.IsPrime] :
    Localization.AtPrime (p.comap (algebraMap R (Localization M))) ≃+*
      Localization.AtPrime p :=
  (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M p).toRingEquiv

theorem local_length_eq (p : Ideal (Localization M)) [p.IsPrime] :
    Module.length (Localization.AtPrime (p.comap (algebraMap R (Localization M))))
        (Localization.AtPrime (p.comap (algebraMap R (Localization M)))) =
      Module.length (Localization.AtPrime p) (Localization.AtPrime p) :=
  ringEquiv_length (localRingEquiv M p)

/-- Actual minimal components of the localized cone contract to actual
minimal components of the original cone. -/
def contractedComponent (p : AffineFundamentalCycle.Component (Localization M)) :
    AffineFundamentalCycle.Component R := by
  refine ⟨p.val.comap (algebraMap R (Localization M)), ?_⟩
  have h := IsLocalization.minimalPrimes_map M (Localization M) (⊥ : Ideal R)
  rw [Ideal.map_bot] at h
  have hp : p.val ∈ (⊥ : Ideal (Localization M)).minimalPrimes := p.property
  rw [h] at hp
  exact hp

/-- Equality of the actual generic-local-ring lengths, including all
possible nonreduced fibre multiplicities. No coefficient-one assumption. -/
theorem multiplicity_localization (p : AffineFundamentalCycle.Component (Localization M)) :
    AffineFundamentalCycle.multiplicity R (contractedComponent M p) =
      AffineFundamentalCycle.multiplicity (Localization M) p := by
  exact congrArg ENat.toNat (local_length_eq M p.val)

/-- In particular, removing the two irrelevant zero-coordinate blocks by
localizing at a chosen coordinate product preserves each surviving weight. -/
theorem multiplicity_coordinateOpen (x y : R)
    (p : AffineFundamentalCycle.Component (Localization.Away (x * y))) :
    AffineFundamentalCycle.multiplicity R
        (contractedComponent (Submonoid.powers (x * y)) p) =
      AffineFundamentalCycle.multiplicity (Localization.Away (x * y)) p :=
  multiplicity_localization (Submonoid.powers (x * y)) p



section Equivalence
variable {S : Type*} [CommRing S]

/-- Equivalent affine-chart presentations give equivalent actual local
rings, including at generic points of nonreduced components. -/
def localRingEquivOfRingEquiv (e : R ≃+* S) (p : Ideal S) [p.IsPrime] :
    Localization.AtPrime (p.comap e) ≃+* Localization.AtPrime p := by
  apply IsLocalization.ringEquivOfRingEquiv (M := (p.comap e).primeCompl)
    (T := p.primeCompl) _ _ e
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change e (e.symm y) ∉ p
    simpa using hy

theorem local_length_ringEquiv (e : R ≃+* S) (p : Ideal S) [p.IsPrime] :
    Module.length (Localization.AtPrime (p.comap e))
        (Localization.AtPrime (p.comap e)) =
      Module.length (Localization.AtPrime p) (Localization.AtPrime p) :=
  ringEquiv_length (localRingEquivOfRingEquiv e p)

/-- Minimal components are transported through the actual ring equivalence. -/
def componentOfRingEquiv (e : R ≃+* S) (p : AffineFundamentalCycle.Component S) :
    AffineFundamentalCycle.Component R := by
  refine ⟨p.val.comap e, ?_⟩
  have hp := Ideal.minimal_primes_comap_of_surjective (f := e.toRingHom) e.surjective p.property
  simpa only [Ideal.comap_bot_of_injective e.toRingHom e.injective] using hp

/-- Actual generic multiplicities agree between equivalent chart rings. -/
theorem multiplicity_ringEquiv (e : R ≃+* S) (p : AffineFundamentalCycle.Component S) :
    AffineFundamentalCycle.multiplicity R (componentOfRingEquiv e p) =
      AffineFundamentalCycle.multiplicity S p :=
  congrArg ENat.toNat (local_length_ringEquiv e p.val)

end Equivalence
end Sheshadri.ProjectiveCycleLengths
