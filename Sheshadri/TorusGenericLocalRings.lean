/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ProjectiveCycleLengths
import Sheshadri.FlatLocalLength
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Actual generic local rings of polynomial and torus extensions

Minimal primes of a polynomial ring are exactly the extensions of the base
minimal primes. Inverting the product of the two torus coordinates removes
none of these primes. The local coefficient map is flat and extends the
actual maximal ideal to the actual maximal ideal.
-/

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section
namespace Sheshadri.TorusGenericLocalRings
open MvPolynomial

variable {R : Type*} [CommRing R]

def polynomialPrime (σ : Type*) (p : Ideal R) : Ideal (MvPolynomial σ R) :=
  p.map MvPolynomial.C

theorem polynomialPrime_eq_ker (σ : Type*) (p : Ideal R) :
    polynomialPrime σ p = RingHom.ker (MvPolynomial.map (σ := σ) (Ideal.Quotient.mk p)) := by
  rw [MvPolynomial.ker_map, Ideal.mk_ker]
  rfl

instance polynomialPrime_isPrime (σ : Type*) (p : Ideal R) [p.IsPrime] :
    (polynomialPrime σ p).IsPrime := by
  rw [polynomialPrime_eq_ker]
  exact RingHom.ker_isPrime _

@[simp] theorem polynomialPrime_comap (σ : Type*) (p : Ideal R) :
    (polynomialPrime σ p).comap MvPolynomial.C = p := by
  ext r
  change C r ∈ p.map (C : R →+* MvPolynomial σ R) ↔ r ∈ p
  rw [MvPolynomial.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h d
    classical
    by_cases hd : d = 0
    · simpa [hd] using h
    · simp [coeff_C, Ne.symm hd]

instance polynomialPrime_liesOver (σ : Type*) (p : Ideal R) :
    (polynomialPrime σ p).LiesOver p :=
  ⟨(polynomialPrime_comap σ p).symm⟩

theorem polynomialPrime_minimal (σ : Type*) (p : Ideal R)
    (hp : p ∈ minimalPrimes R) : polynomialPrime σ p ∈ minimalPrimes (MvPolynomial σ R) := by
  letI : p.IsPrime := hp.1.1
  refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
  intro q hq hle
  apply Ideal.map_le_iff_le_comap.mpr
  apply hp.2 ⟨hq.1.comap _, bot_le⟩
  simpa only [polynomialPrime_comap] using Ideal.comap_mono (f := MvPolynomial.C) hle

/-- Every actual minimal polynomial prime is extended from a minimal base
prime. No reduction or Noetherian hypothesis is needed. -/
theorem polynomial_minimal_eq_extension (σ : Type*) (q : Ideal (MvPolynomial σ R))
    (hq : q ∈ minimalPrimes (MvPolynomial σ R)) :
    q.comap MvPolynomial.C ∈ minimalPrimes R ∧
      polynomialPrime σ (q.comap MvPolynomial.C) = q := by
  letI : q.IsPrime := hq.1.1
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le
    (J := q.comap MvPolynomial.C) bot_le
  have he : polynomialPrime σ p = q := by
    apply le_antisymm
    · exact Ideal.map_le_iff_le_comap.mpr hpq
    · exact hq.2 (polynomialPrime_minimal σ p hp).1
        (Ideal.map_le_iff_le_comap.mpr hpq)
  have hc : q.comap MvPolynomial.C = p := by rw [← he, polynomialPrime_comap]
  exact ⟨hc ▸ hp, by rw [hc, he]⟩

def polynomialComponent (σ : Type*) (p : AffineFundamentalCycle.Component R) :
    AffineFundamentalCycle.Component (MvPolynomial σ R) :=
  ⟨polynomialPrime σ p.val, polynomialPrime_minimal σ p.val p.property⟩

def baseComponent (σ : Type*) (q : AffineFundamentalCycle.Component (MvPolynomial σ R)) :
    AffineFundamentalCycle.Component R :=
  ⟨q.val.comap MvPolynomial.C, (polynomial_minimal_eq_extension σ q.val q.property).1⟩

/-- The actual irreducible components of polynomial extension correspond
bijectively to the actual components of the base. -/
def polynomialComponentEquiv (σ : Type*) :
    AffineFundamentalCycle.Component R ≃
      AffineFundamentalCycle.Component (MvPolynomial σ R) where
  toFun := polynomialComponent σ
  invFun := baseComponent σ
  left_inv p := Subtype.ext (polynomialPrime_comap σ p.val)
  right_inv q := Subtype.ext (polynomial_minimal_eq_extension σ q.val q.property).2

/-- The local coefficient map extends the base maximal ideal exactly to
the target maximal ideal. Its closed fibre is therefore a field. -/
theorem local_maximalIdeal_extension (σ : Type*) (p : Ideal R) [p.IsPrime] :
    (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p)
          (Localization.AtPrime (polynomialPrime σ p))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime (polynomialPrime σ p)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal (I := p), Ideal.map_map]
  rw [← IsScalarTower.algebraMap_eq R (Localization.AtPrime p)
    (Localization.AtPrime (polynomialPrime σ p))]
  rw [IsScalarTower.algebraMap_eq R (MvPolynomial σ R)
    (Localization.AtPrime (polynomialPrime σ p)), ← Ideal.map_map]
  exact Localization.AtPrime.map_eq_maximalIdeal

def torusDenominator (R : Type*) [CommRing R] : MvPolynomial Bool R :=
  MvPolynomial.X true * MvPolynomial.X false

abbrev Torus (R : Type*) [CommRing R] := Localization.Away (torusDenominator R)

def torusPrime (p : Ideal R) : Ideal (Torus R) :=
  (polynomialPrime Bool p).map (algebraMap (MvPolynomial Bool R) (Torus R))

theorem torusDenominator_not_mem (p : Ideal R) [p.IsPrime] :
    torusDenominator R ∉ polynomialPrime Bool p := by
  intro h
  rw [polynomialPrime_eq_ker] at h
  have hz : (MvPolynomial.X true : MvPolynomial Bool (R ⧸ p)) *
      MvPolynomial.X false = 0 := by
    simpa [RingHom.mem_ker, torusDenominator] using h
  exact mul_ne_zero (MvPolynomial.X_ne_zero true) (MvPolynomial.X_ne_zero false) hz

theorem torus_disjoint (p : Ideal R) [p.IsPrime] :
    Disjoint (Submonoid.powers (torusDenominator R) : Set (MvPolynomial Bool R))
      (polynomialPrime Bool p : Set (MvPolynomial Bool R)) :=
  (Ideal.disjoint_powers_iff_not_mem _ (Ideal.IsPrime.isRadical inferInstance)).mpr
    (torusDenominator_not_mem p)

instance torusPrime_isPrime (p : Ideal R) [p.IsPrime] : (torusPrime p).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (torusDenominator R))
    (Torus R) (polynomialPrime Bool p) inferInstance (torus_disjoint p)

@[simp] theorem torusPrime_comap (p : Ideal R) [p.IsPrime] :
    (torusPrime p).comap (algebraMap (MvPolynomial Bool R) (Torus R)) =
      polynomialPrime Bool p :=
  IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers (torusDenominator R))
    (Torus R) (polynomialPrime Bool p) inferInstance (torus_disjoint p)

theorem torusPrime_minimal (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    torusPrime p ∈ minimalPrimes (Torus R) := by
  letI : p.IsPrime := hp.1.1
  have h := IsLocalization.minimalPrimes_map
    (Submonoid.powers (torusDenominator R)) (Torus R) (⊥ : Ideal (MvPolynomial Bool R))
  rw [Ideal.map_bot] at h
  rw [minimalPrimes, h]
  change (torusPrime p).comap (algebraMap (MvPolynomial Bool R) (Torus R)) ∈
    minimalPrimes (MvPolynomial Bool R)
  rw [torusPrime_comap]
  exact polynomialPrime_minimal Bool p hp

def torusComponent (p : AffineFundamentalCycle.Component R) :
    AffineFundamentalCycle.Component (Torus R) :=
  ⟨torusPrime p.val, torusPrime_minimal p.val p.property⟩

def torusBaseComponent (q : AffineFundamentalCycle.Component (Torus R)) :
    AffineFundamentalCycle.Component R :=
  baseComponent Bool (ProjectiveCycleLengths.contractedComponent
    (Submonoid.powers (torusDenominator R)) q)

/-- Inverting the torus coordinates removes no base component; the actual
minimal-prime correspondence is a bijection. -/
def torusComponentEquiv :
    AffineFundamentalCycle.Component R ≃ AffineFundamentalCycle.Component (Torus R) where
  toFun := torusComponent
  invFun := torusBaseComponent
  left_inv p := by
    apply Subtype.ext
    change ((torusPrime p.val).comap (algebraMap (MvPolynomial Bool R) (Torus R))).comap
      MvPolynomial.C = p.val
    rw [torusPrime_comap, polynomialPrime_comap]
  right_inv q := by
    apply Subtype.ext
    let s := ProjectiveCycleLengths.contractedComponent
      (Submonoid.powers (torusDenominator R)) q
    change (polynomialPrime Bool (s.val.comap MvPolynomial.C)).map
      (algebraMap (MvPolynomial Bool R) (Torus R)) = q.val
    rw [(polynomial_minimal_eq_extension Bool s.val s.property).2]
    exact IsLocalization.map_comap (Submonoid.powers (torusDenominator R)) (Torus R) q.val

section Length
variable [IsNoetherianRing R]

def atPrimeEquivOfEq {S : Type*} [CommRing S] (p q : Ideal S)
    [p.IsPrime] [q.IsPrime] (h : p = q) :
    Localization.AtPrime p ≃+* Localization.AtPrime q := by
  subst q
  exact RingEquiv.refl _

/-- Polynomial extension preserves the actual generic local length. The
local map is flat, and the exact maximal-ideal extension above makes its
closed fibre a field; the finite composition series therefore keeps its
length even though the residue field becomes transcendental. -/
theorem polynomial_generic_length (σ : Type*) (p : AffineFundamentalCycle.Component R) :
    Module.length (Localization.AtPrime p.val) (Localization.AtPrime p.val) =
      Module.length (Localization.AtPrime (polynomialPrime σ p.val))
        (Localization.AtPrime (polynomialPrime σ p.val)) := by
  letI : IsNoetherianRing (Localization.AtPrime p.val) :=
    AffineFundamentalCycle.genericLocalRing_noetherian R p
  letI : IsArtinianRing (Localization.AtPrime p.val) :=
    AffineFundamentalCycle.genericLocalRing_artinian R p
  exact (FlatLocalLength.ring_length_eq_of_artinian (local_maximalIdeal_extension σ p.val)).symm

/-- The two invertible scaling variables preserve every actual generic
local-ring length, including all nonreduced multiplicities. -/
theorem torus_generic_length (p : AffineFundamentalCycle.Component R) :
    Module.length (Localization.AtPrime p.val) (Localization.AtPrime p.val) =
      Module.length (Localization.AtPrime (torusPrime p.val))
        (Localization.AtPrime (torusPrime p.val)) := by
  have h := ProjectiveCycleLengths.local_length_eq
    (Submonoid.powers (torusDenominator R)) (torusPrime p.val)
  have he := ProjectiveCycleLengths.ringEquiv_length
    (atPrimeEquivOfEq _ _ (torusPrime_comap p.val))
  exact (polynomial_generic_length Bool p).trans (he.symm.trans h)

theorem polynomial_multiplicity (σ : Type*) (p : AffineFundamentalCycle.Component R) :
    AffineFundamentalCycle.multiplicity R p =
      AffineFundamentalCycle.multiplicity (MvPolynomial σ R) (polynomialComponent σ p) :=
  congrArg ENat.toNat (polynomial_generic_length σ p)

theorem torus_multiplicity (p : AffineFundamentalCycle.Component R) :
    AffineFundamentalCycle.multiplicity R p =
      AffineFundamentalCycle.multiplicity (Torus R) (torusComponent p) :=
  congrArg ENat.toNat (torus_generic_length p)

/-- Cancellation holds for every actual torus component, not only for an
explicitly chosen image component. The bijection identifies its base prime. -/
theorem torus_multiplicity_of_component
    (q : AffineFundamentalCycle.Component (Torus R)) :
    AffineFundamentalCycle.multiplicity (Torus R) q =
      AffineFundamentalCycle.multiplicity R (torusBaseComponent q) := by
  have h := torus_multiplicity (torusBaseComponent q)
  have he : torusComponent (torusBaseComponent q) = q := torusComponentEquiv.apply_symm_apply q
  rw [he] at h
  exact h.symm

end Length

end Sheshadri.TorusGenericLocalRings
