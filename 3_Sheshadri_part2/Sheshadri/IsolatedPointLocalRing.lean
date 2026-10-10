/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.IsolatedLocalMultiplicity
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Zariski-isolated points have actual finite local intersection algebras

An open singleton in the literal spectrum of the equation quotient is a
minimal prime. Since the equation ring in finitely many variables is
Noetherian, its localization at that prime is Artinian. This connects literal
Zariski isolatedness to the local-length and fat-point theorems.
-/

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section
namespace Sheshadri.IsolatedLocalMultiplicity

open MvPolynomial

variable {σ K : Type*} [Field K]

/-- The actual rational point in the prime spectrum of the full equation ring. -/
def pointSpectrum (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) : PrimeSpectrum (EquationQuotient I) :=
  ⟨quotientPointIdeal I p hI, inferInstance⟩

/-- Literal Zariski isolatedness implies that this closed point is a minimal
component of the actual scheme, including its nonreduced structure. -/
theorem point_minimal_of_isOpen (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p)
    (h : IsOpen ({pointSpectrum I p hI} : Set (PrimeSpectrum (EquationQuotient I)))) :
    quotientPointIdeal I p hI ∈ minimalPrimes (EquationQuotient I) :=
  PrimeSpectrum.stableUnderGeneralization_singleton.mp h.stableUnderGeneralization

/-- Algebraic isolatedness at a rational point follows from its actual
minimal-prime property; no reducedness hypothesis is made. -/
theorem localIntersection_artinian_of_minimal [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (p : σ → K) (hI : I ≤ pointIdeal p)
    (h : quotientPointIdeal I p hI ∈ minimalPrimes (EquationQuotient I)) :
    IsArtinianRing (LocalIntersectionRing I p hI) := by
  letI : Ring.KrullDimLE 0 (LocalIntersectionRing I p hI) :=
    Ring.KrullDimLE.of_isLocalization (quotientPointIdeal I p hI) h
      (LocalIntersectionRing I p hI)
  letI : IsNoetherianRing (LocalIntersectionRing I p hI) :=
    IsLocalization.isNoetherianRing (quotientPointIdeal I p hI).primeCompl
      (LocalIntersectionRing I p hI) inferInstance
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/-- A literal Zariski-isolated point of the equation scheme has an Artinian
local intersection ring. Hence the previously constructed finite fat-point
algebras compute its full scheme-theoretic multiplicity. -/
theorem localIntersection_artinian_of_isOpen [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (p : σ → K) (hI : I ≤ pointIdeal p)
    (h : IsOpen ({pointSpectrum I p hI} : Set (PrimeSpectrum (EquationQuotient I)))) :
    IsArtinianRing (LocalIntersectionRing I p hI) :=
  localIntersection_artinian_of_minimal I p hI (point_minimal_of_isOpen I p hI h)

/-- Every actual rational-point local algebra has positive module length. -/
theorem multiplicity_pos (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) : 0 < multiplicity I p hI :=
  Module.length_pos

/-- Every actual isolated rational point contributes a finite positive
scheme-theoretic intersection multiplicity. -/
theorem multiplicity_ne_top [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (p : σ → K) (hI : I ≤ pointIdeal p)
    [IsArtinianRing (LocalIntersectionRing I p hI)] : multiplicity I p hI ≠ ⊤ := by
  rw [multiplicity_eq_finrank I p hI]
  exact ENat.coe_ne_top _

end Sheshadri.IsolatedLocalMultiplicity
