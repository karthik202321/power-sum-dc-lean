/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.LocalResidueLocalization
import Mathlib.RingTheory.MvPolynomial.Localization
import Sheshadri.SingularSpecialFiber

/-!
# Actual local points of nested polynomial equation rings

When localization in the base variables already gives a local graph algebra,
localizing at the full point gives exactly the same ring. All evaluation
ideals and denominator submonoids here are literal.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 3
namespace Sheshadri.NestedPolynomialLocalPoint

open MvPolynomial

variable {Z V K : Type*} [Field K]

attribute [local instance] RingHom.ker_isPrime

def evaluation (p : Z → K) (q : V → K) : MvPolynomial V (MvPolynomial Z K) →+* K :=
  eval₂Hom (eval p) q

def baseDenominators (I : Ideal (MvPolynomial V (MvPolynomial Z K))) (p : Z → K) :
    Submonoid (MvPolynomial V (MvPolynomial Z K) ⧸ I) :=
  ((RingHom.ker (eval p)).primeCompl.map
    (C : MvPolynomial Z K →+* MvPolynomial V (MvPolynomial Z K))).map (Ideal.Quotient.mk I)

def quotientEvaluation (I : Ideal (MvPolynomial V (MvPolynomial Z K)))
    (p : Z → K) (q : V → K) (hI : I ≤ RingHom.ker (evaluation p q)) :
    (MvPolynomial V (MvPolynomial Z K) ⧸ I) →+* K :=
  Ideal.Quotient.lift I (evaluation p q) hI

@[simp] theorem quotientEvaluation_mk (I : Ideal (MvPolynomial V (MvPolynomial Z K)))
    (p : Z → K) (q : V → K) (hI : I ≤ RingHom.ker (evaluation p q))
    (f : MvPolynomial V (MvPolynomial Z K)) :
    quotientEvaluation I p q hI (Ideal.Quotient.mk I f) = evaluation p q f := rfl

def quotientPointIdeal (I : Ideal (MvPolynomial V (MvPolynomial Z K)))
    (p : Z → K) (q : V → K) (hI : I ≤ RingHom.ker (evaluation p q)) :
    Ideal (MvPolynomial V (MvPolynomial Z K) ⧸ I) :=
  RingHom.ker (quotientEvaluation I p q hI)

theorem quotientEvaluation_surjective (I : Ideal (MvPolynomial V (MvPolynomial Z K)))
    (p : Z → K) (q : V → K) (hI : I ≤ RingHom.ker (evaluation p q)) :
    Function.Surjective (quotientEvaluation I p q hI) := by
  intro c
  exact ⟨Ideal.Quotient.mk I (C (C c)), by simp [evaluation]⟩

instance quotientPointIdeal_isMaximal (I : Ideal (MvPolynomial V (MvPolynomial Z K)))
    (p : Z → K) (q : V → K) (hI : I ≤ RingHom.ker (evaluation p q)) :
    (quotientPointIdeal I p q hI).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (quotientEvaluation_surjective I p q hI)

abbrev LocalRing (I : Ideal (MvPolynomial V (MvPolynomial Z K)))
    (p : Z → K) (q : V → K) (hI : I ≤ RingHom.ker (evaluation p q)) :=
  Localization.AtPrime (quotientPointIdeal I p q hI)

/-- Every denominator from the base point is genuinely nonzero at the full
point of the equation quotient. -/
theorem evaluation_denominator_ne_zero (I : Ideal (MvPolynomial V (MvPolynomial Z K)))
    (p : Z → K) (q : V → K) (hI : I ≤ RingHom.ker (evaluation p q))
    (s : baseDenominators I p) : quotientEvaluation I p q hI s ≠ 0 := by
  obtain ⟨t, ht, hst⟩ := s.property
  obtain ⟨f, hf, htf⟩ := ht
  have hs : (s : MvPolynomial V (MvPolynomial Z K) ⧸ I) =
      Ideal.Quotient.mk I (C f) := by rw [← hst, ← htf]
  rw [hs, quotientEvaluation_mk]
  change eval p f ≠ 0 at hf
  simpa only [evaluation, eval₂Hom_C] using hf

/-- Once localization in the base variables is local, it equals the actual
local ring of the full incidence point. -/
def atPointEquivBaseLocalization (I : Ideal (MvPolynomial V (MvPolynomial Z K)))
    (p : Z → K) (q : V → K) (hI : I ≤ RingHom.ker (evaluation p q))
    [IsLocalRing (Localization (baseDenominators I p))] :
    LocalRing I p q hI ≃+* Localization (baseDenominators I p) :=
  LocalResidueLocalization.atKernelEquiv (S := Localization (baseDenominators I p))
    (baseDenominators I p)
    (quotientEvaluation I p q hI) (quotientEvaluation_surjective I p q hI)
      (evaluation_denominator_ne_zero I p q hI)

/-- Localizing the ambient nested polynomial ring and then imposing the
actual equations gives the actual local equation ring at the full point. -/
def localEquationQuotientEquiv (I : Ideal (MvPolynomial V (MvPolynomial Z K)))
    (p : Z → K) (q : V → K) (hI : I ≤ RingHom.ker (evaluation p q)) :
    (Localization.AtPrime (RingHom.ker (evaluation p q)) ⧸
      I.map (algebraMap _ (Localization.AtPrime (RingHom.ker (evaluation p q))))) ≃+*
      LocalRing I p q hI := by
  have he : RingHom.ker (evaluation p q) =
      (quotientPointIdeal I p q hI).comap (Ideal.Quotient.mk I) := by
    ext f
    rfl
  have hk : RingHom.ker (Ideal.Quotient.mk I) = I := Ideal.mk_ker
  exact (Ideal.quotEquivOfEq (congrArg
    (Ideal.map (algebraMap _ (Localization.AtPrime (RingHom.ker (evaluation p q))))) hk).symm).trans
      (SingularSpecialFiber.localizationQuotientEquiv (RingHom.ker (evaluation p q))
        (quotientPointIdeal I p q hI) (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective he)

/-- Equality of the actual localized equation ideals identifies the local
equation rings at the displayed point. -/
def localEquivOfLocalizedIdealsEq
    (I J : Ideal (MvPolynomial V (MvPolynomial Z K))) (p : Z → K) (q : V → K)
    (hI : I ≤ RingHom.ker (evaluation p q)) (hJ : J ≤ RingHom.ker (evaluation p q))
    (hIJ : I.map (algebraMap _ (Localization.AtPrime (RingHom.ker (evaluation p q)))) =
      J.map (algebraMap _ (Localization.AtPrime (RingHom.ker (evaluation p q))))) :
    LocalRing I p q hI ≃+* LocalRing J p q hJ :=
  (localEquationQuotientEquiv I p q hI).symm.trans
    ((Ideal.quotEquivOfEq hIJ).trans (localEquationQuotientEquiv J p q hJ))

end Sheshadri.NestedPolynomialLocalPoint
