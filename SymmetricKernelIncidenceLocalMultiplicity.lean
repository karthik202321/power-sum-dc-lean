/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SymmetricKernelIncidenceAlgebra
import Sheshadri.KernelIncidenceLocalMultiplicity

/-! # Actual local multiplicities of the native symmetric incidence

The one-vector graph and all quadratic polar cuts are flattened into their
literal polynomial ideal. Coefficient localization at an actual point then
identifies this quotient with the actual polar local intersection ring.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 3
namespace Sheshadri.SymmetricKernelIncidenceLocalMultiplicity
open Matrix MvPolynomial SymmetricKernelIncidenceAlgebra

variable {R : Type*} [CommRing R] {m : ℕ} {E : Type*}

abbrev polarIntersectionIdeal := @KernelIncidenceLocalMultiplicity.polarIntersectionIdeal

def incidenceFlagIdeal
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    Ideal (Polynomials R m) :=
  J.map C ⊔ ⨆ e, Ideal.span {polarEquation (H e)}

def incidenceIntersectionIdeal
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1))
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    Ideal (Polynomials R m) := incidenceIdeal A i ⊔ incidenceFlagIdeal H J

def incidenceDoubleQuotientEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1))
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    (IncidenceRing A i ⧸
      (J.map (algebraMap R (IncidenceRing A i)) ⊔
        ⨆ e, Ideal.span {Ideal.Quotient.mk (incidenceIdeal A i) (polarEquation (H e))}))
      ≃+* Polynomials R m ⧸ incidenceIntersectionIdeal A i H J := by
  have he : (incidenceFlagIdeal H J).map (Ideal.Quotient.mk (incidenceIdeal A i)) =
      (J.map (algebraMap R (IncidenceRing A i)) ⊔
        ⨆ e, Ideal.span {Ideal.Quotient.mk (incidenceIdeal A i) (polarEquation (H e))}) := by
    simp only [incidenceFlagIdeal, Ideal.map_sup, Ideal.map_iSup, Ideal.map_span,
      Set.image_singleton, Ideal.map_map]
    rfl
  exact (Ideal.quotEquivOfEq he.symm).trans
    (DoubleQuot.quotQuotEquivQuotSup (incidenceIdeal A i) (incidenceFlagIdeal H J))

def intersectionRingEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (hA : A.transpose = A)
    (i : Fin (m+1)) (ha : IsUnit (A.adjugate i i))
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    (Polynomials R m ⧸ incidenceIntersectionIdeal A i H J) ≃+*
      R ⧸ polarIntersectionIdeal A H J :=
  (incidenceDoubleQuotientEquiv A i H J).symm.trans
    ((cutIncidenceEquivDeterminant A hA i ha H J).toRingEquiv.trans
      (KernelIncidenceLocalMultiplicity.determinantDoubleQuotientEquiv A H J))

section BaseChange
variable {S : Type*} [CommRing S] (φ : R →+* S)

@[simp] theorem map_kernelEquation
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (l : Fin (m+1)) :
    MvPolynomial.map φ (kernelEquation A l) = kernelEquation (A.map φ) l := by
  simp [kernelEquation]

@[simp] theorem map_polarEquation
    (H : Matrix (Fin (m+1)) (Fin (m+1)) R) :
    MvPolynomial.map φ (polarEquation H) = polarEquation (H.map φ) := by
  simp [polarEquation]

theorem incidenceIdeal_map
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1)) :
    (incidenceIdeal A i).map (MvPolynomial.map φ) = incidenceIdeal (A.map φ) i := by
  simp only [incidenceIdeal, Ideal.map_sup, Ideal.map_span, ← Set.range_comp,
    Function.comp_def, map_kernelEquation, Set.image_singleton,
    map_sub, map_one, MvPolynomial.map_X]

theorem incidenceIntersectionIdeal_map
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1))
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    (incidenceIntersectionIdeal A i H J).map (MvPolynomial.map φ) =
      incidenceIntersectionIdeal (A.map φ) i (fun e => (H e).map φ) (J.map φ) := by
  simp only [incidenceIntersectionIdeal, incidenceFlagIdeal, Ideal.map_sup,
    incidenceIdeal_map, Ideal.map_iSup, Ideal.map_span, Set.image_singleton,
    map_polarEquation, Ideal.map_map]
  have hcomp : (MvPolynomial.map (σ := Fin (m+1)) φ).comp C = C.comp φ := by
    apply RingHom.ext
    intro r
    exact MvPolynomial.map_C φ r
  rw [hcomp]

end BaseChange

def coefficientLocalizedIntersectionEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (hA : A.transpose = A)
    (i : Fin (m+1)) (p : Ideal R) [p.IsPrime] (ha : A.adjugate i i ∉ p)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    (Polynomials (Localization.AtPrime p) m ⧸
      (incidenceIntersectionIdeal A i H J).map
        (MvPolynomial.map (algebraMap R (Localization.AtPrime p)))) ≃+*
    (Localization.AtPrime p ⧸
      (polarIntersectionIdeal A H J).map (algebraMap R (Localization.AtPrime p))) := by
  have hu : IsUnit (((A.map (algebraMap R (Localization.AtPrime p))).adjugate) i i) := by
    have hh := (algebraMap R (Localization.AtPrime p)).map_adjugate A
    change IsUnit (((algebraMap R (Localization.AtPrime p)).mapMatrix A).adjugate i i)
    rw [← hh]
    exact IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p)
      ⟨A.adjugate i i, ha⟩
  have hs : (A.map (algebraMap R (Localization.AtPrime p))).transpose =
      A.map (algebraMap R (Localization.AtPrime p)) := by rw [← Matrix.transpose_map, hA]
  exact (Ideal.quotEquivOfEq (incidenceIntersectionIdeal_map
    (algebraMap R (Localization.AtPrime p)) A i H J)).trans
      ((intersectionRingEquiv (A.map (algebraMap R (Localization.AtPrime p))) hs i hu
        (fun e => (H e).map (algebraMap R (Localization.AtPrime p)))
        (J.map (algebraMap R (Localization.AtPrime p)))).trans
          (Ideal.quotEquivOfEq (KernelIncidenceLocalMultiplicity.polarIntersectionIdeal_map
            (algebraMap R (Localization.AtPrime p)) A H J).symm))

attribute [local instance] MvPolynomial.algebraMvPolynomial

def globalIncidenceBaseLocalizationEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (hA : A.transpose = A)
    (i : Fin (m+1)) (p : Ideal R) [p.IsPrime] (ha : A.adjugate i i ∉ p)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    Localization ((p.primeCompl.map (C : R →+* Polynomials R m)).map
      (Ideal.Quotient.mk (incidenceIntersectionIdeal A i H J))) ≃+*
    (Localization.AtPrime p ⧸
      (polarIntersectionIdeal A H J).map (algebraMap R (Localization.AtPrime p))) := by
  let e := KernelIncidenceLocalMultiplicity.quotientLocalizationEquiv
    (U := Polynomials (Localization.AtPrime p) m)
    (p.primeCompl.map (C : R →+* Polynomials R m)) (incidenceIntersectionIdeal A i H J)
  exact e.trans (coefficientLocalizedIntersectionEquiv A hA i p ha H J)

section RationalPoints
variable {Z K : Type*} [Field K]

def pointIncidenceBaseLocalizationEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K)) (hA : A.transpose = A)
    (i : Fin (m+1)) (p : Z → K) (ha : eval p (A.adjugate i i) ≠ 0)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K))
    (hz : polarIntersectionIdeal A H J ≤ IsolatedLocalMultiplicity.pointIdeal p) :
    Localization (((CoordinatePowerRegular.pointIdeal p).primeCompl.map
      (C : MvPolynomial Z K →+* Polynomials (MvPolynomial Z K) m)).map
        (Ideal.Quotient.mk (incidenceIntersectionIdeal A i H J))) ≃+*
      IsolatedLocalMultiplicity.LocalIntersectionRing (polarIntersectionIdeal A H J) p hz :=
  (globalIncidenceBaseLocalizationEquiv A hA i (CoordinatePowerRegular.pointIdeal p) ha H J).trans
    (SingularSpecialFiber.localEquationQuotientEquiv (polarIntersectionIdeal A H J) p hz)

theorem pointIncidenceBaseLocalization_length
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K)) (hA : A.transpose = A)
    (i : Fin (m+1)) (p : Z → K) (ha : eval p (A.adjugate i i) ≠ 0)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K))
    (hz : polarIntersectionIdeal A H J ≤ IsolatedLocalMultiplicity.pointIdeal p) :
    let L := Localization (((CoordinatePowerRegular.pointIdeal p).primeCompl.map
      (C : MvPolynomial Z K →+* Polynomials (MvPolynomial Z K) m)).map
        (Ideal.Quotient.mk (incidenceIntersectionIdeal A i H J)))
    Module.length L L = IsolatedLocalMultiplicity.multiplicity (polarIntersectionIdeal A H J) p hz :=
  ProjectiveCycleLengths.ringEquiv_length (pointIncidenceBaseLocalizationEquiv A hA i p ha H J hz)

/-- Actual local ring comparison at the displayed normalized kernel point.
The incidence point hypothesis is literal vanishing of its equation ideal;
no transversality or reducedness assumption enters this ring isomorphism. -/
def pointIncidenceLocalEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K)) (hA : A.transpose = A) (i : Fin (m+1))
    (p : Z → K) (ha : eval p (A.adjugate i i) ≠ 0)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K))
    (hz : polarIntersectionIdeal A H J ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (q : Fin (m+1) → K)
    (hq : incidenceIntersectionIdeal A i H J ≤
      RingHom.ker (NestedPolynomialLocalPoint.evaluation p q)) :
    NestedPolynomialLocalPoint.LocalRing (incidenceIntersectionIdeal A i H J) p q hq ≃+*
      IsolatedLocalMultiplicity.LocalIntersectionRing (polarIntersectionIdeal A H J) p hz := by
  let e := pointIncidenceBaseLocalizationEquiv A hA i p ha H J hz
  letI : Nontrivial (Localization (NestedPolynomialLocalPoint.baseDenominators
      (incidenceIntersectionIdeal A i H J) p)) := e.symm.injective.nontrivial
  letI : IsLocalRing (Localization (NestedPolynomialLocalPoint.baseDenominators
      (incidenceIntersectionIdeal A i H J) p)) :=
    IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  exact (NestedPolynomialLocalPoint.atPointEquivBaseLocalization
    (incidenceIntersectionIdeal A i H J) p q hq).trans e

/-- Actual isolatedness of the polar root implies actual isolatedness of
the corresponding incidence root, including singular roots. -/
theorem pointIncidenceLocal_artinian
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K)) (hA : A.transpose = A) (i : Fin (m+1))
    (p : Z → K) (ha : eval p (A.adjugate i i) ≠ 0)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K))
    (hz : polarIntersectionIdeal A H J ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (q : Fin (m+1) → K)
    (hq : incidenceIntersectionIdeal A i H J ≤
      RingHom.ker (NestedPolynomialLocalPoint.evaluation p q))
    [IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing
      (polarIntersectionIdeal A H J) p hz)] :
    IsArtinianRing (NestedPolynomialLocalPoint.LocalRing
      (incidenceIntersectionIdeal A i H J) p q hq) :=
  (pointIncidenceLocalEquiv A hA i p ha H J hz q hq).symm.isArtinianRing

/-- The singular isolated-zero multiplicity is preserved by the actual
kernel-incidence graph construction. -/
theorem pointIncidenceLocal_length
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K)) (hA : A.transpose = A) (i : Fin (m+1))
    (p : Z → K) (ha : eval p (A.adjugate i i) ≠ 0)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K))
    (hz : polarIntersectionIdeal A H J ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (q : Fin (m+1) → K)
    (hq : incidenceIntersectionIdeal A i H J ≤
      RingHom.ker (NestedPolynomialLocalPoint.evaluation p q)) :
    let L := NestedPolynomialLocalPoint.LocalRing (incidenceIntersectionIdeal A i H J) p q hq
    Module.length L L = IsolatedLocalMultiplicity.multiplicity (polarIntersectionIdeal A H J) p hz :=
  ProjectiveCycleLengths.ringEquiv_length (pointIncidenceLocalEquiv A hA i p ha H J hz q hq)


end RationalPoints
end Sheshadri.SymmetricKernelIncidenceLocalMultiplicity
