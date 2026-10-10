/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.IsolatedCompleteIntersection
import Sheshadri.IsolatedLocalMultiplicity
import Sheshadri.BezoutRootPersistence
import Mathlib.RingTheory.Localization.Algebra

/-!
# Actual local special-fibre rings

Localization commutes with the displayed quotient maps, including their
kernel ideals. This identifies the local special fibre of a polynomial
deformation with the original polynomial local ring, and identifies ambient
local equation quotients with the local intersection algebras used to define
multiplicity.
-/

noncomputable section
namespace Sheshadri.SingularSpecialFiber
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 3

section General
variable {R S : Type*} [CommRing R] [CommRing S]
    (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (f : R →+* S) (hf : Function.Surjective f) (hPQ : P = Q.comap f)

include hf hPQ

theorem map_primeCompl_eq : P.primeCompl.map f = Q.primeCompl := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change f x ∉ Q
    intro h
    apply hx
    rw [hPQ]
    exact h
  · intro hy
    obtain ⟨x,rfl⟩ := hf y
    refine ⟨x,?_,rfl⟩
    change x ∉ P
    rw [hPQ]
    exact hy

theorem localRingHom_surjective :
    Function.Surjective (Localization.localRingHom P Q f hPQ) := by
  have hm := map_primeCompl_eq P Q f hf hPQ
  letI : IsLocalization (P.primeCompl.map f) (Localization.AtPrime Q) := by
    rw [hm]
    infer_instance
  have h := IsLocalization.map_surjective_of_surjective P.primeCompl
    (Localization.AtPrime P) (Localization.AtPrime Q) hf
  have he : Localization.localRingHom P Q f hPQ =
      IsLocalization.map (Localization.AtPrime Q) f P.primeCompl.le_comap_map := by
    apply Localization.localRingHom_unique
    intro r
    exact IsLocalization.map_eq _ _
  rwa [he]

theorem localRingHom_ker :
    RingHom.ker (Localization.localRingHom P Q f hPQ) =
      (RingHom.ker f).map (algebraMap R (Localization.AtPrime P)) := by
  exact IsLocalization.ker_map (S := Localization.AtPrime P)
    (Localization.AtPrime Q) f (map_primeCompl_eq P Q f hf hPQ)

/-- Localizing a surjective map and quotienting by its actual extended
kernel produces exactly the target local ring. -/
def localizationQuotientEquiv :
    ((Localization.AtPrime P) ⧸
      (RingHom.ker f).map (algebraMap R (Localization.AtPrime P))) ≃+*
        Localization.AtPrime Q :=
  (Ideal.quotEquivOfEq (localRingHom_ker P Q f hf hPQ).symm).trans
    (RingHom.quotientKerEquivOfSurjective (localRingHom_surjective P Q f hf hPQ))

@[simp] theorem localizationQuotientEquiv_mk (r : R) :
    localizationQuotientEquiv P Q f hf hPQ
      (Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime P) r)) =
      algebraMap S (Localization.AtPrime Q) (f r) := by
  change Localization.localRingHom P Q f hPQ (algebraMap R (Localization.AtPrime P) r) = _
  exact Localization.localRingHom_to_map P Q f hPQ r

end General

section EquationLocalization
open MvPolynomial CoordinatePowerRegular
variable {Z K : Type*} [Field K]

/-- The ambient polynomial local ring modulo the localized equation ideal
is the actual local intersection algebra, with its full scheme structure. -/
def localEquationQuotientEquiv (I : Ideal (MvPolynomial Z K)) (p : Z → K)
    (hI : I ≤ IsolatedLocalMultiplicity.pointIdeal p) :
    (PointLocalRing p ⧸ I.map (algebraMap (MvPolynomial Z K) (PointLocalRing p))) ≃+*
      IsolatedLocalMultiplicity.LocalIntersectionRing I p hI := by
  let Q := IsolatedLocalMultiplicity.quotientPointIdeal I p hI
  have he : pointIdeal p = Q.comap (Ideal.Quotient.mk I) := by
    ext f
    rfl
  have hk : RingHom.ker (Ideal.Quotient.mk I) = I := Ideal.mk_ker
  exact (Ideal.quotEquivOfEq (congrArg (Ideal.map (algebraMap _ (PointLocalRing p))) hk).symm).trans
    (localizationQuotientEquiv (pointIdeal p) Q (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective he)

@[simp] theorem localEquationQuotientEquiv_mk
    (I : Ideal (MvPolynomial Z K)) (p : Z → K)
    (hI : I ≤ IsolatedLocalMultiplicity.pointIdeal p) (f : MvPolynomial Z K) :
    localEquationQuotientEquiv I p hI
      (Ideal.Quotient.mk _ (algebraMap _ (PointLocalRing p) f)) =
      IsolatedLocalMultiplicity.localPolynomialMap I p hI f := by
  change Localization.localRingHom (pointIdeal p)
    (IsolatedLocalMultiplicity.quotientPointIdeal I p hI) (Ideal.Quotient.mk I)
    (by ext x; rfl) (algebraMap _ (PointLocalRing p) f) = _
  exact Localization.localRingHom_to_map _ _ _ _ f

/-- Artinian isolatedness stated using the actual intersection algebra
supplies exactly the isolatedness instance needed by the local complete
intersection theorem. -/
theorem local_equation_quotient_artinian
    (I : Ideal (MvPolynomial Z K)) (p : Z → K)
    (hI : I ≤ IsolatedLocalMultiplicity.pointIdeal p)
    [IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing I p hI)] :
    IsArtinianRing (PointLocalRing p ⧸
      I.map (algebraMap (MvPolynomial Z K) (PointLocalRing p))) :=
  (localEquationQuotientEquiv I p hI).symm.isArtinianRing

end EquationLocalization
section Specialization
open MvPolynomial CoordinatePowerRegular
variable {Z K : Type*} [Field K]

/-- Literal specialization of all coefficients at parameter zero. -/
def evalZero : MvPolynomial Z (Polynomial K) →+* MvPolynomial Z K :=
  MvPolynomial.map (Polynomial.evalRingHom 0)

theorem evalZero_surjective : Function.Surjective (evalZero (Z := Z) (K := K)) :=
  MvPolynomial.map_surjective _ (fun x => ⟨Polynomial.C x, by simp⟩)

@[simp] theorem evalZero_C (q : Polynomial K) :
    evalZero (Z := Z) (MvPolynomial.C q) = MvPolynomial.C (q.eval 0) := by
  simp [evalZero]

@[simp] theorem evalZero_X (i : Z) :
    evalZero (K := K) (MvPolynomial.X i) = MvPolynomial.X i := by
  simp [evalZero]

theorem evalZero_ker : RingHom.ker (evalZero (Z := Z) (K := K)) =
    Ideal.span {MvPolynomial.C Polynomial.X} := by
  ext F
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact (MvPolynomial.C_dvd_iff_map_hom_eq_zero (Polynomial.evalRingHom 0)
    Polynomial.X (fun q => by simp [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]) F).symm

/-- The actual maximal ideal of the special total-space point `(0,p)`. -/
def totalPointIdeal (p : Z → K) : Ideal (MvPolynomial Z (Polynomial K)) :=
  (pointIdeal p).comap evalZero

instance totalPointIdeal_isPrime (p : Z → K) : (totalPointIdeal p).IsPrime :=
  Ideal.comap_isPrime _ _

abbrev TotalLocalRing (p : Z → K) := Localization.AtPrime (totalPointIdeal p)

/-- The parameter in the actual total-space local ring. -/
def localParameter (p : Z → K) : TotalLocalRing p :=
  algebraMap (MvPolynomial Z (Polynomial K)) (TotalLocalRing p) (C Polynomial.X)

theorem evalZero_ker_map (p : Z → K) :
    (RingHom.ker (evalZero (Z := Z) (K := K))).map
      (algebraMap _ (TotalLocalRing p)) = Ideal.span {localParameter p} := by
  rw [evalZero_ker, Ideal.map_span]
  simp only [Set.image_singleton, localParameter]

/-- The actual localized special fibre is the original polynomial local ring. -/
def specialFiberEquiv (p : Z → K) :
    (TotalLocalRing p ⧸ Ideal.span {localParameter p}) ≃+* PointLocalRing p :=
  (Ideal.quotEquivOfEq (evalZero_ker_map p).symm).trans
    (localizationQuotientEquiv (totalPointIdeal p) (pointIdeal p) evalZero
      evalZero_surjective rfl)

@[simp] theorem specialFiberEquiv_mk (p : Z → K) (F : MvPolynomial Z (Polynomial K)) :
    specialFiberEquiv p
      (Ideal.Quotient.mk _ (algebraMap _ (TotalLocalRing p) F)) =
      algebraMap _ (PointLocalRing p) (evalZero F) := by
  change Localization.localRingHom (totalPointIdeal p) (pointIdeal p)
    evalZero rfl (algebraMap _ (TotalLocalRing p) F) = _
  exact Localization.localRingHom_to_map _ _ _ _ F

end Specialization
end Sheshadri.SingularSpecialFiber
