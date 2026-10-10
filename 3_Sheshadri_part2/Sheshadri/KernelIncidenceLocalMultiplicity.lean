/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.KernelReducedIncidenceAlgebra
import Sheshadri.ProjectiveCycleLengths
import Sheshadri.SingularSpecialFiber
import Mathlib.RingTheory.MvPolynomial.Localization
import Sheshadri.NestedPolynomialLocalPoint

/-!
# Kernel incidence and actual polar intersection rings

The full incidence quotient, including arbitrary base equations and polar
flags, is identified with the literal polar equation quotient. After localizing
the coefficient ring at a smooth determinant point the required unit cofactor
is derived from its nonvanishing residue.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 3
namespace Sheshadri.KernelIncidenceLocalMultiplicity

open Matrix MvPolynomial KernelIncidenceAlgebra

variable {R : Type*} [CommRing R] {m : ℕ} {E : Type*}

def polarFlagIdeal
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) : Ideal R :=
  J ⊔ ⨆ e, Ideal.span {Matrix.trace (A.adjugate * H e)}

def polarIntersectionIdeal
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) : Ideal R :=
  Ideal.span {A.det} ⊔ polarFlagIdeal A H J

def incidenceFlagIdeal
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    Ideal (Polynomials R m) :=
  J.map C ⊔ ⨆ e, Ideal.span {polarEquation (H e)}

def incidenceIntersectionIdeal
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    Ideal (Polynomials R m) := incidenceIdeal A i j ⊔ incidenceFlagIdeal H J

def reducedIncidenceIntersectionIdeal
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (Λ : Matrix (Fin m) (Fin (m+1)) R) (i j : Fin (m+1))
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    Ideal (Polynomials R m) :=
  KernelReducedIncidenceAlgebra.reducedIncidenceIdeal A Λ i j ⊔ incidenceFlagIdeal H J

/-- The nested quotient on the incidence side is the literal combined
incidence equation quotient. -/
def incidenceDoubleQuotientEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    (IncidenceRing A i j ⧸
      (J.map (algebraMap R (IncidenceRing A i j)) ⊔
        ⨆ e, Ideal.span {Ideal.Quotient.mk (incidenceIdeal A i j) (polarEquation (H e))}))
      ≃+* Polynomials R m ⧸ incidenceIntersectionIdeal A i j H J := by
  have he : (incidenceFlagIdeal H J).map (Ideal.Quotient.mk (incidenceIdeal A i j)) =
      (J.map (algebraMap R (IncidenceRing A i j)) ⊔
        ⨆ e, Ideal.span {Ideal.Quotient.mk (incidenceIdeal A i j) (polarEquation (H e))}) := by
    simp only [incidenceFlagIdeal, Ideal.map_sup, Ideal.map_iSup, Ideal.map_span,
      Set.image_singleton, Ideal.map_map]
    rfl
  exact (Ideal.quotEquivOfEq he.symm).trans
    (DoubleQuot.quotQuotEquivQuotSup (incidenceIdeal A i j) (incidenceFlagIdeal H J))

/-- The nested determinant cut quotient is the literal combined polar
intersection quotient. -/
def determinantDoubleQuotientEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    (DeterminantRing A ⧸
      (J.map (algebraMap R (DeterminantRing A)) ⊔
        ⨆ e, Ideal.span {algebraMap R (DeterminantRing A) (Matrix.trace (A.adjugate * H e))}))
      ≃+* R ⧸ polarIntersectionIdeal A H J := by
  have he : (polarFlagIdeal A H J).map (Ideal.Quotient.mk (Ideal.span {A.det})) =
      (J.map (algebraMap R (DeterminantRing A)) ⊔
        ⨆ e, Ideal.span {algebraMap R (DeterminantRing A) (Matrix.trace (A.adjugate * H e))}) := by
    simp only [polarFlagIdeal, Ideal.map_sup, Ideal.map_iSup, Ideal.map_span,
      Set.image_singleton]
    rfl
  exact (Ideal.quotEquivOfEq he.symm).trans
    (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {A.det}) (polarFlagIdeal A H J))

/-- Actual incidence-to-polar quotient isomorphism, retaining every local
nilpotent multiplicity. -/
def intersectionRingEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (ha : IsUnit (A.adjugate i j))
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    (Polynomials R m ⧸ incidenceIntersectionIdeal A i j H J) ≃+*
      R ⧸ polarIntersectionIdeal A H J :=
  (incidenceDoubleQuotientEquiv A i j H J).symm.trans
    ((cutIncidenceEquivDeterminant A i j ha H J).toRingEquiv.trans
      (determinantDoubleQuotientEquiv A H J))

/-- Local rings at corresponding actual primes are canonically isomorphic. -/
def localIntersectionRingEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (ha : IsUnit (A.adjugate i j))
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R)
    (p : Ideal (R ⧸ polarIntersectionIdeal A H J)) [p.IsPrime] :
    Localization.AtPrime (p.comap (intersectionRingEquiv A i j ha H J).toRingHom) ≃+*
      Localization.AtPrime p :=
  ProjectiveCycleLengths.localRingEquivOfRingEquiv (intersectionRingEquiv A i j ha H J) p

/-- Consequently the actual local intersection lengths agree. -/
theorem localIntersection_length_eq
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (ha : IsUnit (A.adjugate i j))
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R)
    (p : Ideal (R ⧸ polarIntersectionIdeal A H J)) [p.IsPrime] :
    Module.length
      (Localization.AtPrime (p.comap (intersectionRingEquiv A i j ha H J).toRingHom))
      (Localization.AtPrime (p.comap (intersectionRingEquiv A i j ha H J).toRingHom)) =
        Module.length (Localization.AtPrime p) (Localization.AtPrime p) :=
  ProjectiveCycleLengths.ringEquiv_length (localIntersectionRingEquiv A i j ha H J p)


section BaseChange
variable {S : Type*} [CommRing S] (φ : R →+* S)

@[simp] theorem map_leftEquation
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (l : Fin (m+1)) :
    MvPolynomial.map φ (leftEquation A l) = leftEquation (A.map φ) l := by
  simp [leftEquation, leftVariable]

@[simp] theorem map_rightEquation
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (l : Fin (m+1)) :
    MvPolynomial.map φ (rightEquation A l) = rightEquation (A.map φ) l := by
  simp [rightEquation, rightVariable]

@[simp] theorem map_polarEquation
    (H : Matrix (Fin (m+1)) (Fin (m+1)) R) :
    MvPolynomial.map φ (polarEquation H) = polarEquation (H.map φ) := by
  simp [polarEquation, leftVariable, rightVariable]

/-- Coefficient extension sends the literal incidence ideal to exactly the
incidence ideal of the coefficient-extended matrix. -/
theorem incidenceIdeal_map
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1)) :
    (incidenceIdeal A i j).map (MvPolynomial.map φ) = incidenceIdeal (A.map φ) i j := by
  simp only [incidenceIdeal, Ideal.map_sup, Ideal.map_span, ← Set.range_comp,
    Function.comp_def, map_leftEquation, map_rightEquation, Set.image_singleton,
    map_sub, map_one, leftVariable, rightVariable, MvPolynomial.map_X]

/-- The trace polar commutes with every coefficient extension. -/
theorem map_trace_polar
    (A H : Matrix (Fin (m+1)) (Fin (m+1)) R) :
    φ (Matrix.trace (A.adjugate * H)) = Matrix.trace ((A.map φ).adjugate * H.map φ) := by
  have hm := φ.map_adjugate A
  change φ.mapMatrix A.adjugate = (A.map φ).adjugate at hm
  rw [← hm]
  simp only [RingHom.mapMatrix_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.map_apply, map_sum, map_mul]

theorem polarIntersectionIdeal_map
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    (polarIntersectionIdeal A H J).map φ =
      polarIntersectionIdeal (A.map φ) (fun e => (H e).map φ) (J.map φ) := by
  simp only [polarIntersectionIdeal, polarFlagIdeal, Ideal.map_sup, Ideal.map_iSup,
    Ideal.map_span, Set.image_singleton, map_trace_polar]
  congr 2
  exact congrArg (fun x => ({x} : Set S)) (φ.map_det A)

theorem incidenceIntersectionIdeal_map
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    (incidenceIntersectionIdeal A i j H J).map (MvPolynomial.map φ) =
      incidenceIntersectionIdeal (A.map φ) i j (fun e => (H e).map φ) (J.map φ) := by
  simp only [incidenceIntersectionIdeal, incidenceFlagIdeal, Ideal.map_sup,
    incidenceIdeal_map, Ideal.map_iSup, Ideal.map_span, Set.image_singleton,
    map_polarEquation, Ideal.map_map]
  have hcomp : (MvPolynomial.map (σ := Variables m) φ).comp C = C.comp φ := by
    apply RingHom.ext
    intro r
    exact MvPolynomial.map_C φ r
  rw [hcomp]

end BaseChange

/-- Actual coefficient localization at any prime with a nonvanishing
cofactor supplies the unit needed for the graph isomorphism. -/
def coefficientLocalizedIntersectionEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (p : Ideal R) [p.IsPrime] (ha : A.adjugate i j ∉ p)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    (Polynomials (Localization.AtPrime p) m ⧸
      (incidenceIntersectionIdeal A i j H J).map
        (MvPolynomial.map (algebraMap R (Localization.AtPrime p)))) ≃+*
    (Localization.AtPrime p ⧸
      (polarIntersectionIdeal A H J).map (algebraMap R (Localization.AtPrime p))) := by
  have hu : IsUnit (((A.map (algebraMap R (Localization.AtPrime p))).adjugate) i j) := by
    have hh := (algebraMap R (Localization.AtPrime p)).map_adjugate A
    change IsUnit (((algebraMap R (Localization.AtPrime p)).mapMatrix A).adjugate i j)
    rw [← hh]
    exact IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p)
      ⟨A.adjugate i j, ha⟩
  exact (Ideal.quotEquivOfEq (incidenceIntersectionIdeal_map
    (algebraMap R (Localization.AtPrime p)) A i j H J)).trans
      ((intersectionRingEquiv (A.map (algebraMap R (Localization.AtPrime p))) i j hu
        (fun e => (H e).map (algebraMap R (Localization.AtPrime p)))
        (J.map (algebraMap R (Localization.AtPrime p)))).trans
          (Ideal.quotEquivOfEq (polarIntersectionIdeal_map
            (algebraMap R (Localization.AtPrime p)) A H J).symm))


section QuotientLocalization
variable {T U : Type*} [CommRing T] [CommRing U] [Algebra T U]
    (M : Submonoid T) [IsLocalization M U]

/-- Quotienting an actual localization gives the localization of the actual
quotient at the displayed image submonoid. -/
def quotientLocalizationEquiv (I : Ideal T) :
    Localization (M.map (Ideal.Quotient.mk I)) ≃+*
      U ⧸ I.map (algebraMap T U) := by
  letI : Algebra (T ⧸ I) (U ⧸ I.map (algebraMap T U)) :=
    Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map)
  letI : IsLocalization (M.map (Ideal.Quotient.mk I)) (U ⧸ I.map (algebraMap T U)) := by
    apply IsLocalization.of_surjective M U
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk (I.map (algebraMap T U))) Ideal.Quotient.mk_surjective
    · apply RingHom.ext
      intro t
      rfl
    · rw [Ideal.mk_ker, Ideal.mk_ker]
  exact (IsLocalization.algEquiv (M.map (Ideal.Quotient.mk I)) _ _).toRingEquiv

end QuotientLocalization

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The original global incidence equation quotient, localized only by
coefficient polynomials away from the selected base prime, is the actual
base polar local equation quotient. -/
def globalIncidenceBaseLocalizationEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (p : Ideal R) [p.IsPrime] (ha : A.adjugate i j ∉ p)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    Localization ((p.primeCompl.map (C : R →+* Polynomials R m)).map
      (Ideal.Quotient.mk (incidenceIntersectionIdeal A i j H J))) ≃+*
    (Localization.AtPrime p ⧸
      (polarIntersectionIdeal A H J).map (algebraMap R (Localization.AtPrime p))) := by
  let e := quotientLocalizationEquiv (U := Polynomials (Localization.AtPrime p) m)
    (p.primeCompl.map (C : R →+* Polynomials R m)) (incidenceIntersectionIdeal A i j H J)
  exact e.trans (coefficientLocalizedIntersectionEquiv A i j p ha H J)

section RationalPoints
variable {Z K : Type*} [Field K]

/-- The literal block-determinant polynomial evaluates to the matrix
consisting of the left kernel vector and the chosen reduction rows. -/
theorem evaluation_augmentedPolynomialMatrix_det
    (Λ : Matrix (Fin m) (Fin (m+1)) (MvPolynomial Z K))
    (p : Z → K) (q : Variables m → K) :
    NestedPolynomialLocalPoint.evaluation p q
      (KernelReducedIncidenceAlgebra.augmentedPolynomialMatrix Λ).det =
    (KernelReducedIncidenceAlgebra.augmentedMatrix (fun k => q (Sum.inl k))
      (Λ.map (eval p))).det := by
  rw [RingHom.map_det]
  congr 1
  ext l k
  refine Fin.cases ?_ (fun l => ?_) l
  · simp [KernelReducedIncidenceAlgebra.augmentedPolynomialMatrix,
      KernelReducedIncidenceAlgebra.augmentedMatrix, NestedPolynomialLocalPoint.evaluation,
      leftVariable]
  · simp [KernelReducedIncidenceAlgebra.augmentedPolynomialMatrix,
      KernelReducedIncidenceAlgebra.augmentedMatrix, NestedPolynomialLocalPoint.evaluation]

/-- At an actual affine point, coefficient-localized incidence is the actual
polar local intersection algebra, not an abstract ring with matching length. -/
def pointIncidenceBaseLocalizationEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K)) (i j : Fin (m+1))
    (p : Z → K) (ha : eval p (A.adjugate i j) ≠ 0)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K))
    (hz : polarIntersectionIdeal A H J ≤ IsolatedLocalMultiplicity.pointIdeal p) :
    Localization (((CoordinatePowerRegular.pointIdeal p).primeCompl.map
      (C : MvPolynomial Z K →+* Polynomials (MvPolynomial Z K) m)).map
        (Ideal.Quotient.mk (incidenceIntersectionIdeal A i j H J))) ≃+*
      IsolatedLocalMultiplicity.LocalIntersectionRing (polarIntersectionIdeal A H J) p hz :=
  (globalIncidenceBaseLocalizationEquiv A i j (CoordinatePowerRegular.pointIdeal p) ha H J).trans
    (SingularSpecialFiber.localEquationQuotientEquiv (polarIntersectionIdeal A H J) p hz)

/-- Isolatedness transfers from the actual polar local algebra to the actual
coefficient-localized incidence algebra. -/
theorem pointIncidenceBaseLocalization_artinian
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K)) (i j : Fin (m+1))
    (p : Z → K) (ha : eval p (A.adjugate i j) ≠ 0)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K))
    (hz : polarIntersectionIdeal A H J ≤ IsolatedLocalMultiplicity.pointIdeal p)
    [IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing
      (polarIntersectionIdeal A H J) p hz)] :
    IsArtinianRing
      (Localization (((CoordinatePowerRegular.pointIdeal p).primeCompl.map
        (C : MvPolynomial Z K →+* Polynomials (MvPolynomial Z K) m)).map
          (Ideal.Quotient.mk (incidenceIntersectionIdeal A i j H J)))) :=
  (pointIncidenceBaseLocalizationEquiv A i j p ha H J hz).symm.isArtinianRing

/-- The full nilpotent incidence length is the actual polar multiplicity. -/
theorem pointIncidenceBaseLocalization_length
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K)) (i j : Fin (m+1))
    (p : Z → K) (ha : eval p (A.adjugate i j) ≠ 0)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K))
    (hz : polarIntersectionIdeal A H J ≤ IsolatedLocalMultiplicity.pointIdeal p) :
    let L := Localization (((CoordinatePowerRegular.pointIdeal p).primeCompl.map
      (C : MvPolynomial Z K →+* Polynomials (MvPolynomial Z K) m)).map
        (Ideal.Quotient.mk (incidenceIntersectionIdeal A i j H J)))
    Module.length L L = IsolatedLocalMultiplicity.multiplicity (polarIntersectionIdeal A H J) p hz :=
  ProjectiveCycleLengths.ringEquiv_length (pointIncidenceBaseLocalizationEquiv A i j p ha H J hz)

/-- Actual local ring comparison at the displayed normalized kernel point.
The incidence point hypothesis is literal vanishing of its equation ideal;
no transversality or reducedness assumption enters this ring isomorphism. -/
def pointIncidenceLocalEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K)) (i j : Fin (m+1))
    (p : Z → K) (ha : eval p (A.adjugate i j) ≠ 0)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K))
    (hz : polarIntersectionIdeal A H J ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (q : Variables m → K)
    (hq : incidenceIntersectionIdeal A i j H J ≤
      RingHom.ker (NestedPolynomialLocalPoint.evaluation p q)) :
    NestedPolynomialLocalPoint.LocalRing (incidenceIntersectionIdeal A i j H J) p q hq ≃+*
      IsolatedLocalMultiplicity.LocalIntersectionRing (polarIntersectionIdeal A H J) p hz := by
  let e := pointIncidenceBaseLocalizationEquiv A i j p ha H J hz
  letI : Nontrivial (Localization (NestedPolynomialLocalPoint.baseDenominators
      (incidenceIntersectionIdeal A i j H J) p)) := e.symm.injective.nontrivial
  letI : IsLocalRing (Localization (NestedPolynomialLocalPoint.baseDenominators
      (incidenceIntersectionIdeal A i j H J) p)) :=
    IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective
  exact (NestedPolynomialLocalPoint.atPointEquivBaseLocalization
    (incidenceIntersectionIdeal A i j H J) p q hq).trans e

/-- Actual isolatedness of the polar root implies actual isolatedness of
the corresponding incidence root, including singular roots. -/
theorem pointIncidenceLocal_artinian
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K)) (i j : Fin (m+1))
    (p : Z → K) (ha : eval p (A.adjugate i j) ≠ 0)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K))
    (hz : polarIntersectionIdeal A H J ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (q : Variables m → K)
    (hq : incidenceIntersectionIdeal A i j H J ≤
      RingHom.ker (NestedPolynomialLocalPoint.evaluation p q))
    [IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing
      (polarIntersectionIdeal A H J) p hz)] :
    IsArtinianRing (NestedPolynomialLocalPoint.LocalRing
      (incidenceIntersectionIdeal A i j H J) p q hq) :=
  (pointIncidenceLocalEquiv A i j p ha H J hz q hq).symm.isArtinianRing

/-- The singular isolated-zero multiplicity is preserved by the actual
kernel-incidence graph construction. -/
theorem pointIncidenceLocal_length
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K)) (i j : Fin (m+1))
    (p : Z → K) (ha : eval p (A.adjugate i j) ≠ 0)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K))
    (hz : polarIntersectionIdeal A H J ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (q : Variables m → K)
    (hq : incidenceIntersectionIdeal A i j H J ≤
      RingHom.ker (NestedPolynomialLocalPoint.evaluation p q)) :
    let L := NestedPolynomialLocalPoint.LocalRing (incidenceIntersectionIdeal A i j H J) p q hq
    Module.length L L = IsolatedLocalMultiplicity.multiplicity (polarIntersectionIdeal A H J) p hz :=
  ProjectiveCycleLengths.ringEquiv_length (pointIncidenceLocalEquiv A i j p ha H J hz q hq)

/-- Literal reduced incidence equations imply all full incidence equations
at a point where the displayed augmented matrix is invertible. -/
theorem full_root_of_reduced_root
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (Λ : Matrix (Fin m) (Fin (m+1)) (MvPolynomial Z K)) (i j : Fin (m+1))
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K)) (p : Z → K) (q : Variables m → K)
    (hq : reducedIncidenceIntersectionIdeal A Λ i j H J ≤
      RingHom.ker (NestedPolynomialLocalPoint.evaluation p q))
    (hΓ : NestedPolynomialLocalPoint.evaluation p q
      (KernelReducedIncidenceAlgebra.augmentedPolynomialMatrix Λ).det ≠ 0) :
    incidenceIntersectionIdeal A i j H J ≤
      RingHom.ker (NestedPolynomialLocalPoint.evaluation p q) := by
  let φ := NestedPolynomialLocalPoint.evaluation p q
  have he := KernelReducedIncidenceAlgebra.mapped_cutIdeals_eq A Λ i j φ
    (isUnit_iff_ne_zero.mpr hΓ) (incidenceFlagIdeal H J)
  have hr : (reducedIncidenceIntersectionIdeal A Λ i j H J).map φ ≤ ⊥ :=
    Ideal.map_le_iff_le_comap.mpr hq
  have hf : (incidenceIntersectionIdeal A i j H J).map φ ≤ ⊥ := by
    rw [incidenceIntersectionIdeal, he]
    exact hr
  exact Ideal.map_le_iff_le_comap.mp hf

/-- The actual reduced and full incidence local rings agree at the displayed
point. The only additional condition is nonvanishing of the literal block
determinant there. -/
def pointReducedEquivFull
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (Λ : Matrix (Fin m) (Fin (m+1)) (MvPolynomial Z K)) (i j : Fin (m+1))
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K)) (p : Z → K) (q : Variables m → K)
    (hq : reducedIncidenceIntersectionIdeal A Λ i j H J ≤
      RingHom.ker (NestedPolynomialLocalPoint.evaluation p q))
    (hΓ : NestedPolynomialLocalPoint.evaluation p q
      (KernelReducedIncidenceAlgebra.augmentedPolynomialMatrix Λ).det ≠ 0) :
    NestedPolynomialLocalPoint.LocalRing (reducedIncidenceIntersectionIdeal A Λ i j H J) p q hq ≃+*
      NestedPolynomialLocalPoint.LocalRing (incidenceIntersectionIdeal A i j H J) p q
        (full_root_of_reduced_root A Λ i j H J p q hq hΓ) := by
  letI : (RingHom.ker (NestedPolynomialLocalPoint.evaluation p q)).IsPrime := RingHom.ker_isPrime _
  exact NestedPolynomialLocalPoint.localEquivOfLocalizedIdealsEq _ _ p q hq
    (full_root_of_reduced_root A Λ i j H J p q hq hΓ)
    (KernelReducedIncidenceAlgebra.atPrime_cutIdeals_eq A Λ i j
      (RingHom.ker (NestedPolynomialLocalPoint.evaluation p q)) hΓ (incidenceFlagIdeal H J)).symm

/-- The reduced incidence local ring is the actual polar local intersection
ring, with all nilpotents preserved. -/
def pointReducedIncidenceLocalEquiv
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (Λ : Matrix (Fin m) (Fin (m+1)) (MvPolynomial Z K)) (i j : Fin (m+1))
    (p : Z → K) (ha : eval p (A.adjugate i j) ≠ 0)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K))
    (hz : polarIntersectionIdeal A H J ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (q : Variables m → K)
    (hq : reducedIncidenceIntersectionIdeal A Λ i j H J ≤
      RingHom.ker (NestedPolynomialLocalPoint.evaluation p q))
    (hΓ : NestedPolynomialLocalPoint.evaluation p q
      (KernelReducedIncidenceAlgebra.augmentedPolynomialMatrix Λ).det ≠ 0) :
    NestedPolynomialLocalPoint.LocalRing (reducedIncidenceIntersectionIdeal A Λ i j H J) p q hq ≃+*
      IsolatedLocalMultiplicity.LocalIntersectionRing (polarIntersectionIdeal A H J) p hz :=
  (pointReducedEquivFull A Λ i j H J p q hq hΓ).trans
    (pointIncidenceLocalEquiv A i j p ha H J hz q
      (full_root_of_reduced_root A Λ i j H J p q hq hΓ))

/-- Singular isolatedness transfers to the reduced incidence system. -/
theorem pointReducedIncidenceLocal_artinian
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (Λ : Matrix (Fin m) (Fin (m+1)) (MvPolynomial Z K)) (i j : Fin (m+1))
    (p : Z → K) (ha : eval p (A.adjugate i j) ≠ 0)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K))
    (hz : polarIntersectionIdeal A H J ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (q : Variables m → K)
    (hq : reducedIncidenceIntersectionIdeal A Λ i j H J ≤
      RingHom.ker (NestedPolynomialLocalPoint.evaluation p q))
    (hΓ : NestedPolynomialLocalPoint.evaluation p q
      (KernelReducedIncidenceAlgebra.augmentedPolynomialMatrix Λ).det ≠ 0)
    [IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing
      (polarIntersectionIdeal A H J) p hz)] :
    IsArtinianRing (NestedPolynomialLocalPoint.LocalRing
      (reducedIncidenceIntersectionIdeal A Λ i j H J) p q hq) :=
  (pointReducedIncidenceLocalEquiv A Λ i j p ha H J hz q hq hΓ).symm.isArtinianRing

/-- The reduced incidence system has exactly the actual singular polar
multiplicity at the corresponding isolated point. -/
theorem pointReducedIncidenceLocal_length
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (Λ : Matrix (Fin m) (Fin (m+1)) (MvPolynomial Z K)) (i j : Fin (m+1))
    (p : Z → K) (ha : eval p (A.adjugate i j) ≠ 0)
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial Z K))
    (J : Ideal (MvPolynomial Z K))
    (hz : polarIntersectionIdeal A H J ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (q : Variables m → K)
    (hq : reducedIncidenceIntersectionIdeal A Λ i j H J ≤
      RingHom.ker (NestedPolynomialLocalPoint.evaluation p q))
    (hΓ : NestedPolynomialLocalPoint.evaluation p q
      (KernelReducedIncidenceAlgebra.augmentedPolynomialMatrix Λ).det ≠ 0) :
    let L := NestedPolynomialLocalPoint.LocalRing
      (reducedIncidenceIntersectionIdeal A Λ i j H J) p q hq
    Module.length L L = IsolatedLocalMultiplicity.multiplicity (polarIntersectionIdeal A H J) p hz :=
  ProjectiveCycleLengths.ringEquiv_length
    (pointReducedIncidenceLocalEquiv A Λ i j p ha H J hz q hq hΓ)

end RationalPoints

end Sheshadri.KernelIncidenceLocalMultiplicity
