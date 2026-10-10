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
import Sheshadri.LocalLengthDimension
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Actual local intersection algebras and finite fat-point truncations

The point ideal is the kernel of literal polynomial evaluation. The local
intersection algebra is the localization of the actual equation quotient at
that point. Nilpotents and scheme-theoretic intersection multiplicities are
retained throughout.
-/

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section
namespace Sheshadri.IsolatedLocalMultiplicity

open MvPolynomial

variable {σ K : Type*} [Field K]

/-- The actual maximal ideal of an affine rational point. -/
def pointIdeal (p : σ → K) : Ideal (MvPolynomial σ K) := RingHom.ker (eval p)

@[simp] theorem mem_pointIdeal (p : σ → K) (f : MvPolynomial σ K) :
    f ∈ pointIdeal p ↔ eval p f = 0 := Iff.rfl

instance pointIdeal_isMaximal (p : σ → K) : (pointIdeal p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (eval p) (fun x => ⟨C x, by simp⟩)

/-- Evaluation maximal ideals distinguish actual affine points. -/
theorem pointIdeal_injective : Function.Injective (pointIdeal (σ := σ) (K := K)) := by
  intro p q hpq
  funext i
  have h : X i - C (p i) ∈ pointIdeal q := by rw [← hpq]; simp
  have hz : q i - p i = 0 := by simpa using h
  exact (sub_eq_zero.mp hz).symm

/-- The actual equations, together with a power of the point maximal ideal. -/
def fatPointIdeal (I : Ideal (MvPolynomial σ K)) (p : σ → K) (N : ℕ) :
    Ideal (MvPolynomial σ K) := I ⊔ pointIdeal p ^ N

/-- Powers of distinct point ideals, with any additional equations, remain
comaximal. This establishes the actual Chinese remainder hypothesis. -/
theorem fatPointIdeal_isCoprime (I J : Ideal (MvPolynomial σ K))
    (p q : σ → K) (hpq : p ≠ q) (N M : ℕ) :
    IsCoprime (fatPointIdeal I p N) (fatPointIdeal J q M) := by
  have h := (Ideal.isCoprime_of_isMaximal
    (fun he => hpq (pointIdeal_injective he))).pow (m := N) (n := M)
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply top_unique
  rw [← h.sup_eq]
  exact sup_le_sup (show pointIdeal p ^ N ≤ fatPointIdeal I p N from le_sup_right)
    (show pointIdeal q ^ M ≤ fatPointIdeal J q M from le_sup_right)

/-- Distinct actual points give pairwise-comaximal fat-point equation ideals. -/
theorem fatPointIdeal_pairwise {P : Type*}
    (I : P → Ideal (MvPolynomial σ K)) (p : P → σ → K)
    (hp : Function.Injective p) (N : P → ℕ) :
    Pairwise (fun i j => IsCoprime (fatPointIdeal (I i) (p i) (N i))
      (fatPointIdeal (I j) (p j) (N j))) := by
  intro i j hij
  exact fatPointIdeal_isCoprime (I i) (I j) (p i) (p j) (fun h => hij (hp h)) (N i) (N j)

abbrev FatPointQuotient (I : Ideal (MvPolynomial σ K)) (p : σ → K) (N : ℕ) :=
  MvPolynomial σ K ⧸ fatPointIdeal I p N

/-- Every function vanishing at the point is nilpotent in the actual
truncated quotient, with the displayed uniform exponent. -/
theorem fatPoint_nilpotent (I : Ideal (MvPolynomial σ K)) (p : σ → K) (N : ℕ)
    (f : MvPolynomial σ K) (hf : f ∈ pointIdeal p) :
    IsNilpotent (Ideal.Quotient.mk (fatPointIdeal I p N) f) := by
  refine ⟨N, ?_⟩
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show pointIdeal p ^ N ≤ fatPointIdeal I p N from le_sup_right)
      (Ideal.pow_mem_pow hf N))

/-- Every polynomial nonzero at the point becomes a unit in every fat-point
quotient. This is what permits the inverse localization map. -/
theorem fatPoint_isUnit (I : Ideal (MvPolynomial σ K)) (p : σ → K) (N : ℕ)
    (f : MvPolynomial σ K) (hf : eval p f ≠ 0) :
    IsUnit (Ideal.Quotient.mk (fatPointIdeal I p N) f) := by
  have hn := fatPoint_nilpotent I p N (f - C (eval p f)) (by simp)
  have hu : IsUnit (algebraMap K (FatPointQuotient I p N) (eval p f)) :=
    (isUnit_iff_ne_zero.mpr hf).map _
  have h := hn.isUnit_add_right_of_commute hu (Commute.all _ _)
  convert h using 1
  rw [map_sub, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
  exact (sub_add_cancel _ _).symm

/-- A nilpotent element is integral, by its actual monic power equation. -/
theorem integral_of_nilpotent {A : Type*} [CommRing A] [Algebra K A]
    (x : A) (hx : IsNilpotent x) : IsIntegral K x := by
  obtain ⟨N, hN⟩ := hx
  exact ⟨Polynomial.X ^ N, Polynomial.monic_X_pow N, by simpa using hN⟩

/-- Finite variables make every actual fat-point quotient a finite-dimensional
vector space. This is proved from the nilpotence equations of its coordinates. -/
instance fatPointQuotient_finite [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (p : σ → K) (N : ℕ) :
    Module.Finite K (FatPointQuotient I p N) := by
  have hcoord (i : σ) : IsIntegral K
      (Ideal.Quotient.mk (fatPointIdeal I p N) (X i)) := by
    have hn := integral_of_nilpotent (K := K)
      (Ideal.Quotient.mk (fatPointIdeal I p N) (X i - C (p i)))
      (fatPoint_nilpotent I p N _ (by simp))
    have h := hn.add (isIntegral_algebraMap (R := K)
      (A := FatPointQuotient I p N) (x := p i))
    convert h using 1
    rw [map_sub, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
    exact (sub_add_cancel _ _).symm
  letI : Algebra.FiniteType K (MvPolynomial σ K) := Algebra.FiniteType.mvPolynomial K σ
  apply Algebra.finite_iff_isIntegral_and_finiteType.mpr
  refine ⟨⟨?_⟩, inferInstance⟩
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using MvPolynomial.induction_on with
  | C r =>
    rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
    exact isIntegral_algebraMap
  | add f g hf hg => simpa only [map_add] using hf.add hg
  | mul_X f i hf => simpa only [map_mul] using hf.mul (hcoord i)

abbrev EquationQuotient (I : Ideal (MvPolynomial σ K)) := MvPolynomial σ K ⧸ I

/-- The rational point's literal evaluation homomorphism on the equation ring. -/
def quotientEvaluation (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) : EquationQuotient I →ₐ[K] K :=
  Ideal.Quotient.liftₐ I (aeval p) hI

@[simp] theorem quotientEvaluation_mk (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) (f : MvPolynomial σ K) :
    quotientEvaluation I p hI (Ideal.Quotient.mk I f) = eval p f := rfl

def quotientPointIdeal (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) : Ideal (EquationQuotient I) :=
  RingHom.ker (quotientEvaluation I p hI)

instance quotientPointIdeal_isMaximal (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) : (quotientPointIdeal I p hI).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (quotientEvaluation I p hI)
    (fun r => ⟨Ideal.Quotient.mk I (C r), by simp⟩)

/-- The actual local intersection algebra, with the full nonreduced equation ideal. -/
abbrev LocalIntersectionRing (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) := Localization.AtPrime (quotientPointIdeal I p hI)

/-- Its actual intersection multiplicity, defined as generic module length. -/
def multiplicity (I : Ideal (MvPolynomial σ K)) (p : σ → K) (hI : I ≤ pointIdeal p) : ℕ∞ :=
  Module.length (LocalIntersectionRing I p hI) (LocalIntersectionRing I p hI)

def localPolynomialMap (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) : MvPolynomial σ K →ₐ[K] LocalIntersectionRing I p hI :=
  (IsScalarTower.toAlgHom K (EquationQuotient I) (LocalIntersectionRing I p hI)).comp
    (Ideal.Quotient.mkₐ K I)

@[simp] theorem localPolynomialMap_apply (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) (f : MvPolynomial σ K) :
    localPolynomialMap I p hI f =
      algebraMap (EquationQuotient I) (LocalIntersectionRing I p hI) (Ideal.Quotient.mk I f) := rfl

/-- Rational residue evaluation extends uniquely across the localization. -/
def localEvaluation (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) : LocalIntersectionRing I p hI →+* K :=
  IsLocalization.lift (M := (quotientPointIdeal I p hI).primeCompl)
    (g := (quotientEvaluation I p hI).toRingHom)
    (fun s => isUnit_iff_ne_zero.mpr s.property)

@[simp] theorem localEvaluation_algebraMap (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) (x : EquationQuotient I) :
    localEvaluation I p hI (algebraMap (EquationQuotient I) (LocalIntersectionRing I p hI) x) =
      quotientEvaluation I p hI x := IsLocalization.lift_eq _ x

def localEvaluationAlg (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) : LocalIntersectionRing I p hI →ₐ[K] K :=
  { localEvaluation I p hI with
    commutes' := by
      intro r
      change localEvaluation I p hI (algebraMap K (LocalIntersectionRing I p hI) r) = _
      rw [IsScalarTower.algebraMap_apply K (EquationQuotient I) (LocalIntersectionRing I p hI),
        localEvaluation_algebraMap]
      exact (quotientEvaluation I p hI).commutes r }

/-- The actual local residue field is the original rational-point field. -/
theorem localEvaluation_ker (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) :
    RingHom.ker (localEvaluation I p hI) = IsLocalRing.maximalIdeal (LocalIntersectionRing I p hI) := by
  apply IsLocalRing.eq_maximalIdeal
  exact RingHom.ker_isMaximal_of_surjective (localEvaluation I p hI)
    (fun r => ⟨algebraMap K (LocalIntersectionRing I p hI) r, (localEvaluationAlg I p hI).commutes r⟩)

/-- The equation quotient maps canonically to every actual fat-point quotient. -/
def quotientToFat (I : Ideal (MvPolynomial σ K)) (p : σ → K) (N : ℕ) :
    EquationQuotient I →ₐ[K] FatPointQuotient I p N :=
  Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ K (fatPointIdeal I p N))
    (fun _ hf => Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show I ≤ fatPointIdeal I p N from le_sup_left) hf))

@[simp] theorem quotientToFat_mk (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (N : ℕ) (f : MvPolynomial σ K) :
    quotientToFat I p N (Ideal.Quotient.mk I f) =
      Ideal.Quotient.mk (fatPointIdeal I p N) f := rfl

/-- All denominators defining the point localization are units in the
fat-point quotient. No finiteness or isolatedness is used for this map. -/
theorem quotientToFat_unit (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) (N : ℕ) (s : (quotientPointIdeal I p hI).primeCompl) :
    IsUnit (quotientToFat I p N s) := by
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective s.val
  rw [← hf, quotientToFat_mk]
  apply fatPoint_isUnit
  intro hz
  apply s.property
  change quotientEvaluation I p hI s.val = 0
  rw [← hf, quotientEvaluation_mk, hz]

def localToFat (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) (N : ℕ) :
    LocalIntersectionRing I p hI →+* FatPointQuotient I p N :=
  IsLocalization.lift (M := (quotientPointIdeal I p hI).primeCompl)
    (g := (quotientToFat I p N).toRingHom) (quotientToFat_unit I p hI N)

@[simp] theorem localToFat_algebraMap (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) (N : ℕ) (x : EquationQuotient I) :
    localToFat I p hI N (algebraMap (EquationQuotient I) (LocalIntersectionRing I p hI) x) =
      quotientToFat I p N x := IsLocalization.lift_eq _ x

def localToFatAlg (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) (N : ℕ) :
    LocalIntersectionRing I p hI →ₐ[K] FatPointQuotient I p N :=
  { localToFat I p hI N with
    commutes' := by
      intro r
      change localToFat I p hI N (algebraMap K (LocalIntersectionRing I p hI) r) = _
      rw [IsScalarTower.algebraMap_apply K (EquationQuotient I) (LocalIntersectionRing I p hI),
        localToFat_algebraMap]
      exact (quotientToFat I p N).commutes r }

/-- A vanishing power in the actual local ring supplies the inverse map. -/
def fatToLocal (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) (N : ℕ)
    (hN : pointIdeal p ^ N ≤ RingHom.ker (localPolynomialMap I p hI)) :
    FatPointQuotient I p N →ₐ[K] LocalIntersectionRing I p hI :=
  Ideal.Quotient.liftₐ (fatPointIdeal I p N) (localPolynomialMap I p hI) (sup_le
    (by
      intro f hf
      change algebraMap (EquationQuotient I) (LocalIntersectionRing I p hI)
        (Ideal.Quotient.mk I f) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]) hN)

@[simp] theorem fatToLocal_mk (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) (N : ℕ)
    (hN : pointIdeal p ^ N ≤ RingHom.ker (localPolynomialMap I p hI))
    (f : MvPolynomial σ K) :
    fatToLocal I p hI N hN (Ideal.Quotient.mk (fatPointIdeal I p N) f) =
      localPolynomialMap I p hI f := rfl

theorem local_fat_leftInverse (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) (N : ℕ)
    (hN : pointIdeal p ^ N ≤ RingHom.ker (localPolynomialMap I p hI)) :
    Function.LeftInverse (fatToLocal I p hI N hN) (localToFat I p hI N) := by
  have h : (fatToLocal I p hI N hN).toRingHom.comp (localToFat I p hI N) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (quotientPointIdeal I p hI).primeCompl
    apply RingHom.ext
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingHom.comp_apply, localToFat_algebraMap, quotientToFat_mk,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, fatToLocal_mk, localPolynomialMap_apply,
      RingHom.id_apply]
  intro x
  exact DFunLike.congr_fun h x

theorem local_fat_rightInverse (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) (N : ℕ)
    (hN : pointIdeal p ^ N ≤ RingHom.ker (localPolynomialMap I p hI)) :
    Function.RightInverse (fatToLocal I p hI N hN) (localToFat I p hI N) := by
  intro x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [fatToLocal_mk, localPolynomialMap_apply, localToFat_algebraMap, quotientToFat_mk]

/-- Canonical equivalence with the full fat-point algebra once the displayed
power vanishes locally. No global zero-dimensionality of I is required. -/
def localEquivFatPointOfPow (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) (N : ℕ)
    (hN : pointIdeal p ^ N ≤ RingHom.ker (localPolynomialMap I p hI)) :
    LocalIntersectionRing I p hI ≃ₐ[K] FatPointQuotient I p N :=
  { localToFatAlg I p hI N with
    invFun := fatToLocal I p hI N hN
    left_inv := local_fat_leftInverse I p hI N hN
    right_inv := local_fat_rightInverse I p hI N hN }

theorem pointIdeal_le_comap_localMaximal (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) :
    pointIdeal p ≤ (IsLocalRing.maximalIdeal (LocalIntersectionRing I p hI)).comap
      (localPolynomialMap I p hI) := by
  intro f hf
  change algebraMap (EquationQuotient I) (LocalIntersectionRing I p hI) (Ideal.Quotient.mk I f) ∈
    IsLocalRing.maximalIdeal (LocalIntersectionRing I p hI)
  rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (quotientPointIdeal I p hI)]
  exact hf

/-- Algebraic isolatedness (the actual local intersection ring is Artinian)
forces a power of the point maximal ideal to vanish in that local ring. -/
theorem exists_pointIdeal_pow_le_ker (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) [IsArtinianRing (LocalIntersectionRing I p hI)] :
    ∃ N : ℕ, 0 < N ∧ pointIdeal p ^ N ≤ RingHom.ker (localPolynomialMap I p hI) := by
  have hn : IsNilpotent (IsLocalRing.maximalIdeal (LocalIntersectionRing I p hI)) := by
    simpa only [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] using
      (IsArtinianRing.isNilpotent_jacobson_bot (R := LocalIntersectionRing I p hI))
  obtain ⟨N, hN⟩ := hn
  have hN' : IsLocalRing.maximalIdeal (LocalIntersectionRing I p hI) ^ (N+1) = ⊥ := by
    rw [pow_succ, hN]
    simp
  refine ⟨N+1, Nat.zero_lt_succ _, ?_⟩
  calc
    pointIdeal p ^ (N+1) ≤
        ((IsLocalRing.maximalIdeal (LocalIntersectionRing I p hI)).comap
          (localPolynomialMap I p hI)) ^ (N+1) :=
      pow_le_pow_left' (pointIdeal_le_comap_localMaximal I p hI) _
    _ ≤ (IsLocalRing.maximalIdeal (LocalIntersectionRing I p hI) ^ (N+1)).comap
          (localPolynomialMap I p hI) := Ideal.le_comap_pow (localPolynomialMap I p hI).toRingHom (N+1)
    _ = RingHom.ker (localPolynomialMap I p hI) := by rw [hN']; rfl

/-- Actual isolated local intersection algebras are canonically represented
by some finite fat-point truncation, retaining the original equations. -/
theorem exists_localEquivFatPoint (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) [IsArtinianRing (LocalIntersectionRing I p hI)] :
    ∃ N : ℕ, 0 < N ∧ Nonempty (LocalIntersectionRing I p hI ≃ₐ[K] FatPointQuotient I p N) := by
  obtain ⟨N, hN, hpow⟩ := exists_pointIdeal_pow_le_ker I p hI
  exact ⟨N, hN, ⟨localEquivFatPointOfPow I p hI N hpow⟩⟩

/-- Finiteness over the rational-point field is a theorem, not an additional
isolatedness assumption. -/
instance localIntersection_finite [Finite σ] (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) [IsArtinianRing (LocalIntersectionRing I p hI)] :
    Module.Finite K (LocalIntersectionRing I p hI) := by
  obtain ⟨N, _, ⟨e⟩⟩ := exists_localEquivFatPoint I p hI
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- The actual local module length equals vector-space dimension over the
rational residue field. This is the scheme-theoretic intersection multiplicity. -/
theorem multiplicity_eq_finrank [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (p : σ → K) (hI : I ≤ pointIdeal p)
    [IsArtinianRing (LocalIntersectionRing I p hI)] :
    multiplicity I p hI = (Module.finrank K (LocalIntersectionRing I p hI) : ℕ∞) :=
  LocalLengthDimension.length_eq_finrank (localEvaluationAlg I p hI) (LocalIntersectionRing I p hI)

/-- Consequently a sufficiently deep actual fat-point quotient has exactly
the local intersection multiplicity, even with unrelated excess components. -/
theorem exists_multiplicity_eq_fatPoint_finrank [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (p : σ → K) (hI : I ≤ pointIdeal p)
    [IsArtinianRing (LocalIntersectionRing I p hI)] :
    ∃ N : ℕ, 0 < N ∧ multiplicity I p hI = (Module.finrank K (FatPointQuotient I p N) : ℕ∞) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := exists_localEquivFatPoint I p hI
  exact ⟨N, hN, (multiplicity_eq_finrank I p hI).trans (congrArg Nat.cast e.toLinearEquiv.finrank_eq)⟩

/-- The original polynomial ring surjects onto an isolated local algebra:
all inverses needed in its localization are already polynomials modulo the
nilpotent maximal ideal. -/
theorem localPolynomialMap_surjective
    (I : Ideal (MvPolynomial σ K)) (p : σ → K) (hI : I ≤ pointIdeal p)
    [IsArtinianRing (LocalIntersectionRing I p hI)] :
    Function.Surjective (localPolynomialMap I p hI) := by
  obtain ⟨N, _, hN⟩ := exists_pointIdeal_pow_le_ker I p hI
  let e := localEquivFatPointOfPow I p hI N hN
  intro y
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (e y)
  refine ⟨f, e.injective ?_⟩
  change localToFat I p hI N (localPolynomialMap I p hI f) = e y
  simpa only [localPolynomialMap_apply, localToFat_algebraMap, quotientToFat_mk] using hf

/-- The rational point determined by a polynomial presentation and a residue
map. This also applies after changing or normalizing the coordinates. -/
def residuePoint {A : Type*} [CommRing A] [Algebra K A]
    (φ : MvPolynomial σ K →ₐ[K] A) (ε : A →ₐ[K] K) : σ → K :=
  fun i => ε (φ (X i))

theorem residue_comp_eq_aeval {A : Type*} [CommRing A] [Algebra K A]
    (φ : MvPolynomial σ K →ₐ[K] A) (ε : A →ₐ[K] K) :
    ε.comp φ = aeval (residuePoint φ ε) := by
  ext i
  simp [residuePoint]

/-- For every polynomial presentation of an Artinian local algebra, a power
of the actual residue point ideal is killed. The power is derived from local
nilpotence, not assumed as an interpolation hypothesis. -/
theorem exists_residuePoint_pow_le_ker {A : Type*} [CommRing A] [Algebra K A]
    [IsLocalRing A] [IsArtinianRing A]
    (φ : MvPolynomial σ K →ₐ[K] A) (ε : A →ₐ[K] K) :
    ∃ N : ℕ, 0 < N ∧ pointIdeal (residuePoint φ ε) ^ N ≤ RingHom.ker φ := by
  have hm : pointIdeal (residuePoint φ ε) ≤ (IsLocalRing.maximalIdeal A).comap φ := by
    intro f hf
    change φ f ∈ IsLocalRing.maximalIdeal A
    rw [← IsLocalRing.ker_eq_maximalIdeal ε.toRingHom
      (LocalLengthDimension.residue_surjective ε)]
    exact (DFunLike.congr_fun (residue_comp_eq_aeval φ ε) f).trans hf
  have hn : IsNilpotent (IsLocalRing.maximalIdeal A) := by
    simpa only [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] using
      (IsArtinianRing.isNilpotent_jacobson_bot (R := A))
  obtain ⟨N, hN⟩ := hn
  have hN' : IsLocalRing.maximalIdeal A ^ (N+1) = ⊥ := by
    rw [pow_succ, hN]
    simp
  refine ⟨N+1, Nat.zero_lt_succ _, ?_⟩
  calc
    pointIdeal (residuePoint φ ε) ^ (N+1) ≤
        ((IsLocalRing.maximalIdeal A).comap φ) ^ (N+1) := pow_le_pow_left' hm _
    _ ≤ (IsLocalRing.maximalIdeal A ^ (N+1)).comap φ :=
      Ideal.le_comap_pow φ.toRingHom (N+1)
    _ = RingHom.ker φ := by rw [hN']; rfl

section Products
variable {P : Type*} [Fintype P]

/-- Actual Chinese remainder surjectivity for arbitrary quotient maps whose
kernels contain powers of distinct point ideals. This permits new normalized
presentations of the same local algebras, with no prescribed coordinates. -/
theorem piAlgHom_surjective_of_pointPowers
    (A : P → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    (φ : ∀ i, MvPolynomial σ K →ₐ[K] A i)
    (hφ : ∀ i, Function.Surjective (φ i))
    (p : P → σ → K) (hp : Function.Injective p) (N : P → ℕ)
    (hN : ∀ i, pointIdeal (p i) ^ N i ≤ RingHom.ker (φ i)) :
    Function.Surjective (Pi.algHom K _ φ) := by
  have hcop : Pairwise (fun i j => IsCoprime (pointIdeal (p i) ^ N i)
      (pointIdeal (p j) ^ N j)) := by
    intro i j hij
    have h := fatPointIdeal_isCoprime ⊥ ⊥ (p i) (p j)
      (fun h => hij (hp h)) (N i) (N j)
    simpa only [fatPointIdeal, bot_sup_eq] using h
  intro y
  choose f hf using fun i => hφ i (y i)
  obtain ⟨g, hg⟩ := Ideal.exists_forall_sub_mem_ideal hcop f
  refine ⟨g, funext fun i => ?_⟩
  have h : φ i (g - f i) = 0 := hN i (hg i)
  simpa only [map_sub, hf, sub_eq_zero] using h

/-- Chinese remainder interpolation into arbitrary Artinian local algebras
with distinct actual residue points. All nilpotent powers used in the proof
are derived from Artinianness. -/
theorem piAlgHom_surjective_of_distinctResidues
    (A : P → Type*) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)]
    [∀ i, IsLocalRing (A i)] [∀ i, IsArtinianRing (A i)]
    (φ : ∀ i, MvPolynomial σ K →ₐ[K] A i)
    (hφ : ∀ i, Function.Surjective (φ i))
    (ε : ∀ i, A i →ₐ[K] K)
    (hp : Function.Injective (fun i => residuePoint (φ i) (ε i))) :
    Function.Surjective (Pi.algHom K _ φ) := by
  choose N hpos hN using fun i => exists_residuePoint_pow_le_ker (φ i) (ε i)
  exact piAlgHom_surjective_of_pointPowers A φ hφ _ hp N hN

/-- The simultaneous map to the actual local intersection algebras. -/
def localProductMap (I : P → Ideal (MvPolynomial σ K))
    (p : P → σ → K) (hI : ∀ i, I i ≤ pointIdeal (p i)) :
    MvPolynomial σ K →ₐ[K] (∀ i, LocalIntersectionRing (I i) (p i) (hI i)) :=
  Pi.algHom K _ (fun i => localPolynomialMap (I i) (p i) (hI i))

/-- Distinct isolated points admit simultaneous interpolation into their full
local intersection algebras, including every nilpotent multiplicity. -/
theorem localProductMap_surjective (I : P → Ideal (MvPolynomial σ K))
    (p : P → σ → K) (hI : ∀ i, I i ≤ pointIdeal (p i))
    (hp : Function.Injective p)
    [∀ i, IsArtinianRing (LocalIntersectionRing (I i) (p i) (hI i))] :
    Function.Surjective (localProductMap I p hI) := by
  choose N hpos hN using fun i => exists_pointIdeal_pow_le_ker (I i) (p i) (hI i)
  exact piAlgHom_surjective_of_pointPowers _
    (fun i => localPolynomialMap (I i) (p i) (hI i))
    (fun i => localPolynomialMap_surjective (I i) (p i) (hI i)) p hp N hN

end Products

end Sheshadri.IsolatedLocalMultiplicity
