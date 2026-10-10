/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FlatGradedHilbert
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Scalar-compatible base change for graded polynomial quotients

The tensor fibre is identified with the quotient by the extended equations.
The equivalence preserves the literal homogeneous pieces; no surjectivity of
the coefficient map is required.
-/

noncomputable section
namespace Sheshadri.GeneralGradedBaseChange

open MvPolynomial FlatGradedHilbert
open scoped TensorProduct

set_option maxHeartbeats 800000

variable {σ R K : Type*} [CommRing R] [CommRing K] [Algebra R K]

/-- The actual ideal obtained by extending the coefficients. -/
def extendedIdeal (I : Ideal (MvPolynomial σ R)) : Ideal (MvPolynomial σ K) :=
  I.map (MvPolynomial.map (algebraMap R K))

/-- The induced map from the original coordinate ring to the extended one. -/
def quotientCoefficientMap (I : Ideal (MvPolynomial σ R)) :
    (MvPolynomial σ R ⧸ I) →ₐ[R] (MvPolynomial σ K ⧸ extendedIdeal (K := K) I) :=
  Ideal.Quotient.liftₐ I
    ((Ideal.Quotient.mkₐ R _).comp (MvPolynomial.mapAlgHom (Algebra.ofId R K)))
    (fun _ hp => Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap R K)) hp))

@[simp] theorem quotientCoefficientMap_mk (I : Ideal (MvPolynomial σ R))
    (p : MvPolynomial σ R) :
    quotientCoefficientMap (K := K) I (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk (extendedIdeal (K := K) I) (MvPolynomial.map (algebraMap R K) p) := rfl

/-- The forward scalar-compatible fibre map. -/
def tensorToQuotient (I : Ideal (MvPolynomial σ R)) :
    K ⊗[R] (MvPolynomial σ R ⧸ I) →ₐ[K]
      (MvPolynomial σ K ⧸ extendedIdeal (K := K) I) :=
  Algebra.TensorProduct.lift (Algebra.ofId K _) (quotientCoefficientMap I)
    (fun _ _ => Commute.all _ _)

@[simp] theorem tensorToQuotient_tmul_mk (I : Ideal (MvPolynomial σ R))
    (k : K) (p : MvPolynomial σ R) :
    tensorToQuotient I (k ⊗ₜ[R] Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk (extendedIdeal (K := K) I)
        (k • MvPolynomial.map (algebraMap R K) p) := by
  simp only [tensorToQuotient, Algebra.TensorProduct.lift_tmul, quotientCoefficientMap_mk]
  change algebraMap K _ k * Ideal.Quotient.mk _ _ = _
  rw [← Algebra.smul_def]
  exact (map_smul (Ideal.Quotient.mkₐ K _) k _).symm

/-- Polynomial evaluation in the tensor fibre. -/
def polynomialToTensor (I : Ideal (MvPolynomial σ R)) :
    MvPolynomial σ K →ₐ[K] K ⊗[R] (MvPolynomial σ R ⧸ I) :=
  (Algebra.TensorProduct.map (AlgHom.id K K) (Ideal.Quotient.mkₐ R I)).comp
    (MvPolynomial.algebraTensorAlgEquiv R K).symm.toAlgHom

@[simp] theorem polynomialToTensor_monomial (I : Ideal (MvPolynomial σ R))
    (e : σ →₀ ℕ) (k : K) :
    polynomialToTensor I (monomial e k) =
      k ⊗ₜ[R] Ideal.Quotient.mk I (monomial e (1 : R)) := by
  simp [polynomialToTensor]

@[simp] theorem polynomialToTensor_map (I : Ideal (MvPolynomial σ R))
    (p : MvPolynomial σ R) :
    polynomialToTensor (K := K) I (MvPolynomial.map (algebraMap R K) p) =
      1 ⊗ₜ[R] Ideal.Quotient.mk I p := by
  have h : (MvPolynomial.algebraTensorAlgEquiv R K).symm
      (MvPolynomial.map (algebraMap R K) p) = 1 ⊗ₜ[R] p := by
    apply (MvPolynomial.algebraTensorAlgEquiv R K).injective
    simp
  simp [polynomialToTensor, h]

/-- Evaluation annihilates every extended equation, including its ideal multiples. -/
theorem extendedIdeal_le_ker (I : Ideal (MvPolynomial σ R)) :
    extendedIdeal (K := K) I ≤ RingHom.ker (polynomialToTensor (K := K) I) := by
  rw [extendedIdeal, Ideal.map_le_iff_le_comap]
  intro p hp
  change polynomialToTensor I (MvPolynomial.map (algebraMap R K) p) = 0
  rw [polynomialToTensor_map, Ideal.Quotient.eq_zero_iff_mem.mpr hp,
    TensorProduct.tmul_zero]

def quotientToTensor (I : Ideal (MvPolynomial σ R)) :
    (MvPolynomial σ K ⧸ extendedIdeal (K := K) I) →ₐ[K]
      K ⊗[R] (MvPolynomial σ R ⧸ I) :=
  Ideal.Quotient.liftₐ _ (polynomialToTensor I) (fun _ hp => extendedIdeal_le_ker I hp)

@[simp] theorem quotientToTensor_mk (I : Ideal (MvPolynomial σ R))
    (p : MvPolynomial σ K) :
    quotientToTensor I (Ideal.Quotient.mk _ p) = polynomialToTensor I p := rfl

/-- Actual base change, as an algebra equivalence over the fibre coefficient ring. -/
def tensorQuotientEquiv (I : Ideal (MvPolynomial σ R)) :
    K ⊗[R] (MvPolynomial σ R ⧸ I) ≃ₐ[K]
      (MvPolynomial σ K ⧸ extendedIdeal (K := K) I) :=
  AlgEquiv.ofAlgHom (tensorToQuotient I) (quotientToTensor I)
    (by
      apply Ideal.Quotient.algHom_ext
      ext i
      simp [polynomialToTensor, tensorToQuotient, quotientToTensor,
        quotientCoefficientMap])
    (by
      apply Algebra.TensorProduct.ext
      · ext
      · apply Ideal.Quotient.algHom_ext
        ext i
        simp [tensorToQuotient, quotientCoefficientMap, quotientToTensor,
          polynomialToTensor])

@[simp] theorem tensorQuotientEquiv_tmul_mk (I : Ideal (MvPolynomial σ R))
    (k : K) (p : MvPolynomial σ R) :
    tensorQuotientEquiv I (k ⊗ₜ[R] Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk (extendedIdeal (K := K) I)
        (k • MvPolynomial.map (algebraMap R K) p) :=
  tensorToQuotient_tmul_mk I k p

omit [Algebra R K] in
theorem weightedHomogeneous_map (f : R →+* K) (w : σ → ℕ × ℕ) (d : ℕ × ℕ)
    {p : MvPolynomial σ R} (hp : p.IsWeightedHomogeneous w d) :
    (MvPolynomial.map f p).IsWeightedHomogeneous w d := by
  intro e he
  apply hp
  intro hz
  apply he
  rw [coeff_map, hz, map_zero]

/-- Scalar extension carries the actual tensor graded piece onto the
literal graded piece of the quotient by the extended equations. -/
theorem map_fibreBicoordinatePiece (block : σ → Bool)
    (I : Ideal (MvPolynomial σ R)) (a b : ℕ) :
    (fibreBicoordinatePiece σ R block I K a b).map
      (tensorQuotientEquiv I).toLinearMap =
    bicoordinatePiece σ K block (extendedIdeal I) a b := by
  classical
  apply le_antisymm
  · rintro y ⟨x, ⟨t, rfl⟩, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simpa only [map_add] using
        (bicoordinatePiece σ K block (extendedIdeal I) a b).add_mem hx hy
    | tmul k x =>
      obtain ⟨p, hp, hpx⟩ := x.property
      change tensorQuotientEquiv I (k ⊗ₜ[R] (x : MvPolynomial σ R ⧸ I)) ∈ _
      have hpx' : Ideal.Quotient.mk I p = (x : MvPolynomial σ R ⧸ I) := hpx
      rw [← hpx', tensorQuotientEquiv_tmul_mk]
      exact ⟨_, (weightedHomogeneousSubmodule K
        (twoBlockWeight σ block) (a, b)).smul_mem k
          (weightedHomogeneous_map _ _ _ hp), rfl⟩
  · rintro y ⟨p, hp, rfl⟩
    rw [← p.support_sum_monomial_coeff, map_sum]
    apply Submodule.sum_mem
    intro e he
    have hdegree : Finsupp.weight (twoBlockWeight σ block) e = (a, b) :=
      hp (mem_support_iff.mp he)
    let q : MvPolynomial σ R := monomial e 1
    have hq : q.IsWeightedHomogeneous (twoBlockWeight σ block) (a, b) :=
      isWeightedHomogeneous_monomial _ _ _ hdegree
    let x : bicoordinatePiece σ R block I a b := ⟨Ideal.Quotient.mk I q, q, hq, rfl⟩
    refine ⟨coeff e p ⊗ₜ[R] (x : MvPolynomial σ R ⧸ I), ?_, ?_⟩
    · exact ⟨coeff e p ⊗ₜ[R] x, rfl⟩
    · change tensorQuotientEquiv I (coeff e p ⊗ₜ[R] Ideal.Quotient.mk I q) = _
      simp [tensorQuotientEquiv_tmul_mk, q, smul_monomial]

/-- Literal quotient-piece dimensions agree with their tensor fibre values. -/
theorem bicoordinatePiece_finrank_eq_fibre (K : Type*) [Field K] [Algebra R K]
    (block : σ → Bool) (I : Ideal (MvPolynomial σ R)) (a b : ℕ) :
    Module.finrank K (bicoordinatePiece σ K block (extendedIdeal I) a b) =
      Module.finrank K (fibreBicoordinatePiece σ R block I K a b) := by
  rw [← map_fibreBicoordinatePiece]
  exact LinearEquiv.finrank_eq
    ((tensorQuotientEquiv I).toLinearEquiv.submoduleMap
      (fibreBicoordinatePiece σ R block I K a b)).symm

end Sheshadri.GeneralGradedBaseChange
