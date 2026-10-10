/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.CurveThroughBoundary
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Coherent polynomial solutions over finite field extensions

A solution in any field extension proves the literal equation ideal proper.
A maximal ideal and Zariski's lemma then construct a solution in a finite
field extension. The equations and their common solution are retained.
-/

noncomputable section
namespace Sheshadri.GenericPolynomialLift
open MvPolynomial
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

variable {X E K L : Type*} [Finite X] [Field K] [Field L] [Algebra K L]

/-- A jointly solvable finite-variable polynomial system has one coherent
solution in an actual finite extension, constructed as a maximal quotient. -/
theorem finite_field_solution (F : E → MvPolynomial X K) (x : X → L)
    (hx : ∀ e, aeval x (F e) = 0) :
    ∃ P : Ideal (MvPolynomial X K), P.IsMaximal ∧
      Module.Finite K (MvPolynomial X K ⧸ P) ∧
      ∀ e, eval₂ (algebraMap K (MvPolynomial X K ⧸ P))
        (fun i => Ideal.Quotient.mk P (MvPolynomial.X i)) (F e) = 0 := by
  let I := Ideal.span (Set.range F)
  have hI : I ≤ RingHom.ker (aeval x) :=
    Ideal.span_le.mpr (by rintro f ⟨e, rfl⟩; exact hx e)
  have hproper : I ≠ ⊤ := by
    intro he
    have h := hI (show (1 : MvPolynomial X K) ∈ I by simp [he])
    simpa using h
  obtain ⟨P, hP, hIP⟩ := I.exists_le_maximal hproper
  letI := hP
  letI := Ideal.Quotient.field P
  letI : Algebra.FiniteType K (MvPolynomial X K) := Algebra.FiniteType.mvPolynomial K X
  letI : Module.Finite K (MvPolynomial X K ⧸ P) :=
    finite_of_finite_type_of_isJacobsonRing K (MvPolynomial X K ⧸ P)
  refine ⟨P, hP, inferInstance, ?_⟩
  intro e
  have hm : F e ∈ P := hIP (Ideal.subset_span ⟨e, rfl⟩)
  have heval : eval₂Hom (algebraMap K (MvPolynomial X K ⧸ P))
      (fun i => Ideal.Quotient.mk P (MvPolynomial.X i)) = Ideal.Quotient.mk P := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [eval₂Hom_C]
      rfl
    · intro i
      simp
  change eval₂Hom _ _ (F e) = 0
  rw [heval]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hm

section GenericRepresentation
open AlgebraicCurveSelection CurveThroughBoundary
variable {Y : Type*} (F : Y → MvPolynomial X ℂ)

/-- The coordinate functions of the actual selected coefficient curve,
viewed in its actual fraction field. -/
def genericCoefficient (Q : PrimeSpectrum (ImageRing F)) (i : Y) :
    FractionRing (ImageRing F ⧸ Q.asIdeal) :=
  algebraMap (ImageRing F ⧸ Q.asIdeal) (FractionRing (ImageRing F ⧸ Q.asIdeal))
    (Ideal.Quotient.mk Q.asIdeal (Ideal.Quotient.mk (imageIdeal F) (MvPolynomial.X i)))

/-- A generic spectrum preimage supplies one representation over a finite
extension of the actual coefficient curve's fraction field. The equations
are the original polynomial parameterization evaluated on common variables. -/
theorem finite_representation_of_spectrum_preimage
    (Q : PrimeSpectrum (ImageRing F))
    (hQ : Q ∈ Set.range (PrimeSpectrum.comap (imageEmbedding F).toRingHom)) :
    ∃ P : Ideal (MvPolynomial X (FractionRing (ImageRing F ⧸ Q.asIdeal))),
      P.IsMaximal ∧ Module.Finite (FractionRing (ImageRing F ⧸ Q.asIdeal))
        (MvPolynomial X (FractionRing (ImageRing F ⧸ Q.asIdeal)) ⧸ P) ∧
      ∀ i : Y, eval₂ (algebraMap ℂ
          (MvPolynomial X (FractionRing (ImageRing F ⧸ Q.asIdeal)) ⧸ P))
        (fun j => Ideal.Quotient.mk P (MvPolynomial.X j)) (F i) =
        algebraMap (FractionRing (ImageRing F ⧸ Q.asIdeal))
          (MvPolynomial X (FractionRing (ImageRing F ⧸ Q.asIdeal)) ⧸ P)
          (genericCoefficient F Q i) := by
  obtain ⟨W, hW⟩ := hQ
  have hcomap : W.asIdeal.comap (imageEmbedding F).toRingHom = Q.asIdeal :=
    congrArg PrimeSpectrum.asIdeal hW
  let T := ImageRing F ⧸ Q.asIdeal
  let B := MvPolynomial X ℂ ⧸ W.asIdeal
  let K := FractionRing T
  let L := FractionRing B
  let φ : T →ₐ[ℂ] B := Ideal.quotientMapₐ W.asIdeal (imageEmbedding F) hcomap.symm.le
  have hφ : Function.Injective φ := Ideal.quotientMap_injective' (H := hcomap.symm.le) hcomap.le
  letI : Algebra T B := φ.toRingHom.toAlgebra
  letI : IsScalarTower ℂ T B := IsScalarTower.of_algHom φ
  letI : FaithfulSMul T B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hφ
  letI : Algebra K L := FractionRing.liftAlgebra T L
  letI : IsScalarTower T K L := FractionRing.isScalarTower_liftAlgebra T L
  letI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq (fun c => by
    rw [IsScalarTower.algebraMap_apply ℂ T L, IsScalarTower.algebraMap_apply ℂ T K,
      ← IsScalarTower.algebraMap_apply T K L])
  let x : X → L := fun j => algebraMap B L (Ideal.Quotient.mk W.asIdeal (MvPolynomial.X j))
  have heval (f : MvPolynomial X ℂ) :
      eval₂ (algebraMap ℂ L) x f = algebraMap B L (Ideal.Quotient.mk W.asIdeal f) := by
    have hh : eval₂Hom (algebraMap ℂ L) x =
        (algebraMap B L).comp (Ideal.Quotient.mk W.asIdeal) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        rw [eval₂Hom_C]
        rfl
      · intro j
        change eval₂ (algebraMap ℂ L) x (MvPolynomial.X j) = _
        rw [eval₂_X]
        rfl
    exact DFunLike.congr_fun hh f
  let G : Y → MvPolynomial X K := fun i =>
    MvPolynomial.map (algebraMap ℂ K) (F i) - C (genericCoefficient F Q i)
  have hG (i : Y) : aeval x (G i) = 0 := by
    change eval₂ (algebraMap K L) x
      (MvPolynomial.map (algebraMap ℂ K) (F i) - C (genericCoefficient F Q i)) = 0
    rw [eval₂_sub, eval₂_C, eval₂_map, ← IsScalarTower.algebraMap_eq ℂ K L, heval]
    apply sub_eq_zero.mpr
    change algebraMap B L (Ideal.Quotient.mk W.asIdeal (F i)) =
      algebraMap K L (algebraMap T K _)
    rw [← IsScalarTower.algebraMap_apply T K L, IsScalarTower.algebraMap_apply T B L]
    congr 1
    change Ideal.Quotient.mk W.asIdeal (F i) =
      Ideal.Quotient.mk W.asIdeal (pullback F (MvPolynomial.X i))
    simp [pullback]
  obtain ⟨P, hP, hfinite, hsolution⟩ := finite_field_solution G x hG
  refine ⟨P, hP, hfinite, ?_⟩
  intro i
  have h := hsolution i
  dsimp only [G] at h
  rw [eval₂_sub, eval₂_C, eval₂_map, ← IsScalarTower.algebraMap_eq ℂ K
    (MvPolynomial X K ⧸ P), sub_eq_zero] at h
  exact h

end GenericRepresentation
end Sheshadri.GenericPolynomialLift
