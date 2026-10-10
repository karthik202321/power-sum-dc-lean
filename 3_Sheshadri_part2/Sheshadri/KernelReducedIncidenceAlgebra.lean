/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.KernelIncidenceAlgebra
import Mathlib.RingTheory.Localization.AtPrime

/-!
# Exact recovery of reduced right-kernel equations

The full and reduced normalized incidence ideals have identical extensions
where the literal block matrix with rows `u` and `Λ` is invertible. This is an
identity of ideals over arbitrary rings, so it retains scheme multiplicities.
-/

noncomputable section
namespace Sheshadri.KernelReducedIncidenceAlgebra

open Matrix MvPolynomial KernelIncidenceAlgebra
open scoped BigOperators

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The literal block matrix obtained by adjoining the left-kernel row to Λ. -/
def augmentedMatrix (u : Fin (m+1) → R) (Λ : Matrix (Fin m) (Fin (m+1)) R) :
    Matrix (Fin (m+1)) (Fin (m+1)) R := Fin.cons u Λ

/-- Invertibility of the augmented matrix recovers the full right kernel
from the left kernel and the reduced right equations. -/
theorem recover_right_kernel
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (u v : Fin (m+1) → R) (Λ : Matrix (Fin m) (Fin (m+1)) R)
    (hΓ : IsUnit (augmentedMatrix u Λ).det)
    (hu : u ᵥ* A = 0) (hv : Λ *ᵥ (A *ᵥ v) = 0) : A *ᵥ v = 0 := by
  have hzero : augmentedMatrix u Λ *ᵥ (A *ᵥ v) = 0 := by
    ext k
    refine Fin.cases ?_ (fun l => ?_) k
    · change u ⬝ᵥ (A *ᵥ v) = 0
      rw [Matrix.dotProduct_mulVec, hu, zero_dotProduct]
    · exact congrFun hv l
  calc
    A *ᵥ v = (1 : Matrix (Fin (m+1)) (Fin (m+1)) R) *ᵥ (A *ᵥ v) :=
      (Matrix.one_mulVec _).symm
    _ = ((augmentedMatrix u Λ)⁻¹ * augmentedMatrix u Λ) *ᵥ (A *ᵥ v) := by
      rw [Matrix.nonsing_inv_mul _ hΓ]
    _ = (augmentedMatrix u Λ)⁻¹ *ᵥ (augmentedMatrix u Λ *ᵥ (A *ᵥ v)) :=
      (Matrix.mulVec_mulVec _ _ _).symm
    _ = 0 := by rw [hzero, Matrix.mulVec_zero]

/-- Actual reduced right equations, expressed as linear combinations of the
full right equations. -/
def reducedRightEquation
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (Λ : Matrix (Fin m) (Fin (m+1)) R) (l : Fin m) : Polynomials R m :=
  ∑ k, C (Λ l k) * rightEquation A k

def reducedIncidenceIdeal
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (Λ : Matrix (Fin m) (Fin (m+1)) R) (i j : Fin (m+1)) :
    Ideal (Polynomials R m) :=
  Ideal.span (Set.range (leftEquation A)) ⊔
    Ideal.span (Set.range (reducedRightEquation A Λ)) ⊔
    Ideal.span {leftVariable j - 1} ⊔ Ideal.span {rightVariable i - 1}

def augmentedPolynomialMatrix (Λ : Matrix (Fin m) (Fin (m+1)) R) :
    Matrix (Fin (m+1)) (Fin (m+1)) (Polynomials R m) :=
  augmentedMatrix leftVariable (Λ.map C)

/-- The reduced equations belong to the full incidence ideal even before
localization. -/
theorem reduced_le_full
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (Λ : Matrix (Fin m) (Fin (m+1)) R) (i j : Fin (m+1)) :
    reducedIncidenceIdeal A Λ i j ≤ incidenceIdeal A i j := by
  apply sup_le_sup (sup_le_sup (sup_le_sup le_rfl ?_) le_rfl) le_rfl
  apply Ideal.span_le.mpr
  rintro _ ⟨l, rfl⟩
  apply Submodule.sum_mem
  intro k hk
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)

/-- The full and reduced incidence ideals become exactly equal after any
ring map inverting the determinant of the actual augmented block matrix. -/
theorem mapped_incidenceIdeal_eq_reduced {S : Type*} [CommRing S]
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (Λ : Matrix (Fin m) (Fin (m+1)) R) (i j : Fin (m+1))
    (φ : Polynomials R m →+* S)
    (hΓ : IsUnit (φ (augmentedPolynomialMatrix Λ).det)) :
    (incidenceIdeal A i j).map φ = (reducedIncidenceIdeal A Λ i j).map φ := by
  apply le_antisymm ?_ (Ideal.map_mono (reduced_le_full A Λ i j))
  let J := (reducedIncidenceIdeal A Λ i j).map φ
  let ψ : Polynomials R m →+* (S ⧸ J) := (Ideal.Quotient.mk J).comp φ
  have hzero : ∀ f ∈ reducedIncidenceIdeal A Λ i j, ψ f = 0 := by
    intro f hf
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ hf)
  have hleft (l : Fin (m+1)) : ψ (leftEquation A l) = 0 := by
    apply hzero
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.subset_span ⟨l, rfl⟩)))
  have hright (l : Fin m) : ψ (reducedRightEquation A Λ l) = 0 := by
    apply hzero
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨l, rfl⟩)))
  let B := A.map (ψ.comp C)
  let L := Λ.map (ψ.comp C)
  let u := fun k => ψ (leftVariable k)
  let v := fun k => ψ (rightVariable k)
  have hu : u ᵥ* B = 0 := by
    ext l
    simpa only [u, B, Matrix.vecMul, dotProduct, Matrix.map_apply,
      RingHom.comp_apply, leftEquation, map_sum, map_mul] using hleft l
  have hv : L *ᵥ (B *ᵥ v) = 0 := by
    ext l
    simpa only [L, B, v, Matrix.mulVec, dotProduct, Matrix.map_apply,
      RingHom.comp_apply, reducedRightEquation, rightEquation, map_sum, map_mul]
      using hright l
  have hmap : ψ.mapMatrix (augmentedPolynomialMatrix Λ) = augmentedMatrix u L := by
    ext l k
    refine Fin.cases ?_ (fun l => ?_) l <;> rfl
  have hΓ' : IsUnit (augmentedMatrix u L).det := by
    rw [← hmap, ← RingHom.map_det]
    exact hΓ.map (Ideal.Quotient.mk J)
  have hAv := recover_right_kernel B u v L hΓ' hu hv
  have hr (l : Fin (m+1)) : ψ (rightEquation A l) = 0 := by
    simpa only [B, v, Matrix.mulVec, dotProduct, Matrix.map_apply,
      RingHom.comp_apply, rightEquation, map_sum, map_mul] using congrFun hAv l
  rw [Ideal.map_le_iff_le_comap]
  apply sup_le
  · apply sup_le
    · apply sup_le
      · intro f hf
        exact Ideal.mem_map_of_mem φ (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_sup_left hf)))
      · apply Ideal.span_le.mpr
        rintro _ ⟨l, rfl⟩
        change φ (rightEquation A l) ∈ J
        exact Ideal.Quotient.eq_zero_iff_mem.mp (hr l)
    · intro f hf
      exact Ideal.mem_map_of_mem φ (Ideal.mem_sup_left (Ideal.mem_sup_right hf))
  · intro f hf
    exact Ideal.mem_map_of_mem φ (Ideal.mem_sup_right hf)


/-- Additional equations preserve the exact localized ideal equality. -/
theorem mapped_cutIdeals_eq {S : Type*} [CommRing S]
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (Λ : Matrix (Fin m) (Fin (m+1)) R) (i j : Fin (m+1))
    (φ : Polynomials R m →+* S)
    (hΓ : IsUnit (φ (augmentedPolynomialMatrix Λ).det))
    (J : Ideal (Polynomials R m)) :
    (incidenceIdeal A i j ⊔ J).map φ =
      (reducedIncidenceIdeal A Λ i j ⊔ J).map φ := by
  rw [Ideal.map_sup, Ideal.map_sup, mapped_incidenceIdeal_eq_reduced A Λ i j φ hΓ]

/-- The actual reduced and full cut quotient rings are isomorphic wherever
the block determinant is invertible. -/
def mappedReducedEquivFull {S : Type*} [CommRing S]
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (Λ : Matrix (Fin m) (Fin (m+1)) R) (i j : Fin (m+1))
    (φ : Polynomials R m →+* S)
    (hΓ : IsUnit (φ (augmentedPolynomialMatrix Λ).det))
    (J : Ideal (Polynomials R m)) :
    (S ⧸ (reducedIncidenceIdeal A Λ i j ⊔ J).map φ) ≃ₐ[S]
      (S ⧸ (incidenceIdeal A i j ⊔ J).map φ) :=
  Ideal.quotientEquivAlgOfEq S (mapped_cutIdeals_eq A Λ i j φ hΓ J).symm

/-- At a prime where the actual block determinant is nonzero, the localized
full and reduced cut ideals agree. The required unit is derived from the
localization rather than assumed. -/
theorem atPrime_cutIdeals_eq
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (Λ : Matrix (Fin m) (Fin (m+1)) R) (i j : Fin (m+1))
    (p : Ideal (Polynomials R m)) [p.IsPrime]
    (hΓ : (augmentedPolynomialMatrix Λ).det ∉ p)
    (J : Ideal (Polynomials R m)) :
    (incidenceIdeal A i j ⊔ J).map (algebraMap _ (Localization.AtPrime p)) =
      (reducedIncidenceIdeal A Λ i j ⊔ J).map (algebraMap _ (Localization.AtPrime p)) :=
  mapped_cutIdeals_eq A Λ i j _
    (IsLocalization.map_units (M := p.primeCompl) (Localization.AtPrime p)
      ⟨(augmentedPolynomialMatrix Λ).det, hΓ⟩) J

end Sheshadri.KernelReducedIncidenceAlgebra
