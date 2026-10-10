/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.DeterminantDifferential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.DualNumber

/-!
# Actual kernel lines from a nonzero cofactor

A nonzero (m-1)-minor makes the selected coordinate injective on the
right kernel. A normalized adjugate column consequently spans that kernel;
transposition gives the left kernel. No kernel-line hypotheses or geometric
provider axioms occur in these theorems.
-/

namespace Sheshadri

open Matrix
open scoped BigOperators

section Ring

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The deleted-coordinate kernel criterion over arbitrary rings, including
dual numbers and local rings with nilpotents. -/
theorem kernel_zero_of_unit_minor
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (hminor : IsUnit (A.submatrix j.succAbove i.succAbove).det)
    (w : Fin (m+1) → R) (hw : A *ᵥ w = 0) (hi : w i = 0) : w = 0 := by
  let P := A.submatrix j.succAbove i.succAbove
  let w' : Fin m → R := fun k => w (i.succAbove k)
  have hsmall : P *ᵥ w' = 0 := by
    ext k
    have hk := congrFun hw (j.succAbove k)
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hk ⊢
    rw [Fin.sum_univ_succAbove _ i] at hk
    simpa only [hi, mul_zero, zero_add, P, w', Matrix.submatrix_apply] using hk
  have hw' : w' = 0 := by
    have h := congrArg (fun z => P⁻¹ *ᵥ z) hsmall
    simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P hminor,
      Matrix.one_mulVec, Matrix.mulVec_zero] using h
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨l, rfl⟩
  · exact hi
  · exact congrFun hw' l

/-- A unit cofactor has a unit complementary minor. -/
theorem unit_minor_of_unit_adjugate_entry
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (ha : IsUnit (A.adjugate i j)) :
    IsUnit (A.submatrix j.succAbove i.succAbove).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at ha
  exact isUnit_of_mul_isUnit_right ha

/-- Normalized right kernel line over a ring with a unit cofactor. -/
theorem right_kernel_line_of_unit_adjugate_entry
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (hdet : A.det = 0) (ha : IsUnit (A.adjugate i j)) :
    ∃ v : Fin (m+1) → R,
      v i = 1 ∧ A *ᵥ v = 0 ∧
      ∀ w : Fin (m+1) → R, A *ᵥ w = 0 → w = w i • v := by
  have hminor := unit_minor_of_unit_adjugate_entry A i j ha
  obtain ⟨a, ha⟩ := ha
  let col : Fin (m+1) → R := fun k => A.adjugate k j
  let v : Fin (m+1) → R := (↑(a⁻¹) : R) • col
  have hcol : A *ᵥ col = 0 := by
    ext k
    have h := congrArg (fun M : Matrix (Fin (m+1)) (Fin (m+1)) R => M k j)
      (Matrix.mul_adjugate A)
    simpa only [hdet, zero_smul, Matrix.zero_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Pi.zero_apply, col] using h
  have hv : v i = 1 := by
    simp only [v, col, Pi.smul_apply, smul_eq_mul, ← ha, Units.inv_mul]
  have hAv : A *ᵥ v = 0 := by
    simp only [v, Matrix.mulVec_smul, hcol, smul_zero]
  refine ⟨v, hv, hAv, ?_⟩
  intro w hw
  have hz : w - w i • v = 0 := by
    apply kernel_zero_of_unit_minor A i j hminor
    · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hw, hAv, smul_zero, sub_self]
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hv, mul_one, sub_self]
  exact sub_eq_zero.mp hz

/-- Normalized left kernel line over a ring with a unit cofactor. -/
theorem left_kernel_line_of_unit_adjugate_entry
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (hdet : A.det = 0) (ha : IsUnit (A.adjugate i j)) :
    ∃ u : Fin (m+1) → R,
      u j = 1 ∧ u ᵥ* A = 0 ∧
      ∀ w : Fin (m+1) → R, w ᵥ* A = 0 → w = w j • u := by
  have hat : IsUnit (A.transpose.adjugate j i) := by
    rw [← Matrix.adjugate_transpose]
    exact ha
  have hdt : A.transpose.det = 0 := by simpa only [Matrix.det_transpose] using hdet
  simpa only [Matrix.mulVec_transpose] using
    right_kernel_line_of_unit_adjugate_entry A.transpose j i hdt hat

/-- Kernel lines and actual adjugate factorization over any commutative
ring at a unit cofactor. This applies to infinitesimal points over dual numbers.
-/
theorem kernel_lines_and_adjugate_factorization_of_unit
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (hdet : A.det = 0) (ha : IsUnit (A.adjugate i j)) :
    ∃ u v : Fin (m+1) → R,
      u j = 1 ∧ v i = 1 ∧ u ᵥ* A = 0 ∧ A *ᵥ v = 0 ∧
      (∀ w, A *ᵥ w = 0 → w = w i • v) ∧
      (∀ w, w ᵥ* A = 0 → w = w j • u) ∧
      A.adjugate = A.adjugate i j • vecMulVec v u := by
  obtain ⟨v, hv, hAv, hright⟩ := right_kernel_line_of_unit_adjugate_entry A i j hdet ha
  obtain ⟨u, hu, huA, hleft⟩ := left_kernel_line_of_unit_adjugate_entry A i j hdet ha
  refine ⟨u, v, hu, hv, huA, hAv, hright, hleft, ?_⟩
  apply adjugate_factorization_of_kernel_lines A u v i j hdet hv hu
  · intro w hw
    exact ⟨w i, hright w hw⟩
  · intro w hw
    exact ⟨w j, hleft w hw⟩

/-- A kernel vector with a coordinate equal to one forces determinant zero,
over an arbitrary commutative ring. -/
theorem det_eq_zero_of_normalized_right_kernel
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (v : Fin (m+1) → R) (i : Fin (m+1))
    (hv : v i = 1) (hAv : A *ᵥ v = 0) : A.det = 0 := by
  have h := congrArg (fun z => A.adjugate *ᵥ z) hAv
  dsimp only at h
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec_assoc,
    Matrix.one_mulVec, Matrix.mulVec_zero] at h
  simpa only [Pi.smul_apply, smul_eq_mul, hv, mul_one, Pi.zero_apply] using congrFun h i

/-- Adjugate factorization for prescribed normalized kernel vectors. The
determinant-zero condition is derived from the kernel equation, not assumed.
-/
theorem adjugate_factorization_of_unit_cofactor
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (u v : Fin (m+1) → R) (hu : u j = 1) (hv : v i = 1)
    (huA : u ᵥ* A = 0) (hAv : A *ᵥ v = 0)
    (ha : IsUnit (A.adjugate i j)) :
    A.adjugate = A.adjugate i j • vecMulVec v u := by
  have hdet := det_eq_zero_of_normalized_right_kernel A v i hv hAv
  obtain ⟨u₀, v₀, hu₀, hv₀, hu₀A, hAv₀, hright, hleft, hadj⟩ :=
    kernel_lines_and_adjugate_factorization_of_unit A i j hdet ha
  have hvv : v = v₀ := by simpa only [hv, one_smul] using hright v hAv
  have huu : u = u₀ := by simpa only [hu, one_smul] using hleft u huA
  simpa only [hvv, huu] using hadj

end Ring

section DualNumbers

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- The constant term of a dual-number kernel pairing. -/
theorem dual_pairing_fst (u v : ι → DualNumber R) (H : Matrix ι ι R) :
    (u ⬝ᵥ ((H.map TrivSqZeroExt.inl) *ᵥ v)).fst =
      (fun i => (u i).fst) ⬝ᵥ (H *ᵥ (fun i => (v i).fst)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, TrivSqZeroExt.fst_sum,
    TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl]

/-- The infinitesimal term differentiates the two kernel vectors. -/
theorem dual_pairing_snd (u v : ι → DualNumber R) (H : Matrix ι ι R) :
    (u ⬝ᵥ ((H.map TrivSqZeroExt.inl) *ᵥ v)).snd =
      (fun i => (u i).snd) ⬝ᵥ (H *ᵥ (fun i => (v i).fst)) +
      (fun i => (u i).fst) ⬝ᵥ (H *ᵥ (fun i => (v i).snd)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, TrivSqZeroExt.snd_sum,
    TrivSqZeroExt.fst_sum, DualNumber.snd_mul, TrivSqZeroExt.fst_mul,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, zero_mul, add_zero,
    Finset.sum_add_distrib]
  ring

/-- Along normalized infinitesimal kernel lifts, a vanishing base polar
equation eliminates the derivative of the adjugate scalar. This proves the
first-order conormal/flag comparison needed in the isolatedness argument.
-/
theorem dual_adjugate_pairing_snd {m : ℕ}
    (A : Matrix (Fin (m+1)) (Fin (m+1)) (DualNumber R))
    (i j : Fin (m+1)) (u v : Fin (m+1) → DualNumber R)
    (H : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (hu : u j = 1) (hv : v i = 1)
    (huA : u ᵥ* A = 0) (hAv : A *ᵥ v = 0)
    (ha : IsUnit (A.adjugate i j))
    (hflag : (fun k => (u k).fst) ⬝ᵥ (H *ᵥ (fun k => (v k).fst)) = 0) :
    (Matrix.trace (A.adjugate * H.map TrivSqZeroExt.inl)).snd =
      (A.adjugate i j).fst *
        ((fun k => (u k).snd) ⬝ᵥ (H *ᵥ (fun k => (v k).fst)) +
          (fun k => (u k).fst) ⬝ᵥ (H *ᵥ (fun k => (v k).snd))) := by
  have hadj := adjugate_factorization_of_unit_cofactor A i j u v hu hv huA hAv ha
  have hp := adjugate_trace_pairing A (H.map TrivSqZeroExt.inl) u v _ hadj
  have hs := congrArg TrivSqZeroExt.snd hp
  rw [DualNumber.snd_mul, dual_pairing_fst, dual_pairing_snd,
    hflag, mul_zero, add_zero] at hs
  exact hs

end DualNumbers

variable {F : Type*} [Field F] {m : ℕ}

/-- Deleting one column loses no kernel information when that coordinate
vanishes and the complementary minor is invertible. -/
theorem kernel_zero_of_minor_and_coordinate
    (A : Matrix (Fin (m+1)) (Fin (m+1)) F) (i j : Fin (m+1))
    (hminor : (A.submatrix j.succAbove i.succAbove).det ≠ 0)
    (w : Fin (m+1) → F) (hw : A *ᵥ w = 0) (hi : w i = 0) : w = 0 := by
  let P := A.submatrix j.succAbove i.succAbove
  let w' : Fin m → F := fun k => w (i.succAbove k)
  have hsmall : P *ᵥ w' = 0 := by
    ext k
    have hk := congrFun hw (j.succAbove k)
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at hk ⊢
    rw [Fin.sum_univ_succAbove _ i] at hk
    simpa only [hi, mul_zero, zero_add, P, w', Matrix.submatrix_apply] using hk
  have hP : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr
    (isUnit_iff_ne_zero.mpr hminor)
  have hinj : Function.Injective P.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hP
  have hw' : w' = 0 := hinj (hsmall.trans (Matrix.mulVec_zero P).symm)
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl | ⟨l, rfl⟩
  · exact hi
  · exact congrFun hw' l

/-- A nonzero cofactor supplies the required nonzero complementary minor. -/
theorem minor_ne_zero_of_adjugate_entry
    (A : Matrix (Fin (m+1)) (Fin (m+1)) F) (i j : Fin (m+1))
    (ha : A.adjugate i j ≠ 0) :
    (A.submatrix j.succAbove i.succAbove).det ≠ 0 := by
  intro hz
  apply ha
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, hz, mul_zero]

/-- The normalized adjugate column is a kernel generator; every right
kernel vector is its unique multiple determined by the selected coordinate.
-/
theorem right_kernel_line_of_adjugate_entry
    (A : Matrix (Fin (m+1)) (Fin (m+1)) F) (i j : Fin (m+1))
    (hdet : A.det = 0) (ha : A.adjugate i j ≠ 0) :
    ∃ v : Fin (m+1) → F,
      v i = 1 ∧ A *ᵥ v = 0 ∧
      ∀ w : Fin (m+1) → F, A *ᵥ w = 0 → w = w i • v := by
  let col : Fin (m+1) → F := fun k => A.adjugate k j
  let v : Fin (m+1) → F := (A.adjugate i j)⁻¹ • col
  have hcol : A *ᵥ col = 0 := by
    ext k
    have h := congrArg (fun M : Matrix (Fin (m+1)) (Fin (m+1)) F => M k j)
      (Matrix.mul_adjugate A)
    simpa only [hdet, zero_smul, Matrix.zero_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Pi.zero_apply, col] using h
  have hv : v i = 1 := by
    simp only [v, col, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ ha
  have hAv : A *ᵥ v = 0 := by
    simp only [v, Matrix.mulVec_smul, hcol, smul_zero]
  refine ⟨v, hv, hAv, ?_⟩
  intro w hw
  have hz : w - w i • v = 0 := by
    apply kernel_zero_of_minor_and_coordinate A i j
      (minor_ne_zero_of_adjugate_entry A i j ha)
    · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hw, hAv, smul_zero, sub_self]
    · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hv, mul_one, sub_self]
  exact sub_eq_zero.mp hz

/-- A normalized left kernel generator and its unique-multiple property. -/
theorem left_kernel_line_of_adjugate_entry
    (A : Matrix (Fin (m+1)) (Fin (m+1)) F) (i j : Fin (m+1))
    (hdet : A.det = 0) (ha : A.adjugate i j ≠ 0) :
    ∃ u : Fin (m+1) → F,
      u j = 1 ∧ u ᵥ* A = 0 ∧
      ∀ w : Fin (m+1) → F, w ᵥ* A = 0 → w = w j • u := by
  have hat : A.transpose.adjugate j i ≠ 0 := by
    rw [← Matrix.adjugate_transpose]
    exact ha
  have hdt : A.transpose.det = 0 := by simpa only [Matrix.det_transpose] using hdet
  simpa only [Matrix.mulVec_transpose] using
    right_kernel_line_of_adjugate_entry A.transpose j i hdt hat

/-- The adjugate factorization, with existence and uniqueness of normalized
left and right kernels all proved from one nonzero cofactor. -/
theorem kernel_lines_and_adjugate_factorization
    (A : Matrix (Fin (m+1)) (Fin (m+1)) F) (i j : Fin (m+1))
    (hdet : A.det = 0) (ha : A.adjugate i j ≠ 0) :
    ∃ u v : Fin (m+1) → F,
      u j = 1 ∧ v i = 1 ∧ u ᵥ* A = 0 ∧ A *ᵥ v = 0 ∧
      (∀ w, A *ᵥ w = 0 → w = w i • v) ∧
      (∀ w, w ᵥ* A = 0 → w = w j • u) ∧
      A.adjugate = A.adjugate i j • vecMulVec v u := by
  obtain ⟨v, hv, hAv, hright⟩ := right_kernel_line_of_adjugate_entry A i j hdet ha
  obtain ⟨u, hu, huA, hleft⟩ := left_kernel_line_of_adjugate_entry A i j hdet ha
  refine ⟨u, v, hu, hv, huA, hAv, hright, hleft, ?_⟩
  apply adjugate_factorization_of_kernel_lines A u v i j hdet hv hu
  · intro w hw
    exact ⟨w i, hright w hw⟩
  · intro w hw
    exact ⟨w j, hleft w hw⟩

/-- An actual smooth determinant point has normalized kernel lifts and the
conormal pairing identity in every algebraic tangent direction. No kernel
description or adjugate factorization is assumed.
-/
theorem exists_normalized_conormal_lift
    {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (φ : R →+* F)
    (D : Derivation K R R)
    (hdet : φ A.det = 0) (hsmooth : φ (D A.det) ≠ 0) :
    ∃ (i j : Fin (m+1)) (u v : Fin (m+1) → F) (a : F),
      u j = 1 ∧ v i = 1 ∧ a ≠ 0 ∧
      u ᵥ* A.map φ = 0 ∧ A.map φ *ᵥ v = 0 ∧
      (∀ w, A.map φ *ᵥ w = 0 → w = w i • v) ∧
      (∀ w, w ᵥ* A.map φ = 0 → w = w j • u) ∧
      ∀ E : Derivation K R R,
        φ (E A.det) = a * (u ⬝ᵥ (A.map (fun x => φ (E x)) *ᵥ v)) := by
  obtain ⟨i, j, hij⟩ := exists_adjugate_entry_ne_zero_eval D A φ hsmooth
  have hd : (A.map φ).det = 0 := by
    exact (φ.map_det A).symm.trans hdet
  obtain ⟨u, v, hu, hv, huA, hAv, hright, hleft, hadj⟩ :=
    kernel_lines_and_adjugate_factorization (A.map φ) i j hd hij
  refine ⟨i, j, u, v, (A.map φ).adjugate i j, hu, hv, hij,
    huA, hAv, hright, hleft, ?_⟩
  intro E
  exact derivation_det_eval_pairing E A φ u v _ hadj

end Sheshadri
