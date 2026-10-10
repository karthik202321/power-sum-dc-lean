/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Invertible
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The determinant equation in the local Schur chart

This file proves, for the actual block matrix, the identity
`det A = det B * (s - r dot (C mulVec c))`.  It then proves equality of
the principal ideals of the determinant and Schur complement, and proves
that invertibility of a matrix over a residue field lifts to invertibility
over the local ring.  All statements are theorems, not geometric axioms.
-/

namespace Sheshadri

open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The matrix with leading block `B`, last column `c`, last row `r`, and
bottom-right entry `s`.  The singleton last index is represented by `Unit`. -/
def schurBlockMatrix (B : Matrix ι ι R) (c r : ι → R) (s : R) :
    Matrix (Sum ι Unit) (Sum ι Unit) R :=
  Matrix.fromBlocks B (fun i _ => c i) (fun _ j => r j) (fun _ _ => s)

/-- The purely algebraic part of the Schur determinant formula.  Proving
the block factorization directly avoids importing unrelated positivity
theory from the more general Mathlib Schur-complement file. -/
theorem det_block_schur {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (D : Matrix κ κ R) [Invertible A] :
    (Matrix.fromBlocks A B C D).det = A.det * (D - C * ⅟ A * B).det := by
  have hfactor : Matrix.fromBlocks A B C D =
      Matrix.fromBlocks 1 0 (C * ⅟ A) 1 *
        Matrix.fromBlocks A 0 0 (D - C * ⅟ A * B) *
          Matrix.fromBlocks 1 (⅟ A * B) 0 1 := by
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, invOf_mul_self,
      Matrix.mul_invOf_cancel_left, Matrix.invOf_mul_cancel_right,
      Matrix.mul_assoc, add_sub_cancel]
  rw [hfactor, Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, Matrix.det_one, one_mul, one_mul, mul_one]

/-- Exact Schur determinant identity over any commutative ring. -/
theorem schurBlockMatrix_det (B C : Matrix ι ι R) (c r : ι → R) (s : R)
    (hCB : C * B = 1) (hBC : B * C = 1) :
    (schurBlockMatrix B c r s).det = B.det * (s - r ⬝ᵥ (C *ᵥ c)) := by
  letI : Invertible B := ⟨C, hCB, hBC⟩
  rw [schurBlockMatrix, det_block_schur]
  congr 1
  rw [Matrix.det_unique]
  change s - ((Matrix.of (fun (_ : Unit) j => r j) * C) *
    Matrix.of (fun i (_ : Unit) => c i)) () () = _
  rw [Matrix.mul_assoc]
  rfl

/-- The determinant and Schur complement generate the same ideal: the
leading determinant is a unit, so its factor does not thicken the scheme. -/
theorem schur_principal_ideal (B C : Matrix ι ι R) (c r : ι → R) (s : R)
    (hCB : C * B = 1) (hBC : B * C = 1) :
    Ideal.span {(schurBlockMatrix B c r s).det} =
      Ideal.span {s - r ⬝ᵥ (C *ᵥ c)} := by
  rw [schurBlockMatrix_det B C c r s hCB hBC]
  exact Ideal.span_singleton_mul_left_unit
    (Matrix.isUnit_det_of_left_inverse hCB) _

/-- Nonzero determinant in the residue field means unit determinant in a
local ring.  This is the precise passage from a nonzero minor at a point
to an invertible block in the local ring. -/
theorem matrix_det_isUnit_of_residue_det_ne_zero [IsLocalRing R]
    (B : Matrix ι ι R)
    (h : (B.map (IsLocalRing.residue R)).det ≠ 0) : IsUnit B.det := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit B.det).mp
  simpa only [RingHom.map_det] using h

/-- An invertible residue matrix has an inverse over the local ring. -/
theorem matrix_isUnit_of_residue_isUnit [IsLocalRing R]
    (B : Matrix ι ι R)
    (h : IsUnit (B.map (IsLocalRing.residue R))) : IsUnit B := by
  apply (Matrix.isUnit_iff_isUnit_det B).mpr
  apply matrix_det_isUnit_of_residue_det_ne_zero B
  exact ((Matrix.isUnit_iff_isUnit_det _).mp h).ne_zero

/-- Explicit two-sided inverse recovered from residue invertibility. -/
theorem matrix_inverse_of_residue_isUnit [IsLocalRing R]
    (B : Matrix ι ι R)
    (h : IsUnit (B.map (IsLocalRing.residue R))) :
    ∃ C : Matrix ι ι R, C * B = 1 ∧ B * C = 1 := by
  obtain ⟨u, hu⟩ := matrix_isUnit_of_residue_isUnit B h
  refine ⟨↑(u⁻¹), ?_, ?_⟩
  · rw [← hu]
    exact u.inv_val
  · rw [← hu]
    exact u.val_inv

end Sheshadri
