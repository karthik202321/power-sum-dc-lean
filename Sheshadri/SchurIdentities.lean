/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

/-!
# Actual Schur-coordinate identities (paper, Section 4.3, Step 5(ii))

These are identities over an arbitrary commutative ring, including a local ring
with nilpotents. `C` is a two-sided inverse of the leading block `B`. No geometric
shortcut, reducedness hypothesis, or equality only of zero sets is used.
-/

namespace Sheshadri

open Matrix

section
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
variable (B C : Matrix ι ι R) (r c u v : ι → R) (s : R)

/-- The first left-kernel equations become `p B`. -/
theorem schur_left_top (hCB : C * B = 1) :
    u ᵥ* B + r = (u + r ᵥ* C) ᵥ* B := by
  rw [add_vecMul, vecMul_vecMul, hCB, vecMul_one]

omit [DecidableEq ι] in
/-- The last left-kernel equation becomes `p · c + g`. -/
theorem schur_left_last :
    u ⬝ᵥ c + s = (u + r ᵥ* C) ⬝ᵥ c + (s - r ⬝ᵥ (C *ᵥ c)) := by
  rw [add_dotProduct, ← dotProduct_mulVec]
  ring

/-- The upper right-kernel block becomes `B z`. -/
theorem schur_right_top (hBC : B * C = 1) :
    B *ᵥ v + c = B *ᵥ (v + C *ᵥ c) := by
  rw [mulVec_add, mulVec_mulVec, hBC, one_mulVec]

omit [DecidableEq ι] in
/-- The last right-kernel equation becomes `r · z + g`. -/
theorem schur_right_last :
    r ⬝ᵥ v + s = r ⬝ᵥ (v + C *ᵥ c) + (s - r ⬝ᵥ (C *ᵥ c)) := by
  rw [dotProduct_add]
  ring

/-- The reduced right block, before any equation is imposed.
`L` and `lam` are the first columns and last column of Λ respectively. -/
theorem schur_reduced_right {κ : Type*} (L : Matrix κ ι R) (lam : κ → R)
    (hBC : B * C = 1) :
    L *ᵥ (B *ᵥ v + c) + (r ⬝ᵥ v + s) • lam =
      (L * B + vecMulVec lam r) *ᵥ (v + C *ᵥ c) +
        (s - r ⬝ᵥ (C *ᵥ c)) • lam := by
  rw [schur_right_top B C c v hBC,
    schur_right_last C r c v s, mulVec_mulVec, add_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hout (z : ι → R) : (vecMulVec lam r *ᵥ z) i = lam i * (r ⬝ᵥ z) := by
    change (∑ j, lam i * r j * z j) = lam i * ∑ j, r j * z j
    simp only [Finset.mul_sum, mul_assoc]
  rw [hout]
  ring

end
end Sheshadri
