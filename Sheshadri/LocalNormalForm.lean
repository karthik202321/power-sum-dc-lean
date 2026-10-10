/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SchurIdentities
import Sheshadri.IdealReduction

/-! The paper's equation (7), starting from the actual unrecentered block
equations. The block inverse and the reduced-right inverse are explicit inputs.
Everything else in this ideal equality is proved. -/

namespace Sheshadri
open Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Ordinary Schur normal form for the combined left and reduced-right ideal.
Here `L` is Λ_top, `lam` its last column, and `M = Λ [B;r]`. -/
theorem ordinary_local_normal_form
    (B C L Minv : Matrix ι ι R) (r c u v lam : ι → R) (s : R)
    (hBC : B * C = 1) (hCB : C * B = 1)
    (hM : Minv * (L * B + vecMulVec lam r) = 1) :
    tripleIdeal (u ᵥ* B + r) (u ⬝ᵥ c + s)
      (fun i => (L *ᵥ (B *ᵥ v + c)) i + (r ⬝ᵥ v + s) * lam i) =
    tripleIdeal (u + r ᵥ* C) (s - r ⬝ᵥ (C *ᵥ c)) (v + C *ᵥ c) := by
  have hright :
      (fun i => (L *ᵥ (B *ᵥ v + c)) i + (r ⬝ᵥ v + s) * lam i) =
      (fun i => ((L * B + vecMulVec lam r) *ᵥ (v + C *ᵥ c)) i +
        (s - r ⬝ᵥ (C *ᵥ c)) * lam i) := by
    exact schur_reduced_right B C r c v s L lam hBC
  rw [schur_left_top B C r u hCB, schur_left_last C r c u s, hright]
  exact ordinary_kernel_ideal B C (L * B + vecMulVec lam r) Minv
    (u + r ᵥ* C) c (v + C *ᵥ c) lam (s - r ⬝ᵥ (C *ᵥ c)) hBC hM

/-- Single-kernel normal form. Symmetry is needed to identify this incidence
with the symmetric determinant's conormal, but not for this algebraic identity. -/
theorem single_kernel_local_normal_form
    (B C : Matrix ι ι R) (r c v : ι → R) (s : R)
    (hBC : B * C = 1) (hCB : C * B = 1) :
    equationIdeal (B *ᵥ v + c) ⊔ Ideal.span {r ⬝ᵥ v + s} =
      equationIdeal (v + C *ᵥ c) ⊔ Ideal.span {s - r ⬝ᵥ (C *ᵥ c)} := by
  rw [schur_right_top B C c v hBC, schur_right_last C r c v s]
  exact symmetric_kernel_ideal B C (v + C *ᵥ c) r (s - r ⬝ᵥ (C *ᵥ c)) hCB

end Sheshadri
