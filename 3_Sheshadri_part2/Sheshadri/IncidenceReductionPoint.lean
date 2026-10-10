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
import Sheshadri.NestedPolynomialLocalPoint

/-! Common kernel reductions supply the actual local unit determinant. -/
noncomputable section
namespace Sheshadri.IncidenceReductionPoint
open Matrix MvPolynomial KernelReducedIncidenceAlgebra
set_option synthInstance.maxHeartbeats 200000

variable {K Z : Type*} [Field K] {m : ℕ}

theorem augmentedMatrix_det_ne_zero (u : Fin (m+1) → K)
    (Λ : Matrix (Fin m) (Fin (m+1)) K)
    (hΛ : ∀ z, u ⬝ᵥ z = 0 → Λ *ᵥ z = 0 → z = 0) :
    (augmentedMatrix u Λ).det ≠ 0 := by
  have hker (z : Fin (m+1) → K) (hz : augmentedMatrix u Λ *ᵥ z = 0) : z = 0 := by
    apply hΛ z
    · exact congrFun hz 0
    · ext k
      exact congrFun hz k.succ
  have hinj : Function.Injective (Matrix.mulVec (augmentedMatrix u Λ)) := by
    intro z w hzw
    apply sub_eq_zero.mp
    apply hker
    rw [Matrix.mulVec_sub, hzw, sub_self]
  exact isUnit_iff_ne_zero.mp (Matrix.isUnit_iff_isUnit_det _ |>.mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj))

theorem evaluation_augmentedPolynomialMatrix (p : Z → K)
    (u v : Fin (m+1) → K) (Λ : Matrix (Fin m) (Fin (m+1)) K) :
    NestedPolynomialLocalPoint.evaluation p (Sum.elim u v)
      (augmentedPolynomialMatrix (Λ.map (C : K →+* MvPolynomial Z K))).det =
        (augmentedMatrix u Λ).det := by
  rw [RingHom.map_det]
  congr 1
  ext a b
  refine Fin.cases ?_ (fun k => ?_) a <;>
    simp [augmentedPolynomialMatrix, augmentedMatrix, KernelIncidenceAlgebra.leftVariable,
      NestedPolynomialLocalPoint.evaluation]

theorem evaluation_augmentedPolynomialMatrix_ne_zero (p : Z → K)
    (u v : Fin (m+1) → K) (Λ : Matrix (Fin m) (Fin (m+1)) K)
    (hΛ : ∀ z, u ⬝ᵥ z = 0 → Λ *ᵥ z = 0 → z = 0) :
    NestedPolynomialLocalPoint.evaluation p (Sum.elim u v)
      (augmentedPolynomialMatrix (Λ.map (C : K →+* MvPolynomial Z K))).det ≠ 0 := by
  rw [evaluation_augmentedPolynomialMatrix]
  exact augmentedMatrix_det_ne_zero u Λ hΛ

end Sheshadri.IncidenceReductionPoint
