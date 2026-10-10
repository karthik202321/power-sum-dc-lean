/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.IncidenceSystem
import Sheshadri.MultiProjectiveBezout

/-!
# The actual Jacobian rows of the incidence equations

All derivatives below use the formal partial derivatives of the actual global
polynomials.  The formulas separate the `x`, `u`, and `v` tangent directions and
can be used directly in the `SimpleInCharts` premise of multiprojective Bezout.
No rank, transversality, or isolatedness assertion is assumed in this file.
-/

noncomputable section

namespace Sheshadri.IncidenceDifferential

open MvPolynomial Incidence MultiProjective Matrix
open scoped Matrix

section Calculus
variable {σ : Type*} [Fintype σ]

@[simp] theorem directional_C (p v : σ → ℂ) (c : ℂ) :
    directional (C c) p v = 0 := by
  classical
  simp [directional]

@[simp] theorem directional_X (p v : σ → ℂ) (j : σ) :
    directional (X j) p v = v j := by
  classical
  simp [directional, Pi.single_apply]

@[simp] theorem directional_add (p v : σ → ℂ) (f g : MvPolynomial σ ℂ) :
    directional (f + g) p v = directional f p v + directional g p v := by
  classical
  simp [directional, add_mul, Finset.sum_add_distrib]

@[simp] theorem directional_mul (p v : σ → ℂ) (f g : MvPolynomial σ ℂ) :
    directional (f * g) p v =
      directional f p v * eval p g + eval p f * directional g p v := by
  classical
  simp only [directional, pderiv_mul, map_add, map_mul, add_mul,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ac_rfl

@[simp] theorem directional_sum {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ ℂ) (p v : σ → ℂ) :
    directional (∑ i ∈ s, f i) p v = ∑ i ∈ s, directional (f i) p v := by
  classical
  simp only [directional, map_sum, Finset.sum_mul]
  exact Finset.sum_comm

end Calculus

variable {n m : ℕ}

@[simp] theorem directional_pencilEntry (A : PencilCoefficients n m ℂ)
    (x dx : Fin (n + 1) → ℂ) (u v du dv : Fin m → ℂ) (a b : Fin m) :
    directional (pencilEntry A a b) (ordinaryAssignment x u v)
      (ordinaryAssignment dx du dv) = pencil A dx a b := by
  simp [pencilEntry, ordinaryAssignment, pencil]

theorem directional_leftEquation (A : PencilCoefficients n m ℂ)
    (x dx : Fin (n + 1) → ℂ) (u v du dv : Fin m → ℂ) (j : Fin m) :
    directional (leftEquation A j) (ordinaryAssignment x u v)
      (ordinaryAssignment dx du dv) =
        (du ᵥ* pencil A x) j + (u ᵥ* pencil A dx) j := by
  simp [leftEquation, ordinaryAssignment, Matrix.vecMul, dotProduct,
    Finset.sum_add_distrib]

theorem directional_rightEquation (A : PencilCoefficients n m ℂ)
    (Λ : Matrix (Fin (m - 1)) (Fin m) ℂ)
    (x dx : Fin (n + 1) → ℂ) (u v du dv : Fin m → ℂ) (i : Fin (m - 1)) :
    directional (rightEquation A Λ i) (ordinaryAssignment x u v)
      (ordinaryAssignment dx du dv) =
        (Λ *ᵥ ((pencil A dx *ᵥ v) + (pencil A x *ᵥ dv))) i := by
  simp [rightEquation, ordinaryAssignment, Matrix.mulVec, dotProduct,
    Finset.sum_add_distrib, mul_add]

theorem directional_kernelPairing (A : PencilCoefficients n m ℂ)
    (x dx : Fin (n + 1) → ℂ) (u v du dv : Fin m → ℂ) (i : Fin (n + 1)) :
    directional (kernelPairing A i) (ordinaryAssignment x u v)
      (ordinaryAssignment dx du dv) =
        du ⬝ᵥ (A i *ᵥ v) + u ⬝ᵥ (A i *ᵥ dv) := by
  simp [kernelPairing, ordinaryAssignment, Matrix.mulVec, dotProduct,
    Finset.sum_add_distrib, Finset.mul_sum, add_mul, mul_assoc]

theorem directional_dualEquation (A : PencilCoefficients n m ℂ)
    (ℓ : Fin (n + 1) → ℂ) (x dx : Fin (n + 1) → ℂ) (u v du dv : Fin m → ℂ) :
    directional (dualEquation A ℓ) (ordinaryAssignment x u v)
      (ordinaryAssignment dx du dv) =
        ∑ i, ℓ i * (du ⬝ᵥ (A i *ᵥ v) + u ⬝ᵥ (A i *ᵥ dv)) := by
  simp [dualEquation, directional_kernelPairing]

@[simp] theorem directional_primalEquation (M : Fin (n + 1) → ℂ)
    (x dx : Fin (n + 1) → ℂ) (u v du dv : Fin m → ℂ) :
    directional (primalEquation M) (ordinaryAssignment x u v)
      (ordinaryAssignment dx du dv) = ∑ i, M i * dx i := by
  simp [primalEquation, ordinaryAssignment]

@[simp] theorem directional_symmetricPencilEntry (A : PencilCoefficients n m ℂ)
    (x dx : Fin (n + 1) → ℂ) (v dv : Fin m → ℂ) (a b : Fin m) :
    directional (symmetricPencilEntry A a b) (symmetricAssignment x v)
      (symmetricAssignment dx dv) = pencil A dx a b := by
  simp [symmetricPencilEntry, symmetricAssignment, pencil]

theorem directional_symmetricKernelEquation (A : PencilCoefficients n m ℂ)
    (x dx : Fin (n + 1) → ℂ) (v dv : Fin m → ℂ) (a : Fin m) :
    directional (symmetricKernelEquation A a) (symmetricAssignment x v)
      (symmetricAssignment dx dv) =
        (pencil A dx *ᵥ v) a + (pencil A x *ᵥ dv) a := by
  simp [symmetricKernelEquation, symmetricAssignment, Matrix.mulVec, dotProduct,
    Finset.sum_add_distrib]

theorem directional_symmetricPairing (A : PencilCoefficients n m ℂ)
    (x dx : Fin (n + 1) → ℂ) (v dv : Fin m → ℂ) (i : Fin (n + 1)) :
    directional (symmetricPairing A i) (symmetricAssignment x v)
      (symmetricAssignment dx dv) =
        dv ⬝ᵥ (A i *ᵥ v) + v ⬝ᵥ (A i *ᵥ dv) := by
  simp [symmetricPairing, symmetricAssignment, Matrix.mulVec, dotProduct,
    Finset.sum_add_distrib, Finset.mul_sum, add_mul, mul_assoc]

theorem directional_symmetricDualEquation (A : PencilCoefficients n m ℂ)
    (ℓ : Fin (n + 1) → ℂ) (x dx : Fin (n + 1) → ℂ) (v dv : Fin m → ℂ) :
    directional (symmetricDualEquation A ℓ) (symmetricAssignment x v)
      (symmetricAssignment dx dv) =
        ∑ i, ℓ i * (dv ⬝ᵥ (A i *ᵥ v) + v ⬝ᵥ (A i *ᵥ dv)) := by
  simp [symmetricDualEquation, directional_symmetricPairing]

@[simp] theorem directional_symmetricPrimalEquation (M : Fin (n + 1) → ℂ)
    (x dx : Fin (n + 1) → ℂ) (v dv : Fin m → ℂ) :
    directional (symmetricPrimalEquation M) (symmetricAssignment x v)
      (symmetricAssignment dx dv) = ∑ i, M i * dx i := by
  simp [symmetricPrimalEquation, symmetricAssignment]

/-- The full formal Jacobian kernel is exactly this explicit system of matrix
and flag equations. This is an equivalence, not a transversality assumption. -/
theorem ordinarySystem_directional_zero_iff (A : PencilCoefficients n m ℂ)
    (Λ : Matrix (Fin (m - 1)) (Fin m) ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (x dx : Fin (n + 1) → ℂ) (u v du dv : Fin m → ℂ) :
    (∀ e, directional (ordinarySystem A Λ flags M e) (ordinaryAssignment x u v)
      (ordinaryAssignment dx du dv) = 0) ↔
      (du ᵥ* pencil A x + u ᵥ* pencil A dx = 0 ∧
        Λ *ᵥ ((pencil A dx *ᵥ v) + (pencil A x *ᵥ dv)) = 0 ∧
        (∀ t, ∑ i, flags t i * (du ⬝ᵥ (A i *ᵥ v) + u ⬝ᵥ (A i *ᵥ dv)) = 0) ∧
        ∑ i, M i * dx i = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext j
      simpa [ordinarySystem, directional_leftEquation] using h (Sum.inl j)
    · funext i
      simpa [ordinarySystem, directional_rightEquation] using h (Sum.inr (Sum.inl i))
    · intro t
      simpa [ordinarySystem, directional_dualEquation] using
        h (Sum.inr (Sum.inr (Sum.inl t)))
    · simpa [ordinarySystem] using h (Sum.inr (Sum.inr (Sum.inr ())))
  · rintro ⟨hl, hr, hd, hp⟩ e
    rcases e with j | (i | (t | last))
    · simpa [ordinarySystem, directional_leftEquation] using congrFun hl j
    · simpa [ordinarySystem, directional_rightEquation] using congrFun hr i
    · simpa [ordinarySystem, directional_dualEquation] using hd t
    · simpa [ordinarySystem] using hp

theorem symmetricSystem_directional_zero_iff (A : PencilCoefficients n m ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (x dx : Fin (n + 1) → ℂ) (v dv : Fin m → ℂ) :
    (∀ e, directional (symmetricSystem A flags M e) (symmetricAssignment x v)
      (symmetricAssignment dx dv) = 0) ↔
      (pencil A dx *ᵥ v + pencil A x *ᵥ dv = 0 ∧
        (∀ t, ∑ i, flags t i * (dv ⬝ᵥ (A i *ᵥ v) + v ⬝ᵥ (A i *ᵥ dv)) = 0) ∧
        ∑ i, M i * dx i = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · funext a
      simpa [symmetricSystem, directional_symmetricKernelEquation] using h (Sum.inl a)
    · intro t
      simpa [symmetricSystem, directional_symmetricDualEquation] using h (Sum.inr (Sum.inl t))
    · simpa [symmetricSystem] using h (Sum.inr (Sum.inr ()))
  · rintro ⟨hk, hd, hp⟩ e
    rcases e with a | (t | last)
    · simpa [symmetricSystem, directional_symmetricKernelEquation] using congrFun hk a
    · simpa [symmetricSystem, directional_symmetricDualEquation] using hd t
    · simpa [symmetricSystem] using hp

end Sheshadri.IncidenceDifferential
