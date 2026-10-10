/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.AffineIncidenceCharts
import Sheshadri.KernelReducedIncidenceAlgebra
import Sheshadri.PolynomialModel
import Sheshadri.ProjectiveLocalMultiplicity

/-! Literal incidence equations under the proved affine primal-chart map. -/
noncomputable section
namespace Sheshadri.IncidenceAffineEquations
open MvPolynomial Matrix Incidence PolynomialModel AffineIncidenceCharts
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

variable {K : Type*} [CommRing K] {n m : ℕ}

@[simp] theorem dehom_pencilEntry (A : PencilCoefficients n m K) (a b : Fin m) :
    dehom (pencilEntry A a b) = C (affinePencil A a b) := by
  simp [pencilEntry, affinePencil, Fin.sum_univ_succ]

@[simp] theorem dehom_leftEquation (A : PencilCoefficients n (m+1) K) (j : Fin (m+1)) :
    dehom (Incidence.leftEquation A j) =
      KernelIncidenceAlgebra.leftEquation (affinePencil A) j := by
  simp [Incidence.leftEquation, KernelIncidenceAlgebra.leftEquation,
    KernelIncidenceAlgebra.leftVariable]

@[simp] theorem dehom_rightEquation (A : PencilCoefficients n (m+1) K)
    (Λ : Matrix (Fin m) (Fin (m+1)) K) (i : Fin m) :
    dehom (Incidence.rightEquation A Λ i) =
      KernelReducedIncidenceAlgebra.reducedRightEquation (affinePencil A) (Λ.map C) i := by
  simp [Incidence.rightEquation, KernelReducedIncidenceAlgebra.reducedRightEquation,
    KernelIncidenceAlgebra.rightEquation, KernelIncidenceAlgebra.rightVariable]

@[simp] theorem dehom_kernelPairing (A : PencilCoefficients n (m+1) K)
    (i : Fin (n+1)) :
    dehom (kernelPairing A i) = KernelIncidenceAlgebra.polarEquation ((A i).map C) := by
  simp [kernelPairing, KernelIncidenceAlgebra.polarEquation,
    KernelIncidenceAlgebra.leftVariable, KernelIncidenceAlgebra.rightVariable]

def flagMatrix (A : PencilCoefficients n (m+1) K) (ell : Fin (n+1) → K) :
    Matrix (Fin (m+1)) (Fin (m+1)) (MvPolynomial (Fin n) K) :=
  fun a b => ∑ i, C (ell i) * C (A i a b)

theorem dehom_dualEquation (A : PencilCoefficients n (m+1) K)
    (ell : Fin (n+1) → K) :
    dehom (dualEquation A ell) = KernelIncidenceAlgebra.polarEquation (flagMatrix A ell) := by
  simp only [dualEquation, map_sum, map_mul, dehom_C, dehom_kernelPairing]
  simp only [KernelIncidenceAlgebra.polarEquation, flagMatrix, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul, Matrix.map_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  ring

def primalPolynomial (M : Fin (n+1) → K) : MvPolynomial (Fin n) K :=
  C (M 0) + ∑ i, C (M i.succ) * MvPolynomial.X i

@[simp] theorem dehom_primalEquation (M : Fin (n+1) → K) :
    dehom (T := Fin (m+1) ⊕ Fin (m+1)) (primalEquation (m := m+1) M) =
      C (primalPolynomial M) := by
  simp [primalEquation, primalPolynomial, Fin.sum_univ_succ]

end Sheshadri.IncidenceAffineEquations
