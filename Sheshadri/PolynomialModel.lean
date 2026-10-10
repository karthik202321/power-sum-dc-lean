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
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! A literal affine determinant model shared by the explicit-lift and tangent
arguments. The homogeneous incidence chart is x₀=1, so no homogenization or
projective conormal assumption is required for the exact case. -/

noncomputable section
namespace Sheshadri.PolynomialModel
open Matrix MvPolynomial Incidence
variable {K : Type*} [CommRing K] {n m : ℕ}

def affinePencil (A : PencilCoefficients n m K) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin n) K) :=
  fun a b => C (A 0 a b) + ∑ i : Fin n, C (A i.succ a b) * X i

def determinant (A : PencilCoefficients n m K) : MvPolynomial (Fin n) K :=
  (affinePencil A).det

def fermat (n : ℕ) : MvPolynomial (Fin n) K := ∑ i, X i ^ n

def ExactRepresentation (n m : ℕ) (K : Type*) [CommRing K] : Prop :=
  ∃ A : PencilCoefficients n m K, determinant A = fermat n

def SymmetricExactRepresentation (n m : ℕ) (K : Type*) [CommRing K] : Prop :=
  ∃ A : PencilCoefficients n m K, (∀ i, (A i).transpose = A i) ∧
    determinant A = fermat n

theorem eval_affinePencil (A : PencilCoefficients n m K) (x : Fin (n + 1) → K)
    (hx : x 0 = 1) :
    (affinePencil A).map (eval (fun i => x i.succ)) = pencil A x := by
  ext a b
  simp [affinePencil, pencil, Fin.sum_univ_succ, hx]

theorem eval_determinant (A : PencilCoefficients n m K) (x : Fin (n + 1) → K)
    (hx : x 0 = 1) :
    eval (fun i => x i.succ) (determinant A) = (pencil A x).det := by
  rw [determinant, RingHom.map_det]
  change ((affinePencil A).map (eval (fun i => x i.succ))).det = _
  rw [eval_affinePencil A x hx]

theorem pderiv_affinePencil (A : PencilCoefficients n m K)
    (i : Fin n) (a b : Fin m) :
    pderiv i (affinePencil A a b) = C (A i.succ a b) := by
  simp [affinePencil, pderiv_X, pderiv_mul, Pi.single_apply, mul_ite]

theorem eval_pderiv_affinePencil (A : PencilCoefficients n m K)
    (x : Fin n → K) (i : Fin n) :
    (affinePencil A).map (fun f => eval x (pderiv i f)) = A i.succ := by
  ext a b
  simp [Matrix.map_apply, pderiv_affinePencil]

end Sheshadri.PolynomialModel
