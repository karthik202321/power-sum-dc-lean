/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Basic
import Lean.Elab.Tactic.Omega

/-!
# The actual global incidence equations and their multidegrees

The variables of the three projective factors are disjoint.  Multidegrees are
proved with Mathlib's `MvPolynomial.IsWeightedHomogeneous`, using weights in
`ℕ × ℕ × ℕ` (ordinary model) and `ℕ × ℕ` (symmetric model).  These are assertions
about every nonzero monomial coefficient, not labels assigned to equations.

The construction does not assert that the full zero set is zero-dimensional.
The separate local normal-form and transversality arguments are needed for that.
-/

noncomputable section

namespace Sheshadri.Incidence

open Finset Matrix MvPolynomial
open scoped Matrix

variable {R : Type*} [CommRing R] {n m : ℕ}

abbrev PencilCoefficients (n m : ℕ) (R : Type*) :=
  Fin (n + 1) → Matrix (Fin m) (Fin m) R

/-- The homogeneous pencil with coefficients `A₀,...,Aₙ`. -/
def pencil (A : PencilCoefficients n m R) (x : Fin (n + 1) → R) :
    Matrix (Fin m) (Fin m) R :=
  fun a b => ∑ i, A i a b * x i

theorem pencil_eq_sum_smul (A : PencilCoefficients n m R) (x : Fin (n + 1) → R) :
    pencil A x = ∑ i, x i • A i := by
  ext a b
  simp [pencil, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_comm]

/-- Variables `(x,u,v)` of `Pⁿ × Pᵐ⁻¹ × Pᵐ⁻¹`. -/
abbrev OrdinaryVar (n m : ℕ) := Fin (n + 1) ⊕ (Fin m ⊕ Fin m)

def ordinaryWeight : OrdinaryVar n m → ℕ × ℕ × ℕ
  | Sum.inl _ => (1, 0, 0)
  | Sum.inr (Sum.inl _) => (0, 1, 0)
  | Sum.inr (Sum.inr _) => (0, 0, 1)

def ordinaryAssignment (x : Fin (n + 1) → R) (u v : Fin m → R) :
    OrdinaryVar n m → R
  | Sum.inl i => x i
  | Sum.inr (Sum.inl a) => u a
  | Sum.inr (Sum.inr b) => v b

def pencilEntry (A : PencilCoefficients n m R) (a b : Fin m) :
    MvPolynomial (OrdinaryVar n m) R :=
  ∑ i, C (A i a b) * X (Sum.inl i)

/-- The `j`-th coordinate of `uᵀ A(x)`. -/
def leftEquation (A : PencilCoefficients n m R) (j : Fin m) :
    MvPolynomial (OrdinaryVar n m) R :=
  ∑ a, X (Sum.inr (Sum.inl a)) * pencilEntry A a j

/-- The `i`-th coordinate of `Λ A(x) v`. -/
def rightEquation (A : PencilCoefficients n m R)
    (Λ : Matrix (Fin (m - 1)) (Fin m) R) (i : Fin (m - 1)) :
    MvPolynomial (OrdinaryVar n m) R :=
  ∑ a, C (Λ i a) * (∑ b, pencilEntry A a b * X (Sum.inr (Sum.inr b)))

/-- The polynomial `uᵀ Aᵢ v`, independent of `x`. -/
def kernelPairing (A : PencilCoefficients n m R) (i : Fin (n + 1)) :
    MvPolynomial (OrdinaryVar n m) R :=
  ∑ a, ∑ b, X (Sum.inr (Sum.inl a)) * C (A i a b) * X (Sum.inr (Sum.inr b))

/-- A dual flag form evaluated on the kernel-pairing covector. -/
def dualEquation (A : PencilCoefficients n m R) (ℓ : Fin (n + 1) → R) :
    MvPolynomial (OrdinaryVar n m) R :=
  ∑ i, C (ℓ i) * kernelPairing A i

def primalEquation (M : Fin (n + 1) → R) : MvPolynomial (OrdinaryVar n m) R :=
  ∑ i, C (M i) * X (Sum.inl i)

theorem pencilEntry_multidegree (A : PencilCoefficients n m R) (a b : Fin m) :
    IsWeightedHomogeneous ordinaryWeight (pencilEntry A a b) (1, 0, 0) := by
  apply IsWeightedHomogeneous.sum
  intro i hi
  simpa [ordinaryWeight] using
    (isWeightedHomogeneous_C ordinaryWeight (A i a b)).mul
      (isWeightedHomogeneous_X R ordinaryWeight (Sum.inl i))

theorem leftEquation_multidegree (A : PencilCoefficients n m R) (j : Fin m) :
    IsWeightedHomogeneous ordinaryWeight (leftEquation A j) (1, 1, 0) := by
  apply IsWeightedHomogeneous.sum
  intro a ha
  simpa [ordinaryWeight] using
    (isWeightedHomogeneous_X R ordinaryWeight (Sum.inr (Sum.inl a))).mul
      (pencilEntry_multidegree A a j)

theorem rightEquation_multidegree (A : PencilCoefficients n m R)
    (Λ : Matrix (Fin (m - 1)) (Fin m) R) (i : Fin (m - 1)) :
    IsWeightedHomogeneous ordinaryWeight (rightEquation A Λ i) (1, 0, 1) := by
  apply IsWeightedHomogeneous.sum
  intro a ha
  have hsum : IsWeightedHomogeneous ordinaryWeight
      (∑ b, pencilEntry A a b * X (Sum.inr (Sum.inr b))) (1, 0, 1) := by
    apply IsWeightedHomogeneous.sum
    intro b hb
    simpa [ordinaryWeight] using (pencilEntry_multidegree A a b).mul
      (isWeightedHomogeneous_X R ordinaryWeight (Sum.inr (Sum.inr b)))
  simpa using (isWeightedHomogeneous_C ordinaryWeight (Λ i a)).mul hsum

theorem kernelPairing_multidegree (A : PencilCoefficients n m R) (i : Fin (n + 1)) :
    IsWeightedHomogeneous ordinaryWeight (kernelPairing A i) (0, 1, 1) := by
  apply IsWeightedHomogeneous.sum
  intro a ha
  apply IsWeightedHomogeneous.sum
  intro b hb
  simpa [ordinaryWeight] using
    ((isWeightedHomogeneous_X R ordinaryWeight (Sum.inr (Sum.inl a))).mul
      (isWeightedHomogeneous_C ordinaryWeight (A i a b))).mul
      (isWeightedHomogeneous_X R ordinaryWeight (Sum.inr (Sum.inr b)))

theorem dualEquation_multidegree (A : PencilCoefficients n m R) (ℓ : Fin (n + 1) → R) :
    IsWeightedHomogeneous ordinaryWeight (dualEquation A ℓ) (0, 1, 1) := by
  apply IsWeightedHomogeneous.sum
  intro i hi
  simpa using (isWeightedHomogeneous_C ordinaryWeight (ℓ i)).mul
    (kernelPairing_multidegree A i)

theorem primalEquation_multidegree (M : Fin (n + 1) → R) :
    IsWeightedHomogeneous ordinaryWeight (primalEquation (m := m) M) (1, 0, 0) := by
  apply IsWeightedHomogeneous.sum
  intro i hi
  simpa [ordinaryWeight] using
    (isWeightedHomogeneous_C ordinaryWeight (M i)).mul
      (isWeightedHomogeneous_X R ordinaryWeight (Sum.inl i))

@[simp] theorem eval_pencilEntry (A : PencilCoefficients n m R)
    (x : Fin (n + 1) → R) (u v : Fin m → R) (a b : Fin m) :
    eval (ordinaryAssignment x u v) (pencilEntry A a b) = pencil A x a b := by
  simp [pencilEntry, pencil, ordinaryAssignment]

@[simp] theorem eval_leftEquation (A : PencilCoefficients n m R)
    (x : Fin (n + 1) → R) (u v : Fin m → R) (j : Fin m) :
    eval (ordinaryAssignment x u v) (leftEquation A j) = (u ᵥ* pencil A x) j := by
  simp [leftEquation, ordinaryAssignment, Matrix.vecMul, dotProduct]

@[simp] theorem eval_rightEquation (A : PencilCoefficients n m R)
    (Λ : Matrix (Fin (m - 1)) (Fin m) R)
    (x : Fin (n + 1) → R) (u v : Fin m → R) (i : Fin (m - 1)) :
    eval (ordinaryAssignment x u v) (rightEquation A Λ i) =
      (Λ *ᵥ (pencil A x *ᵥ v)) i := by
  simp [rightEquation, ordinaryAssignment, Matrix.mulVec, dotProduct]

@[simp] theorem eval_kernelPairing (A : PencilCoefficients n m R)
    (x : Fin (n + 1) → R) (u v : Fin m → R) (i : Fin (n + 1)) :
    eval (ordinaryAssignment x u v) (kernelPairing A i) = u ⬝ᵥ (A i *ᵥ v) := by
  simp [kernelPairing, ordinaryAssignment, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_assoc]

@[simp] theorem eval_dualEquation (A : PencilCoefficients n m R)
    (ℓ : Fin (n + 1) → R) (x : Fin (n + 1) → R) (u v : Fin m → R) :
    eval (ordinaryAssignment x u v) (dualEquation A ℓ) =
      ∑ i, ℓ i * (u ⬝ᵥ (A i *ᵥ v)) := by
  simp [dualEquation]

@[simp] theorem eval_primalEquation (M : Fin (n + 1) → R)
    (x : Fin (n + 1) → R) (u v : Fin m → R) :
    eval (ordinaryAssignment x u v) (primalEquation M) = ∑ i, M i * x i := by
  simp [primalEquation, ordinaryAssignment]

/-- Variables `(x,v)` of the symmetric incidence. -/
abbrev SymmetricVar (n m : ℕ) := Fin (n + 1) ⊕ Fin m

def symmetricWeight : SymmetricVar n m → ℕ × ℕ
  | Sum.inl _ => (1, 0)
  | Sum.inr _ => (0, 1)

def symmetricAssignment (x : Fin (n + 1) → R) (v : Fin m → R) :
    SymmetricVar n m → R
  | Sum.inl i => x i
  | Sum.inr a => v a

def symmetricPencilEntry (A : PencilCoefficients n m R) (a b : Fin m) :
    MvPolynomial (SymmetricVar n m) R :=
  ∑ i, C (A i a b) * X (Sum.inl i)

def symmetricKernelEquation (A : PencilCoefficients n m R) (a : Fin m) :
    MvPolynomial (SymmetricVar n m) R :=
  ∑ b, symmetricPencilEntry A a b * X (Sum.inr b)

def symmetricPairing (A : PencilCoefficients n m R) (i : Fin (n + 1)) :
    MvPolynomial (SymmetricVar n m) R :=
  ∑ a, ∑ b, X (Sum.inr a) * C (A i a b) * X (Sum.inr b)

def symmetricDualEquation (A : PencilCoefficients n m R) (ℓ : Fin (n + 1) → R) :
    MvPolynomial (SymmetricVar n m) R :=
  ∑ i, C (ℓ i) * symmetricPairing A i

def symmetricPrimalEquation (M : Fin (n + 1) → R) : MvPolynomial (SymmetricVar n m) R :=
  ∑ i, C (M i) * X (Sum.inl i)

theorem symmetricPencilEntry_multidegree (A : PencilCoefficients n m R) (a b : Fin m) :
    IsWeightedHomogeneous symmetricWeight (symmetricPencilEntry A a b) (1, 0) := by
  apply IsWeightedHomogeneous.sum
  intro i hi
  simpa [symmetricWeight] using
    (isWeightedHomogeneous_C symmetricWeight (A i a b)).mul
      (isWeightedHomogeneous_X R symmetricWeight (Sum.inl i))

theorem symmetricKernelEquation_multidegree (A : PencilCoefficients n m R) (a : Fin m) :
    IsWeightedHomogeneous symmetricWeight (symmetricKernelEquation A a) (1, 1) := by
  apply IsWeightedHomogeneous.sum
  intro b hb
  simpa [symmetricWeight] using (symmetricPencilEntry_multidegree A a b).mul
    (isWeightedHomogeneous_X R symmetricWeight (Sum.inr b))

theorem symmetricPairing_multidegree (A : PencilCoefficients n m R) (i : Fin (n + 1)) :
    IsWeightedHomogeneous symmetricWeight (symmetricPairing A i) (0, 2) := by
  apply IsWeightedHomogeneous.sum
  intro a ha
  apply IsWeightedHomogeneous.sum
  intro b hb
  simpa [symmetricWeight] using
    ((isWeightedHomogeneous_X R symmetricWeight (Sum.inr a)).mul
      (isWeightedHomogeneous_C symmetricWeight (A i a b))).mul
      (isWeightedHomogeneous_X R symmetricWeight (Sum.inr b))

theorem symmetricDualEquation_multidegree (A : PencilCoefficients n m R)
    (ℓ : Fin (n + 1) → R) :
    IsWeightedHomogeneous symmetricWeight (symmetricDualEquation A ℓ) (0, 2) := by
  apply IsWeightedHomogeneous.sum
  intro i hi
  simpa using (isWeightedHomogeneous_C symmetricWeight (ℓ i)).mul
    (symmetricPairing_multidegree A i)

theorem symmetricPrimalEquation_multidegree (M : Fin (n + 1) → R) :
    IsWeightedHomogeneous symmetricWeight (symmetricPrimalEquation (m := m) M) (1, 0) := by
  apply IsWeightedHomogeneous.sum
  intro i hi
  simpa [symmetricWeight] using
    (isWeightedHomogeneous_C symmetricWeight (M i)).mul
      (isWeightedHomogeneous_X R symmetricWeight (Sum.inl i))

@[simp] theorem eval_symmetricPencilEntry (A : PencilCoefficients n m R)
    (x : Fin (n + 1) → R) (v : Fin m → R) (a b : Fin m) :
    eval (symmetricAssignment x v) (symmetricPencilEntry A a b) = pencil A x a b := by
  simp [symmetricPencilEntry, pencil, symmetricAssignment]

@[simp] theorem eval_symmetricKernelEquation (A : PencilCoefficients n m R)
    (x : Fin (n + 1) → R) (v : Fin m → R) (a : Fin m) :
    eval (symmetricAssignment x v) (symmetricKernelEquation A a) = (pencil A x *ᵥ v) a := by
  simp [symmetricKernelEquation, symmetricAssignment, Matrix.mulVec, dotProduct]

@[simp] theorem eval_symmetricPairing (A : PencilCoefficients n m R)
    (x : Fin (n + 1) → R) (v : Fin m → R) (i : Fin (n + 1)) :
    eval (symmetricAssignment x v) (symmetricPairing A i) = v ⬝ᵥ (A i *ᵥ v) := by
  simp [symmetricPairing, symmetricAssignment, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_assoc]

@[simp] theorem eval_symmetricDualEquation (A : PencilCoefficients n m R)
    (ℓ : Fin (n + 1) → R) (x : Fin (n + 1) → R) (v : Fin m → R) :
    eval (symmetricAssignment x v) (symmetricDualEquation A ℓ) =
      ∑ i, ℓ i * (v ⬝ᵥ (A i *ᵥ v)) := by
  simp [symmetricDualEquation]

@[simp] theorem eval_symmetricPrimalEquation (M : Fin (n + 1) → R)
    (x : Fin (n + 1) → R) (v : Fin m → R) :
    eval (symmetricAssignment x v) (symmetricPrimalEquation M) = ∑ i, M i * x i := by
  simp [symmetricPrimalEquation, symmetricAssignment]

/-- One index per equation; the four summands are left, right, dual, primal. -/
abbrev OrdinaryEquationIndex (n m : ℕ) :=
  Fin m ⊕ (Fin (m - 1) ⊕ (Fin (n - 2) ⊕ Unit))

def ordinarySystem (A : PencilCoefficients n m R)
    (Λ : Matrix (Fin (m - 1)) (Fin m) R)
    (flags : Fin (n - 2) → Fin (n + 1) → R) (M : Fin (n + 1) → R) :
    OrdinaryEquationIndex n m → MvPolynomial (OrdinaryVar n m) R
  | Sum.inl j => leftEquation A j
  | Sum.inr (Sum.inl i) => rightEquation A Λ i
  | Sum.inr (Sum.inr (Sum.inl t)) => dualEquation A (flags t)
  | Sum.inr (Sum.inr (Sum.inr _)) => primalEquation M

def ordinaryDegree : OrdinaryEquationIndex n m → ℕ × ℕ × ℕ
  | Sum.inl _ => (1, 1, 0)
  | Sum.inr (Sum.inl _) => (1, 0, 1)
  | Sum.inr (Sum.inr (Sum.inl _)) => (0, 1, 1)
  | Sum.inr (Sum.inr (Sum.inr _)) => (1, 0, 0)

theorem ordinarySystem_multidegree (A : PencilCoefficients n m R)
    (Λ : Matrix (Fin (m - 1)) (Fin m) R)
    (flags : Fin (n - 2) → Fin (n + 1) → R) (M : Fin (n + 1) → R)
    (e : OrdinaryEquationIndex n m) :
    IsWeightedHomogeneous ordinaryWeight (ordinarySystem A Λ flags M e) (ordinaryDegree e) := by
  rcases e with j | (i | (t | last))
  · exact leftEquation_multidegree A j
  · exact rightEquation_multidegree A Λ i
  · exact dualEquation_multidegree A (flags t)
  · exact primalEquation_multidegree M

/-- Every monomial in an actual equation has the claimed three separate degrees. -/
theorem ordinarySystem_support_degree (A : PencilCoefficients n m R)
    (Λ : Matrix (Fin (m - 1)) (Fin m) R)
    (flags : Fin (n - 2) → Fin (n + 1) → R) (M : Fin (n + 1) → R)
    (e : OrdinaryEquationIndex n m) {d : OrdinaryVar n m →₀ ℕ}
    (hd : d ∈ (ordinarySystem A Λ flags M e).support) :
    Finsupp.weight ordinaryWeight d = ordinaryDegree e :=
  ordinarySystem_multidegree A Λ flags M e (mem_support_iff.mp hd)

theorem ordinarySystem_equation_count (hn : 2 ≤ n) (hm : 1 ≤ m) :
    Fintype.card (OrdinaryEquationIndex n m) = n + 2 * m - 2 := by
  simp only [OrdinaryEquationIndex, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  omega

theorem ordinarySystem_zero_iff (A : PencilCoefficients n m R)
    (Λ : Matrix (Fin (m - 1)) (Fin m) R)
    (flags : Fin (n - 2) → Fin (n + 1) → R) (M : Fin (n + 1) → R)
    (x : Fin (n + 1) → R) (u v : Fin m → R) :
    (∀ e, eval (ordinaryAssignment x u v) (ordinarySystem A Λ flags M e) = 0) ↔
      (u ᵥ* pencil A x = 0 ∧ Λ *ᵥ (pencil A x *ᵥ v) = 0 ∧
        (∀ t, ∑ i, flags t i * (u ⬝ᵥ (A i *ᵥ v)) = 0) ∧ ∑ i, M i * x i = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext j
      simpa [ordinarySystem] using h (Sum.inl j)
    · funext i
      simpa [ordinarySystem] using h (Sum.inr (Sum.inl i))
    · intro t
      simpa [ordinarySystem] using h (Sum.inr (Sum.inr (Sum.inl t)))
    · simpa [ordinarySystem] using h (Sum.inr (Sum.inr (Sum.inr ())))
  · rintro ⟨hl, hr, hd, hp⟩ e
    rcases e with j | (i | (t | last))
    · simpa [ordinarySystem] using congrFun hl j
    · simpa [ordinarySystem] using congrFun hr i
    · simpa [ordinarySystem] using hd t
    · simpa [ordinarySystem] using hp

/-- The three blocks of the symmetric system are kernel, dual, primal. -/
abbrev SymmetricEquationIndex (n m : ℕ) := Fin m ⊕ (Fin (n - 2) ⊕ Unit)

def symmetricSystem (A : PencilCoefficients n m R)
    (flags : Fin (n - 2) → Fin (n + 1) → R) (M : Fin (n + 1) → R) :
    SymmetricEquationIndex n m → MvPolynomial (SymmetricVar n m) R
  | Sum.inl a => symmetricKernelEquation A a
  | Sum.inr (Sum.inl t) => symmetricDualEquation A (flags t)
  | Sum.inr (Sum.inr _) => symmetricPrimalEquation M

def symmetricDegree : SymmetricEquationIndex n m → ℕ × ℕ
  | Sum.inl _ => (1, 1)
  | Sum.inr (Sum.inl _) => (0, 2)
  | Sum.inr (Sum.inr _) => (1, 0)

theorem symmetricSystem_multidegree (A : PencilCoefficients n m R)
    (flags : Fin (n - 2) → Fin (n + 1) → R) (M : Fin (n + 1) → R)
    (e : SymmetricEquationIndex n m) :
    IsWeightedHomogeneous symmetricWeight (symmetricSystem A flags M e) (symmetricDegree e) := by
  rcases e with a | (t | last)
  · exact symmetricKernelEquation_multidegree A a
  · exact symmetricDualEquation_multidegree A (flags t)
  · exact symmetricPrimalEquation_multidegree M

theorem symmetricSystem_support_degree (A : PencilCoefficients n m R)
    (flags : Fin (n - 2) → Fin (n + 1) → R) (M : Fin (n + 1) → R)
    (e : SymmetricEquationIndex n m) {d : SymmetricVar n m →₀ ℕ}
    (hd : d ∈ (symmetricSystem A flags M e).support) :
    Finsupp.weight symmetricWeight d = symmetricDegree e :=
  symmetricSystem_multidegree A flags M e (mem_support_iff.mp hd)

theorem symmetricSystem_equation_count (hn : 2 ≤ n) :
    Fintype.card (SymmetricEquationIndex n m) = n + m - 1 := by
  simp only [SymmetricEquationIndex, Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  omega

theorem symmetricSystem_zero_iff (A : PencilCoefficients n m R)
    (flags : Fin (n - 2) → Fin (n + 1) → R) (M : Fin (n + 1) → R)
    (x : Fin (n + 1) → R) (v : Fin m → R) :
    (∀ e, eval (symmetricAssignment x v) (symmetricSystem A flags M e) = 0) ↔
      (pencil A x *ᵥ v = 0 ∧
        (∀ t, ∑ i, flags t i * (v ⬝ᵥ (A i *ᵥ v)) = 0) ∧ ∑ i, M i * x i = 0) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · funext a
      simpa [symmetricSystem] using h (Sum.inl a)
    · intro t
      simpa [symmetricSystem] using h (Sum.inr (Sum.inl t))
    · simpa [symmetricSystem] using h (Sum.inr (Sum.inr ()))
  · rintro ⟨hk, hd, hp⟩ e
    rcases e with a | (t | last)
    · simpa [symmetricSystem] using congrFun hk a
    · simpa [symmetricSystem] using hd t
    · simpa [symmetricSystem] using hp

end Sheshadri.Incidence
