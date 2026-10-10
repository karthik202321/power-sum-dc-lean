/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.PolynomialModel
import Sheshadri.CompleteIntersectionHilbert

/-!
# Homogeneous determinant pencils and their actual hypersurface Hilbert bound

The homogeneous polynomial is literally the determinant of the homogeneous
matrix pencil. Its standard affine chart is the original affine determinant,
and taking affine partial derivatives commutes with this chart operation.
For a nonzero determinant the homogeneous principal ideal has the ordinary
hypersurface Hilbert polynomial of degree at most `n-1`.
-/

noncomputable section
namespace Sheshadri.HomogeneousDeterminant

open Matrix MvPolynomial Incidence PolynomialModel
open FlatGradedHilbert HomogeneousQuotientExact CompleteIntersectionHilbert

variable {K : Type*} [CommRing K] {n m : ℕ}

def homogeneousPencil (A : PencilCoefficients n m K) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin (n+1)) K) :=
  fun a b => ∑ i : Fin (n+1), C (A i a b) * X i

def homogeneousDeterminant (A : PencilCoefficients n m K) :
    MvPolynomial (Fin (n+1)) K := (homogeneousPencil A).det

def dehom : MvPolynomial (Fin (n+1)) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval (Fin.cons 1 X)

@[simp] theorem dehom_C (c : K) : dehom (n := n) (C c) = C c := by
  simp [dehom]

@[simp] theorem dehom_X_zero : dehom (X (0 : Fin (n+1)) : MvPolynomial _ K) = 1 := by
  simp [dehom]

@[simp] theorem dehom_X_succ (i : Fin n) :
    dehom (X i.succ : MvPolynomial _ K) = X i := by
  simp [dehom]

theorem dehom_homogeneousPencil (A : PencilCoefficients n m K) :
    (homogeneousPencil A).map (dehom (n := n)) = affinePencil A := by
  ext a b
  simp [homogeneousPencil, affinePencil, Fin.sum_univ_succ]

theorem dehom_homogeneousDeterminant (A : PencilCoefficients n m K) :
    dehom (homogeneousDeterminant A) = determinant A := by
  change dehom.toRingHom (homogeneousPencil A).det = _
  rw [RingHom.map_det]
  change ((homogeneousPencil A).map (dehom (n := n))).det = _
  rw [dehom_homogeneousPencil]
  rfl

theorem dehom_pderiv_succ (f : MvPolynomial (Fin (n+1)) K) (i : Fin n) :
    dehom (pderiv i.succ f) = pderiv i (dehom f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f j hf =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [pderiv_mul, pderiv_X, Pi.single_apply, hf]
    · by_cases hji : j = i <;>
        simp [pderiv_mul, pderiv_X, Pi.single_apply, hf, mul_ite, hji]

theorem dehom_pderiv_homogeneousDeterminant (A : PencilCoefficients n m K)
    (i : Fin n) :
    dehom (pderiv i.succ (homogeneousDeterminant A)) = pderiv i (determinant A) := by
  rw [dehom_pderiv_succ, dehom_homogeneousDeterminant]

theorem homogeneousPencil_homogeneous (A : PencilCoefficients n m K) (a b : Fin m) :
    (homogeneousPencil A a b).IsHomogeneous 1 := by
  exact IsHomogeneous.sum _ _ _ (fun i _ => isHomogeneous_C_mul_X _ _)

theorem homogeneousDeterminant_homogeneous (A : PencilCoefficients n m K) :
    (homogeneousDeterminant A).IsHomogeneous m := by
  classical
  rw [homogeneousDeterminant, Matrix.det_apply']
  apply IsHomogeneous.sum
  intro s _
  have hp : (∏ i : Fin m, homogeneousPencil A (s i) i).IsHomogeneous m := by
    simpa using IsHomogeneous.prod Finset.univ
      (fun i : Fin m => homogeneousPencil A (s i) i) (fun _ => 1)
      (fun i _ => homogeneousPencil_homogeneous A _ _)
  simpa using hp.C_mul (↑(Equiv.Perm.sign s) : K)

theorem homogeneousDeterminant_ne_zero (A : PencilCoefficients n m K)
    (hA : determinant A ≠ 0) : homogeneousDeterminant A ≠ 0 := by
  intro h
  apply hA
  rw [← dehom_homogeneousDeterminant A, h, map_zero]

def hypersurfacePolynomial (n m : ℕ) : Polynomial ℚ :=
  completeIntersectionPolynomial (Z := Fin (n+1)) (fun _ => m) 1

theorem hypersurfacePolynomial_natDegree_le (n m : ℕ) (hn : 0 < n) :
    (hypersurfacePolynomial n m).natDegree ≤ n-1 := by
  simpa [hypersurfacePolynomial] using
    completeIntersectionPolynomial_natDegree_le (Z := Fin (n+1)) (fun _ => m) 1
      (by simpa using hn)

section Hilbert
variable [IsDomain K]

theorem quotientBot_regular_of_ne_zero {Z : Type*} (f : MvPolynomial Z K)
    (hf : f ≠ 0) : IsRegular (Ideal.Quotient.mk (⊥ : Ideal (MvPolynomial Z K)) f) := by
  let e := RingEquiv.quotientBot (MvPolynomial Z K)
  constructor
  · intro a b hab
    apply e.injective
    apply mul_left_cancel₀ hf
    have he := congrArg e hab
    simpa only [map_mul, RingEquiv.quotientBot_mk] using he
  · intro a b hab
    apply e.injective
    apply mul_right_cancel₀ hf
    have he := congrArg e hab
    simpa only [map_mul, RingEquiv.quotientBot_mk] using he

end Hilbert

section Field
variable {L : Type*} [Field L]

/-- The principal-ideal Hilbert calculation applies to any nonzero homogeneous
equation, including one with a power of the chart coordinate as a factor. -/
theorem eventual_homogeneous_hypersurface_hilbert
    (f : MvPolynomial (Fin (n+1)) L) (hf : f.IsHomogeneous m) (hfn : f ≠ 0) :
    ∃ N : ℕ, ∀ k > N,
      (hypersurfacePolynomial n m).eval (k : ℚ) =
        (Module.finrank L (coordinatePiece (Fin (n+1)) L (Ideal.span {f}) k) : ℚ) := by
  refine ⟨(numerator (fun _ => m) 1).natDegree, fun k hk => ?_⟩
  have hh := completeIntersectionPolynomial_eval
    (fun _ => f) (fun _ => m) 1 (by simp) (fun _ _ => hf)
    (fun j hj => by
      have hj0 : j = 0 := by omega
      subst j
      exact quotientBot_regular_of_ne_zero _ hfn) k hk
  have hI : idealSequence (⊥ : Ideal (MvPolynomial (Fin (n+1)) L))
      (fun _ => f) 1 = Ideal.span {f} := by
    change ⊥ ⊔ Ideal.span {f} = _
    exact bot_sup_eq _
  rw [hI] at hh
  exact hh

/-- Literal homogeneous hypersurface quotient dimensions have the displayed
eventual Hilbert polynomial; no smoothness assumption is required. -/
theorem eventual_hypersurface_hilbert (A : PencilCoefficients n m L)
    (hA : determinant A ≠ 0) :
    ∃ N : ℕ, ∀ k > N,
      (hypersurfacePolynomial n m).eval (k : ℚ) =
        (Module.finrank L (coordinatePiece (Fin (n+1)) L
          (Ideal.span {homogeneousDeterminant A}) k) : ℚ) := by
  exact eventual_homogeneous_hypersurface_hilbert _
    (homogeneousDeterminant_homogeneous A) (homogeneousDeterminant_ne_zero A hA)

end Field
end Sheshadri.HomogeneousDeterminant
