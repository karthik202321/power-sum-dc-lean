/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.Roots

/-!
# Moment-curve hyperplanes for a split Bézout system

These are generic auxiliary hyperplanes, independent of any polynomial from
the determinantal-complexity application.  In projective dimension `r`, the
hyperplane with parameter `a` has coefficients `(1,a,...,a^r)`.
-/

noncomputable section
open scoped BigOperators Matrix
namespace Sheshadri.SplitHyperplanes

variable {K : Type*} [Field K]

/-- Affine moment-curve hyperplane in the chart whose last coordinate is one. -/
def affineForm (r : ℕ) (a : K) : MvPolynomial (Fin r) K :=
  (∑ j : Fin r, MvPolynomial.C (a ^ (j : ℕ)) * MvPolynomial.X j) +
    MvPolynomial.C (a ^ r)

/-- Homogeneous moment-curve hyperplane. -/
def projectiveForm (r : ℕ) (a : K) : MvPolynomial (Fin (r + 1)) K :=
  ∑ j : Fin (r + 1), MvPolynomial.C (a ^ (j : ℕ)) * MvPolynomial.X j

@[simp] theorem eval_affineForm (r : ℕ) (a : K) (x : Fin r → K) :
    MvPolynomial.eval x (affineForm r a) =
      (∑ j : Fin r, a ^ (j : ℕ) * x j) + a ^ r := by
  simp [affineForm]

@[simp] theorem eval_projectiveForm (r : ℕ) (a : K) (x : Fin (r + 1) → K) :
    MvPolynomial.eval x (projectiveForm r a) =
      ∑ j : Fin (r + 1), a ^ (j : ℕ) * x j := by
  simp [projectiveForm]

/-- Distinct moment-curve hyperplanes in the correct number have invertible
affine coefficient matrix. -/
theorem vandermonde_isUnit {r : ℕ} (a : Fin r → K) (ha : Function.Injective a) :
    IsUnit (Matrix.vandermonde a).det :=
  isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr ha)

/-- The explicit affine intersection point of `r` chosen hyperplanes. -/
def intersectionPoint {r : ℕ} (a : Fin r → K) : Fin r → K :=
  (Matrix.vandermonde a)⁻¹ *ᵥ (fun i => -(a i ^ r))

theorem intersectionPoint_zero {r : ℕ} (a : Fin r → K)
    (ha : Function.Injective a) (i : Fin r) :
    MvPolynomial.eval (intersectionPoint a) (affineForm r (a i)) = 0 := by
  rw [eval_affineForm]
  have h : (Matrix.vandermonde a) *ᵥ intersectionPoint a = fun i => -(a i ^ r) := by
    simp [intersectionPoint, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (vandermonde_isUnit a ha)]
  have hi := congrFun h i
  change (∑ j : Fin r, a i ^ (j : ℕ) * intersectionPoint a j) = -(a i ^ r) at hi
  rw [hi, neg_add_cancel]

theorem intersectionPoint_unique {r : ℕ} (a : Fin r → K)
    (ha : Function.Injective a) (x : Fin r → K)
    (hx : ∀ i, MvPolynomial.eval x (affineForm r (a i)) = 0) :
    x = intersectionPoint a := by
  apply (Matrix.mulVec_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (vandermonde_isUnit a ha)))
  funext i
  have h₁ := hx i
  have h₂ := intersectionPoint_zero a ha i
  simp only [eval_affineForm] at h₁ h₂
  change (∑ j : Fin r, a i ^ (j : ℕ) * x j) =
    ∑ j : Fin r, a i ^ (j : ℕ) * intersectionPoint a j
  exact add_right_cancel (h₁.trans h₂.symm)

/-- A projective block cannot lie on more than its projective dimension many
distinct chosen hyperplanes.  This is the Vandermonde argument, with no
generic-position hypothesis left to discharge. -/
theorem projective_intersection_eq_zero {r : ℕ} (a : Fin (r + 1) → K)
    (ha : Function.Injective a) (x : Fin (r + 1) → K)
    (hx : ∀ i, MvPolynomial.eval x (projectiveForm r (a i)) = 0) : x = 0 := by
  apply Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero ha
  simpa only [eval_projectiveForm] using hx

/-- Tangent equations for a quota-sized affine branch have trivial kernel. -/
theorem affine_tangent_eq_zero {r : ℕ} (a : Fin r → K)
    (ha : Function.Injective a) (v : Fin r → K)
    (hv : ∀ i, (∑ j : Fin r, a i ^ (j : ℕ) * v j) = 0) : v = 0 :=
  Matrix.eq_zero_of_forall_index_sum_pow_mul_eq_zero ha hv

/-- The equations of a quota-sized branch generate every coordinate
difference, in any ambient polynomial ring.  This ideal statement retains
scheme structure; it is stronger than identifying a zero set. -/
theorem coordinateDifference_mem {r : ℕ} {σ : Type*} (ι : Fin r → σ)
    (a : Fin r → K) (ha : Function.Injective a)
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ i, MvPolynomial.rename ι (affineForm r (a i)) ∈ I)
    (j : Fin r) :
    MvPolynomial.X (ι j) - MvPolynomial.C (intersectionPoint a j) ∈ I := by
  classical
  let q := Ideal.Quotient.mk I
  let Cq : K →+* MvPolynomial σ K ⧸ I := q.comp MvPolynomial.C
  let x : Fin r → MvPolynomial σ K ⧸ I := fun j => q (MvPolynomial.X (ι j))
  have hm : (Matrix.vandermonde a).map Cq *ᵥ x = Cq ∘ (fun i => -(a i ^ r)) := by
    funext i
    have hi := (Ideal.Quotient.eq_zero_iff_mem).mpr (hI i)
    change q (MvPolynomial.rename ι (affineForm r (a i))) = 0 at hi
    simp only [affineForm, map_add, map_sum, map_mul, MvPolynomial.rename_C,
      MvPolynomial.rename_X] at hi
    change (∑ j : Fin r, Cq (a i ^ (j : ℕ)) * x j) + Cq (a i ^ r) = 0 at hi
    change (∑ j : Fin r, Cq (a i ^ (j : ℕ)) * x j) = Cq (-(a i ^ r))
    simpa only [map_neg] using eq_neg_of_add_eq_zero_left hi
  have hx : x = Cq ∘ intersectionPoint a := by
    have h := congrArg (fun v => (Matrix.vandermonde a)⁻¹.map Cq *ᵥ v) hm
    dsimp only at h
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul,
      Matrix.nonsing_inv_mul _ (vandermonde_isUnit a ha),
      Matrix.map_one _ (map_zero Cq) (map_one Cq),
      Matrix.one_mulVec] at h
    refine h.trans ?_
    funext i
    exact (Cq.map_mulVec _ _ i).symm
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  change q (MvPolynomial.X (ι j) - MvPolynomial.C (intersectionPoint a j)) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun hx j)

/-- A polynomial vanishing at a point lies in any ideal containing all
coordinate differences at that point. -/
theorem eval_kernel_le {σ : Type*} (p : σ → K) (I : Ideal (MvPolynomial σ K))
    (hI : ∀ j, MvPolynomial.X j - MvPolynomial.C (p j) ∈ I) :
    RingHom.ker (MvPolynomial.eval p) ≤ I := by
  let q := Ideal.Quotient.mk I
  have hmaps : q = q.comp (MvPolynomial.C.comp (MvPolynomial.eval p)) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp
    · intro j
      have hj := (Ideal.Quotient.eq_zero_iff_mem).mpr (hI j)
      change q (MvPolynomial.X j - MvPolynomial.C (p j)) = 0 at hj
      simpa only [RingHom.comp_apply, MvPolynomial.eval_X] using sub_eq_zero.mp
        ((map_sub q _ _).symm.trans hj)
  intro f hf
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  change q f = 0
  rw [hmaps]
  simp only [RingHom.comp_apply, RingHom.mem_ker.mp hf, map_zero]

/-- The selected affine forms generate exactly the point's evaluation ideal. -/
theorem affine_span_eq_eval_kernel {r : ℕ} (a : Fin r → K)
    (ha : Function.Injective a) :
    Ideal.span (Set.range fun i => affineForm r (a i)) =
      RingHom.ker (MvPolynomial.eval (intersectionPoint a)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact intersectionPoint_zero a ha i
  · apply eval_kernel_le
    intro j
    simpa using coordinateDifference_mem id a ha _
      (fun i => by simpa using Ideal.subset_span (Set.mem_range_self i)) j

theorem affine_span_isMaximal {r : ℕ} (a : Fin r → K)
    (ha : Function.Injective a) :
    (Ideal.span (Set.range fun i => affineForm r (a i))).IsMaximal := by
  rw [affine_span_eq_eval_kernel a ha]
  exact RingHom.ker_isMaximal_of_surjective _ (fun k => ⟨MvPolynomial.C k, by simp⟩)

/-- Invertible scalar combinations do not change ideal membership. -/
theorem coordinate_mem_of_linear_combinations {n : Type*} [Fintype n] [DecidableEq n]
    {σ : Type*} (A : Matrix n n K) (hA : IsUnit A.det)
    (v : n → MvPolynomial σ K) (I : Ideal (MvPolynomial σ K))
    (hv : ∀ i, (∑ j, MvPolynomial.C (A i j) * v j) ∈ I) (j : n) : v j ∈ I := by
  let q := Ideal.Quotient.mk I
  let Cq : K →+* MvPolynomial σ K ⧸ I := q.comp MvPolynomial.C
  have hm : A.map Cq *ᵥ (q ∘ v) = 0 := by
    funext i
    have hi := (Ideal.Quotient.eq_zero_iff_mem).mpr (hv i)
    simpa only [map_sum, map_mul] using hi
  have h := congrArg (fun w => A⁻¹.map Cq *ᵥ w) hm
  dsimp only at h
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA,
    Matrix.map_one _ (map_zero Cq) (map_one Cq), Matrix.one_mulVec,
    Matrix.mulVec_zero] at h
  exact (Ideal.Quotient.eq_zero_iff_mem).mp (congrFun h j)

/-- Any dimension-plus-one distinct moment-curve forms generate the whole
block of homogeneous variables, even inside a larger polynomial ring. -/
theorem projectiveCoordinate_mem {r : ℕ} {σ : Type*} (ι : Fin (r + 1) → σ)
    (a : Fin (r + 1) → K) (ha : Function.Injective a)
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ i, MvPolynomial.rename ι (projectiveForm r (a i)) ∈ I)
    (j : Fin (r + 1)) : MvPolynomial.X (ι j) ∈ I := by
  apply coordinate_mem_of_linear_combinations (Matrix.vandermonde a)
    (vandermonde_isUnit a ha) (fun j => MvPolynomial.X (ι j)) I _ j
  intro i
  simpa only [projectiveForm, map_sum, map_mul, MvPolynomial.rename_C,
    MvPolynomial.rename_X, Matrix.vandermonde_apply] using hI i

/-- A quota-sized homogeneous branch identifies the other coordinates with
scalar multiples of the last coordinate, as an equality in its quotient ring. -/
theorem homogeneousCoordinateDifference_mem {r : ℕ} {σ : Type*}
    (ι : Fin (r + 1) → σ) (a : Fin r → K) (ha : Function.Injective a)
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ i, MvPolynomial.rename ι (projectiveForm r (a i)) ∈ I)
    (j : Fin r) :
    MvPolynomial.X (ι j.castSucc) -
      MvPolynomial.C (intersectionPoint a j) * MvPolynomial.X (ι (Fin.last r)) ∈ I := by
  apply coordinate_mem_of_linear_combinations (Matrix.vandermonde a)
    (vandermonde_isUnit a ha)
    (fun j => MvPolynomial.X (ι j.castSucc) -
      MvPolynomial.C (intersectionPoint a j) * MvPolynomial.X (ι (Fin.last r))) I _ j
  intro i
  have hi := intersectionPoint_zero a ha i
  simp only [eval_affineForm] at hi
  have hs : (∑ j : Fin r, a i ^ (j : ℕ) * intersectionPoint a j) = -(a i ^ r) :=
    eq_neg_of_add_eq_zero_left hi
  have he : (∑ j : Fin r, MvPolynomial.C ((Matrix.vandermonde a) i j) *
      (MvPolynomial.X (ι j.castSucc) -
        MvPolynomial.C (intersectionPoint a j) * MvPolynomial.X (ι (Fin.last r)))) =
      MvPolynomial.rename ι (projectiveForm r (a i)) := by
    simp only [projectiveForm, map_sum, map_mul,
      MvPolynomial.rename_C, MvPolynomial.rename_X]
    rw [Fin.sum_univ_castSucc]
    simp only [Matrix.vandermonde_apply, Fin.coe_castSucc, Fin.val_last,
      mul_sub, ← mul_assoc, ← MvPolynomial.C_mul, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← map_sum, hs, map_neg, neg_mul, sub_neg_eq_add]
  exact he.symm ▸ hI i

end Sheshadri.SplitHyperplanes
