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
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.Defs

/-!
# A common finite coefficient space for all size-m determinants

The affine determinant degree bound is proved from the Leibniz expansion.
An explicit finite box of exponent vectors then contains every monomial of
every size-m determinant, as well as Fermat whenever the box bound is at least
n. Thus a closure formed in this finite coefficient space is not restricting
the allowed size-m representations.
-/

noncomputable section
namespace Sheshadri.DegreeBound

open Matrix MvPolynomial Incidence PolynomialModel

section Degree
variable {K σ ι : Type*} [CommRing K] [Nontrivial K] [Fintype ι] [DecidableEq ι]

omit [Nontrivial K] in
/-- A determinant of entries of degree at most d has degree at most size*d. -/
theorem matrix_det_totalDegree_le (A : Matrix ι ι (MvPolynomial σ K)) (d : ℕ)
    (hA : ∀ i j, (A i j).totalDegree ≤ d) :
    A.det.totalDegree ≤ Fintype.card ι * d := by
  classical
  rw [Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro p hp
  have hconst :
      (((Equiv.Perm.sign p : ℤ) : MvPolynomial σ K)).totalDegree = 0 := by
    simpa only [map_intCast] using
      (totalDegree_C ((Equiv.Perm.sign p : ℤ) : K) :
        (C ((Equiv.Perm.sign p : ℤ) : K) : MvPolynomial σ K).totalDegree = 0)
  calc
    _ ≤ (((Equiv.Perm.sign p : ℤ) : MvPolynomial σ K)).totalDegree +
        (∏ i, A (p i) i).totalDegree := totalDegree_mul _ _
    _ = (∏ i, A (p i) i).totalDegree := by rw [hconst, zero_add]
    _ ≤ ∑ i, (A (p i) i).totalDegree := totalDegree_finset_prod _ _
    _ ≤ ∑ _i : ι, d := Finset.sum_le_sum (fun i _ => hA (p i) i)
    _ = Fintype.card ι * d := by simp

theorem affinePencil_entry_totalDegree_le {n m : ℕ}
    (A : PencilCoefficients n m K) (a b : Fin m) :
    (affinePencil A a b).totalDegree ≤ 1 := by
  unfold affinePencil
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · apply totalDegree_finsetSum_le
    intro i hi
    simpa only [totalDegree_C, totalDegree_X, zero_add] using
      (totalDegree_mul (C (A i.succ a b)) (X i))

/-- Every actual affine size-m determinant lies in degree at most m. -/
theorem determinant_totalDegree_le {n m : ℕ} (A : PencilCoefficients n m K) :
    (determinant A).totalDegree ≤ m := by
  simpa only [determinant, Fintype.card_fin, mul_one] using
    matrix_det_totalDegree_le (affinePencil A) 1 (affinePencil_entry_totalDegree_le A)

theorem fermat_totalDegree_le (n : ℕ) :
    (PolynomialModel.fermat n : MvPolynomial (Fin n) K).totalDegree ≤ n := by
  unfold PolynomialModel.fermat
  apply totalDegree_finsetSum_le
  intro i hi
  simp

end Degree

section Box
variable (σ : Type*) [Fintype σ]

/-- A concrete finite monomial index set: each exponent is at most D. -/
def exponentBox (D : ℕ) : Finset (σ →₀ ℕ) := by
  classical
  exact (Finset.univ : Finset (σ → Fin (D + 1))).image
    (fun f => Finsupp.equivFunOnFinite.symm (fun i => (f i : ℕ)))

theorem mem_exponentBox (D : ℕ) (d : σ →₀ ℕ) :
    d ∈ exponentBox σ D ↔ ∀ i, d i ≤ D := by
  classical
  constructor
  · intro h
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp h
    intro i
    exact Nat.le_of_lt_succ (f i).isLt
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨fun i => ⟨d i, Nat.lt_succ_of_le (h i)⟩, Finset.mem_univ _, ?_⟩
    ext i
    rfl

variable {K : Type*} [CommSemiring K]

/-- Degree bounded polynomials have support in the fixed box. -/
theorem support_subset_exponentBox (f : MvPolynomial σ K) (D : ℕ)
    (hf : f.totalDegree ≤ D) : f.support ⊆ exponentBox σ D := by
  intro d hd
  apply (mem_exponentBox σ D d).2
  intro i
  exact (degreeOf_le_iff.mp ((degreeOf_le_totalDegree f i).trans hf)) d hd

/-- Reconstruction uses coefficients on the whole finite box, including zero
coefficients for monomials absent from the polynomial. -/
theorem reconstruct_from_exponentBox (f : MvPolynomial σ K) (D : ℕ)
    (hf : f.totalDegree ≤ D) :
    (∑ d ∈ exponentBox σ D, monomial d (coeff d f)) = f := by
  classical
  calc
    _ = ∑ d ∈ f.support, monomial d (coeff d f) := by
      symm
      apply Finset.sum_subset (support_subset_exponentBox σ f D hf)
      intro d hd hdnot
      have hc : coeff d f = 0 := not_mem_support_iff.mp hdnot
      simp [hc]
    _ = f := support_sum_monomial_coeff f

end Box

/-- One fixed box includes every size-m ordinary or symmetric representation. -/
theorem determinant_support_subset_box {K : Type*} [CommRing K] [Nontrivial K]
    {n m : ℕ} (A : PencilCoefficients n m K) (D : ℕ) (hm : m ≤ D) :
    (determinant A).support ⊆ exponentBox (Fin n) D :=
  support_subset_exponentBox (Fin n) _ D ((determinant_totalDegree_le A).trans hm)

theorem fermat_support_subset_box {K : Type*} [CommRing K] [Nontrivial K]
    (n D : ℕ) (hn : n ≤ D) :
    (PolynomialModel.fermat n : MvPolynomial (Fin n) K).support ⊆ exponentBox (Fin n) D :=
  support_subset_exponentBox (Fin n) _ D ((fermat_totalDegree_le n).trans hn)

/-- The canonical bound max(n,m) works simultaneously for the target and the
entire representation locus. -/
theorem common_coefficient_support {K : Type*} [CommRing K] [Nontrivial K]
    (n m : ℕ) :
    (PolynomialModel.fermat n : MvPolynomial (Fin n) K).support ⊆
      exponentBox (Fin n) (max n m) ∧
    ∀ A : PencilCoefficients n m K,
      (determinant A).support ⊆ exponentBox (Fin n) (max n m) := by
  exact ⟨fermat_support_subset_box n (max n m) (le_max_left _ _),
    fun A => determinant_support_subset_box A (max n m) (le_max_right _ _)⟩

end Sheshadri.DegreeBound
