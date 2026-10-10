/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.MultiProjectiveBezout
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.CharZero.Infinite

/-!
# A common hyperplane chart for finitely many projective points

An explicit moment-curve family of linear forms has only finitely many bad
parameters at any nonzero point. This constructs a chart containing all the
selected points, with no generic-position assumption. The construction serves
finite-scheme interpolation; it does not count a slice of the Fermat polynomial.
-/

noncomputable section
namespace Sheshadri.CommonProjectiveChart
open MvPolynomial MultiProjective
open scoped BigOperators

variable {K Z P : Type*} [Field K] [Infinite K] [Fintype Z] [Fintype P]

def coordinatePolynomial (x : Z → K) : Polynomial K :=
  ∑ i : Z, Polynomial.monomial ((Fintype.equivFin Z i).val) (x i)

theorem coefficient_coordinatePolynomial (x : Z → K) (i : Z) :
    (coordinatePolynomial x).coeff (Fintype.equivFin Z i).val = x i := by
  classical
  rw [coordinatePolynomial, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have h : (Fintype.equivFin Z j).val ≠ (Fintype.equivFin Z i).val := by
      intro he
      exact hji ((Fintype.equivFin Z).injective (Fin.ext he))
    simp [Polynomial.coeff_monomial, h]
  · simp

theorem coordinatePolynomial_ne_zero (x : Z → K) (hx : ∃ i, x i ≠ 0) :
    coordinatePolynomial x ≠ 0 := by
  obtain ⟨i,hi⟩ := hx
  intro he
  have h := coefficient_coordinatePolynomial x i
  rw [he, Polynomial.coeff_zero] at h
  exact hi h.symm

theorem exists_common_linear_form (points : P → Z → K)
    (hn : ∀ p, ∃ i, points p i ≠ 0) :
    ∃ l : Z → K, ∀ p, (∑ i, l i * points p i) ≠ 0 := by
  classical
  have hfinite : Set.Finite (⋃ p : P, {a : K | (coordinatePolynomial (points p)).IsRoot a}) :=
    Set.finite_iUnion (fun p => Polynomial.finite_setOf_isRoot
      (coordinatePolynomial_ne_zero (points p) (hn p)))
  obtain ⟨a,ha⟩ := hfinite.exists_not_mem
  refine ⟨fun i => a ^ (Fintype.equivFin Z i).val, ?_⟩
  intro p hp
  apply ha
  apply Set.mem_iUnion.mpr
  refine ⟨p, ?_⟩
  change (coordinatePolynomial (points p)).eval a = 0
  simpa [coordinatePolynomial, Polynomial.eval_finset_sum, mul_comm] using hp

variable {X U V : Type*} [Fintype X] [Fintype U] [Fintype V]

def firstForm (l : X → ℂ) : MvPolynomial (Variables X U V) ℂ :=
  ∑ i, C (l i) * MvPolynomial.X (Sum.inl i)

def secondForm (l : U → ℂ) : MvPolynomial (Variables X U V) ℂ :=
  ∑ i, C (l i) * MvPolynomial.X (Sum.inr (Sum.inl i))

def thirdForm (l : V → ℂ) : MvPolynomial (Variables X U V) ℂ :=
  ∑ i, C (l i) * MvPolynomial.X (Sum.inr (Sum.inr i))

theorem firstForm_homogeneous (l : X → ℂ) :
    (firstForm (U := U) (V := V) l).IsWeightedHomogeneous (weight X U V) (1,0,0) := by
  apply IsWeightedHomogeneous.sum
  intro i _
  simpa [weight] using (isWeightedHomogeneous_C (weight X U V) (l i)).mul
    (isWeightedHomogeneous_X ℂ (weight X U V) (Sum.inl i))

theorem secondForm_homogeneous (l : U → ℂ) :
    (secondForm (X := X) (V := V) l).IsWeightedHomogeneous (weight X U V) (0,1,0) := by
  apply IsWeightedHomogeneous.sum
  intro i _
  simpa [weight] using (isWeightedHomogeneous_C (weight X U V) (l i)).mul
    (isWeightedHomogeneous_X ℂ (weight X U V) (Sum.inr (Sum.inl i)))

theorem thirdForm_homogeneous (l : V → ℂ) :
    (thirdForm (X := X) (U := U) l).IsWeightedHomogeneous (weight X U V) (0,0,1) := by
  apply IsWeightedHomogeneous.sum
  intro i _
  simpa [weight] using (isWeightedHomogeneous_C (weight X U V) (l i)).mul
    (isWeightedHomogeneous_X ℂ (weight X U V) (Sum.inr (Sum.inr i)))

/-- Three actual linear forms, one in each block, simultaneously avoid all
selected points. The finite points need not initially share a coordinate chart. -/
theorem exists_three_common_forms (points : P → Variables X U V → ℂ)
    (hn : ∀ p, HasNonzeroBlocks (points p)) :
    ∃ (lx : X → ℂ) (lu : U → ℂ) (lv : V → ℂ),
      (∀ p, eval (points p) (firstForm lx) ≠ 0) ∧
      (∀ p, eval (points p) (secondForm lu) ≠ 0) ∧
      (∀ p, eval (points p) (thirdForm lv) ≠ 0) := by
  obtain ⟨lx,hx⟩ := exists_common_linear_form
    (fun p i => points p (Sum.inl i)) (fun p => (hn p).1)
  obtain ⟨lu,hu⟩ := exists_common_linear_form
    (fun p i => points p (Sum.inr (Sum.inl i))) (fun p => (hn p).2.1)
  obtain ⟨lv,hv⟩ := exists_common_linear_form
    (fun p i => points p (Sum.inr (Sum.inr i))) (fun p => (hn p).2.2)
  refine ⟨lx,lu,lv,?_,?_,?_⟩
  · simpa [firstForm] using hx
  · simpa [secondForm] using hu
  · simpa [thirdForm] using hv

/-- Scaling in the three projective blocks, used only to present the same
finite local schemes in a common affine chart. -/
def normalizedPoint (p : Variables X U V → ℂ) (a b c : ℂ) :
    Variables X U V → ℂ
  | .inl i => p (.inl i) * a⁻¹
  | .inr (.inl i) => p (.inr (.inl i)) * b⁻¹
  | .inr (.inr i) => p (.inr (.inr i)) * c⁻¹

theorem projectivelyEquivalent_of_normalized_eq
    (p q : Variables X U V → ℂ) (a b c a' b' c' : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ha' : a' ≠ 0) (hb' : b' ≠ 0) (hc' : c' ≠ 0)
    (he : normalizedPoint p a b c = normalizedPoint q a' b' c') :
    ProjectivelyEquivalent p q := by
  refine ⟨a/a', b/b', c/c', div_ne_zero ha ha', div_ne_zero hb hb',
    div_ne_zero hc hc', ?_, ?_, ?_⟩
  · intro i
    have h := congrFun he (.inl i)
    change p (.inl i) * a⁻¹ = q (.inl i) * a'⁻¹ at h
    calc
      p (.inl i) = (p (.inl i) * a⁻¹) * a := by simp [ha]
      _ = (q (.inl i) * a'⁻¹) * a := by rw [h]
      _ = (a/a') * q (.inl i) := by ring
  · intro i
    have h := congrFun he (.inr (.inl i))
    change p (.inr (.inl i)) * b⁻¹ = q (.inr (.inl i)) * b'⁻¹ at h
    calc
      p (.inr (.inl i)) = (p (.inr (.inl i)) * b⁻¹) * b := by simp [hb]
      _ = (q (.inr (.inl i)) * b'⁻¹) * b := by rw [h]
      _ = (b/b') * q (.inr (.inl i)) := by ring
  · intro i
    have h := congrFun he (.inr (.inr i))
    change p (.inr (.inr i)) * c⁻¹ = q (.inr (.inr i)) * c'⁻¹ at h
    calc
      p (.inr (.inr i)) = (p (.inr (.inr i)) * c⁻¹) * c := by simp [hc]
      _ = (q (.inr (.inr i)) * c'⁻¹) * c := by rw [h]
      _ = (c/c') * q (.inr (.inr i)) := by ring

theorem normalizedPoints_injective
    (points : P → Variables X U V → ℂ) (a b c : P → ℂ)
    (ha : ∀ p, a p ≠ 0) (hb : ∀ p, b p ≠ 0) (hc : ∀ p, c p ≠ 0)
    (hd : ∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q) :
    Function.Injective (fun p => normalizedPoint (points p) (a p) (b p) (c p)) := by
  intro p q he
  exact hd p q (projectivelyEquivalent_of_normalized_eq _ _ _ _ _ _ _ _
    (ha p) (hb p) (hc p) (ha q) (hb q) (hc q) he)

end Sheshadri.CommonProjectiveChart
