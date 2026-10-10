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
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Homogeneous components of equations of a scaling-stable set

The coefficient extraction below proves homogeneity from vanishing under
weighted scalar multiplication. It applies to actual vanishing ideals; no
homogeneity of those ideals is postulated.
-/

noncomputable section

namespace Sheshadri.HomogeneousVanishing

open MvPolynomial

variable {σ R K : Type*} [CommRing R] [CommRing K]

theorem prod_polynomial_monomial {ι : Type*} (s : Finset ι)
    (d : ι → ℕ) (c : ι → K) :
    ∏ i ∈ s, Polynomial.monomial (d i) (c i) =
      Polynomial.monomial (∑ i ∈ s, d i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih,
      Polynomial.monomial_mul_monomial]

def scalingPolynomial (f : R →+* K) (v : σ → K) (w : σ → ℕ)
    (p : MvPolynomial σ R) : Polynomial K :=
  p.eval₂ (Polynomial.C.comp f) (fun i => Polynomial.monomial (w i) (v i))

theorem scalingPolynomial_monomial (f : R →+* K) (v : σ → K) (w : σ → ℕ)
    (e : σ →₀ ℕ) (r : R) :
    scalingPolynomial f v w (monomial e r) =
      Polynomial.monomial (Finsupp.weight w e) ((monomial e r).eval₂ f v) := by
  classical
  simp only [scalingPolynomial, eval₂_monomial, RingHom.coe_comp, Function.comp_apply,
    Polynomial.monomial_pow, Finsupp.prod, prod_polynomial_monomial,
    Polynomial.C_mul_monomial, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  exact Nat.mul_comm _ _

theorem weightedComponent_monomial (w : σ → ℕ) (d : ℕ)
    (e : σ →₀ ℕ) (r : R) :
    weightedHomogeneousComponent w d (monomial e r) =
      if Finsupp.weight w e = d then monomial e r else 0 := by
  classical
  have h := isWeightedHomogeneous_monomial (w := w) e r rfl
  by_cases he : Finsupp.weight w e = d
  · rw [if_pos he, ← he]
    exact h.weightedHomogeneousComponent_same
  · rw [if_neg he]
    exact h.weightedHomogeneousComponent_ne d (Ne.symm he)

theorem scalingPolynomial_coeff (f : R →+* K) (v : σ → K) (w : σ → ℕ)
    (p : MvPolynomial σ R) (d : ℕ) :
    (scalingPolynomial f v w p).coeff d =
      (weightedHomogeneousComponent w d p).eval₂ f v := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e r =>
    rw [scalingPolynomial_monomial, weightedComponent_monomial]
    by_cases he : Finsupp.weight w e = d
    · simp [he]
    · simp [Polynomial.coeff_monomial, he, Ne.symm he]
  | add p q hp hq =>
    simp only [scalingPolynomial, eval₂_add, Polynomial.coeff_add,
      map_add] at *
    exact congrArg₂ (· + ·) hp hq

theorem scalingPolynomial_eval (f : R →+* K) (v : σ → K) (w : σ → ℕ)
    (p : MvPolynomial σ R) (t : K) :
    (scalingPolynomial f v w p).eval t = p.eval₂ f (fun i => t ^ w i * v i) := by
  change (Polynomial.evalRingHom t)
    (eval₂Hom (Polynomial.C.comp f) (fun i => Polynomial.monomial (w i) (v i)) p) = _
  rw [map_eval₂Hom]
  have hf : (Polynomial.evalRingHom t).comp (Polynomial.C.comp f) = f := by
    ext r
    simp
  rw [hf]
  simp [Polynomial.eval_monomial, mul_comm]

/-- Vanishing on all nonzero weighted rescalings forces every weighted
homogeneous component to vanish at the original point. -/
theorem weightedComponent_eval_zero [IsDomain K] [Infinite K]
    (f : R →+* K) (v : σ → K) (w : σ → ℕ) (p : MvPolynomial σ R)
    (h : ∀ t : K, t ≠ 0 → p.eval₂ f (fun i => t ^ w i * v i) = 0) (d : ℕ) :
    (weightedHomogeneousComponent w d p).eval₂ f v = 0 := by
  have hz : scalingPolynomial f v w p = 0 := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_univ.diff (Set.finite_singleton (0 : K))).mono
    intro t ht
    simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and] at ht
    simp only [Set.mem_setOf_eq, Polynomial.eval_zero, scalingPolynomial_eval]
    exact h t ht
  rw [← scalingPolynomial_coeff, hz, Polynomial.coeff_zero]

theorem weight_pair (w : σ → ℕ × ℕ) (e : σ →₀ ℕ) :
    Finsupp.weight w e =
      (Finsupp.weight (fun i => (w i).1) e, Finsupp.weight (fun i => (w i).2) e) := by
  classical
  simp only [Finsupp.weight_apply, Finsupp.sum]
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

/-- The two-graded projection is the composition of its two ordinary
weighted projections. -/
theorem biweightedComponent_eq_composition (w : σ → ℕ × ℕ)
    (p : MvPolynomial σ R) (a b : ℕ) :
    weightedHomogeneousComponent w (a, b) p =
      weightedHomogeneousComponent (fun i => (w i).2) b
        (weightedHomogeneousComponent (fun i => (w i).1) a p) := by
  classical
  ext e
  simp only [coeff_weightedHomogeneousComponent, weight_pair, Prod.mk.injEq]
  by_cases ha : Finsupp.weight (fun i => (w i).1) e = a <;>
    by_cases hb : Finsupp.weight (fun i => (w i).2) e = b <;> simp [ha, hb]

/-- Independent rescaling in two homogeneous blocks proves vanishing of
every bihomogeneous component. Zero-weight parameters are permitted. -/
theorem biweightedComponent_eval_zero [IsDomain K] [Infinite K]
    (f : R →+* K) (v : σ → K) (w : σ → ℕ × ℕ) (p : MvPolynomial σ R)
    (h : ∀ s t : K, s ≠ 0 → t ≠ 0 →
      p.eval₂ f (fun i => s ^ (w i).1 * (t ^ (w i).2 * v i)) = 0) (a b : ℕ) :
    (weightedHomogeneousComponent w (a, b) p).eval₂ f v = 0 := by
  rw [biweightedComponent_eq_composition]
  apply weightedComponent_eval_zero
  intro t ht
  apply weightedComponent_eval_zero
  intro s hs
  exact h s t hs ht

end Sheshadri.HomogeneousVanishing
