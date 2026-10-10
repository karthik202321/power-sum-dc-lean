/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.GenericHomogeneousSections
import Sheshadri.CompleteIntersectionHilbert

/-!
# Hilbert degree of filter-regular homogeneous sections

The actual eventual Hilbert polynomial has the expected complete-intersection
numerator even when multiplication has low-degree torsion. This extends the
globally regular exact-sequence calculation without imposing regularity on
irrelevant components of a homogeneous coordinate ring.
-/

noncomputable section
namespace Sheshadri.FilterRegularCompleteIntersection
open MvPolynomial FlatGradedHilbert HomogeneousQuotientExact
open GenericHomogeneousSections CompleteIntersectionHilbert

/-- Multiplication of a Hilbert-series numerator by `1-X^d` is the actual
degree-`d` finite difference of its eventual coefficient polynomial. -/
theorem hilbertPoly_mul_one_sub_X_pow (P : Polynomial ℚ) (s d : ℕ) :
    Polynomial.hilbertPoly (P * (1 - Polynomial.X ^ d)) s =
      Polynomial.hilbertPoly P s -
        (Polynomial.hilbertPoly P s).comp (Polynomial.X - Polynomial.C (d : ℚ)) := by
  symm
  apply Polynomial.eq_hilbertPoly_of_forall_coeff_eq_eval (P.natDegree + d)
  intro k hk
  have hdk : d ≤ k := by omega
  have hser : (((P * (1 - Polynomial.X ^ d) : Polynomial ℚ) : PowerSeries ℚ) *
      (PowerSeries.invOneSubPow ℚ s).val) =
        (P : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ s).val -
          PowerSeries.X ^ d * ((P : PowerSeries ℚ) * (PowerSeries.invOneSubPow ℚ s).val) := by
    simp only [Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_pow, Polynomial.coe_X]
    ring
  rw [hser, map_sub, PowerSeries.coeff_X_pow_mul', if_pos hdk,
    Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval s (by omega),
    Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval s (by omega)]
  simp only [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_X,
    Polynomial.eval_C, Nat.cast_sub hdk]

variable {Z K : Type*} [Fintype Z] [Field K]

theorem completeIntersectionPolynomial_succ (d : ℕ → ℕ) (r : ℕ) :
    completeIntersectionPolynomial (Z := Z) d (r + 1) =
      completeIntersectionPolynomial (Z := Z) d r -
        (completeIntersectionPolynomial (Z := Z) d r).comp
          (Polynomial.X - Polynomial.C (d r : ℚ)) := by
  unfold completeIntersectionPolynomial
  rw [show numerator d (r+1) = numerator d r * (1 - Polynomial.X ^ d r) by
    simp only [numerator, Finset.prod_range_succ]]
  exact hilbertPoly_mul_one_sub_X_pow _ _ _

/-- The expected complete-intersection polynomial is proved to describe
the actual quotient dimensions for filter-regular sequences. -/
theorem eventual_coordinate_polynomial_filterSequence
    (g : ℕ → MvPolynomial Z K) (d : ℕ → ℕ) (r : ℕ)
    (hZ : 0 < Fintype.card Z)
    (hg : ∀ j < r, (g j).IsHomogeneous (d j))
    (hreg : ∀ (j : ℕ) (hj : j < r), FilterRegular
      (idealSequence (⊥ : Ideal (MvPolynomial Z K)) g j) (g j) (hg j hj)) :
    ∃ N : ℕ, ∀ k > N,
      (completeIntersectionPolynomial (Z := Z) d r).eval (k : ℚ) =
        (Module.finrank K (coordinatePiece Z K
          (idealSequence (⊥ : Ideal (MvPolynomial Z K)) g r) k) : ℚ) := by
  induction r with
  | zero =>
    exact ⟨(numerator d 0).natDegree, fun k hk =>
      completeIntersectionPolynomial_eval g d 0 hZ hg (by intros; omega) k hk⟩
  | succ r ih =>
    have hg' := fun j (hj : j < r) => hg j (by omega)
    obtain ⟨N, hN⟩ := ih hg' (fun j hj => hreg j (by omega))
    have hI := idealSequence_homogeneous (⊥ : Ideal (MvPolynomial Z K))
      (by intro k p hp; simpa only [Ideal.mem_bot.mp hp, map_zero] using
        (Ideal.zero_mem (⊥ : Ideal (MvPolynomial Z K)))) g d r hg'
    obtain ⟨Q, M, hQ⟩ := HilbertPolynomialExistence.exists_coordinate_hilbert_polynomial
      (enlargedIdeal (idealSequence (⊥ : Ideal (MvPolynomial Z K)) g r) (g r))
      (enlargedIdeal_homogeneous _ hI (g r) (hg r (by omega)))
    have hdiff := hilbert_polynomial_difference_of_filterRegular _ hI (g r)
      (hg r (by omega)) (hreg r (by omega))
      (completeIntersectionPolynomial (Z := Z) d r) Q
      ⟨N, fun k hk => (hN k hk).symm⟩
      ⟨M, fun k hk => (hQ k (by omega)).symm⟩
    refine ⟨M, fun k hk => ?_⟩
    rw [completeIntersectionPolynomial_succ, ← hdiff]
    exact hQ k (by omega)

/-- At projective dimension zero, full eventual quotient dimension equals
the product of equation degrees for a filter-regular system. The statement
does not confuse quotient dimension with reduced point count. -/
theorem eventual_coordinate_finrank_eq_product_filterRegular
    (g : ℕ → MvPolynomial Z K) (d : ℕ → ℕ) (r : ℕ)
    (hr : Fintype.card Z = r + 1)
    (hg : ∀ j < r, (g j).IsHomogeneous (d j))
    (hreg : ∀ (j : ℕ) (hj : j < r), FilterRegular
      (idealSequence (⊥ : Ideal (MvPolynomial Z K)) g j) (g j) (hg j hj)) :
    ∃ N : ℕ, ∀ k > N,
      Module.finrank K (coordinatePiece Z K
        (idealSequence (⊥ : Ideal (MvPolynomial Z K)) g r) k) =
          ∏ j ∈ Finset.range r, d j := by
  have hlt : r < Fintype.card Z := by omega
  have hdegree : (completeIntersectionPolynomial (Z := Z) d r).natDegree = 0 := by
    have h := completeIntersectionPolynomial_natDegree_le (Z := Z) d r hlt
    omega
  have hconst : completeIntersectionPolynomial (Z := Z) d r =
      Polynomial.C (∏ j ∈ Finset.range r, (d j : ℚ)) := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdegree]
    congr 1
    have h := completeIntersectionPolynomial_degree_product (Z := Z) d r hlt
    simpa [hr] using h
  obtain ⟨N, hN⟩ := eventual_coordinate_polynomial_filterSequence g d r (by omega) hg hreg
  refine ⟨N, fun k hk => ?_⟩
  have he := hN k hk
  rw [hconst, Polynomial.eval_C] at he
  exact_mod_cast he.symm

end Sheshadri.FilterRegularCompleteIntersection
