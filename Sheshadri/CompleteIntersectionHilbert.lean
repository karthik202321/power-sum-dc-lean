/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.HomogeneousQuotientExact
import Sheshadri.MonomialHilbert

/-! Hilbert series and degree of actual homogeneous complete intersections.
Regularity is the conventional nonzerodivisor condition in the actual
successive quotient rings. Generic polar sections have not been asserted to
satisfy it here. -/

noncomputable section
namespace Sheshadri.CompleteIntersectionHilbert
open MvPolynomial FlatGradedHilbert HomogeneousQuotientExact MonomialHilbert

variable {Z K : Type*} [Fintype Z] [Field K]

theorem finrank_coordinatePiece_bot (k : ℕ) :
    Module.finrank K (coordinatePiece Z K (⊥ : Ideal (MvPolynomial Z K)) k) =
      (Fintype.card Z + k - 1).choose k := by
  classical
  have hinj : Function.Injective
      (Ideal.Quotient.mkₐ K (⊥ : Ideal (MvPolynomial Z K))).toLinearMap := by
    intro p q hpq
    exact sub_eq_zero.mp (Ideal.mem_bot.mp (Ideal.Quotient.eq.mp hpq))
  calc
    _ = Module.finrank K (homogeneousSubmodule Z K k) :=
      ((homogeneousSubmodule Z K k).equivMapOfInjective _ hinj).symm.finrank_eq
    _ = Module.finrank K (Finsupp.supported K K {e : Z →₀ ℕ | e.degree = k}) := by
      rw [homogeneousSubmodule_eq_finsupp_supported]
      rfl
    _ = Module.finrank K (DegreeMonomials Z k →₀ K) :=
      (Finsupp.supportedEquivFinsupp (R := K) {e : Z →₀ ℕ | e.degree = k}).finrank_eq
    _ = Fintype.card (DegreeMonomials Z k) := Module.finrank_finsupp_self K
    _ = _ := card_degreeMonomials Z k

theorem coordinateHilbertSeries_bot (hZ : 0 < Fintype.card Z) :
    coordinateHilbertSeries (⊥ : Ideal (MvPolynomial Z K)) =
      (PowerSeries.invOneSubPow ℚ (Fintype.card Z)).val := by
  ext k
  rw [coeff_coordinateHilbertSeries, finrank_coordinatePiece_bot,
    PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos _ _ hZ,
    PowerSeries.coeff_mk]
  congr 1
  rw [show Fintype.card Z + k - 1 = k + (Fintype.card Z - 1) by omega,
    ← Nat.choose_symm (show k ≤ k + (Fintype.card Z - 1) by omega)]
  congr 1 <;> omega

def numerator (d : ℕ → ℕ) (r : ℕ) : Polynomial ℚ :=
  ∏ j ∈ Finset.range r, (1 - Polynomial.X ^ d j)

def reducedNumerator (d : ℕ → ℕ) (r : ℕ) : Polynomial ℚ :=
  ∏ j ∈ Finset.range r, ∑ i ∈ Finset.range (d j), Polynomial.X ^ i

theorem numerator_factor (d : ℕ → ℕ) (r : ℕ) :
    numerator d r = reducedNumerator d r * (1 - Polynomial.X) ^ r := by
  unfold numerator reducedNumerator
  simp_rw [← geom_sum_mul_neg Polynomial.X]
  rw [Finset.prod_mul_distrib]
  simp

theorem reducedNumerator_eval_one (d : ℕ → ℕ) (r : ℕ) :
    (reducedNumerator d r).eval 1 = ∏ j ∈ Finset.range r, (d j : ℚ) := by
  simp [reducedNumerator, Polynomial.eval_prod, Polynomial.eval_finset_sum]

theorem regular_sequence_series
    (g : ℕ → MvPolynomial Z K) (d : ℕ → ℕ) (r : ℕ)
    (hZ : 0 < Fintype.card Z)
    (hg : ∀ j < r, (g j).IsHomogeneous (d j))
    (hreg : ∀ j < r, IsRegular (Ideal.Quotient.mk
      (idealSequence (⊥ : Ideal (MvPolynomial Z K)) g j) (g j))) :
    coordinateHilbertSeries (idealSequence (⊥ : Ideal (MvPolynomial Z K)) g r) =
      (numerator d r : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ (Fintype.card Z)).val := by
  rw [coordinateHilbertSeries_regular_sequence _
    (by intro k p hp; simpa only [Ideal.mem_bot.mp hp, map_zero] using (Ideal.zero_mem (⊥ : Ideal (MvPolynomial Z K))))
    g d r hg hreg, coordinateHilbertSeries_bot hZ]
  congr 1
  change _ = Polynomial.coeToPowerSeries.ringHom (numerator d r)
  simp [numerator, map_prod, Polynomial.coe_sub]

def completeIntersectionPolynomial (d : ℕ → ℕ) (r : ℕ) : Polynomial ℚ :=
  Polynomial.hilbertPoly (numerator d r) (Fintype.card Z)

/-- An explicit polynomial for the actual quotient dimensions. -/
theorem completeIntersectionPolynomial_eval
    (g : ℕ → MvPolynomial Z K) (d : ℕ → ℕ) (r : ℕ)
    (hZ : 0 < Fintype.card Z)
    (hg : ∀ j < r, (g j).IsHomogeneous (d j))
    (hreg : ∀ j < r, IsRegular (Ideal.Quotient.mk
      (idealSequence (⊥ : Ideal (MvPolynomial Z K)) g j) (g j)))
    (k : ℕ) (hk : (numerator d r).natDegree < k) :
    (completeIntersectionPolynomial (Z := Z) d r).eval (k : ℚ) =
      (Module.finrank K (coordinatePiece Z K
        (idealSequence (⊥ : Ideal (MvPolynomial Z K)) g r) k) : ℚ) := by
  rw [← coeff_coordinateHilbertSeries, regular_sequence_series g d r hZ hg hreg]
  exact (Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval _ hk).symm

theorem coeff_hilbertPoly_succ (P : Polynomial ℚ) (s : ℕ) :
    (Polynomial.hilbertPoly P (s + 1)).coeff s = P.eval 1 / (s.factorial : ℚ) := by
  rw [Polynomial.hilbertPoly_succ]
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_smul,
    Polynomial.coeff_preHilbertPoly_self, smul_eq_mul, ← Finset.sum_mul]
  rw [div_eq_mul_inv]
  congr 1
  simp [Polynomial.eval_eq_sum, Polynomial.sum_def]

/-- The product of the equation degrees is the factorial-normalized top
Hilbert coefficient of the actual complete intersection. -/
theorem completeIntersectionPolynomial_degree_product
    (d : ℕ → ℕ) (r : ℕ) (hr : r < Fintype.card Z) :
    (completeIntersectionPolynomial (Z := Z) d r).coeff (Fintype.card Z - r - 1) *
      ((Fintype.card Z - r - 1).factorial : ℚ) =
        ∏ j ∈ Finset.range r, (d j : ℚ) := by
  have hn : Fintype.card Z = (Fintype.card Z - r - 1) + 1 + r := by omega
  rw [completeIntersectionPolynomial, numerator_factor]
  nth_rw 1 [hn]
  rw [Polynomial.hilbertPoly_mul_one_sub_pow_add, coeff_hilbertPoly_succ,
    div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)),
    reducedNumerator_eval_one]

theorem completeIntersectionPolynomial_natDegree_le
    (d : ℕ → ℕ) (r : ℕ) (hr : r < Fintype.card Z) :
    (completeIntersectionPolynomial (Z := Z) d r).natDegree ≤ Fintype.card Z - r - 1 := by
  have hn : Fintype.card Z = (Fintype.card Z - r - 1) + 1 + r := by omega
  rw [completeIntersectionPolynomial, numerator_factor]
  nth_rw 1 [hn]
  rw [Polynomial.hilbertPoly_mul_one_sub_pow_add]
  by_cases h : Polynomial.hilbertPoly (reducedNumerator d r)
      (Fintype.card Z - r - 1 + 1) = 0
  · rw [h, Polynomial.natDegree_zero]
    omega
  · rw [Polynomial.natDegree_hilbertPoly_of_ne_zero h]
    omega

theorem completeIntersectionPolynomial_natDegree
    (d : ℕ → ℕ) (r : ℕ) (hr : r < Fintype.card Z)
    (hd : ∀ j < r, 0 < d j) :
    (completeIntersectionPolynomial (Z := Z) d r).natDegree = Fintype.card Z - r - 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (completeIntersectionPolynomial_natDegree_le d r hr)
  intro hz
  have hprod : (∏ j ∈ Finset.range r, (d j : ℚ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact Nat.cast_ne_zero.mpr (hd j (Finset.mem_range.mp hj)).ne'
  have he := completeIntersectionPolynomial_degree_product (Z := Z) d r hr
  rw [hz, zero_mul] at he
  exact hprod he.symm

/-- In projective dimension zero the eventual coordinate Hilbert function
is exactly the product of the degrees. Reduced-point counting requires a
separate identification with the resulting zero-dimensional scheme. -/
theorem eventual_coordinate_finrank_eq_product
    (g : ℕ → MvPolynomial Z K) (d : ℕ → ℕ) (r : ℕ)
    (hr : Fintype.card Z = r + 1)
    (hg : ∀ j < r, (g j).IsHomogeneous (d j))
    (hreg : ∀ j < r, IsRegular (Ideal.Quotient.mk
      (idealSequence (⊥ : Ideal (MvPolynomial Z K)) g j) (g j))) :
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
  refine ⟨(numerator d r).natDegree, ?_⟩
  intro k hk
  have he := completeIntersectionPolynomial_eval g d r (by omega) hg hreg k hk
  rw [hconst, Polynomial.eval_C] at he
  exact_mod_cast he.symm

end Sheshadri.CompleteIntersectionHilbert
