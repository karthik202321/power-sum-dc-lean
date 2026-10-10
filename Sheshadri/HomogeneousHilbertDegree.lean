/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.MonomialOrthantDecomposition
import Sheshadri.GenericHomogeneousSections

/-!
# Actual Hilbert degree under saturation and regular sections

Ideal enlargement cannot increase the degree of the actual Hilbert polynomial.
The proof constructs disjoint standard-monomial orthants, whose top coefficients
are positive. A filter-regular homogeneous equation takes a finite difference
and lowers the degree by one, with natural subtraction handling constant and
zero polynomials. These are actual quotient statements, not dimension axioms.
-/
noncomputable section
namespace Sheshadri.HomogeneousHilbertDegree
open MvPolynomial HilbertStandardMonomials MonomialOrthantDecomposition
open FlatGradedHilbert GenericHomogeneousSections HomogeneousQuotientExact
attribute [local instance] Classical.propDecidable

variable {σ K : Type*} [Fintype σ] [Field K]

/-- Positive orthant expansion for one grading. -/
def orthantPolynomial (B : ℕ) (P : Cell σ B → Prop) : Polynomial ℚ :=
  ∑ c : {c : Cell σ B // P c}, cellPolynomial c.val

theorem orthantPolynomial_eval (B : ℕ) (P : Cell σ B → Prop) (d : ℕ)
    (hd : ∀ c : Cell σ B, (base c).degree < d) :
    (orthantPolynomial B P).eval (d : ℚ) =
      Nat.card {e : MonomialHilbert.DegreeMonomials σ d // P (cell B e.val)} := by
  classical
  rw [card_degree_cells B P d (fun c => (hd c).le)]
  simp only [orthantPolynomial, Polynomial.eval_finset_sum, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun c _ => cellPolynomial_eval c.val d (hd _))

theorem cellPolynomial_coeff_nonneg {B : ℕ} (c : Cell σ B) (i : ℕ)
    (hi : Fintype.card (Free c) - 1 ≤ i) : 0 ≤ (cellPolynomial c).coeff i := by
  by_cases hc : 0 < Fintype.card (Free c)
  · by_cases heq : i = Fintype.card (Free c) - 1
    · rw [heq, cellPolynomial_top_coefficient c hc]
      positivity
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      simpa only [cellPolynomial, if_pos hc, Polynomial.natDegree_preHilbertPoly] using
        (show Fintype.card (Free c) - 1 < i by omega)
  · simp [cellPolynomial,hc]

/-- Positive top terms prevent cancellation of high-dimensional orthants. -/
theorem active_cell_degree_le (B : ℕ) (P : Cell σ B → Prop) (r : ℕ)
    (hr : (orthantPolynomial B P).natDegree ≤ r)
    (c : {c : Cell σ B // P c}) (hc : 0 < Fintype.card (Free c.val)) :
    Fintype.card (Free c.val) - 1 ≤ r := by
  classical
  let S : Finset {c : Cell σ B // P c} :=
    Finset.univ.filter fun c => 0 < Fintype.card (Free c.val)
  have hcS : c ∈ S := by simp [S,hc]
  obtain ⟨e,he,hmax⟩ := Finset.exists_max_image S
    (fun c => Fintype.card (Free c.val) - 1) ⟨c,hcS⟩
  have heA : 0 < Fintype.card (Free e.val) := (Finset.mem_filter.mp he).2
  have hpos : 0 < (orthantPolynomial B P).coeff (Fintype.card (Free e.val) - 1) := by
    simp only [orthantPolynomial,Polynomial.finset_sum_coeff]
    apply Finset.sum_pos'
    · intro z _
      by_cases hz : 0 < Fintype.card (Free z.val)
      · exact cellPolynomial_coeff_nonneg z.val _ (hmax z (by simp [S,hz]))
      · simp [cellPolynomial,hz]
    · refine ⟨e,Finset.mem_univ _,?_⟩
      rw [cellPolynomial_top_coefficient e.val heA]
      positivity
  have hedeg : Fintype.card (Free e.val) - 1 ≤ r := by
    by_contra h
    have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (p := orthantPolynomial B P)
      (show (orthantPolynomial B P).natDegree < Fintype.card (Free e.val) - 1 by omega)
    rw [hz] at hpos
    exact lt_irrefl _ hpos
  exact (hmax c hcS).trans hedeg

/-- Selecting fewer of the actual orthants cannot increase Hilbert degree. -/
theorem orthant_natDegree_mono (B : ℕ) (P Q : Cell σ B → Prop)
    (hQP : ∀ c, Q c → P c) :
    (orthantPolynomial B Q).natDegree ≤ (orthantPolynomial B P).natDegree := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro c _
  by_cases hc : 0 < Fintype.card (Free c.val)
  · rw [cellPolynomial,if_pos hc,Polynomial.natDegree_preHilbertPoly]
    exact active_cell_degree_le B P _ le_rfl ⟨c.val,hQP c.val c.property⟩ hc
  · simp [cellPolynomial,hc]

/-- Finite truncation detects every standard monomial of an actual ideal. -/
theorem exists_standard_cell_bound (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) :
    ∃ B₀ : ℕ, ∀ B, B₀ ≤ B → ∀ e,
      standardExponent m I e ↔ standardExponent m I (base (cell B e)) := by
  obtain ⟨G,hG⟩ := exists_finite_standard_exponent_test m I
  refine ⟨generatorBound G, fun B hB e => ?_⟩
  rw [hG,hG]
  exact avoids_iff_cell_avoids G B hB e

/-- The positive expansion equals the actual eventual Hilbert polynomial. -/
theorem hilbertPolynomial_eq_orthant (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ d p, p ∈ I → homogeneousComponent d p ∈ I)
    (H : Polynomial ℚ) (N : ℕ)
    (hH : ∀ d : ℕ, N ≤ d → H.eval (d : ℚ) =
      (Module.finrank K (coordinatePiece σ K I d) : ℚ))
    (B : ℕ) (hB : ∀ e, standardExponent m I e ↔ standardExponent m I (base (cell B e))) :
    H = orthantPolynomial B (fun c => standardExponent m I (base c)) := by
  classical
  let T := (Finset.univ : Finset (Cell σ B)).sup (fun c => (base c).degree)
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Ici_infinite (max N (T+1))).image
    (Nat.cast_injective (R := ℚ)).injOn).mono
  rintro x ⟨d,hd,rfl⟩
  change max N (T+1) ≤ d at hd
  have hdeg : ∀ c : Cell σ B, (base c).degree < d := by
    intro c
    have hle : (base c).degree ≤ T := Finset.le_sup
      (f := fun c : Cell σ B => (base c).degree) (Finset.mem_univ c)
    omega
  change H.eval (d : ℚ) = _
  rw [hH d (by omega), orthantPolynomial_eval B _ d hdeg,
    finrank_coordinatePiece m I hI]
  congr 1
  apply Nat.card_congr
  exact
    { toFun := fun e => ⟨⟨e.val,e.property.2⟩,(hB e.val).mp e.property.1⟩
      invFun := fun e => ⟨e.val.val,(hB e.val.val).mpr e.property,e.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Degree cannot increase under an actual homogeneous ideal enlargement.
This includes every literal saturation, since saturation enlarges its ideal. -/
theorem quotient_hilbert_natDegree_le
    (I J : Ideal (MvPolynomial σ K)) (hIJ : I ≤ J)
    (hI : ∀ d p, p ∈ I → homogeneousComponent d p ∈ I)
    (hJ : ∀ d p, p ∈ J → homogeneousComponent d p ∈ J)
    (PI PJ : Polynomial ℚ) (NI NJ : ℕ)
    (hPI : ∀ d : ℕ, NI ≤ d → PI.eval (d : ℚ) =
      (Module.finrank K (coordinatePiece σ K I d) : ℚ))
    (hPJ : ∀ d : ℕ, NJ ≤ d → PJ.eval (d : ℚ) =
      (Module.finrank K (coordinatePiece σ K J d) : ℚ)) :
    PJ.natDegree ≤ PI.natDegree := by
  let m := finiteMonomialOrder (σ := σ)
  obtain ⟨BI,hBI⟩ := exists_standard_cell_bound m I
  obtain ⟨BJ,hBJ⟩ := exists_standard_cell_bound m J
  let B := max BI BJ
  rw [hilbertPolynomial_eq_orthant m I hI PI NI hPI B (hBI B (le_max_left _ _)),
    hilbertPolynomial_eq_orthant m J hJ PJ NJ hPJ B (hBJ B (le_max_right _ _))]
  apply orthant_natDegree_mono
  intro c hc p hp hne
  exact hc p (hIJ hp) hne

/-- Finite differences lower polynomial degree, including constant and
zero polynomials. The shift may even be zero. -/
theorem natDegree_sub_comp_le (P : Polynomial ℚ) (a : ℚ) :
    (P - P.comp (Polynomial.X - Polynomial.C a)).natDegree ≤ P.natDegree - 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  have hc : (P.comp (Polynomial.X - Polynomial.C a)).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_comp,Polynomial.natDegree_X_sub_C,mul_one]
  rw [Polynomial.coeff_sub]
  by_cases hlt : P.natDegree < i
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hc ▸ hlt),sub_self]
  · have heq : i = P.natDegree := by omega
    rw [heq,Polynomial.coeff_natDegree,← hc,Polynomial.coeff_natDegree,
      Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_X_sub_C]; decide),
      Polynomial.leadingCoeff_X_sub_C,one_pow,mul_one,sub_self]

/-- The actual quotient by a filter-regular equation has Hilbert degree at
most one less than the original quotient. -/
theorem filterRegular_cut_natDegree_le
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ d p, p ∈ I → homogeneousComponent d p ∈ I)
    (g : MvPolynomial σ K) {e : ℕ} (hg : g.IsHomogeneous e)
    (hreg : FilterRegular I g hg) (P Q : Polynomial ℚ) (NP NQ : ℕ)
    (hP : ∀ d : ℕ, NP ≤ d → P.eval (d : ℚ) =
      (Module.finrank K (coordinatePiece σ K I d) : ℚ))
    (hQ : ∀ d : ℕ, NQ ≤ d → Q.eval (d : ℚ) =
      (Module.finrank K (coordinatePiece σ K (enlargedIdeal I g) d) : ℚ)) :
    Q.natDegree ≤ P.natDegree - 1 := by
  have heq := hilbert_polynomial_difference_of_filterRegular I hI g hg hreg P Q
    ⟨NP,fun d hd => (hP d hd.le).symm⟩ ⟨NQ,fun d hd => (hQ d hd.le).symm⟩
  rw [heq]
  exact natDegree_sub_comp_le P (e : ℚ)

/-- Globally regular equations give the same proved degree drop. -/
theorem regular_cut_natDegree_le
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ d p, p ∈ I → homogeneousComponent d p ∈ I)
    (g : MvPolynomial σ K) {e : ℕ} (hg : g.IsHomogeneous e)
    (hreg : IsRegular (Ideal.Quotient.mk I g))
    (P Q : Polynomial ℚ) (NP NQ : ℕ)
    (hP : ∀ d : ℕ, NP ≤ d → P.eval (d : ℚ) =
      (Module.finrank K (coordinatePiece σ K I d) : ℚ))
    (hQ : ∀ d : ℕ, NQ ≤ d → Q.eval (d : ℚ) =
      (Module.finrank K (coordinatePiece σ K (enlargedIdeal I g) d) : ℚ)) :
    Q.natDegree ≤ P.natDegree - 1 :=
  filterRegular_cut_natDegree_le I hI g hg (regular_filterRegular I g hg hreg)
    P Q NP NQ hP hQ

/-- Cutting an eventual constant Hilbert polynomial by a filter-regular
equation makes the next actual Hilbert polynomial zero. -/
theorem filterRegular_cut_eq_zero_of_natDegree_eq_zero
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ d p, p ∈ I → homogeneousComponent d p ∈ I)
    (g : MvPolynomial σ K) {e : ℕ} (hg : g.IsHomogeneous e)
    (hreg : FilterRegular I g hg) (P Q : Polynomial ℚ) (NP NQ : ℕ)
    (hP : ∀ d : ℕ, NP ≤ d → P.eval (d : ℚ) =
      (Module.finrank K (coordinatePiece σ K I d) : ℚ))
    (hQ : ∀ d : ℕ, NQ ≤ d → Q.eval (d : ℚ) =
      (Module.finrank K (coordinatePiece σ K (enlargedIdeal I g) d) : ℚ))
    (hdeg : P.natDegree = 0) : Q = 0 := by
  have heq := hilbert_polynomial_difference_of_filterRegular I hI g hg hreg P Q
    ⟨NP,fun d hd => (hP d hd.le).symm⟩ ⟨NQ,fun d hd => (hQ d hd.le).symm⟩
  rw [heq,Polynomial.eq_C_of_natDegree_eq_zero hdeg]
  simp

end Sheshadri.HomogeneousHilbertDegree
