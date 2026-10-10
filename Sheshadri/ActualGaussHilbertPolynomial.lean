/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.GradedGaussBaseChange
import Sheshadri.HilbertPolynomialExistence

/-!
# Constructed Hilbert polynomials of the actual Gauss fibres

Homogeneity of the specialized ideal is proved by commuting coefficient
specialization with weighted projection. Eventual-polynomial existence then
applies to this literal field quotient; the scalar-compatible base-change
equivalence identifies its graded pieces with the actual family fibres.
-/

noncomputable section

namespace Sheshadri.ActualGaussHilbertPolynomial

open MvPolynomial ActualGaussFamily ActualGaussCoefficientRing
open GradedGaussBaseChange FlatGradedHilbert

/-- Coefficient specialization commutes with the actual homogeneous
projection, over arbitrary coefficient rings and grading monoids. -/
theorem weightedComponent_map {σ R S Γ : Type*} [CommRing R] [CommRing S]
    [AddCommMonoid Γ] [DecidableEq Γ] (f : R →+* S) (w : σ → Γ)
    (d : Γ) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w d (MvPolynomial.map f p) =
      MvPolynomial.map f (weightedHomogeneousComponent w d p) := by
  classical
  ext e
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp

variable {Z : Type} [Fintype Z]

/-- The actual specialized fibre ideal is bihomogeneous. This property
is derived from the total ideal, not postulated for the fibre. -/
theorem fibreIdeal_bihomogeneous
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ) :
    IsBihomogeneous (SpatialVariables Z) ℂ ActualGaussHilbert.spatialBlock
      (fibreIdeal F U (fun _ => c)) := by
  intro a b p hp
  obtain ⟨q, hq, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective (specialize (Z := Z) (fun _ : Unit => c))
      (ActualGaussBaseChange.specialize_surjective (fun _ : Unit => c))).mp hp
  let q' := coefficientAlgEquiv q
  have hq' : q' ∈ coefficientIdeal F U :=
    Ideal.mem_map_of_mem coefficientAlgEquiv.toRingHom hq
  have hh := coefficientIdeal_bihomogeneous F U a b q' hq'
  have hh' := (mem_coefficientIdeal_iff F U _).mp hh
  have hmap : specialize (fun _ : Unit => c) q =
      MvPolynomial.map (Polynomial.evalRingHom c) q' := by
    simpa only [q', AlgEquiv.symm_apply_apply] using
      specialize_coefficientEquiv_symm c q'
  rw [hmap, weightedComponent_map]
  rw [← specialize_coefficientEquiv_symm]
  exact Ideal.mem_map_of_mem (specialize (fun _ : Unit => c)) hh'

open ActualGaussHilbert HilbertPolynomialExistence

/-- Eventual polynomiality of the actual Gauss-family fibre Hilbert values.
The polynomial and its evaluation law are conclusions, not supplied data. -/
theorem exists_actual_gauss_hilbert_polynomial
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ) :
    ∃ H : Polynomial (Polynomial ℚ), ∃ N : ℕ, ∀ a b : ℕ, N ≤ a → N ≤ b →
      BiMonomialHilbert.biEval H a b = (specialHilbertValue F U c a b : ℚ) := by
  obtain ⟨H, N, hH⟩ := exists_bicoordinate_hilbert_polynomial
    (fibreIdeal F U (fun _ : Unit => c)) (fibreIdeal_bihomogeneous F U c)
  refine ⟨H, N, ?_⟩
  intro a b ha hb
  rw [← specializedPiece_finrank_eq_specialHilbertValue]
  exact hH a b ha hb

/-- A Hilbert polynomial constructed from the actual specialized ideal. -/
def actualHilbertPolynomial
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ) :
    Polynomial (Polynomial ℚ) :=
  (exists_actual_gauss_hilbert_polynomial F U c).choose

def actualHilbertThreshold
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ) : ℕ :=
  (exists_actual_gauss_hilbert_polynomial F U c).choose_spec.choose

theorem actualHilbertPolynomial_eval
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ)
    (a b : ℕ) (ha : actualHilbertThreshold F U c ≤ a)
    (hb : actualHilbertThreshold F U c ≤ b) :
    BiMonomialHilbert.biEval (actualHilbertPolynomial F U c) a b =
      (specialHilbertValue F U c a b : ℚ) :=
  (exists_actual_gauss_hilbert_polynomial F U c).choose_spec.choose_spec a b ha hb

/-- Conservation of the actual, constructed two-variable Hilbert
polynomials. The only family hypothesis is openness of the good parameters. -/
theorem actualHilbertPolynomial_constant
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U)
    (c c' : ℂ) : actualHilbertPolynomial F U c = actualHilbertPolynomial F U c' := by
  let N := max (actualHilbertThreshold F U c) (actualHilbertThreshold F U c')
  apply polynomial_eq_of_nat_grid_tail_eval_eq _ _ N N
  intro a b ha hb
  change BiMonomialHilbert.biEval (actualHilbertPolynomial F U c) a b =
    BiMonomialHilbert.biEval (actualHilbertPolynomial F U c') a b
  rw [actualHilbertPolynomial_eval F U c a b ((le_max_left _ _).trans ha)
      ((le_max_left _ _).trans hb),
    actualHilbertPolynomial_eval F U c' a b ((le_max_right _ _).trans ha)
      ((le_max_right _ _).trans hb),
    actual_gauss_specialHilbertValue_constant F U hU c c' a b]

/-- Every coefficient of the actual fibre Hilbert polynomial is conserved.
Relating these coefficients to projective intersection numbers is separate. -/
theorem actualHilbertPolynomial_coefficients_constant
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U)
    (c c' : ℂ) (i j : ℕ) :
    ((actualHilbertPolynomial F U c).coeff i).coeff j =
      ((actualHilbertPolynomial F U c').coeff i).coeff j := by
  rw [actualHilbertPolynomial_constant F U hU c c']

end Sheshadri.ActualGaussHilbertPolynomial
