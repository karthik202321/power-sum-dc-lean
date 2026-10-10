/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.HilbertStandardMonomials
import Sheshadri.MonomialHilbert
import Sheshadri.BiMonomialHilbert

/-!
# Hilbert-polynomial existence for actual homogeneous quotients

This proves eventual polynomiality of the actual dimensions of the graded
pieces of `K[variables]/I`, for any homogeneous ideal over a field. The proof
constructs standard-monomial coordinates, uses Dickson's lemma to obtain a
finite exponent obstruction set, and applies the explicit inclusion-exclusion
polynomial. No Hilbert polynomial or evaluation identity is assumed.
-/

noncomputable section

namespace Sheshadri.HilbertPolynomialExistence

open MvPolynomial HilbertStandardMonomials MonomialHilbert

variable {σ K : Type*} [Finite σ] [Field K]

/-- Genuine Hilbert-polynomial existence for the actual homogeneous
coordinate modules of any homogeneous ideal, including zero variables. -/
theorem exists_coordinate_hilbert_polynomial
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ d p, p ∈ I → homogeneousComponent d p ∈ I) :
    ∃ H : Polynomial ℚ, ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      H.eval (d : ℚ) =
        (Module.finrank K (FlatGradedHilbert.coordinatePiece σ K I d) : ℚ) := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  by_cases hσ : 0 < Fintype.card σ
  · obtain ⟨G, hG⟩ := exists_finite_hilbert_function (finiteMonomialOrder (σ := σ)) I hI
    refine ⟨standardHilbertPolynomial G, threshold G, ?_⟩
    intro d hd
    rw [hG d]
    exact standardHilbertPolynomial_eval hσ G d hd
  · have hz : Fintype.card σ = 0 := Nat.eq_zero_of_not_pos hσ
    letI : IsEmpty σ := Fintype.card_eq_zero_iff.mp hz
    refine ⟨0, 1, ?_⟩
    intro d hd
    rw [finrank_coordinatePiece (finiteMonomialOrder (σ := σ)) I hI d]
    letI : IsEmpty {e : σ →₀ ℕ //
        standardExponent (finiteMonomialOrder (σ := σ)) I e ∧ e.degree = d} :=
      ⟨by
        rintro ⟨e, _, hdeg⟩
        have he : e = 0 := Subsingleton.elim _ _
        simp only [he, Finsupp.degree_zero] at hdeg
        omega⟩
    simp

section Bigraded

variable {τ : Type*} [Finite τ]

def sumBlock : σ ⊕ τ → Bool := Sum.elim (fun _ => true) (fun _ => false)

def exponentEquiv : (σ ⊕ τ →₀ ℕ) ≃ BiMonomialHilbert.Exponent σ τ :=
  Finsupp.sumFinsuppEquivProdFinsupp

theorem exponentEquiv_le (e f : σ ⊕ τ →₀ ℕ) :
    exponentEquiv e ≤ exponentEquiv f ↔ e ≤ f := by
  constructor
  · intro h i
    cases i with
    | inl i => exact h.1 i
    | inr i => exact h.2 i
  · intro h
    exact ⟨fun i => h (Sum.inl i), fun i => h (Sum.inr i)⟩

theorem weight_eq_exponent_degrees (e : σ ⊕ τ →₀ ℕ) :
    Finsupp.weight (FlatGradedHilbert.twoBlockWeight (σ ⊕ τ) sumBlock) e =
      ((exponentEquiv e).1.degree, (exponentEquiv e).2.degree) := by
  classical
  obtain ⟨⟨l, r⟩, rfl⟩ := exponentEquiv.symm.surjective e
  simp only [Equiv.apply_symm_apply, exponentEquiv, Finsupp.sumFinsuppEquivProdFinsupp_symm_apply,
    Finsupp.weight_apply, Finsupp.sum_sumElim]
  ext <;> simp [FlatGradedHilbert.twoBlockWeight, sumBlock, Finsupp.sum, Finsupp.degree,
    Prod.fst_sum, Prod.snd_sum]

/-- Genuine two-variable Hilbert-polynomial existence for an arbitrary
bihomogeneous ideal, with nonempty variable blocks as in a projective product. -/
theorem exists_bicoordinate_hilbert_polynomial [Nonempty σ] [Nonempty τ]
    (I : Ideal (MvPolynomial (σ ⊕ τ) K))
    (hI : FlatGradedHilbert.IsBihomogeneous (σ ⊕ τ) K sumBlock I) :
    ∃ H : Polynomial (Polynomial ℚ), ∃ N : ℕ, ∀ a b : ℕ, N ≤ a → N ≤ b →
      BiMonomialHilbert.biEval H a b =
        (Module.finrank K (FlatGradedHilbert.bicoordinatePiece (σ ⊕ τ) K sumBlock I a b) : ℚ) := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  letI : Fintype τ := Fintype.ofFinite τ
  let w := FlatGradedHilbert.twoBlockWeight (σ ⊕ τ) (sumBlock (σ := σ) (τ := τ))
  obtain ⟨G, hG⟩ := exists_finite_weighted_hilbert_function w
    (finiteMonomialOrder (σ := σ ⊕ τ)) I
    (fun d => hI d.1 d.2) (fun d =>
      FlatGradedHilbert.finite_monomials_of_bidegree (σ ⊕ τ) sumBlock d.1 d.2)
  let G' := G.image exponentEquiv
  have hc (a b : ℕ) :
      Module.finrank K (FlatGradedHilbert.bicoordinatePiece (σ ⊕ τ) K sumBlock I a b) =
        BiMonomialHilbert.biStandardCount G' a b := by
    change Module.finrank K (weightedCoordinatePiece w I (a, b)) = _
    rw [hG (a, b)]
    apply Nat.card_congr
    refine Equiv.subtypeEquiv exponentEquiv ?_
    intro e
    change (Finsupp.weight w e = (a,b) ∧ ∀g∈G, ¬g≤e) ↔ _
    simp only [w, weight_eq_exponent_degrees, Prod.mk.injEq,
      G', Finset.forall_mem_image, exponentEquiv_le, and_assoc]
  refine ⟨BiMonomialHilbert.biStandardHilbertPolynomial G',
    max (BiMonomialHilbert.thresholdLeft G') (BiMonomialHilbert.thresholdRight G'), ?_⟩
  intro a b ha hb
  rw [hc a b]
  exact BiMonomialHilbert.biStandardHilbertPolynomial_eval
    Fintype.card_pos Fintype.card_pos G' a b
    ((le_max_left _ _).trans ha) ((le_max_right _ _).trans hb)

end Bigraded

end Sheshadri.HilbertPolynomialExistence
