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
import Sheshadri.HilbertPolynomialExistence

/-!
# Top mixed Hilbert coefficients are monotone for actual closed subschemes

The proof uses one common monomial order for two nested bihomogeneous ideals.
Their standard monomials form nested sets and admit a shared finite disjoint
orthant decomposition. Positivity follows from the top terms of those actual
orthants. It is not inferred from pointwise inequalities of Hilbert functions.
-/
noncomputable section
namespace Sheshadri.MixedHilbertComparison
open MvPolynomial HilbertStandardMonomials HilbertPolynomialExistence
open MonomialOrthantDecomposition FlatGradedHilbert
attribute [local instance] Classical.propDecidable

variable {σ τ K : Type*} [Fintype σ] [Fintype τ] [Field K]

/-- Combine the two actual exponent blocks. -/
def join (e : (σ →₀ ℕ) × (τ →₀ ℕ)) : σ ⊕ τ →₀ ℕ := exponentEquiv.symm e

def joinedBase {B : ℕ} (c : BiCell σ τ B) : σ ⊕ τ →₀ ℕ :=
  join (base c.1, base c.2)

def exponentCell (B : ℕ) (e : σ ⊕ τ →₀ ℕ) : BiCell σ τ B :=
  (cell B (exponentEquiv e).1, cell B (exponentEquiv e).2)

theorem joinedBase_exponentCell (B : ℕ) (e : σ ⊕ τ →₀ ℕ) :
    joinedBase (exponentCell B e) = base (cell B e) := by
  ext i
  rcases i with i | i <;> rfl

/-- A common finite truncation suffices for the actual standard monomials
of any ideal. No chosen Gröbner basis is an assumption. -/
theorem exists_standard_cell_bound (m : MonomialOrder (σ ⊕ τ))
    (I : Ideal (MvPolynomial (σ ⊕ τ) K)) :
    ∃ B₀ : ℕ, ∀ B, B₀ ≤ B → ∀ e,
      standardExponent m I e ↔ standardExponent m I (joinedBase (exponentCell B e)) := by
  obtain ⟨G,hG⟩ := exists_finite_standard_exponent_test m I
  refine ⟨generatorBound G, fun B hB e => ?_⟩
  rw [joinedBase_exponentCell, hG, hG]
  exact avoids_iff_cell_avoids G B hB e

/-- Actual bidegree dimensions are counts of standard exponents in the
separate degree slices of the two blocks. -/
theorem finrank_eq_bistandard_card (m : MonomialOrder (σ ⊕ τ))
    (I : Ideal (MvPolynomial (σ ⊕ τ) K))
    (hI : IsBihomogeneous (σ ⊕ τ) K sumBlock I) (a b : ℕ) :
    Module.finrank K (bicoordinatePiece (σ ⊕ τ) K sumBlock I a b) =
      Nat.card {e : MonomialHilbert.DegreeMonomials σ a × MonomialHilbert.DegreeMonomials τ b //
        standardExponent m I (join (e.1.val,e.2.val))} := by
  let w := twoBlockWeight (σ ⊕ τ) (sumBlock (σ := σ) (τ := τ))
  have hf : {e : σ ⊕ τ →₀ ℕ | standardExponent m I e ∧ Finsupp.weight w e = (a,b)}.Finite :=
    (finite_monomials_of_bidegree (σ ⊕ τ) sumBlock a b).subset (fun e he => he.2)
  change Module.finrank K (weightedCoordinatePiece w I (a,b)) = _
  rw [finrank_weightedCoordinatePiece w m I (fun d => hI d.1 d.2) (a,b) hf]
  apply Nat.card_congr
  refine { toFun := ?_, invFun := ?_, left_inv := ?_, right_inv := ?_ }
  · intro e
    have hd := e.property.2
    change Finsupp.weight (twoBlockWeight (σ ⊕ τ) sumBlock) e.val = (a,b) at hd
    rw [weight_eq_exponent_degrees, Prod.mk.injEq] at hd
    exact ⟨(⟨(exponentEquiv e.val).1,hd.1⟩,⟨(exponentEquiv e.val).2,hd.2⟩),
      by simpa only [join, Prod.mk.eta, Equiv.symm_apply_apply] using e.property.1⟩
  · intro e
    refine ⟨join (e.val.1.val,e.val.2.val),e.property,?_⟩
    change Finsupp.weight (twoBlockWeight (σ ⊕ τ) sumBlock) _ = _
    rw [weight_eq_exponent_degrees]
    simp only [join, Equiv.apply_symm_apply, e.val.1.property, e.val.2.property]
  · intro e
    apply Subtype.ext
    exact exponentEquiv.symm_apply_apply e.val
  · intro e
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst (exponentEquiv.apply_symm_apply (e.val.1.val,e.val.2.val))
    · exact congrArg Prod.snd (exponentEquiv.apply_symm_apply (e.val.1.val,e.val.2.val))

/-- At the finite truncation bound, the constructed orthant polynomial is
exactly the actual bivariate Hilbert polynomial of the quotient. -/
theorem hilbertPolynomial_eq_orthant (m : MonomialOrder (σ ⊕ τ))
    (I : Ideal (MvPolynomial (σ ⊕ τ) K))
    (hI : IsBihomogeneous (σ ⊕ τ) K sumBlock I)
    (H : Polynomial (Polynomial ℚ)) (N : ℕ)
    (hH : ∀ a b : ℕ, N ≤ a → N ≤ b → BiMonomialHilbert.biEval H a b =
      (Module.finrank K (bicoordinatePiece (σ ⊕ τ) K sumBlock I a b) : ℚ))
    (B : ℕ) (hB : ∀ e, standardExponent m I e ↔
      standardExponent m I (joinedBase (exponentCell B e))) :
    H = orthantPolynomial B (fun c => standardExponent m I (joinedBase c)) := by
  classical
  let L := 1 + (Finset.univ : Finset (Cell σ B)).sup (fun c => (base c).degree)
  let R := 1 + (Finset.univ : Finset (Cell τ B)).sup (fun c => (base c).degree)
  apply polynomial_eq_of_nat_grid_tail_eval_eq _ _ (max N L) (max N R)
  intro a b ha hb
  have ha' : ∀ c : Cell σ B, (base c).degree < a := by
    intro c
    have hh := Finset.le_sup (s := Finset.univ) (f := fun c : Cell σ B => (base c).degree)
      (Finset.mem_univ c)
    have ht : L ≤ a := (le_max_right N L).trans ha
    change 1 + (Finset.univ : Finset (Cell σ B)).sup (fun c => (base c).degree) ≤ a at ht
    exact lt_of_le_of_lt hh (by omega)
  have hb' : ∀ c : Cell τ B, (base c).degree < b := by
    intro c
    have hh := Finset.le_sup (s := Finset.univ) (f := fun c : Cell τ B => (base c).degree)
      (Finset.mem_univ c)
    have ht : R ≤ b := (le_max_right N R).trans hb
    change 1 + (Finset.univ : Finset (Cell τ B)).sup (fun c => (base c).degree) ≤ b at ht
    exact lt_of_le_of_lt hh (by omega)
  change BiMonomialHilbert.biEval H a b = BiMonomialHilbert.biEval _ a b
  rw [hH a b (by omega) (by omega), finrank_eq_bistandard_card m I hI,
    orthantPolynomial_eval B _ a b ha' hb']
  congr 1
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro e
  simpa only [exponentCell, join, Equiv.apply_symm_apply] using
    hB (join (e.1.val,e.2.val))

/-- True monotonicity for nested unions of disjoint orthants. Only the
larger polynomial requires a total-degree bound; its construction proves
that no higher-dimensional summands are hidden by cancellation. -/
theorem orthant_top_coeff_mono (B : ℕ) (P Q : BiCell σ τ B → Prop)
    (hQP : ∀ c, Q c → P c) (d : ℕ)
    (hd : TotalDegreeLE (orthantPolynomial B P) d) (i j : ℕ) (hij : d ≤ i+j) :
    ((orthantPolynomial B Q).coeff i).coeff j ≤
      ((orthantPolynomial B P).coeff i).coeff j := by
  classical
  let f : {c : BiCell σ τ B // P c} → ℚ :=
    fun c => ((biCellPolynomial c.val).coeff i).coeff j
  have hnonneg (c : {c : BiCell σ τ B // P c}) : 0 ≤ f c := by
    by_cases hc : Active c.val
    · exact biCellPolynomial_coeff_nonneg c.val i j
        ((active_cell_degree_le B P d hd c hc).trans hij)
    · dsimp [f]
      rw [biCellPolynomial_eq_zero_of_not_active c.val hc]
      simp
  let E : {c : {c : BiCell σ τ B // P c} // Q c.val} ≃
      {c : BiCell σ τ B // Q c} :=
    { toFun := fun c => ⟨c.val.val,c.property⟩
      invFun := fun c => ⟨⟨c.val,hQP c.val c.property⟩,c.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := E.sum_comp (fun c => ((biCellPolynomial c.val).coeff i).coeff j)
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun c : {c : BiCell σ τ B // P c} =>
    Q c.val) f
  have hrest : 0 ≤ ∑ c : {c : {c : BiCell σ τ B // P c} // ¬ Q c.val}, f c.val :=
    Finset.sum_nonneg (fun c _ => hnonneg c.val)
  simp only [orthantPolynomial, Polynomial.finset_sum_coeff]
  change (∑ c : {c : BiCell σ τ B // Q c},
    ((biCellPolynomial c.val).coeff i).coeff j) ≤ ∑ c, f c
  rw [← hsplit]
  have he' : (∑ c : {c : {c : BiCell σ τ B // P c} // Q c.val}, f c.val) =
      ∑ c : {c : BiCell σ τ B // Q c}, ((biCellPolynomial c.val).coeff i).coeff j := he
  rw [he']
  exact le_add_of_nonneg_right hrest

/-- The geometric closed-subscheme comparison, stated for literal nested
bihomogeneous ideals and their actual eventual Hilbert polynomials.

The top mixed coefficient of the smaller subscheme cannot exceed that of
the larger. The proof supplies positivity of the residual contribution; it
does not assume effectivity or the desired coefficient inequality. -/
theorem top_mixed_coefficient_mono
    (I J : Ideal (MvPolynomial (σ ⊕ τ) K)) (hIJ : I ≤ J)
    (hI : IsBihomogeneous (σ ⊕ τ) K sumBlock I)
    (hJ : IsBihomogeneous (σ ⊕ τ) K sumBlock J)
    (HI HJ : Polynomial (Polynomial ℚ)) (NI NJ : ℕ)
    (hHI : ∀ a b : ℕ, NI ≤ a → NI ≤ b → BiMonomialHilbert.biEval HI a b =
      (Module.finrank K (bicoordinatePiece (σ ⊕ τ) K sumBlock I a b) : ℚ))
    (hHJ : ∀ a b : ℕ, NJ ≤ a → NJ ≤ b → BiMonomialHilbert.biEval HJ a b =
      (Module.finrank K (bicoordinatePiece (σ ⊕ τ) K sumBlock J a b) : ℚ))
    (d : ℕ) (hd : TotalDegreeLE HI d) (i j : ℕ) (hij : d ≤ i+j) :
    (HJ.coeff i).coeff j ≤ (HI.coeff i).coeff j := by
  let m := finiteMonomialOrder (σ := σ ⊕ τ)
  obtain ⟨BI,hBI⟩ := exists_standard_cell_bound m I
  obtain ⟨BJ,hBJ⟩ := exists_standard_cell_bound m J
  let B := max BI BJ
  have heI := hilbertPolynomial_eq_orthant m I hI HI NI hHI B
    (hBI B (le_max_left _ _))
  have heJ := hilbertPolynomial_eq_orthant m J hJ HJ NJ hHJ B
    (hBJ B (le_max_right _ _))
  rw [heI] at hd ⊢
  rw [heJ]
  apply orthant_top_coeff_mono B _ _ _ d hd i j hij
  intro c hc p hp hne
  exact hc p (hIJ hp) hne

end Sheshadri.MixedHilbertComparison
