/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Sym.Card
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Hilbert polynomials for finite monomial exclusions

This constructs an eventual polynomial for the actual number of degree-`d`
monomials outside a finitely generated monomial ideal. The formula is finite
inclusion-exclusion of shifted stars-and-bars polynomials. Its later use with
an initial ideal requires the separately proved standard-monomial basis.
-/

noncomputable section
namespace Sheshadri.MonomialHilbert

open scoped BigOperators
open Finset

variable (σ : Type*) [Fintype σ]

abbrev DegreeMonomials (d : ℕ) := {e : σ →₀ ℕ // e.degree = d}

instance degreeMonomials_fintype (d : ℕ) : Fintype (DegreeMonomials σ d) := by
  classical
  exact Fintype.ofEquiv (Sym σ d) (Sym.equivNatSum σ d)

theorem card_degreeMonomials (d : ℕ) :
    Fintype.card (DegreeMonomials σ d) = (Fintype.card σ + d - 1).choose d := by
  classical
  have e : Sym σ d ≃ DegreeMonomials σ d := Sym.equivNatSum σ d
  exact (Fintype.card_congr e).symm.trans (Sym.card_sym_eq_choose d)

theorem card_degreeMonomials_of_pos (hσ : 0 < Fintype.card σ) (d : ℕ) :
    Fintype.card (DegreeMonomials σ d) = (d + (Fintype.card σ - 1)).choose
      (Fintype.card σ - 1) := by
  rw [card_degreeMonomials, show Fintype.card σ + d - 1 =
    d + (Fintype.card σ - 1) by omega, ← Nat.choose_symm (show d ≤ d +
      (Fintype.card σ - 1) by omega)]
  congr 1
  omega

/-- Translation by an exponent is a bijection onto its multiples of fixed degree. -/
def multiplesEquiv (g : σ →₀ ℕ) (d : ℕ) (hgd : g.degree ≤ d) :
    {e : DegreeMonomials σ d // g ≤ e.val} ≃ DegreeMonomials σ (d - g.degree) where
  toFun e := ⟨e.val.val - g, by
    have h := congrArg Finsupp.degree (tsub_add_cancel_of_le e.property)
    rw [Finsupp.degree_add, e.val.property] at h
    omega⟩
  invFun e := ⟨⟨e.val + g, by rw [Finsupp.degree_add, e.property]; omega⟩,
    le_add_self⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact tsub_add_cancel_of_le e.property
  right_inv e := by
    apply Subtype.ext
    exact add_tsub_cancel_right e.val g

theorem card_multiples (g : σ →₀ ℕ) (d : ℕ) (hgd : g.degree ≤ d) :
    Fintype.card {e : DegreeMonomials σ d // g ≤ e.val} =
      Fintype.card (DegreeMonomials σ (d - g.degree)) := by
  classical
  exact Fintype.card_congr (multiplesEquiv σ g d hgd)

variable {σ}

theorem mem_finset_inf {ι α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset ι) (S : ι → Finset α) (x : α) :
    x ∈ s.inf S ↔ ∀ i ∈ s, x ∈ S i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.inf_insert, hi, ih]

/-- The actual standard-monomial count for a finite set of forbidden divisors. -/
def standardCount (G : Finset (σ →₀ ℕ)) (d : ℕ) : ℕ :=
  Nat.card {e : σ →₀ ℕ // e.degree = d ∧ ∀ g ∈ G, ¬g ≤ e}

private theorem standardCount_eq_card_filter (G : Finset (σ →₀ ℕ)) (d : ℕ) :
    standardCount G d =
      (Finset.univ.filter fun e : DegreeMonomials σ d => ∀ g ∈ G, ¬g ≤ e.val).card := by
  classical
  let E : {e : σ →₀ ℕ // e.degree = d ∧ ∀ g ∈ G, ¬g ≤ e} ≃
      {e : DegreeMonomials σ d // ∀ g ∈ G, ¬g ≤ e.val} :=
    { toFun := fun e => ⟨⟨e.val, e.property.1⟩, e.property.2⟩
      invFun := fun e => ⟨e.val.val, e.val.property, e.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [standardCount, Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Exact inclusion-exclusion, before passing to a sufficiently large degree. -/
theorem standardCount_inclusion_exclusion (G : Finset (σ →₀ ℕ)) (d : ℕ) :
    (standardCount G d : ℤ) =
      ∑ T ∈ G.powerset, (-1 : ℤ) ^ T.card *
        Fintype.card {e : DegreeMonomials σ d // T.sup id ≤ e.val} := by
  classical
  let S : (σ →₀ ℕ) → Finset (DegreeMonomials σ d) :=
    fun g => Finset.univ.filter (fun e => g ≤ e.val)
  have hc : G.inf (fun g => (S g)ᶜ) =
      Finset.univ.filter (fun e : DegreeMonomials σ d => ∀ g ∈ G, ¬g ≤ e.val) := by
    ext e
    simp [mem_finset_inf, S]
  have hT (T : Finset (σ →₀ ℕ)) :
      (T.inf S).card = Fintype.card {e : DegreeMonomials σ d // T.sup id ≤ e.val} := by
    rw [Fintype.card_subtype]
    congr 1
    ext e
    simp [mem_finset_inf, Finset.sup_le_iff, S]
  rw [standardCount_eq_card_filter, ← hc, Finset.inclusion_exclusion_card_inf_compl]
  simp_rw [hT]

/-- A concrete polynomial, not a candidate supplied with an evaluation law. -/
def standardHilbertPolynomial (G : Finset (σ →₀ ℕ)) : Polynomial ℚ :=
  ∑ T ∈ G.powerset, (-1 : ℚ) ^ T.card •
    Polynomial.preHilbertPoly ℚ (Fintype.card σ - 1) (T.sup id).degree

def threshold (G : Finset (σ →₀ ℕ)) : ℕ :=
  G.powerset.sup (fun T => (T.sup id).degree)

theorem standardHilbertPolynomial_eval (hσ : 0 < Fintype.card σ)
    (G : Finset (σ →₀ ℕ)) (d : ℕ) (hd : threshold G ≤ d) :
    (standardHilbertPolynomial G).eval (d : ℚ) = standardCount G d := by
  classical
  have hdeg (T : Finset (σ →₀ ℕ)) (hT : T ∈ G.powerset) : (T.sup id).degree ≤ d :=
    (Finset.le_sup (f := fun T : Finset (σ →₀ ℕ) => (T.sup id).degree) hT).trans hd
  have hc := congrArg (fun z : ℤ => (z : ℚ)) (standardCount_inclusion_exclusion G d)
  push_cast at hc
  rw [hc]
  simp only [standardHilbertPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_smul,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add ℚ _ (hdeg T hT),
    card_multiples σ (T.sup id) d (hdeg T hT), card_degreeMonomials_of_pos σ hσ]

end Sheshadri.MonomialHilbert
