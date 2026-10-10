/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.MonomialHilbert

/-!
# Eventual polynomials for actual bigraded monomial counts

Two independent stars-and-bars counts and finite inclusion-exclusion construct
the polynomial. No eventual polynomial or evaluation identity is an input.
The outer polynomial variable records the first block degree, the inner
variable the second block degree.
-/

noncomputable section
namespace Sheshadri.BiMonomialHilbert

open scoped BigOperators
open MonomialHilbert

variable (σ τ : Type*) [Fintype σ] [Fintype τ]

abbrev Exponent := (σ →₀ ℕ) × (τ →₀ ℕ)
abbrev BiDegreeMonomials (a b : ℕ) := DegreeMonomials σ a × DegreeMonomials τ b

def exponent {a b : ℕ} (e : BiDegreeMonomials σ τ a b) : Exponent σ τ :=
  (e.1.val, e.2.val)

theorem card_bimultiples (g : Exponent σ τ) (a b : ℕ)
    (ha : g.1.degree ≤ a) (hb : g.2.degree ≤ b) :
    Fintype.card {e : BiDegreeMonomials σ τ a b // g ≤ exponent σ τ e} =
      Fintype.card (DegreeMonomials σ (a - g.1.degree)) *
      Fintype.card (DegreeMonomials τ (b - g.2.degree)) := by
  classical
  let E : {e : BiDegreeMonomials σ τ a b // g ≤ exponent σ τ e} ≃
      {e : DegreeMonomials σ a // g.1 ≤ e.val} ×
      {e : DegreeMonomials τ b // g.2 ≤ e.val} :=
    { toFun := fun e => (⟨e.val.1, e.property.1⟩, ⟨e.val.2, e.property.2⟩)
      invFun := fun e => ⟨(e.1.val, e.2.val), ⟨e.1.property, e.2.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr E, Fintype.card_prod,
    card_multiples σ g.1 a ha, card_multiples τ g.2 b hb]

variable {σ τ}

/-- The count of actual exponent pairs avoiding the finite monomial generators. -/
def biStandardCount (G : Finset (Exponent σ τ)) (a b : ℕ) : ℕ :=
  Nat.card {e : Exponent σ τ //
    e.1.degree = a ∧ e.2.degree = b ∧ ∀ g ∈ G, ¬g ≤ e}

private theorem biStandardCount_eq_card_filter (G : Finset (Exponent σ τ)) (a b : ℕ) :
    biStandardCount G a b =
      (Finset.univ.filter fun e : BiDegreeMonomials σ τ a b =>
        ∀ g ∈ G, ¬g ≤ exponent σ τ e).card := by
  classical
  let E : {e : Exponent σ τ //
      e.1.degree = a ∧ e.2.degree = b ∧ ∀ g ∈ G, ¬g ≤ e} ≃
      {e : BiDegreeMonomials σ τ a b // ∀ g ∈ G, ¬g ≤ exponent σ τ e} :=
    { toFun := fun e => ⟨(⟨e.val.1, e.property.1⟩, ⟨e.val.2, e.property.2.1⟩),
        e.property.2.2⟩
      invFun := fun e => ⟨exponent σ τ e.val,
        e.val.1.property, e.val.2.property, e.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [biStandardCount, Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem biStandardCount_inclusion_exclusion (G : Finset (Exponent σ τ)) (a b : ℕ) :
    (biStandardCount G a b : ℤ) =
      ∑ T ∈ G.powerset, (-1 : ℤ) ^ T.card *
        Fintype.card {e : BiDegreeMonomials σ τ a b // T.sup id ≤ exponent σ τ e} := by
  classical
  let S : Exponent σ τ → Finset (BiDegreeMonomials σ τ a b) :=
    fun g => Finset.univ.filter (fun e => g ≤ exponent σ τ e)
  have hc : G.inf (fun g => (S g)ᶜ) =
      Finset.univ.filter (fun e : BiDegreeMonomials σ τ a b =>
        ∀ g ∈ G, ¬g ≤ exponent σ τ e) := by
    ext e
    simp [mem_finset_inf, S]
  have hT (T : Finset (Exponent σ τ)) :
      (T.inf S).card = Fintype.card {e : BiDegreeMonomials σ τ a b //
        T.sup id ≤ exponent σ τ e} := by
    rw [Fintype.card_subtype]
    congr 1
    ext e
    simp [mem_finset_inf, Finset.sup_le_iff, S]
  rw [biStandardCount_eq_card_filter, ← hc, Finset.inclusion_exclusion_card_inf_compl]
  simp_rw [hT]

/-- The actual bivariate polynomial constructed from the finite exponent set. -/
def biStandardHilbertPolynomial (G : Finset (Exponent σ τ)) : Polynomial (Polynomial ℚ) :=
  ∑ T ∈ G.powerset, (-1 : ℚ) ^ T.card •
    ((Polynomial.preHilbertPoly ℚ (Fintype.card σ - 1) (T.sup id).1.degree).map
        Polynomial.C *
      Polynomial.C (Polynomial.preHilbertPoly ℚ (Fintype.card τ - 1) (T.sup id).2.degree))

def thresholdLeft (G : Finset (Exponent σ τ)) : ℕ :=
  G.powerset.sup (fun T => (T.sup id).1.degree)

def thresholdRight (G : Finset (Exponent σ τ)) : ℕ :=
  G.powerset.sup (fun T => (T.sup id).2.degree)

/-- Evaluation convention for the two actual block degrees. -/
def biEval (H : Polynomial (Polynomial ℚ)) (a b : ℚ) : ℚ :=
  (H.eval (Polynomial.C a)).eval b

theorem biStandardHilbertPolynomial_eval
    (hσ : 0 < Fintype.card σ) (hτ : 0 < Fintype.card τ)
    (G : Finset (Exponent σ τ)) (a b : ℕ)
    (ha : thresholdLeft G ≤ a) (hb : thresholdRight G ≤ b) :
    biEval (biStandardHilbertPolynomial G) a b = biStandardCount G a b := by
  classical
  have hleft (T : Finset (Exponent σ τ)) (hT : T ∈ G.powerset) :
      (T.sup id).1.degree ≤ a :=
    (Finset.le_sup (f := fun T : Finset (Exponent σ τ) => (T.sup id).1.degree) hT).trans ha
  have hright (T : Finset (Exponent σ τ)) (hT : T ∈ G.powerset) :
      (T.sup id).2.degree ≤ b :=
    (Finset.le_sup (f := fun T : Finset (Exponent σ τ) => (T.sup id).2.degree) hT).trans hb
  have hc := congrArg (fun z : ℤ => (z : ℚ)) (biStandardCount_inclusion_exclusion G a b)
  push_cast at hc
  rw [hc]
  simp only [biEval, biStandardHilbertPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
    Polynomial.eval₂_at_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add ℚ _ (hleft T hT),
    Polynomial.preHilbertPoly_eq_choose_sub_add ℚ _ (hright T hT),
    card_bimultiples σ τ (T.sup id) a b (hleft T hT) (hright T hT),
    card_degreeMonomials_of_pos σ hσ, card_degreeMonomials_of_pos τ hτ]
  push_cast
  rfl

end Sheshadri.BiMonomialHilbert
