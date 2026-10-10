/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FlatGradedHilbert
import Mathlib.RingTheory.MvPolynomial.Groebner

/-!
# Standard monomials in actual homogeneous quotient pieces

Division against the nonzero elements of an ideal yields standard-monomial
representatives. When the ideal is homogeneous, projecting the remainder
preserves both the represented quotient class and standard support. This
constructs an actual linear equivalence between each homogeneous quotient
piece and the finitely supported functions on its standard monomials.
-/

noncomputable section

namespace Sheshadri.HilbertStandardMonomials

open MvPolynomial

variable {σ K : Type*} [Field K]

/-- A standard exponent is not divisible by the leading monomial of any
nonzero element of the ideal. -/
def standardExponent (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (e : σ →₀ ℕ) : Prop :=
  ∀ p ∈ I, p ≠ 0 → ¬ m.degree p ≤ e

def standardSubmodule (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K)) :
    Submodule K (MvPolynomial σ K) :=
  Finsupp.supported K K {e | standardExponent m I e}

/-- A standard polynomial in the ideal is zero. This is the uniqueness
part of the normal-form construction. -/
theorem standard_mem_ideal_eq_zero (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) (p : MvPolynomial σ K)
    (hp : p ∈ standardSubmodule m I) (hI : p ∈ I) : p = 0 := by
  by_contra hne
  have hlead : m.degree p ∈ p.support :=
    MvPolynomial.mem_support_iff.mpr ((MonomialOrder.leadingCoeff_ne_zero_iff (m := m)).mpr hne)
  exact hp hlead p hI hne le_rfl

/-- Existence of a genuine standard remainder modulo an arbitrary ideal.
No assumed Gröbner basis or reduction certificate is required. -/
theorem exists_standard_remainder (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) (p : MvPolynomial σ K) :
    ∃ r : MvPolynomial σ K, p - r ∈ I ∧ r ∈ standardSubmodule m I := by
  let B := {f : MvPolynomial σ K // f ∈ I ∧ f ≠ 0}
  obtain ⟨g, r, hpr, _, hr⟩ := m.div
    (b := fun f : B => (f : MvPolynomial σ K))
    (fun f => (MonomialOrder.isUnit_leadingCoeff (m := m)).mpr f.property.2) p
  refine ⟨r, ?_, ?_⟩
  · rw [hpr, add_sub_cancel_right]
    change g.sum (fun b q => q * (b : MvPolynomial σ K)) ∈ I
    exact I.sum_mem fun b _ => I.mul_mem_left _ b.property.1
  · intro e he f hf hne
    exact hr e he ⟨f, hf, hne⟩

section Weighted

variable {Γ : Type*} [AddCommMonoid Γ] [DecidableEq Γ]
variable (w : σ → Γ) (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))

def weightedStandardSubmodule (d : Γ) : Submodule K (MvPolynomial σ K) :=
  Finsupp.supported K K {e | standardExponent m I e ∧ Finsupp.weight w e = d}

def weightedCoordinatePiece (d : Γ) : Submodule K (MvPolynomial σ K ⧸ I) :=
  (weightedHomogeneousSubmodule K w d).map (Ideal.Quotient.mkₐ K I).toLinearMap

theorem weightedStandardSubmodule_le_standard (d : Γ) :
    weightedStandardSubmodule w m I d ≤ standardSubmodule m I := by
  intro p hp e he
  exact (hp he).1

theorem weightedStandardSubmodule_le_homogeneous (d : Γ) :
    weightedStandardSubmodule w m I d ≤ weightedHomogeneousSubmodule K w d := by
  intro p hp e he
  exact (hp (mem_support_iff.mpr he)).2

theorem weightedComponent_preserves_standard (d : Γ) (p : MvPolynomial σ K)
    (hp : p ∈ standardSubmodule m I) :
    weightedHomogeneousComponent w d p ∈ weightedStandardSubmodule w m I d := by
  intro e he
  have hcoeff := mem_support_iff.mp he
  rw [coeff_weightedHomogeneousComponent] at hcoeff
  split_ifs at hcoeff with hweight
  · exact ⟨hp (mem_support_iff.mpr hcoeff), hweight⟩
  · exact False.elim (hcoeff rfl)

/-- The actual quotient map on standard homogeneous polynomials. -/
def standardToPiece (d : Γ) :
    weightedStandardSubmodule w m I d →ₗ[K] weightedCoordinatePiece w I d :=
  (((Ideal.Quotient.mkₐ K I).toLinearMap.comp
    (weightedStandardSubmodule w m I d).subtype).codRestrict _ (by
      intro p
      exact ⟨p, weightedStandardSubmodule_le_homogeneous w m I d p.property, rfl⟩))

theorem standardToPiece_injective (d : Γ) :
    Function.Injective (standardToPiece w m I d) := by
  intro p q hpq
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply standard_mem_ideal_eq_zero m I
  · exact (standardSubmodule m I).sub_mem
      (weightedStandardSubmodule_le_standard w m I d p.property)
      (weightedStandardSubmodule_le_standard w m I d q.property)
  · apply Ideal.Quotient.eq.mp
    exact congrArg Subtype.val hpq

/-- Homogeneity is an ordinary closure property of the actual ideal. It
allows a standard remainder to be projected to the requested degree. -/
theorem standardToPiece_surjective
    (hI : ∀ d p, p ∈ I → weightedHomogeneousComponent w d p ∈ I) (d : Γ) :
    Function.Surjective (standardToPiece w m I d) := by
  intro x
  obtain ⟨p, hp, hpx⟩ := x.property
  obtain ⟨r, hpr, hr⟩ := exists_standard_remainder m I p
  refine ⟨⟨weightedHomogeneousComponent w d r,
    weightedComponent_preserves_standard w m I d r hr⟩, ?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk I (weightedHomogeneousComponent w d r) = (x : MvPolynomial σ K ⧸ I)
  rw [← hpx]
  apply Ideal.Quotient.eq.mpr
  have h := hI d (p - r) hpr
  rw [map_sub, hp.weightedHomogeneousComponent_same] at h
  simpa only [neg_sub] using I.neg_mem h

/-- A canonical linear equivalence from standard homogeneous polynomials
to the actual homogeneous coordinate piece. -/
def standardPieceEquiv
    (hI : ∀ d p, p ∈ I → weightedHomogeneousComponent w d p ∈ I) (d : Γ) :
    weightedStandardSubmodule w m I d ≃ₗ[K] weightedCoordinatePiece w I d :=
  LinearEquiv.ofBijective (standardToPiece w m I d)
    ⟨standardToPiece_injective w m I d, standardToPiece_surjective w m I hI d⟩

/-- Counting standard monomials computes the actual vector-space dimension
of the quotient piece, rather than merely bounding it. -/
theorem finrank_weightedCoordinatePiece
    (hI : ∀ d p, p ∈ I → weightedHomogeneousComponent w d p ∈ I) (d : Γ)
    (hfinite : {e : σ →₀ ℕ | standardExponent m I e ∧ Finsupp.weight w e = d}.Finite) :
    Module.finrank K (weightedCoordinatePiece w I d) =
      Nat.card {e : σ →₀ ℕ // standardExponent m I e ∧ Finsupp.weight w e = d} := by
  let S := {e : σ →₀ ℕ | standardExponent m I e ∧ Finsupp.weight w e = d}
  letI : Fintype S := hfinite.fintype
  calc
    Module.finrank K (weightedCoordinatePiece w I d) =
        Module.finrank K (weightedStandardSubmodule w m I d) :=
      (standardPieceEquiv w m I hI d).symm.finrank_eq
    _ = Module.finrank K (S →₀ K) :=
      (Finsupp.supportedEquivFinsupp (R := K) S).finrank_eq
    _ = Nat.card S := by rw [Module.finrank_finsupp_self, Nat.card_eq_fintype_card]

end Weighted

section FiniteGenerators

variable [Finite σ]

/-- Choose a monomial order for an arbitrary finite variable type. The
eventual polynomial theorem therefore requires no user-supplied order. -/
def finiteMonomialOrder : MonomialOrder σ := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact MonomialOrder.lex

/-- Dickson's lemma transferred to exponent vectors. -/
theorem exponent_set_isPWO (s : Set (σ →₀ ℕ)) : s.IsPWO := by
  apply Set.isPWO_iff_exists_monotone_subseq.mpr
  intro f hf
  obtain ⟨g, hg⟩ := (Pi.isPWO (Set.univ : Set (σ → ℕ))).exists_monotone_subseq
    (f := fun n => (f n : σ → ℕ)) (fun _ => Set.mem_univ _)
  exact ⟨g, fun _ _ h => hg h⟩

/-- Every set of exponent vectors has a finite divisibility basis. This
is the finiteness input behind monomial Hilbert-polynomial existence. -/
theorem exists_finite_divisibility_basis (s : Set (σ →₀ ℕ)) :
    ∃ G : Finset (σ →₀ ℕ), (∀ g ∈ G, g ∈ s) ∧
      ∀ e ∈ s, ∃ g ∈ G, g ≤ e := by
  classical
  have hfin : {e | Minimal (· ∈ s) e}.Finite :=
    (setOf_minimal_antichain (· ∈ s)).finite_of_partiallyWellOrderedOn
      (exponent_set_isPWO _)
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · intro g hg
    exact (hfin.mem_toFinset.mp hg).1
  · intro e he
    obtain ⟨g, hg, hmin⟩ := (inferInstance : WellFoundedLT (σ →₀ ℕ)).wf.has_min
      {x | x ∈ s ∧ x ≤ e} ⟨e, he, le_rfl⟩
    refine ⟨g, hfin.mem_toFinset.mpr ⟨hg.1, ?_⟩, hg.2⟩
    intro b hb hbg
    by_contra hgb
    exact hmin b ⟨hb, hbg.trans hg.2⟩ (lt_of_le_not_le hbg hgb)

/-- A finite set of leading exponents describes every standard monomial.
Its existence is proved by Dickson's lemma, not assumed as a Gröbner basis. -/
theorem exists_finite_standard_exponent_test (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) :
    ∃ G : Finset (σ →₀ ℕ),
      ∀ e, standardExponent m I e ↔ ∀ g ∈ G, ¬ g ≤ e := by
  let S := {e : σ →₀ ℕ | ∃ p ∈ I, p ≠ 0 ∧ m.degree p = e}
  obtain ⟨G, hG, hcover⟩ := exists_finite_divisibility_basis S
  refine ⟨G, ?_⟩
  intro e
  constructor
  · intro he g hg
    obtain ⟨p, hp, hne, rfl⟩ := hG g hg
    exact he p hp hne
  · intro he p hp hne hpe
    obtain ⟨g, hg, hgp⟩ := hcover (m.degree p) ⟨p, hp, hne, rfl⟩
    exact he g hg (hgp.trans hpe)

theorem finrank_coordinatePiece (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ d p, p ∈ I → homogeneousComponent d p ∈ I) (d : ℕ) :
    Module.finrank K (FlatGradedHilbert.coordinatePiece σ K I d) =
      Nat.card {e : σ →₀ ℕ // standardExponent m I e ∧ e.degree = d} := by
  have hf : {e : σ →₀ ℕ | standardExponent m I e ∧ Finsupp.weight (fun _ => 1) e = d}.Finite := by
    apply (FlatGradedHilbert.finite_monomials_of_degree σ d).subset
    intro e he
    simpa only [Finsupp.degree_eq_weight_one] using he.2
  simpa only [Finsupp.degree_eq_weight_one] using
    finrank_weightedCoordinatePiece (fun _ => (1 : ℕ)) m I hI d hf

/-- A single finite monomial obstruction set computes every actual Hilbert
function value of a homogeneous ideal. -/
theorem exists_finite_hilbert_function (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ d p, p ∈ I → homogeneousComponent d p ∈ I) :
    ∃ G : Finset (σ →₀ ℕ), ∀ d : ℕ,
      Module.finrank K (FlatGradedHilbert.coordinatePiece σ K I d) =
        Nat.card {e : σ →₀ ℕ // e.degree = d ∧ ∀ g ∈ G, ¬ g ≤ e} := by
  obtain ⟨G, hG⟩ := exists_finite_standard_exponent_test m I
  refine ⟨G, ?_⟩
  intro d
  rw [finrank_coordinatePiece m I hI d]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun e => by rw [hG e]; exact and_comm)

/-- The same reduction applies to a genuine multigrading, in particular
the two projective coordinate blocks. Finiteness of the exponent fibres
is the positive-grading condition, not a Hilbert-polynomial assumption. -/
theorem exists_finite_weighted_hilbert_function
    {Γ : Type*} [AddCommMonoid Γ] [DecidableEq Γ]
    (w : σ → Γ) (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (hI : ∀ d p, p ∈ I → weightedHomogeneousComponent w d p ∈ I)
    (hw : ∀ d, {e : σ →₀ ℕ | Finsupp.weight w e = d}.Finite) :
    ∃ G : Finset (σ →₀ ℕ), ∀ d : Γ,
      Module.finrank K (weightedCoordinatePiece w I d) =
        Nat.card {e : σ →₀ ℕ // Finsupp.weight w e = d ∧ ∀ g ∈ G, ¬ g ≤ e} := by
  obtain ⟨G, hG⟩ := exists_finite_standard_exponent_test m I
  refine ⟨G, ?_⟩
  intro d
  rw [finrank_weightedCoordinatePiece w m I hI d ((hw d).subset (fun _ he => he.2))]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun e => by rw [hG e]; exact and_comm)

end FiniteGenerators

end Sheshadri.HilbertStandardMonomials
