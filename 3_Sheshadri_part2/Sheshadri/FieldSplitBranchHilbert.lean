/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldBezoutSplitSystem

noncomputable section
open Sheshadri.MultiProjective
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

namespace Sheshadri.FieldSplitBranchHilbert
variable {k₀ : Type*} [Field k₀] [CharZero k₀]
open MvPolynomial ProjectivePointInterpolation
set_option synthInstance.maxHeartbeats 200000

section Character
variable {σ K A D : Type*} [CommRing K] [CommRing A] [Algebra K A] [AddCommMonoid D]

theorem character_weight (w : σ → D) (χ : Multiplicative D →* A) (e : σ →₀ ℕ) :
    χ (Multiplicative.ofAdd (Finsupp.weight w e)) =
      e.prod (fun i n => χ (Multiplicative.ofAdd (w i)) ^ n) := by
  classical
  simp [Finsupp.weight_apply, Finsupp.sum, Finsupp.prod,
    ofAdd_sum, ofAdd_nsmul]

/-- Substituting proportional coordinates in a homogeneous polynomial
factors out the common character of its degree. -/
theorem aeval_weighted_character
    (w : σ → D) (χ : Multiplicative D →* A) (c : σ → K)
    (f : MvPolynomial σ K) (d : D) (hf : IsWeightedHomogeneous w f d) :
    aeval (fun i => c i • χ (Multiplicative.ofAdd (w i))) f =
      eval c f • χ (Multiplicative.ofAdd d) := by
  classical
  have hprod (e : σ →₀ ℕ) :
      e.prod (fun i n => (c i • χ (Multiplicative.ofAdd (w i))) ^ n) =
      algebraMap K A (e.prod (fun i n => c i ^ n)) *
        χ (Multiplicative.ofAdd (Finsupp.weight w e)) := by
    rw [character_weight]
    simp only [Finsupp.prod, Algebra.smul_def, mul_pow,
      Finset.prod_mul_distrib, map_prod, map_pow]
  rw [← f.support_sum_monomial_coeff, map_sum, map_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro e he
  have hd := hf (mem_support_iff.mp he)
  simp only [aeval_def, eval₂_monomial, eval_monomial]
  rw [hprod, hd]
  simp only [Algebra.smul_def, map_mul, mul_assoc]

/-- The same factorization for any actual polynomial-quotient algebra map. -/
theorem map_weighted_character
    (w : σ → D) (χ : Multiplicative D →* A) (c : σ → K)
    (φ : MvPolynomial σ K →ₐ[K] A)
    (hX : ∀ i, φ (X i) = c i • χ (Multiplicative.ofAdd (w i)))
    (f : MvPolynomial σ K) (d : D) (hf : IsWeightedHomogeneous w f d) :
    φ f = eval c f • χ (Multiplicative.ofAdd d) := by
  have hφ : φ = aeval (fun i => c i • χ (Multiplicative.ofAdd (w i))) := by
    ext i
    simpa using hX i
  rw [hφ]
  exact aeval_weighted_character w χ c f d hf

end Character

section CharacterDimension
variable {σ K D : Type*} [Field K] [AddCommMonoid D]

theorem character_piece_finrank_le_one
    (w : σ → D) (I : Ideal (MvPolynomial σ K))
    (χ : Multiplicative D →* (MvPolynomial σ K ⧸ I)) (scalars : σ → K)
    (hvar : ∀ i, (Ideal.Quotient.mkₐ K I) (X i) =
      scalars i • χ (Multiplicative.ofAdd (w i)))
    (d : D) (g : MvPolynomial σ K) (hg : IsWeightedHomogeneous w g d)
    (hchar : χ (Multiplicative.ofAdd d) = Ideal.Quotient.mk I g) :
    Module.finrank K (coordinatePiece w I d) ≤ 1 := by
  let z : coordinatePiece w I d := ⟨Ideal.Quotient.mk I g, g, hg, rfl⟩
  apply finrank_le_one z
  intro y
  obtain ⟨f, hf, hfy⟩ := y.property
  refine ⟨eval scalars f, ?_⟩
  apply Subtype.ext
  change eval scalars f • Ideal.Quotient.mk I g = (y : MvPolynomial σ K ⧸ I)
  rw [← hfy]
  have h := map_weighted_character w χ scalars (Ideal.Quotient.mkₐ K I) hvar f d hf
  rw [hchar] at h
  exact h.symm

end CharacterDimension

section KilledDegree
variable {σ K D : Type*} [CommRing K] [AddCommMonoid D]

/-- Positive weighted degree forces every monomial to contain a coordinate
from the block whose coordinates have been killed by the ideal. -/
theorem homogeneous_mem_of_positive_killed_degree
    (w : σ → D) (π : D →+ ℕ) (I : Ideal (MvPolynomial σ K))
    (hkill : ∀ i, 0 < π (w i) → X i ∈ I)
    (f : MvPolynomial σ K) (d : D) (hd : 0 < π d)
    (hf : IsWeightedHomogeneous w f d) : f ∈ I := by
  classical
  rw [← f.support_sum_monomial_coeff]
  apply I.sum_mem
  intro e he
  have hedeg : Finsupp.weight w e = d := hf (mem_support_iff.mp he)
  have hsum : (∑ i ∈ e.support, e i * π (w i)) = π d := by
    rw [← hedeg]
    simp [Finsupp.weight_apply, Finsupp.sum, map_sum]
  have hex : ∃ i ∈ e.support, 0 < e i * π (w i) := by
    by_contra h
    push_neg at h
    have hz : (∑ i ∈ e.support, e i * π (w i)) = 0 :=
      Finset.sum_eq_zero (fun i hi => Nat.eq_zero_of_le_zero (h i hi))
    omega
  obtain ⟨i, hi, hpos⟩ := hex
  have hei : 0 < e i := Nat.pos_of_mul_pos_right hpos
  have hwi : 0 < π (w i) := Nat.pos_of_mul_pos_left hpos
  exact I.mem_of_dvd (X_dvd_monomial.mpr (Or.inr (Nat.ne_of_gt hei))) (hkill i hwi)

theorem killed_degree_piece_eq_bot
    (w : σ → D) (π : D →+ ℕ) (I : Ideal (MvPolynomial σ K))
    (hkill : ∀ i, 0 < π (w i) → X i ∈ I)
    (d : D) (hd : 0 < π d) : coordinatePiece w I d = ⊥ := by
  apply le_antisymm _ bot_le
  rintro y ⟨f, hf, rfl⟩
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (homogeneous_mem_of_positive_killed_degree w π I hkill f d hd hf)

theorem killed_degree_piece_finrank_zero
    [Nontrivial K]
    (w : σ → D) (π : D →+ ℕ) (I : Ideal (MvPolynomial σ K))
    (hkill : ∀ i, 0 < π (w i) → X i ∈ I)
    (d : D) (hd : 0 < π d) : Module.finrank K (coordinatePiece w I d) = 0 := by
  rw [killed_degree_piece_eq_bot w π I hkill d hd]
  exact finrank_bot K _

end KilledDegree

section ThreeFactors
open FieldMultiProjective
variable {X U V K : Type*} [Field K]

def threeCharacter {A : Type*} [CommRing A] (x u v : A) : Multiplicative Degree →* A where
  toFun d := x ^ d.toAdd.1 * u ^ d.toAdd.2.1 * v ^ d.toAdd.2.2
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, pow_add]
    ring

/-- Literal monomial generating the one-dimensional branch piece. -/
def branchMonomial (ix : X) (iu : U) (iv : V) (a b c : ℕ) :
    MvPolynomial (Variables X U V) K :=
  MvPolynomial.X (.inl ix) ^ a * MvPolynomial.X (.inr (.inl iu)) ^ b *
    MvPolynomial.X (.inr (.inr iv)) ^ c

theorem branchMonomial_homogeneous (ix : X) (iu : U) (iv : V) (a b c : ℕ) :
    IsWeightedHomogeneous (weight X U V) (branchMonomial (K := K) ix iu iv a b c)
      (a, b, c) := by
  simpa [branchMonomial, weight] using
    (((isWeightedHomogeneous_X K (weight X U V) (.inl ix)).pow a).mul
      ((isWeightedHomogeneous_X K (weight X U V) (.inr (.inl iu))).pow b)).mul
      ((isWeightedHomogeneous_X K (weight X U V) (.inr (.inr iv))).pow c)

theorem branch_piece_finrank_le_one
    (I : Ideal (MvPolynomial (Variables X U V) K)) (ix : X) (iu : U) (iv : V)
    (scalars : Variables X U V → K)
    (hx : ∀ i, Ideal.Quotient.mk I (MvPolynomial.X (.inl i)) =
      scalars (.inl i) • Ideal.Quotient.mk I (MvPolynomial.X (.inl ix)))
    (hu : ∀ i, Ideal.Quotient.mk I (MvPolynomial.X (.inr (.inl i))) =
      scalars (.inr (.inl i)) • Ideal.Quotient.mk I (MvPolynomial.X (.inr (.inl iu))))
    (hv : ∀ i, Ideal.Quotient.mk I (MvPolynomial.X (.inr (.inr i))) =
      scalars (.inr (.inr i)) • Ideal.Quotient.mk I (MvPolynomial.X (.inr (.inr iv))))
    (a b c : ℕ) :
    Module.finrank K (coordinatePiece (weight X U V) I (a, b, c)) ≤ 1 := by
  let χ := threeCharacter (Ideal.Quotient.mk I (MvPolynomial.X (.inl ix)))
    (Ideal.Quotient.mk I (MvPolynomial.X (.inr (.inl iu))))
    (Ideal.Quotient.mk I (MvPolynomial.X (.inr (.inr iv))))
  let g := branchMonomial (K := K) ix iu iv a b c
  let z : coordinatePiece (weight X U V) I (a, b, c) :=
    ⟨Ideal.Quotient.mk I g, g, branchMonomial_homogeneous ix iu iv a b c, rfl⟩
  apply finrank_le_one z
  intro y
  obtain ⟨f, hf, hfy⟩ := y.property
  refine ⟨eval scalars f, ?_⟩
  apply Subtype.ext
  change eval scalars f • Ideal.Quotient.mk I g = (y : MvPolynomial (Variables X U V) K ⧸ I)
  rw [← hfy]
  have hvar : ∀ i : Variables X U V,
      (Ideal.Quotient.mkₐ K I) (MvPolynomial.X i) =
        scalars i • χ (Multiplicative.ofAdd (weight X U V i)) := by
    rintro (i | (i | i))
    · simpa [χ, threeCharacter, weight] using hx i
    · simpa [χ, threeCharacter, weight] using hu i
    · simpa [χ, threeCharacter, weight] using hv i
  have h := map_weighted_character (weight X U V) χ scalars (Ideal.Quotient.mkₐ K I)
    hvar f (a, b, c) hf
  simpa [g, branchMonomial, χ, threeCharacter, map_mul, map_pow] using h.symm

end ThreeFactors

section SplitSystem
open FieldMultiProjective FieldBezoutSplitSystem BezoutSplitBudget
variable {E : Type*} [Fintype E]

theorem degree_eq_sum_sigmaBlockWeight (dim : Fin 3 → ℕ)
    (e : ProjectiveVariables dim →₀ ℕ) :
    e.degree = (Finsupp.weight (blockWeight dim) e).1 +
      (Finsupp.weight (blockWeight dim) e).2.1 +
      (Finsupp.weight (blockWeight dim) e).2.2 := by
  classical
  simp only [Finsupp.degree, Finsupp.weight_apply, Finsupp.sum,
    Prod.fst_sum, Prod.snd_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  rintro ⟨b, i⟩ hi
  fin_cases b <;> simp [blockWeight, blockDegree]

instance sigma_homogeneous_finite (dim : Fin 3 → ℕ) (R : Type*) [CommRing R] (d : Degree) :
    Module.Finite R (weightedHomogeneousSubmodule R (blockWeight dim) d) := by
  have hfinite : {e : ProjectiveVariables dim →₀ ℕ |
      Finsupp.weight (blockWeight dim) e = d}.Finite := by
    apply (Finsupp.finite_of_degree_le (σ := ProjectiveVariables dim) (d.1 + d.2.1 + d.2.2)).subset
    intro e he
    rw [Set.mem_setOf_eq, degree_eq_sum_sigmaBlockWeight, he]
  apply Module.Finite.iff_fg.mpr
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported, Finsupp.supported_eq_span_single]
  exact Submodule.fg_span (hfinite.image _)

instance sigma_coordinatePiece_finite (dim : Fin 3 → ℕ) {R : Type*} [CommRing R]
    (I : Ideal (MvPolynomial (ProjectiveVariables dim) R)) (d : Degree) :
    Module.Finite R (coordinatePiece (blockWeight dim) I d) := by
  unfold coordinatePiece
  infer_instance

def degreeProjection : Fin 3 → (Degree →+ ℕ) :=
  ![AddMonoidHom.fst ℕ (ℕ × ℕ),
    (AddMonoidHom.fst ℕ ℕ).comp (AddMonoidHom.snd ℕ (ℕ × ℕ)),
    (AddMonoidHom.snd ℕ ℕ).comp (AddMonoidHom.snd ℕ (ℕ × ℕ))]

theorem degreeProjection_blockDegree (b j : Fin 3) :
    degreeProjection b (blockDegree j) = if j = b then 1 else 0 := by
  fin_cases b <;> fin_cases j <;> simp [degreeProjection, blockDegree]

/-- Overquota branches have identically zero Hilbert function in every
degree positive in the overfull block. -/
theorem excess_branch_piece_finrank_zero
    (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (hα : Function.Injective α)
    (s : ∀ e, Factor (degree e)) (b : Fin 3)
    (hb : dim b < Fintype.card (Selected degree s b))
    (d : Degree) (hd : 0 < degreeProjection b d) :
    Module.finrank k₀ (coordinatePiece (blockWeight dim)
      (homogeneousBranchIdeal dim degree α s) d) = 0 := by
  apply killed_degree_piece_finrank_zero (blockWeight dim) (degreeProjection b) _ _ d hd
  rintro ⟨j, i⟩ hi
  simp only [blockWeight, degreeProjection_blockDegree] at hi
  have hj : j = b := by split_ifs at hi with hj <;> simp_all
  subst j
  exact excess_variables_mem dim degree α hα s b hb i

/-- The actual product of the chosen last coordinates has the requested
multidegree in the sigma-variable presentation. -/
def sigmaBranchMonomial (dim : Fin 3 → ℕ) (d : Degree) :
    MvPolynomial (ProjectiveVariables dim) k₀ :=
  X ⟨0, Fin.last (dim 0)⟩ ^ d.1 * X ⟨1, Fin.last (dim 1)⟩ ^ d.2.1 *
    X ⟨2, Fin.last (dim 2)⟩ ^ d.2.2

theorem sigmaBranchMonomial_homogeneous (dim : Fin 3 → ℕ) (d : Degree) :
    IsWeightedHomogeneous (blockWeight dim) (sigmaBranchMonomial (k₀ := k₀) dim d) d := by
  simpa [sigmaBranchMonomial, blockWeight, blockDegree] using
    (((isWeightedHomogeneous_X k₀ (blockWeight dim) ⟨0, Fin.last (dim 0)⟩).pow d.1).mul
      ((isWeightedHomogeneous_X k₀ (blockWeight dim) ⟨1, Fin.last (dim 1)⟩).pow d.2.1)).mul
      ((isWeightedHomogeneous_X k₀ (blockWeight dim) ⟨2, Fin.last (dim 2)⟩).pow d.2.2)

/-- Correct-quota branches contribute at most one to every actual
multigraded Hilbert value. All proportionality relations are proved by the
explicit Vandermonde start system. -/
theorem quota_branch_piece_finrank_le_one
    (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (hα : Function.Injective α)
    (s : ∀ e, Factor (degree e))
    (hquota : ∀ b, Fintype.card (Selected degree s b) = dim b)
    (d : Degree) :
    Module.finrank k₀ (coordinatePiece (blockWeight dim)
      (homogeneousBranchIdeal dim degree α s) d) ≤ 1 := by
  let I := homogeneousBranchIdeal dim degree α s
  let scalars : ProjectiveVariables dim → k₀ := fun i =>
    Fin.lastCases 1 (quotaPoint dim degree α s hquota i.1) i.2
  let χ := threeCharacter (Ideal.Quotient.mk I (X ⟨0, Fin.last (dim 0)⟩))
    (Ideal.Quotient.mk I (X ⟨1, Fin.last (dim 1)⟩))
    (Ideal.Quotient.mk I (X ⟨2, Fin.last (dim 2)⟩))
  have hχ (b : Fin 3) : χ (Multiplicative.ofAdd (blockDegree b)) =
      Ideal.Quotient.mk I (X ⟨b, Fin.last (dim b)⟩) := by
    fin_cases b <;> simp [χ, threeCharacter, blockDegree]
  apply character_piece_finrank_le_one (blockWeight dim) I χ scalars _ d
    (sigmaBranchMonomial dim d) (sigmaBranchMonomial_homogeneous dim d) _
  · rintro ⟨b, i⟩
    change Ideal.Quotient.mk I (X ⟨b, i⟩) =
      scalars ⟨b, i⟩ • χ (Multiplicative.ofAdd (blockDegree b))
    rw [hχ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [scalars]
    · have hmem := quota_coordinateDifference_mem dim degree α hα s hquota b j
      have heq : Ideal.Quotient.mk I (X ⟨b, j.castSucc⟩) =
          Ideal.Quotient.mk I (C (quotaPoint dim degree α s hquota b j) *
            X ⟨b, Fin.last (dim b)⟩) := Ideal.Quotient.eq.mpr hmem
      simpa [scalars, map_mul, Algebra.smul_def] using heq
  · simp [χ, threeCharacter, sigmaBranchMonomial]

/-- Branch contributions are bounded by the exact indicator counted by
the coefficient of the multihomogeneous class polynomial. -/
theorem branch_piece_finrank_le_quotaIndicator
    (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (hα : Function.Injective α)
    (s : ∀ e, Factor (degree e))
    (hN : Fintype.card E = ∑ b, dim b)
    (d : Degree) (hd : ∀ b, 0 < degreeProjection b d) :
    Module.finrank k₀ (coordinatePiece (blockWeight dim)
      (homogeneousBranchIdeal dim degree α s) d) ≤
      if choiceExponent degree s = exponent (dim 0) (dim 1) (dim 2) then 1 else 0 := by
  classical
  split_ifs with hquota
  · exact quota_branch_piece_finrank_le_one dim degree α hα s
      ((choiceExponent_eq_iff_dim degree s dim).mp hquota) d
  · have hnot : ¬ ∀ b, Fintype.card (Selected degree s b) = dim b := by
      intro h
      exact hquota ((choiceExponent_eq_iff_dim degree s dim).mpr h)
    obtain ⟨b, hb⟩ := exists_excess_of_not_quota dim degree s hN hnot
    rw [excess_branch_piece_finrank_zero dim degree α hα s b hb d (hd b)]

end SplitSystem
end Sheshadri.FieldSplitBranchHilbert
