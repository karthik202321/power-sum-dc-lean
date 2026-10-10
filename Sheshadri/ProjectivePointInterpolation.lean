/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.MultiProjectiveBezout
import Sheshadri.FlatGradedHilbert
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Finite projective points impose independent conditions in high degree

Explicit homogeneous interpolation bounds a finite set of distinct projective
zeros by the dimension of the actual coordinate-ring piece. Extra components
of the zero scheme are permitted throughout. This is one ingredient of Bezout,
not an assumed or proved upper bound for that dimension.
-/

noncomputable section
namespace Sheshadri.ProjectivePointInterpolation
open MvPolynomial

/-- An actual weighted piece of a polynomial quotient. -/
def coordinatePiece {σ K D : Type*} [CommRing K] [AddCommMonoid D]
    (w : σ → D) (I : Ideal (MvPolynomial σ K)) (d : D) :
    Submodule K (MvPolynomial σ K ⧸ I) :=
  (weightedHomogeneousSubmodule K w d).map (Ideal.Quotient.mkₐ K I).toLinearMap

section General
variable {σ K D P : Type*} [Field K] [AddCommMonoid D] [Fintype P]

/-- Evaluation on the actual quotient, when its equations vanish at the point. -/
def quotientEvaluation (I : Ideal (MvPolynomial σ K)) (x : σ → K)
    (hx : ∀ f ∈ I, eval x f = 0) : (MvPolynomial σ K ⧸ I) →ₐ[K] K :=
  Ideal.Quotient.liftₐ I (aeval x) (by
    intro f hf
    simpa [aeval_def] using hx f hf)

/-- Actual diagonal evaluation values prove independence in the quotient. -/
theorem independent_of_separating_polynomials
    (w : σ → D) (I : Ideal (MvPolynomial σ K)) (d : D)
    (points : P → σ → K) (hI : ∀ p f, f ∈ I → eval (points p) f = 0)
    (f : P → MvPolynomial σ K)
    (hf : ∀ p, IsWeightedHomogeneous w (f p) d)
    (hdiag : ∀ p, eval (points p) (f p) ≠ 0)
    (hoff : ∀ p q, p ≠ q → eval (points p) (f q) = 0) :
    LinearIndependent K (fun p : P =>
      (⟨Ideal.Quotient.mk I (f p), ⟨f p, hf p, rfl⟩⟩ : coordinatePiece w I d)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc p
  have h := congrArg (fun z : coordinatePiece w I d =>
    quotientEvaluation I (points p) (hI p) z.val) hc
  have heval (q : P) :
      quotientEvaluation I (points p) (hI p) (Ideal.Quotient.mk I (f q)) =
        eval (points p) (f q) := by
    simp [quotientEvaluation, aeval_def]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
    map_sum, map_smul, map_zero, heval, smul_eq_mul] at h
  have hs : (∑ q, c q * eval (points p) (f q)) =
      c p * eval (points p) (f p) := by
    apply Finset.sum_eq_single p
    · intro q _ hqp
      rw [hoff p q (Ne.symm hqp), mul_zero]
    · simp
  rw [hs] at h
  exact (mul_eq_zero.mp h).resolve_right (hdiag p)

theorem card_le_finrank_of_separating_polynomials
    (w : σ → D) (I : Ideal (MvPolynomial σ K)) (d : D)
    [Module.Finite K (coordinatePiece w I d)]
    (points : P → σ → K) (hI : ∀ p f, f ∈ I → eval (points p) f = 0)
    (f : P → MvPolynomial σ K)
    (hf : ∀ p, IsWeightedHomogeneous w (f p) d)
    (hdiag : ∀ p, eval (points p) (f p) ≠ 0)
    (hoff : ∀ p q, p ≠ q → eval (points p) (f q) = 0) :
    Fintype.card P ≤ Module.finrank K (coordinatePiece w I d) :=
  (independent_of_separating_polynomials w I d points hI f hf hdiag hoff).fintype_card_le_finrank

/-- The actual evaluation linear map on the coordinate piece. -/
def pieceEvaluation (w : σ → D) (I : Ideal (MvPolynomial σ K)) (d : D)
    (points : P → σ → K) (hI : ∀ p f, f ∈ I → eval (points p) f = 0) :
    coordinatePiece w I d →ₗ[K] (P → K) :=
  LinearMap.pi (fun p =>
    (quotientEvaluation I (points p) (hI p)).toLinearMap.comp
      (coordinatePiece w I d).subtype)

/-- Explicit interpolation makes evaluation onto all functions on the chosen
finite points surjective. This remains valid with excess components. -/
theorem pieceEvaluation_surjective_of_separating_polynomials
    (w : σ → D) (I : Ideal (MvPolynomial σ K)) (d : D)
    (points : P → σ → K) (hI : ∀ p f, f ∈ I → eval (points p) f = 0)
    (f : P → MvPolynomial σ K)
    (hf : ∀ p, IsWeightedHomogeneous w (f p) d)
    (hdiag : ∀ p, eval (points p) (f p) ≠ 0)
    (hoff : ∀ p q, p ≠ q → eval (points p) (f q) = 0) :
    Function.Surjective (pieceEvaluation w I d points hI) := by
  classical
  let b (p : P) : coordinatePiece w I d :=
    ⟨Ideal.Quotient.mk I (f p), ⟨f p, hf p, rfl⟩⟩
  intro y
  refine ⟨∑ p, (y p / eval (points p) (f p)) • b p, ?_⟩
  ext p
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    pieceEvaluation, LinearMap.pi_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, Submodule.subtype_apply, b]
  have heval (q : P) :
      quotientEvaluation I (points p) (hI p) (Ideal.Quotient.mk I (f q)) =
        eval (points p) (f q) := by simp [quotientEvaluation, aeval_def]
  simp only [heval, smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · exact div_mul_cancel₀ _ (hdiag p)
  · intro q _ hqp
    rw [hoff p q (Ne.symm hqp), mul_zero]
  · simp

/-- Pairwise degree-`d` separators give interpolation in every degree `k • d`
with `k ≥ #P - 1`. The polynomials are products of actual separators and
nonvanishing padding forms, not a numerical interpolation assumption. -/
theorem exists_interpolation
    (w : σ → D) (d : D) (points : P → σ → K)
    (hsep : ∀ p q, p ≠ q → ∃ f : MvPolynomial σ K,
      IsWeightedHomogeneous w f d ∧ eval (points p) f ≠ 0 ∧
        eval (points q) f = 0)
    (hpad : ∀ p, ∃ f : MvPolynomial σ K,
      IsWeightedHomogeneous w f d ∧ eval (points p) f ≠ 0)
    (k : ℕ) (hk : Fintype.card P - 1 ≤ k) :
    ∃ f : P → MvPolynomial σ K,
      (∀ p, IsWeightedHomogeneous w (f p) (k • d)) ∧
      (∀ p, eval (points p) (f p) ≠ 0) ∧
      (∀ p q, p ≠ q → eval (points p) (f q) = 0) := by
  classical
  have hsep' (p q : P) : ∃ f : MvPolynomial σ K,
      IsWeightedHomogeneous w f d ∧ eval (points p) f ≠ 0 ∧
        (p ≠ q → eval (points q) f = 0) := by
    by_cases hpq : p = q
    · obtain ⟨f, hf, hfp⟩ := hpad p
      exact ⟨f, hf, hfp, fun h => (h hpq).elim⟩
    · obtain ⟨f, hf, hfp, hfq⟩ := hsep p q hpq
      exact ⟨f, hf, hfp, fun _ => hfq⟩
  choose sep hsepH hsepP hsepQ using hsep'
  choose pad hpadH hpadP using hpad
  let f : P → MvPolynomial σ K := fun p =>
    (∏ q ∈ Finset.univ.erase p, sep p q) * pad p ^ (k - (Fintype.card P - 1))
  refine ⟨f, ?_, ?_, ?_⟩
  · intro p
    have hc : (Finset.univ.erase p).card = Fintype.card P - 1 := by simp
    have hh := (IsWeightedHomogeneous.prod (Finset.univ.erase p) (sep p)
      (fun _ => d) (fun q _ => hsepH p q)).mul
        ((hpadH p).pow (k - (Fintype.card P - 1)))
    simpa only [f, Finset.sum_const, hc, ← add_nsmul,
      Nat.add_sub_of_le hk] using hh
  · intro p
    simp only [f, map_mul, map_prod, map_pow]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun q _ => hsepP p q))
      (pow_ne_zero _ (hpadP p))
  · intro p q hpq
    simp only [f, map_mul, map_prod, map_pow]
    have hz : (∏ r ∈ Finset.univ.erase q, eval (points p) (sep q r)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hpq, Finset.mem_univ p⟩)
        (hsepQ q p (Ne.symm hpq))
    rw [hz, zero_mul]

end General

section LinearSeparation
variable {σ K : Type*} [Field K]

/-- Two nonzero, nonproportional vectors are separated by a linear form.
The explicit separator is a coordinate minor. -/
theorem exists_linear_separator (p q : σ → K)
    (hp : ∃ i, p i ≠ 0) (hq : ∃ i, q i ≠ 0)
    (hne : ¬ ∃ a : K, a ≠ 0 ∧ ∀ i, p i = a * q i) :
    ∃ i j, q j * p i - q i * p j ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨j, hj⟩ := hq
  have hpj : p j ≠ 0 := by
    intro hz
    obtain ⟨i, hi⟩ := hp
    have hh := h i j
    rw [hz, mul_zero, sub_zero] at hh
    exact hi ((mul_eq_zero.mp hh).resolve_left hj)
  apply hne
  refine ⟨p j / q j, div_ne_zero hpj hj, fun i => ?_⟩
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hj).mpr
  simpa [mul_comm] using sub_eq_zero.mp (h i j)

end LinearSeparation

section WeightedLinearSeparation
variable {σ ι K D : Type*} [Field K] [AddCommMonoid D]

theorem exists_weighted_linear_separator
    (w : σ → D) (d : D) (index : ι → σ) (hw : ∀ i, w (index i) = d)
    (p q : σ → K)
    (hp : ∃ i, p (index i) ≠ 0) (hq : ∃ i, q (index i) ≠ 0)
    (hne : ¬ ∃ a : K, a ≠ 0 ∧ ∀ i, p (index i) = a * q (index i)) :
    ∃ f : MvPolynomial σ K, IsWeightedHomogeneous w f d ∧
      eval p f ≠ 0 ∧ eval q f = 0 := by
  obtain ⟨i, j, hij⟩ := exists_linear_separator (p ∘ index) (q ∘ index) hp hq hne
  refine ⟨C (q (index j)) * X (index i) - C (q (index i)) * X (index j), ?_, ?_, ?_⟩
  · apply (weightedHomogeneousSubmodule K w d).sub_mem
    · simpa only [zero_add, hw] using
        (isWeightedHomogeneous_C w (q (index j))).mul (isWeightedHomogeneous_X K w (index i))
    · simpa only [zero_add, hw] using
        (isWeightedHomogeneous_C w (q (index i))).mul (isWeightedHomogeneous_X K w (index j))
  · simpa using hij
  · simp [mul_comm]

end WeightedLinearSeparation

section ThreeFactors
open MultiProjective
variable {X U V P : Type*}

/-- A degree `(1,1,1)` form nonzero at any genuine multiprojective point. -/
theorem exists_padding_form (p : Variables X U V → ℂ) (hp : HasNonzeroBlocks p) :
    ∃ f : MvPolynomial (Variables X U V) ℂ,
      IsWeightedHomogeneous (weight X U V) f (1, 1, 1) ∧ eval p f ≠ 0 := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩⟩ := hp
  refine ⟨MvPolynomial.X (.inl i) * MvPolynomial.X (.inr (.inl j)) *
    MvPolynomial.X (.inr (.inr k)), ?_, ?_⟩
  · exact ((isWeightedHomogeneous_X ℂ (weight X U V) (.inl i)).mul
      (isWeightedHomogeneous_X ℂ (weight X U V) (.inr (.inl j)))).mul
      (isWeightedHomogeneous_X ℂ (weight X U V) (.inr (.inr k)))
  · simpa using mul_ne_zero (mul_ne_zero hi hj) hk

/-- Multiprojective nonequivalence gives an explicit separator of common
tridegree `(1,1,1)`. No choice of a global affine slice is made. -/
theorem exists_three_factor_separator (p q : Variables X U V → ℂ)
    (hp : HasNonzeroBlocks p) (hq : HasNonzeroBlocks q)
    (hne : ¬ ProjectivelyEquivalent p q) :
    ∃ f : MvPolynomial (Variables X U V) ℂ,
      IsWeightedHomogeneous (weight X U V) f (1, 1, 1) ∧
        eval p f ≠ 0 ∧ eval q f = 0 := by
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩⟩ := hp
  by_cases hx : ∃ a : ℂ, a ≠ 0 ∧ ∀ i, p (.inl i) = a * q (.inl i)
  · by_cases hu : ∃ b : ℂ, b ≠ 0 ∧ ∀ j, p (.inr (.inl j)) = b * q (.inr (.inl j))
    · have hv : ¬ ∃ c : ℂ, c ≠ 0 ∧ ∀ k, p (.inr (.inr k)) = c * q (.inr (.inr k)) := by
        rintro ⟨c, hc, hvc⟩
        obtain ⟨a, ha, hxa⟩ := hx
        obtain ⟨b, hb, hub⟩ := hu
        exact hne ⟨a, b, c, ha, hb, hc, hxa, hub, hvc⟩
      obtain ⟨f, hf, hfp, hfq⟩ := exists_weighted_linear_separator
        (weight X U V) (0, 0, 1) (fun k => .inr (.inr k)) (fun _ => rfl)
        p q ⟨k, hk⟩ hq.2.2 hv
      refine ⟨MvPolynomial.X (.inl i) * MvPolynomial.X (.inr (.inl j)) * f, ?_, ?_, ?_⟩
      · exact ((isWeightedHomogeneous_X ℂ (weight X U V) (.inl i)).mul
          (isWeightedHomogeneous_X ℂ (weight X U V) (.inr (.inl j)))).mul hf
      · simpa using mul_ne_zero (mul_ne_zero hi hj) hfp
      · simp [hfq]
    · obtain ⟨f, hf, hfp, hfq⟩ := exists_weighted_linear_separator
        (weight X U V) (0, 1, 0) (fun j => .inr (.inl j)) (fun _ => rfl)
        p q ⟨j, hj⟩ hq.2.1 hu
      refine ⟨MvPolynomial.X (.inl i) * f * MvPolynomial.X (.inr (.inr k)), ?_, ?_, ?_⟩
      · exact ((isWeightedHomogeneous_X ℂ (weight X U V) (.inl i)).mul hf).mul
          (isWeightedHomogeneous_X ℂ (weight X U V) (.inr (.inr k)))
      · simpa using mul_ne_zero (mul_ne_zero hi hfp) hk
      · simp [hfq]
  · obtain ⟨f, hf, hfp, hfq⟩ := exists_weighted_linear_separator
      (weight X U V) (1, 0, 0) Sum.inl (fun _ => rfl) p q ⟨i, hi⟩ hq.1 hx
    refine ⟨f * MvPolynomial.X (.inr (.inl j)) * MvPolynomial.X (.inr (.inr k)), ?_, ?_, ?_⟩
    · exact (hf.mul (isWeightedHomogeneous_X ℂ (weight X U V) (.inr (.inl j)))).mul
        (isWeightedHomogeneous_X ℂ (weight X U V) (.inr (.inr k)))
    · simpa using mul_ne_zero (mul_ne_zero hfp hj) hk
    · simp [hfq]

theorem exists_three_factor_interpolation [Fintype P]
    (points : P → Variables X U V → ℂ)
    (hp : ∀ p, HasNonzeroBlocks (points p))
    (hdist : ∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q)
    (k : ℕ) (hk : Fintype.card P - 1 ≤ k) :
    ∃ f : P → MvPolynomial (Variables X U V) ℂ,
      (∀ p, IsWeightedHomogeneous (weight X U V) (f p) (k, k, k)) ∧
      (∀ p, eval (points p) (f p) ≠ 0) ∧
      (∀ p q, p ≠ q → eval (points p) (f q) = 0) := by
  simpa using exists_interpolation (weight X U V) (1, 1, 1) points
    (fun p q hpq => exists_three_factor_separator (points p) (points q) (hp p) (hp q)
      (fun h => hpq (hdist p q h)))
    (fun p => exists_padding_form (points p) (hp p)) k hk

theorem degree_eq_sum_threeBlockWeight (e : Variables X U V →₀ ℕ) :
    e.degree = (Finsupp.weight (weight X U V) e).1 +
      (Finsupp.weight (weight X U V) e).2.1 +
      (Finsupp.weight (weight X U V) e).2.2 := by
  classical
  simp only [Finsupp.degree, Finsupp.weight_apply, Finsupp.sum,
    Prod.fst_sum, Prod.snd_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rcases i with i | (i | i) <;> simp [weight]

theorem three_factor_homogeneous_finite [Finite X] [Finite U] [Finite V]
    (R : Type*) [CommRing R] (a b c : ℕ) :
    Module.Finite R (weightedHomogeneousSubmodule R (weight X U V) (a, b, c)) := by
  have hfinite : {e : Variables X U V →₀ ℕ |
      Finsupp.weight (weight X U V) e = (a, b, c)}.Finite := by
    apply (Finsupp.finite_of_degree_le (σ := Variables X U V) (a + b + c)).subset
    intro e he
    rw [Set.mem_setOf_eq, degree_eq_sum_threeBlockWeight, he]
  apply Module.Finite.iff_fg.mpr
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported, Finsupp.supported_eq_span_single]
  exact Submodule.fg_span (hfinite.image _)

instance three_factor_piece_finite [Finite X] [Finite U] [Finite V]
    {R : Type*} [CommRing R]
    (I : Ideal (MvPolynomial (Variables X U V) R)) (a b c : ℕ) :
    Module.Finite R (coordinatePiece (weight X U V) I (a, b, c)) := by
  letI := three_factor_homogeneous_finite (X := X) (U := U) (V := V) R a b c
  unfold coordinatePiece
  infer_instance

/-- Arbitrary extra components of `I` do not affect this lower bound. It
counts the specified finite projectively distinct common zeros, in the actual
trigraded coordinate ring, at every diagonal degree `k ≥ #P - 1`. -/
theorem card_le_three_factor_piece_finrank [Finite X] [Finite U] [Finite V] [Fintype P]
    (I : Ideal (MvPolynomial (Variables X U V) ℂ))
    (points : P → Variables X U V → ℂ)
    (hp : ∀ p, HasNonzeroBlocks (points p))
    (hdist : ∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q)
    (hI : ∀ p f, f ∈ I → eval (points p) f = 0)
    (k : ℕ) (hk : Fintype.card P - 1 ≤ k) :
    Fintype.card P ≤ Module.finrank ℂ
      (coordinatePiece (weight X U V) I (k, k, k)) := by
  obtain ⟨f, hf, hdiag, hoff⟩ := exists_three_factor_interpolation points hp hdist k hk
  exact card_le_finrank_of_separating_polynomials
    (weight X U V) I (k, k, k) points hI f hf hdiag hoff

theorem three_factor_pieceEvaluation_surjective [Fintype P]
    (I : Ideal (MvPolynomial (Variables X U V) ℂ))
    (points : P → Variables X U V → ℂ)
    (hp : ∀ p, HasNonzeroBlocks (points p))
    (hdist : ∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q)
    (hI : ∀ p f, f ∈ I → eval (points p) f = 0)
    (k : ℕ) (hk : Fintype.card P - 1 ≤ k) :
    Function.Surjective (pieceEvaluation (weight X U V) I (k, k, k) points hI) := by
  obtain ⟨f, hf, hdiag, hoff⟩ := exists_three_factor_interpolation points hp hdist k hk
  exact pieceEvaluation_surjective_of_separating_polynomials
    (weight X U V) I (k, k, k) points hI f hf hdiag hoff

/-- The lower-bound ingredient applies directly to the ideal generated by
an actual incidence system, without a separate vanishing-ideal certificate. -/
theorem card_le_equations_piece_finrank
    [Finite X] [Finite U] [Finite V] [Fintype P] {E : Type*}
    (equations : E → MvPolynomial (Variables X U V) ℂ)
    (points : P → Variables X U V → ℂ)
    (hp : ∀ p, HasNonzeroBlocks (points p))
    (hdist : ∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q)
    (hzero : ∀ p e, eval (points p) (equations e) = 0)
    (k : ℕ) (hk : Fintype.card P - 1 ≤ k) :
    Fintype.card P ≤ Module.finrank ℂ
      (coordinatePiece (weight X U V) (Ideal.span (Set.range equations)) (k, k, k)) := by
  apply card_le_three_factor_piece_finrank _ points hp hdist _ k hk
  intro p f hf
  have hle : Ideal.span (Set.range equations) ≤ RingHom.ker (eval (points p)) := by
    apply Ideal.span_le.mpr
    rintro g ⟨e, rfl⟩
    exact hzero p e
  exact hle hf

end ThreeFactors

end Sheshadri.ProjectivePointInterpolation
