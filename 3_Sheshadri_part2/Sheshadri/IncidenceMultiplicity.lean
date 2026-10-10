/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.IncidenceBezout
import Sheshadri.SingularBezoutWithExcess
import Sheshadri.BezoutArity
import Sheshadri.BiProjectiveLocalMultiplicity

/-!
# Determinant incidence bounds with singular intersection multiplicities

These bounds count lengths of the actual local equation rings. Only the
selected zeros must be isolated (their local rings Artinian); other components
can have arbitrary excess. No simplicity or transversality is required.
The symmetric statement uses the literal embedding into a third projective
factor of dimension zero, whose sole coordinate is fixed to one.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
namespace Sheshadri.Incidence
open Matrix MvPolynomial MultiProjective ProjectiveLocalMultiplicity
open scoped BigOperators

theorem ordinary_incidence_multiplicity_bound
    {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) {P : Type} [Fintype P]
    (A : PencilCoefficients n m ℂ) (Λ : Matrix (Fin (m - 1)) (Fin m) ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (points : P → OrdinaryVar n m → ℂ) (charts : ∀ p, Chart (points p))
    (hzero : ∀ p e, eval (points p) (ordinarySystem A Λ flags M e) = 0)
    [∀ p, IsArtinianRing (LocalRing (ordinarySystem A Λ flags M)
      (points p) (charts p) (hzero p))]
    (hdistinct : ∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q) :
    (∑ p, multiplicity (ordinarySystem A Λ flags M) (points p) (charts p) (hzero p)) ≤
      (ordinaryBezout m n : ℕ∞) := by
  letI : NeZero m := ⟨by omega⟩
  have hc : Fintype.card (OrdinaryEquationIndex n m) =
      (Fintype.card (Fin (n + 1)) - 1) + (Fintype.card (Fin m) - 1) +
        (Fintype.card (Fin m) - 1) := by
    rw [ordinarySystem_equation_count hn hm]
    simp only [Fintype.card_fin]
    omega
  have hd : ∀ e, IsWeightedHomogeneous (weight (Fin (n + 1)) (Fin m) (Fin m))
      (ordinarySystem A Λ flags M e) (ordinaryDegree e) := by
    have hw : weight (Fin (n + 1)) (Fin m) (Fin m) =
        ordinaryWeight (n := n) (m := m) := by
      funext i
      rcases i with i | (i | i) <;> rfl
    rw [hw]
    exact ordinarySystem_multidegree A Λ flags M
  have h := SingularBezoutWithExcess.isolated_multiplicity_bound
    (ordinarySystem A Λ flags M) ordinaryDegree points charts hc hd hzero hdistinct
  simpa only [Fintype.card_fin, Nat.add_sub_cancel, ordinary_budget_eq m n hm hn] using h

/-- The actual symmetric system with a projective zero-space factor.
The extra coordinate has degree zero in every incidence equation. -/
def symmetricSystemThree {n m : ℕ} (A : PencilCoefficients n m ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ) :=
  fun e => rename BezoutArity.embed (symmetricSystem A flags M e)

theorem symmetric_incidence_multiplicity_bound_three
    {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) {P : Type} [Fintype P]
    (A : PencilCoefficients n m ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (points : P → SymmetricVar n m → ℂ)
    (charts : ∀ p, Chart (BezoutArity.extendPoint (points p)))
    (hzero : ∀ p e, eval (BezoutArity.extendPoint (points p))
      (symmetricSystemThree A flags M e) = 0)
    [∀ p, IsArtinianRing (LocalRing (symmetricSystemThree A flags M)
      (BezoutArity.extendPoint (points p)) (charts p) (hzero p))]
    (hdistinct : ∀ p q, BiProjectivelyEquivalent (points p) (points q) → p = q) :
    (∑ p, multiplicity (symmetricSystemThree A flags M)
      (BezoutArity.extendPoint (points p)) (charts p) (hzero p)) ≤
      (symmetricBezout m n : ℕ∞) := by
  letI : NeZero m := ⟨by omega⟩
  have hc : Fintype.card (SymmetricEquationIndex n m) =
      (Fintype.card (Fin (n + 1)) - 1) + (Fintype.card (Fin m) - 1) +
        (Fintype.card Unit - 1) := by
    rw [symmetricSystem_equation_count hn]
    simp only [Fintype.card_fin, Fintype.card_unit]
    omega
  have hd : ∀ e, IsWeightedHomogeneous (weight (Fin (n + 1)) (Fin m) Unit)
      (symmetricSystemThree A flags M e) (symmetricDegreeThree e) := by
    intro e
    apply BezoutArity.homogeneous_embed
    have hw : biWeight (Fin (n + 1)) (Fin m) = symmetricWeight (n := n) (m := m) := by
      funext i
      cases i <;> rfl
    rw [hw]
    exact symmetricSystem_multidegree A flags M e
  have hdist : ∀ p q, ProjectivelyEquivalent (BezoutArity.extendPoint (points p))
      (BezoutArity.extendPoint (points q)) → p = q := by
    intro p q h
    obtain ⟨a,b,c,ha,hb,_,hx,hu,_⟩ := h
    exact hdistinct p q ⟨a,b,ha,hb,hx,hu⟩
  have h := SingularBezoutWithExcess.isolated_multiplicity_bound
    (symmetricSystemThree A flags M) symmetricDegreeThree
    (fun p => BezoutArity.extendPoint (points p)) charts hc hd hzero hdist
  simpa only [Fintype.card_fin, Nat.add_sub_cancel, Fintype.card_unit, Nat.sub_self,
    symmetric_budget_eq m n hm hn] using h

/-- The symmetric bound for literal two-factor chart local rings. The
projective zero-space factor is removed by a proved local-ring isomorphism. -/
theorem symmetric_incidence_multiplicity_bound
    {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) {P : Type} [Fintype P]
    (A : PencilCoefficients n m ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (points : P → SymmetricVar n m → ℂ)
    (charts : ∀ p, BiProjectiveLocalMultiplicity.Chart (points p))
    (hzero : ∀ p e, eval (points p) (symmetricSystem A flags M e) = 0)
    [∀ p, IsArtinianRing (BiProjectiveLocalMultiplicity.LocalRing
      (symmetricSystem A flags M) (points p) (charts p) (hzero p))]
    (hdistinct : ∀ p q, BiProjectivelyEquivalent (points p) (points q) → p = q) :
    (∑ p, BiProjectiveLocalMultiplicity.multiplicity (symmetricSystem A flags M)
      (points p) (charts p) (hzero p)) ≤ (symmetricBezout m n : ℕ∞) := by
  let hz := fun p => BiProjectiveLocalMultiplicity.extend_zero
    (symmetricSystem A flags M) (points p) (hzero p)
  letI (p : P) : IsArtinianRing (LocalRing (symmetricSystemThree A flags M)
      (BezoutArity.extendPoint (points p)) (charts p).extend (hz p)) :=
    (BiProjectiveLocalMultiplicity.localRingEquiv (symmetricSystem A flags M)
      (points p) (charts p) (hzero p)).symm.isArtinianRing
  have h := symmetric_incidence_multiplicity_bound_three hn hm A flags M points
    (fun p => (charts p).extend) hz hdistinct
  have he : (∑ p, BiProjectiveLocalMultiplicity.multiplicity (symmetricSystem A flags M)
      (points p) (charts p) (hzero p)) =
      ∑ p, multiplicity (symmetricSystemThree A flags M)
        (BezoutArity.extendPoint (points p)) (charts p).extend (hz p) := by
    apply Finset.sum_congr rfl
    intro p _
    exact (BiProjectiveLocalMultiplicity.multiplicity_extend
      (symmetricSystem A flags M) (points p) (charts p) (hzero p)).symm
  rwa [he]

end Sheshadri.Incidence
