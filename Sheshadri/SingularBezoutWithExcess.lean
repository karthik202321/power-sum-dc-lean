/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SingularBezoutDeformationBound
import Sheshadri.BezoutSplitHilbert
import Sheshadri.BezoutVariableTransport
import Sheshadri.IsolatedPointLocalRing

/-!
# Multihomogeneous Bézout with singular isolated-zero multiplicities

The multiplicity at each selected point is the length of its actual local
equation quotient in a valid projective chart. Artinian isolatedness is the
only local condition; the Jacobian may be singular. All other components of
the global zero scheme, including positive-dimensional excess, are allowed.
-/

noncomputable section
namespace Sheshadri.SingularBezoutWithExcess
open MvPolynomial MultiProjective ProjectivePointInterpolation
open BezoutSplitSystem BezoutVariableTransport BezoutSplitHilbert
open ProjectiveLocalMultiplicity
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

/-- The full numerical theorem with the actual local rings exposed. -/
theorem isolated_multiplicity_bound
    {X U V E P : Type} [Fintype X] [Fintype U] [Fintype V]
    [Fintype E] [Fintype P] [Nonempty X] [Nonempty U] [Nonempty V]
    (f : E → MvPolynomial (Variables X U V) ℂ) (degree : E → Degree)
    (points : P → Variables X U V → ℂ) (charts : ∀ p, Chart (points p))
    (hcard : Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
      (Fintype.card V - 1))
    (hf : ∀ e, (f e).IsWeightedHomogeneous (weight X U V) (degree e))
    (hzero : ∀ p e, eval (points p) (f e) = 0)
    [∀ p, IsArtinianRing (LocalRing f (points p) (charts p) (hzero p))]
    (hdist : ∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q) :
    (∑ p, multiplicity f (points p) (charts p) (hzero p)) ≤
      (coefficientBudget degree (Fintype.card X-1) (Fintype.card U-1)
        (Fintype.card V-1) : ℕ∞) := by
  classical
  have hdim : Fintype.card E = ∑ b, dimensions X U V b := by
    rw [sum_dimensions]
    exact hcard
  obtain ⟨N,hN⟩ := canonicalSplitSystem_eventualBound (dimensions X U V) degree hdim
  obtain ⟨M,hM⟩ :=
    SingularBezoutDeformationBound.isolated_multiplicities_le_comparison_piece
      (K := FractionRing (Polynomial ℂ)) f (transportedSplitEquation X U V degree)
      degree points charts hcard hf (transportedSplitEquation_homogeneous X U V degree)
      hzero hdist
  let k := max N M
  have hbound := hM k (le_max_right _ _)
  rw [transportedSplitEquation_piece_finrank] at hbound
  have hnum := hbound.trans (hN k k k (le_max_left _ _) (le_max_left _ _) (le_max_left _ _))
  simp_rw [multiplicity_eq_finrank]
  rw [← Nat.cast_sum]
  exact_mod_cast hnum

/-- The universal proposition mentions only actual polynomials, valid
projective charts, actual isolated local rings, and their lengths. -/
def UniversalMultiplicityBezout : Prop :=
  ∀ (X U V E P : Type) [Fintype X] [Fintype U] [Fintype V]
    [Fintype E] [Fintype P] [Nonempty X] [Nonempty U] [Nonempty V],
    ∀ (f : E → MvPolynomial (Variables X U V) ℂ) (degree : E → Degree)
      (points : P → Variables X U V → ℂ) (charts : ∀ p, Chart (points p)),
      Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
        (Fintype.card V - 1) →
      (∀ e, IsWeightedHomogeneous (weight X U V) (f e) (degree e)) →
      ∀ hzero : ∀ p e, eval (points p) (f e) = 0,
      (∀ p, IsArtinianRing (LocalRing f (points p) (charts p) (hzero p))) →
      (∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q) →
      (∑ p, multiplicity f (points p) (charts p) (hzero p)) ≤
        (coefficientBudget degree (Fintype.card X-1) (Fintype.card U-1)
          (Fintype.card V-1) : ℕ∞)

/-- No regularity, flatness, multiplicity-conservation, intersection-count,
or genericity hypothesis remains in this universal Bézout theorem. -/
theorem universal_multiplicity_bezout : UniversalMultiplicityBezout := by
  intro X U V E P _ _ _ _ _ _ _ _ f degree points charts hcard hf hzero hArt hdist
  letI := hArt
  exact isolated_multiplicity_bound f degree points charts hcard hf hzero hdist

/-- Literal isolatedness in each actual chart spectrum also suffices; its
Artinian local algebra is derived, not supplied as a separate certificate. -/
theorem isolated_multiplicity_bound_of_isOpen
    {X U V E P : Type} [Fintype X] [Fintype U] [Fintype V]
    [Fintype E] [Fintype P] [Nonempty X] [Nonempty U] [Nonempty V]
    (f : E → MvPolynomial (Variables X U V) ℂ) (degree : E → Degree)
    (points : P → Variables X U V → ℂ) (charts : ∀ p, Chart (points p))
    (hcard : Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
      (Fintype.card V - 1))
    (hf : ∀ e, (f e).IsWeightedHomogeneous (weight X U V) (degree e))
    (hzero : ∀ p e, eval (points p) (f e) = 0)
    (hopen : ∀ p, IsOpen {IsolatedLocalMultiplicity.pointSpectrum
      (chartIdeal f (points p) (charts p)) (points p)
        (chartIdeal_le_pointIdeal f (points p) (charts p) (hzero p))})
    (hdist : ∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q) :
    (∑ p, multiplicity f (points p) (charts p) (hzero p)) ≤
      (coefficientBudget degree (Fintype.card X-1) (Fintype.card U-1)
        (Fintype.card V-1) : ℕ∞) := by
  letI (p : P) : IsArtinianRing (LocalRing f (points p) (charts p) (hzero p)) :=
    IsolatedLocalMultiplicity.localIntersection_artinian_of_isOpen
      (chartIdeal f (points p) (charts p)) (points p)
      (chartIdeal_le_pointIdeal f (points p) (charts p) (hzero p)) (hopen p)
  exact isolated_multiplicity_bound f degree points charts hcard hf hzero hdist

end Sheshadri.SingularBezoutWithExcess
