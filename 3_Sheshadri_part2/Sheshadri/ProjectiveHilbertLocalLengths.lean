/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FiniteProjectiveHilbert
import Sheshadri.ArtinianLocalDecomposition

/-!
# The eventual projective Hilbert value is the sum of actual local lengths

The common-chart support condition implies that the literal normalized chart
algebra is finite. Its decomposition includes every maximal ideal and every
nilpotent local contribution. Thus the identification of the numerical Hilbert
value with the zero-dimensional cycle degree is proved, not postulated.
-/

noncomputable section
namespace Sheshadri.ProjectiveHilbertLocalLengths
open MvPolynomial MultiProjective ProjectivePointInterpolation
open FlatMultiGradedHilbert FiniteProjectiveHilbert

variable {X U V K : Type*} [Fintype X] [Fintype U] [Fintype V]
  [Field K] [IsAlgClosed K]

/-- The degree of the literal chart's zero-dimensional cycle: sum over ALL
closed points of lengths of their actual local rings. -/
def chartCycleDegree (I : Ideal (MvPolynomial (Variables X U V) K))
    (lx lu lv : MvPolynomial (Variables X U V) K) : ℕ∞ :=
  ∑ᶠ p : MaximalSpectrum (ChartAlgebra I lx lu lv),
    Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)

/-- The chart support condition yields the full equality between actual
high homogeneous-piece dimensions and the degree of the actual local cycle.
There is no assumed local-length conservation, CRT isomorphism, rational
residue-field identification, or numerical degree formula. -/
theorem eventually_hilbert_eq_sum_local_lengths
    (I : Ideal (MvPolynomial (Variables X U V) K))
    (lx lu lv : MvPolynomial (Variables X U V) K)
    (hI : IsHomogeneous (weight X U V) I)
    (hx : IsWeightedHomogeneous (weight X U V) lx (1, 0, 0))
    (hu : IsWeightedHomogeneous (weight X U V) lu (0, 1, 0))
    (hv : IsWeightedHomogeneous (weight X U V) lv (0, 0, 1))
    (hboundary : BoundaryAvoidance I (lx * lu * lv)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      (Module.finrank K (coordinatePiece (weight X U V) I (n, n, n)) : ℕ∞) =
        chartCycleDegree I lx lu lv := by
  letI : Module.Finite K (ChartAlgebra I lx lu lv) :=
    chartAlgebra_finite I lx lu lv hI hx hu hv hboundary
  letI : IsArtinianRing (ChartAlgebra I lx lu lv) :=
    IsArtinianRing.of_finite K _
  letI := Fintype.ofFinite (MaximalSpectrum (ChartAlgebra I lx lu lv))
  obtain ⟨N, hN⟩ := eventually_finrank_piece_eq_chart I lx lu lv hI hx hu hv hboundary
  refine ⟨N, fun n hn => ?_⟩
  rw [hN n hn, ArtinianLocalDecomposition.finrank_eq_sum_local_length K]
  exact (finsum_eq_sum_of_fintype _).symm

theorem chartCycleDegree_ne_top
    (I : Ideal (MvPolynomial (Variables X U V) K))
    (lx lu lv : MvPolynomial (Variables X U V) K)
    (hI : IsHomogeneous (weight X U V) I)
    (hx : IsWeightedHomogeneous (weight X U V) lx (1, 0, 0))
    (hu : IsWeightedHomogeneous (weight X U V) lu (0, 1, 0))
    (hv : IsWeightedHomogeneous (weight X U V) lv (0, 0, 1))
    (hboundary : BoundaryAvoidance I (lx * lu * lv)) :
    chartCycleDegree I lx lu lv ≠ ⊤ := by
  obtain ⟨N, hN⟩ := eventually_hilbert_eq_sum_local_lengths I lx lu lv hI hx hu hv hboundary
  rw [← hN N le_rfl]
  exact ENat.coe_ne_top _

/-- The full local-length degree is independent of the common chart. -/
theorem chartCycleDegree_eq_of_boundary
    (I : Ideal (MvPolynomial (Variables X U V) K))
    (lx lu lv mx mu mv : MvPolynomial (Variables X U V) K)
    (hI : IsHomogeneous (weight X U V) I)
    (hlx : IsWeightedHomogeneous (weight X U V) lx (1, 0, 0))
    (hlu : IsWeightedHomogeneous (weight X U V) lu (0, 1, 0))
    (hlv : IsWeightedHomogeneous (weight X U V) lv (0, 0, 1))
    (hmx : IsWeightedHomogeneous (weight X U V) mx (1, 0, 0))
    (hmu : IsWeightedHomogeneous (weight X U V) mu (0, 1, 0))
    (hmv : IsWeightedHomogeneous (weight X U V) mv (0, 0, 1))
    (hl : BoundaryAvoidance I (lx * lu * lv))
    (hm : BoundaryAvoidance I (mx * mu * mv)) :
    chartCycleDegree I lx lu lv = chartCycleDegree I mx mu mv := by
  obtain ⟨N, hN⟩ := eventually_hilbert_eq_sum_local_lengths I lx lu lv hI hlx hlu hlv hl
  obtain ⟨M, hM⟩ := eventually_hilbert_eq_sum_local_lengths I mx mu mv hI hmx hmu hmv hm
  exact (hN (max N M) (le_max_left _ _)).symm.trans (hM (max N M) (le_max_right _ _))

end Sheshadri.ProjectiveHilbertLocalLengths
