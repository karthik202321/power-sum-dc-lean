/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.BezoutDeformationBound
import Sheshadri.BezoutSplitHilbert
import Sheshadri.BezoutVariableTransport
import Sheshadri.BezoutArity

/-!
# Multihomogeneous Bézout for simple isolated zeros with excess

This proves the complete `UniversalSimpleBezout` proposition. Only the chosen
finite family of zeros must be simple; arbitrary further components are allowed.
All comparison equations, homogeneous quotient pieces and their bounds are
constructed. The proof does not assume an intersection count or regularity of
the Cox equations. This is not the multiplicity theorem for singular zeros.
-/

noncomputable section
namespace Sheshadri.BezoutWithExcess
open MvPolynomial MultiProjective ProjectivePointInterpolation
open BezoutSplitSystem BezoutVariableTransport BezoutSplitHilbert

set_option maxHeartbeats 800000

/-- The previously explicit universal input is now a proved theorem,
including the possibility of positive-dimensional excess components. -/
theorem universal_simple_bezout : UniversalSimpleBezout := by
  intro X U V E P _ _ _ _ _ _ _ _ f degree points hcard hf hzero hsimple hdist
  classical
  have hdim : Fintype.card E = ∑ b, dimensions X U V b := by
    rw [sum_dimensions]
    exact hcard
  obtain ⟨N,hN⟩ := canonicalSplitSystem_eventualBound (dimensions X U V) degree hdim
  let k := max N (Fintype.card P - 1)
  have hbound := BezoutDeformationBound.simple_roots_le_comparison_piece
    (K := FractionRing (Polynomial ℂ)) f (transportedSplitEquation X U V degree)
    degree points hcard hf (transportedSplitEquation_homogeneous X U V degree)
    hzero hsimple hdist k (le_max_right _ _)
  rw [transportedSplitEquation_piece_finrank] at hbound
  exact hbound.trans (hN k k k (le_max_left _ _) (le_max_left _ _) (le_max_left _ _))

/-- The same excess-compatible result for two projective factors. -/
theorem universal_bi_simple_bezout : UniversalBiSimpleBezout :=
  BezoutArity.universal_bi_of_universal universal_simple_bezout

end Sheshadri.BezoutWithExcess
