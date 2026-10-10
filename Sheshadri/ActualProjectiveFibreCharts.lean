/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalChartTorus
import Sheshadri.ProjectiveCycleLengths
import Sheshadri.ActualGaussHilbertPolynomial

/-!
# Actual projective fibre charts and their generic multiplicities

The specialized Gauss ideal is proved bihomogeneous elsewhere. Applying the
explicit chart isomorphism gives literal normalized quotients, actual affine
schemes, and fundamental cycles computed from their generic local rings.
Their weights agree with those of the coordinate-ratio chart presentation.
No reducedness is imposed on the specialized fibre.

The actual coordinate-open cone is also proved isomorphic to the two-torus
over this chart. Removing the torus factor from generic multiplicities, and
gluing chart schemes to a global biprojective scheme, remain separate steps.
-/

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section
namespace Sheshadri.ActualProjectiveFibreCharts

open ActualGaussFamily ConormalProjectiveCharts

variable {Z : Type} [Fintype Z]
variable (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ)
variable (i j : Option Z)

/-- The coordinate algebra of the actual standard projective fibre chart. -/
abbrev ChartRing := NormalizedChart (fibreIdeal F U (fun _ => c)) i j

abbrev RatioRing := RatioChart (fibreIdeal F U (fun _ => c)) i j

/-- An actual isomorphism, derived from the bihomogeneity of the literal
specialized Gauss ideal. This also covers nonreduced special fibres. -/
def chartEquivRatios : ChartRing F U c i j ≃ₐ[ℂ] RatioRing F U c i j :=
  normalizedChartEquivRatioChart (fibreIdeal F U (fun _ => c)) i j
    (ActualGaussHilbertPolynomial.fibreIdeal_bihomogeneous F U c)

/-- The kernel is exactly the specialized Gauss equations and the two
chart normalization equations, not a newly chosen presentation ideal. -/
theorem chart_kernel :
    RingHom.ker (ratioEvaluation (fibreIdeal F U (fun _ => c)) i j) =
      normalizedIdeal (fibreIdeal F U (fun _ => c)) i j :=
  ker_ratioEvaluation (fibreIdeal F U (fun _ => c)) i j
    (ActualGaussHilbertPolynomial.fibreIdeal_bihomogeneous F U c)

/-- The actual affine scheme associated to the displayed projective chart. -/
def chartScheme : AlgebraicGeometry.Scheme :=
  normalizedChartScheme (fibreIdeal F U (fun _ => c)) i j

instance chartRing_noetherian : IsNoetherianRing (ChartRing F U c i j) := inferInstance

instance ratioRing_noetherian : IsNoetherianRing (RatioRing F U c i j) :=
  isNoetherianRing_of_ringEquiv (ChartRing F U c i j)
    (chartEquivRatios F U c i j).toRingEquiv

/-- The actual fundamental cycle on an affine projective chart. -/
def chartCycle : ConormalCycles.EffectiveCycle
    (AffineFundamentalCycle.Component (ChartRing F U c i j)) :=
  AffineFundamentalCycle.cycle (ChartRing F U c i j)

/-- Every actual irreducible component occurs with positive local length. -/
theorem chartCycle_positive
    (p : AffineFundamentalCycle.Component (ChartRing F U c i j)) :
    0 < chartCycle F U c i j p :=
  AffineFundamentalCycle.multiplicity_pos _ p

/-- These actual chart cycles cover precisely the entire chart spectrum. -/
theorem chartCycle_support :
    ConormalCycles.supportSet (AffineFundamentalCycle.componentSet (ChartRing F U c i j))
      (chartCycle F U c i j) = Set.univ :=
  AffineFundamentalCycle.supportSet_eq_univ _

/-- Generic local rings, hence all nilpotent multiplicities, agree under
the proved quotient/ratio isomorphism. -/
theorem chart_generic_multiplicity
    (p : AffineFundamentalCycle.Component (RatioRing F U c i j)) :
    AffineFundamentalCycle.multiplicity (ChartRing F U c i j)
      (ProjectiveCycleLengths.componentOfRingEquiv
        (chartEquivRatios F U c i j).toRingEquiv p) =
      AffineFundamentalCycle.multiplicity (RatioRing F U c i j) p :=
  ProjectiveCycleLengths.multiplicity_ringEquiv (chartEquivRatios F U c i j).toRingEquiv p

/-- The actual selected principal open of the specialized affine Gauss cone. -/
abbrev FibreConeOpen := ConeOpen (fibreIdeal F U (fun _ => c)) i j

/-- The literal algebra of two invertible variables over the projective chart. -/
abbrev FibreChartTorus := ConormalChartTorus.TorusRing (fibreIdeal F U (fun _ => c)) i j

/-- The actual projective chart/cone bridge: invert the selected coordinates
of the literal fibre, obtaining its normalized chart times two tori. -/
def fibreConeOpenEquivTorus : FibreConeOpen F U c i j ≃+* FibreChartTorus F U c i j :=
  ConormalChartTorus.coneOpenEquivTorus (fibreIdeal F U (fun _ => c)) i j
    (ActualGaussHilbertPolynomial.fibreIdeal_bihomogeneous F U c)

/-- Generic lengths agree under the actual cone-open/torus coordinate
isomorphism. This does not yet cancel the torus factor from the length. -/
theorem fibreConeOpen_torus_multiplicity
    (p : AffineFundamentalCycle.Component (FibreChartTorus F U c i j)) :
    AffineFundamentalCycle.multiplicity (FibreConeOpen F U c i j)
      (ProjectiveCycleLengths.componentOfRingEquiv
        (fibreConeOpenEquivTorus F U c i j) p) =
      AffineFundamentalCycle.multiplicity (FibreChartTorus F U c i j) p :=
  ProjectiveCycleLengths.multiplicity_ringEquiv (fibreConeOpenEquivTorus F U c i j) p

end Sheshadri.ActualProjectiveFibreCharts
