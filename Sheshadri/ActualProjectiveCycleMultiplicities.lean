/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ActualProjectiveFibreCharts
import Sheshadri.TorusGenericLocalRings

/-!
# Actual conormal chart and cone multiplicities agree

The previously constructed coordinate-open cone isomorphism is combined with
proved torus cancellation of actual local lengths. This identifies every
component of each literal projective fibre chart with a component of the cone
coordinate open, preserving its full nonreduced multiplicity. This is an
affine-chart cycle statement; global scheme gluing and intersection degrees
are separate constructions.
-/

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section
namespace Sheshadri.ActualProjectiveCycleMultiplicities

open AffineFundamentalCycle ActualProjectiveFibreCharts ConormalProjectiveCharts
  TorusGenericLocalRings

/-- Actual minimal-prime correspondence under a ring isomorphism. -/
def componentRingEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Component R ≃ Component S where
  toFun := ProjectiveCycleLengths.componentOfRingEquiv e.symm
  invFun := ProjectiveCycleLengths.componentOfRingEquiv e
  left_inv p := by
    apply Subtype.ext
    ext r
    change e.symm (e r) ∈ p.val ↔ r ∈ p.val
    rw [e.symm_apply_apply]
  right_inv p := by
    apply Subtype.ext
    ext r
    change e (e.symm r) ∈ p.val ↔ r ∈ p.val
    rw [e.apply_symm_apply]

variable {Z : Type} [Fintype Z]
variable (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ)
variable (i j : Option Z)

instance fibreConeOpen_noetherian : IsNoetherianRing (FibreConeOpen F U c i j) :=
  IsLocalization.isNoetherianRing
    (Submonoid.powers
      (leftCoordinate (ActualGaussFamily.fibreIdeal F U (fun _ => c)) i *
        rightCoordinate (ActualGaussFamily.fibreIdeal F U (fun _ => c)) j))
    (FibreConeOpen F U c i j) inferInstance

/-- Every actual chart component corresponds to exactly one component of
the coordinate-open affine Gauss cone. No relevant component is discarded. -/
def chartConeComponentEquiv :
    Component (ChartRing F U c i j) ≃ Component (FibreConeOpen F U c i j) :=
  torusComponentEquiv.trans
    (componentRingEquiv (fibreConeOpenEquivTorus F U c i j).symm)

/-- Remove the two scaling directions from an arbitrary actual cone-open
component. Its base component is determined by the proved prime bijection. -/
def chartComponentOfConeOpen (q : Component (FibreConeOpen F U c i j)) :
    Component (ChartRing F U c i j) :=
  (chartConeComponentEquiv F U c i j).symm q

/-- Actual generic multiplicities agree after removing both torus factors.
This closes the local-length gap left by the cone/chart algebra isomorphism. -/
theorem chart_coneOpen_generic_length (p : Component (ChartRing F U c i j)) :
    Module.length (Localization.AtPrime p.val) (Localization.AtPrime p.val) =
      Module.length (Localization.AtPrime (chartConeComponentEquiv F U c i j p).val)
        (Localization.AtPrime (chartConeComponentEquiv F U c i j p).val) := by
  have ht := torus_generic_length p
  have he := ProjectiveCycleLengths.local_length_ringEquiv
    (fibreConeOpenEquivTorus F U c i j) (torusComponent p).val
  exact ht.trans he.symm

/-- The natural-number coefficients of the two actual fundamental cycles
agree as a consequence of the equality of their full local lengths. -/
theorem chart_coneOpen_multiplicity (p : Component (ChartRing F U c i j)) :
    multiplicity (ChartRing F U c i j) p =
      multiplicity (FibreConeOpen F U c i j) (chartConeComponentEquiv F U c i j p) := by
  exact congrArg ENat.toNat (chart_coneOpen_generic_length F U c i j p)

/-- The statement holds for every surviving cone component, and includes
all nilpotent generic lengths of the specialized fibre. -/
theorem coneOpen_chart_multiplicity (q : Component (FibreConeOpen F U c i j)) :
    multiplicity (FibreConeOpen F U c i j) q =
      multiplicity (ChartRing F U c i j) (chartComponentOfConeOpen F U c i j q) := by
  have h := chart_coneOpen_multiplicity F U c i j
    (chartComponentOfConeOpen F U c i j q)
  rw [show chartConeComponentEquiv F U c i j (chartComponentOfConeOpen F U c i j q) = q from
    (chartConeComponentEquiv F U c i j).apply_symm_apply q] at h
  exact h.symm

/-- The actual chart fundamental cycle has precisely the multiplicities
of the actual cone-open fundamental cycle under the component bijection. -/
theorem chartCycle_eq_coneOpenCycle (p : Component (ChartRing F U c i j)) :
    chartCycle F U c i j p =
      cycle (FibreConeOpen F U c i j) (chartConeComponentEquiv F U c i j p) :=
  chart_coneOpen_multiplicity F U c i j p

/-- Combining ordinary localization and torus cancellation identifies the
weight of each surviving component of the original affine Gauss fibre with
its actual projective chart weight. -/
theorem fibreCone_chart_multiplicity (q : Component (FibreConeOpen F U c i j)) :
    multiplicity (ConeRing (ActualGaussFamily.fibreIdeal F U (fun _ => c)))
      (ProjectiveCycleLengths.contractedComponent
        (Submonoid.powers
          (leftCoordinate (ActualGaussFamily.fibreIdeal F U (fun _ => c)) i *
            rightCoordinate (ActualGaussFamily.fibreIdeal F U (fun _ => c)) j)) q) =
      multiplicity (ChartRing F U c i j) (chartComponentOfConeOpen F U c i j q) := by
  exact (ProjectiveCycleLengths.multiplicity_localization _ q).trans
    (coneOpen_chart_multiplicity F U c i j q)

end Sheshadri.ActualProjectiveCycleMultiplicities
