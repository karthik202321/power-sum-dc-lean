/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldBezoutRootPersistence

noncomputable section
open Sheshadri.MultiProjective
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

namespace Sheshadri.FieldBezoutDeformationBound
variable {k₀ : Type*} [Field k₀] [CharZero k₀]
set_option maxHeartbeats 800000
open MvPolynomial FieldMultiProjective ProjectivePointInterpolation
open BezoutHorizontalFamily FieldBezoutRootPersistence FlatMultiGradedHilbert

variable {X U V E P : Type*} [Fintype X] [Fintype U] [Fintype V]
  [Fintype E] [Fintype P] [Nonempty X] [Nonempty U] [Nonempty V]

theorem map_coefficient_interpolation (f g : MvPolynomial (Variables X U V) k₀) (a : k₀) :
    MvPolynomial.map (Polynomial.evalRingHom a) (coefficientEquiv (interpolation f g)) =
      C (1-a) * f + C a * g := by
  rw [coefficientEquiv_interpolation]
  have hc : (Polynomial.evalRingHom a).comp Polynomial.C = RingHom.id k₀ := by
    ext c
    simp
  simp only [map_add, map_mul, map_C,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
  simp only [MvPolynomial.map_map, hc, MvPolynomial.map_id]
  simp


end Sheshadri.FieldBezoutDeformationBound
