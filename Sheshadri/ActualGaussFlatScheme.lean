/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ActualGaussFlatness
import Sheshadri.SaturatedFlatFamily
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Flatness of the constructed affine-line Gauss family

These theorems apply the proved scalar saturation of the *actual* Gauss
vanishing ideal to its actual quotient ring and spectrum.  No flatness,
componentwise-dominance, or torsion-freeness hypothesis is assumed.

The base here is an affine line.  This module does not assert that every
border point admits an algebraic arc parametrized by an affine line.
-/

noncomputable section
namespace Sheshadri.ActualGaussFlatScheme

open ActualGaussFamily ActualGaussFlatness

variable {Z : Type} [Fintype Z]

/-- The actual Gauss-closure coordinate ring has no base torsion. -/
theorem coordinateRing_torsionfree
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U) :
    NoZeroSMulDivisors (Polynomial ℂ) (CoordinateRing F U) :=
  SaturatedFlatFamily.quotient_torsionfree_of_saturated (totalIdeal F U)
    (totalIdeal_saturated F U hU)

/-- Flatness is proved for the actual coordinate ring, from persistence
and the polynomial PID structure of the base. -/
theorem coordinateRing_flat
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U) :
    Module.Flat (Polynomial ℂ) (CoordinateRing F U) :=
  SaturatedFlatFamily.quotient_flat_of_saturated (totalIdeal F U)
    (totalIdeal_saturated F U hU)

/-- Flatness of the actual map of affine schemes. -/
theorem structureMorphism_flat
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U) :
    AlgebraicGeometry.Flat
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap (Polynomial ℂ) (CoordinateRing F U)))) := by
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)]
  exact flat_algebraMap_iff.mpr (coordinateRing_flat F U hU)

end Sheshadri.ActualGaussFlatScheme
