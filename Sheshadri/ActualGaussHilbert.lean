/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ActualGaussCoefficientHomogeneous
import Sheshadri.FlatGradedHilbert

/-!
# Hilbert-function conservation for the constructed total Gauss family

This file applies the proved finite-module theorem to the actual quotient
ring constructed from the polynomial closure of the smooth Gauss graph.
The base is the affine complex line. Torsion-freeness is obtained from the
proved smooth-zero persistence argument, and finite generation of every
coordinate piece is proved from its monomials. No assumption asserts
constancy of fibre dimensions.

A general smooth algebraic curve need not admit the global polynomial-line
parametrization used here. Applying the same argument locally over its DVRs,
and relating coordinate Hilbert data to cycles, remain distinct tasks.
-/

noncomputable section

namespace Sheshadri.ActualGaussHilbert

open MvPolynomial ActualGaussCoefficientRing FlatGradedHilbert
open scoped TensorProduct

variable {Z : Type} [Fintype Z]

/-- Which projective block a spatial variable belongs to. -/
def spatialBlock : SpatialVariables Z → Bool := Sum.elim (fun _ => true) (fun _ => false)

/-- The actual bidegree module in the actual total Gauss coordinate ring. -/
abbrev gaussCoordinatePiece (F : MvPolynomial (Unit ⊕ Z) ℂ)
    (U : Set (Unit → ℂ)) (a b : ℕ) :=
  bicoordinatePiece (SpatialVariables Z) (Polynomial ℂ) spatialBlock
    (coefficientIdeal F U) a b

/-- The generic field and every residue field give the same dimension for
each of these concrete finite coordinate modules. -/
theorem actual_gauss_coordinate_dimensions_constant
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U)
    (K L : Type*) [Field K] [Field L]
    [Algebra (Polynomial ℂ) K] [Algebra (Polynomial ℂ) L] (a b : ℕ) :
    Module.finrank K (K ⊗[Polynomial ℂ] gaussCoordinatePiece F U a b) =
      Module.finrank L (L ⊗[Polynomial ℂ] gaussCoordinatePiece F U a b) := by
  letI := coefficientRing_torsionfree F U hU
  exact bicoordinate_piece_fibre_dimensions_equal (SpatialVariables Z) (Polynomial ℂ)
    spatialBlock (coefficientIdeal F U) K L a b

/-- The actual homogeneous image inside the actual tensor fibre algebra. -/
abbrev gaussFibrePiece (F : MvPolynomial (Unit ⊕ Z) ℂ)
    (U : Set (Unit → ℂ)) (K : Type*) [Field K] [Algebra (Polynomial ℂ) K] (a b : ℕ) :=
  fibreBicoordinatePiece (SpatialVariables Z) (Polynomial ℂ) spatialBlock
    (coefficientIdeal F U) K a b

/-- Homogeneity of the actual ideal was proved from literal Gauss-graph
scaling. Thus the constant dimensions belong to actual submodules of the
two fibre algebras, not merely isolated tensor modules. -/
theorem actual_gauss_fibre_dimensions_constant
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U)
    (K L : Type*) [Field K] [Field L]
    [Algebra (Polynomial ℂ) K] [Algebra (Polynomial ℂ) L] (a b : ℕ) :
    Module.finrank K (gaussFibrePiece F U K a b) =
      Module.finrank L (gaussFibrePiece F U L a b) := by
  letI := coefficientRing_torsionfree F U hU
  exact fibre_bicoordinate_dimensions_equal (SpatialVariables Z) (Polynomial ℂ)
    spatialBlock (coefficientIdeal F U) (coefficientIdeal_bihomogeneous F U) K L a b

/-- A copy of `ℂ` carrying the base algebra structure `t ↦ c`. Distinct
copies allow two specializations to appear in the same theorem. -/
def SpecialField (_c : ℂ) := ℂ

instance specialField_field (c : ℂ) : Field (SpecialField c) := inferInstanceAs (Field ℂ)

instance specialField_algebra (c : ℂ) : Algebra (Polynomial ℂ) (SpecialField c) :=
  (Polynomial.evalRingHom c).toAlgebra

def specialHilbertValue (F : MvPolynomial (Unit ⊕ Z) ℂ)
    (U : Set (Unit → ℂ)) (c : ℂ) (a b : ℕ) : ℕ :=
  Module.finrank (SpecialField c)
    (gaussFibrePiece F U (SpecialField c) a b)

/-- Fully concrete equality at two arbitrary complex parameters: no field
or algebra structures need be supplied by the caller. -/
theorem actual_gauss_specialHilbertValue_constant
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U)
    (c c' : ℂ) (a b : ℕ) :
    specialHilbertValue F U c a b = specialHilbertValue F U c' a b := by
  exact actual_gauss_fibre_dimensions_constant F U hU
    (SpecialField c) (SpecialField c') a b

open ConormalEulerHilbert

/-- Eventual Hilbert polynomials of two actual fibre coordinate modules
are equal. Their representation of the actual dimensions, rather than
their equality, is the remaining polynomial hypothesis. -/
theorem actual_gauss_hilbert_polynomials_equal
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U)
    (c c' : ℂ) (H J : Polynomial (Polynomial ℚ)) (Q T : ℕ)
    (hH : ∀ q t : ℕ, Q ≤ q → T ≤ t → gridEval H q t =
      (specialHilbertValue F U c q (q * t) : ℚ))
    (hJ : ∀ q t : ℕ, Q ≤ q → T ≤ t → gridEval J q t =
      (specialHilbertValue F U c' q (q * t) : ℚ)) : H = J := by
  apply polynomial_eq_of_nat_grid_tail_eval_eq H J Q T
  intro q t hq ht
  rw [hH q t hq ht, hJ q t hq ht,
    actual_gauss_specialHilbertValue_constant F U hU c c' q (q * t)]

/-- Multidegree conservation, conditional only on the explicit classical
Hilbert/intersection interpretation of these actual fibre modules. -/
theorem actual_gauss_multidegrees_equal
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U)
    (c c' : ℂ) (H J : Polynomial (Polynomial ℚ)) (Q T d : ℕ)
    (δ ε : Fin (d + 1) → ℚ)
    (hH : ∀ q t : ℕ, Q ≤ q → T ≤ t → gridEval H q t =
      (specialHilbertValue F U c q (q * t) : ℚ))
    (hJ : ∀ q t : ℕ, Q ≤ q → T ≤ t → gridEval J q t =
      (specialHilbertValue F U c' q (q * t) : ℚ))
    (hδ : H.coeff d = ConormalHilbert.topHilbertPolynomial d δ)
    (hε : J.coeff d = ConormalHilbert.topHilbertPolynomial d ε) : δ = ε := by
  have h := actual_gauss_hilbert_polynomials_equal F U hU c c' H J Q T hH hJ
  apply ConormalHilbert.multidegrees_eq_of_topHilbertPolynomial_eq d
  rw [← hδ, ← hε, h]

end Sheshadri.ActualGaussHilbert
