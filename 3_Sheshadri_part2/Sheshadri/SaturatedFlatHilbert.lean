/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.GeneralFlatHilbertPolynomial
import Sheshadri.SaturatedFlatFamily
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal

/-!
# Hilbert conservation for the constructed horizontal closure

Starting with an actual radical bihomogeneous generic ideal, contraction
constructs its reduced horizontal closure. Its bihomogeneity and
base-torsion-freeness are proved, so the general Hilbert theorem applies
without any family-flatness or Hilbert-evaluation assumptions.
-/

noncomputable section
namespace Sheshadri.SaturatedFlatHilbert

open MvPolynomial FlatGradedHilbert HilbertPolynomialExistence
open SaturatedFlatFamily GeneralGradedBaseChange GeneralFlatHilbertPolynomial

variable {σ R K : Type*} [Finite σ] [CommRing R] [Field K] [Algebra R K]

/-- The horizontal closure of a radical bihomogeneous generic ideal is
bihomogeneous by commuting coefficient extension with projection. -/
theorem horizontalIdeal_bihomogeneous (block : σ → Bool)
    (I : Ideal (MvPolynomial σ K)) (hred : I.IsRadical)
    (hI : IsBihomogeneous σ K block I) :
    IsBihomogeneous σ R block (horizontalIdeal R K I) := by
  intro a b p hp
  rw [horizontalIdeal_eq_comap, hred.radical] at hp ⊢
  change MvPolynomial.map (algebraMap R K)
    (weightedHomogeneousComponent (twoBlockWeight σ block) (a, b) p) ∈ I
  rw [← GeneralHomogeneousBaseChange.weightedComponent_map]
  exact hI a b _ hp

/-- Extension back to the generic field recovers exactly the generic
radical ideal. This uses localization, not a surjectivity assertion for
the coefficient homomorphism. -/
theorem extended_horizontalIdeal_eq_radical [IsDomain R] [IsFractionRing R K]
    (I : Ideal (MvPolynomial σ K)) :
    extendedIdeal (K := K) (horizontalIdeal R K I) = I.radical := by
  letI := MvPolynomial.algebraMvPolynomial (σ := σ) (R := R) (S := K)
  rw [extendedIdeal, horizontalIdeal_eq_comap]
  exact IsLocalization.map_comap ((nonZeroDivisors R).map (MvPolynomial.C (σ := σ)))
    (MvPolynomial σ K) I.radical

variable {τ : Type*} [Finite τ] [Nonempty σ] [Nonempty τ]
variable [IsDomain R] [IsFractionRing R K] [IsPrincipalIdealRing R]

/-- A constructed Hilbert polynomial of a fibre of the actual horizontal
closure of the generic bihomogeneous ideal. -/
def horizontalHilbertPolynomial (I : Ideal (MvPolynomial (σ ⊕ τ) K))
    (hred : I.IsRadical) (hI : IsBihomogeneous (σ ⊕ τ) K sumBlock I)
    (L : Type*) [Field L] [Algebra R L] : Polynomial (Polynomial ℚ) :=
  fieldHilbertPolynomial (horizontalIdeal R K I)
    (horizontalIdeal_bihomogeneous sumBlock I hred hI) L

/-- Every field fibre of the constructed reduced horizontal closure has
the same actual, constructed bivariate Hilbert polynomial. -/
theorem horizontalHilbertPolynomial_constant
    (I : Ideal (MvPolynomial (σ ⊕ τ) K))
    (hred : I.IsRadical) (hI : IsBihomogeneous (σ ⊕ τ) K sumBlock I)
    (L M : Type*) [Field L] [Field M] [Algebra R L] [Algebra R M] :
    horizontalHilbertPolynomial (R := R) I hred hI L =
      horizontalHilbertPolynomial (R := R) I hred hI M :=
  fieldHilbertPolynomial_constant (horizontalIdeal R K I)
    (horizontalIdeal_bihomogeneous sumBlock I hred hI) L M

/-- The original generic ideal and every actual field fibre of its
horizontal closure have identical graded dimensions, at every bidegree. -/
theorem horizontal_fibre_dimensions_eq_generic
    (I : Ideal (MvPolynomial (σ ⊕ τ) K))
    (hred : I.IsRadical) (hI : IsBihomogeneous (σ ⊕ τ) K sumBlock I)
    (L : Type*) [Field L] [Algebra R L] (a b : ℕ) :
    Module.finrank L (bicoordinatePiece (σ ⊕ τ) L sumBlock
      (extendedIdeal (K := L) (horizontalIdeal R K I)) a b) =
      Module.finrank K (bicoordinatePiece (σ ⊕ τ) K sumBlock I a b) := by
  rw [extended_ideal_hilbert_values_equal (horizontalIdeal R K I)
    (horizontalIdeal_bihomogeneous sumBlock I hred hI) L K a b,
    extended_horizontalIdeal_eq_radical, hred.radical]

end Sheshadri.SaturatedFlatHilbert
