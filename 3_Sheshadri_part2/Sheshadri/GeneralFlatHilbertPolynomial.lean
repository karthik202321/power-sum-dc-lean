/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.GeneralGradedBaseChange
import Sheshadri.GeneralHomogeneousBaseChange
import Sheshadri.HilbertPolynomialExistence

/-!
# Constructed Hilbert polynomials over a PID or DVR

For a bihomogeneous ideal with torsion-free coordinate quotient over a PID,
the actual field quotients all have one constructed two-variable Hilbert
polynomial. Every polynomial and every eventual evaluation law is proved;
no candidate polynomial, intersection formula, or constancy certificate is
an input. In particular the result applies to the fraction field and every
residue field of a DVR.
-/

noncomputable section
namespace Sheshadri.GeneralFlatHilbertPolynomial

open MvPolynomial FlatGradedHilbert HilbertPolynomialExistence
open GeneralGradedBaseChange GeneralHomogeneousBaseChange

variable {σ τ R : Type*} [Finite σ] [Finite τ] [Nonempty σ] [Nonempty τ]
variable [CommRing R]

/-- The polynomial quotient by the extended equations has an actual
bivariate Hilbert polynomial over every field algebra. -/
theorem exists_field_hilbert_polynomial
    (I : Ideal (MvPolynomial (σ ⊕ τ) R))
    (hI : IsBihomogeneous (σ ⊕ τ) R sumBlock I)
    (K : Type*) [Field K] [Algebra R K] :
    ∃ H : Polynomial (Polynomial ℚ), ∃ N : ℕ, ∀ a b : ℕ, N ≤ a → N ≤ b →
      BiMonomialHilbert.biEval H a b =
        (Module.finrank K (bicoordinatePiece (σ ⊕ τ) K sumBlock
          (extendedIdeal (K := K) I) a b) : ℚ) :=
  exists_bicoordinate_hilbert_polynomial _ (bihomogeneous_map (algebraMap R K) _ I hI)

/-- Constructed from the literal extended ideal, using finite standard
monomials and inclusion-exclusion. -/
def fieldHilbertPolynomial (I : Ideal (MvPolynomial (σ ⊕ τ) R))
    (hI : IsBihomogeneous (σ ⊕ τ) R sumBlock I)
    (K : Type*) [Field K] [Algebra R K] : Polynomial (Polynomial ℚ) :=
  (exists_field_hilbert_polynomial I hI K).choose

def fieldHilbertThreshold (I : Ideal (MvPolynomial (σ ⊕ τ) R))
    (hI : IsBihomogeneous (σ ⊕ τ) R sumBlock I)
    (K : Type*) [Field K] [Algebra R K] : ℕ :=
  (exists_field_hilbert_polynomial I hI K).choose_spec.choose

theorem fieldHilbertPolynomial_eval (I : Ideal (MvPolynomial (σ ⊕ τ) R))
    (hI : IsBihomogeneous (σ ⊕ τ) R sumBlock I)
    (K : Type*) [Field K] [Algebra R K] (a b : ℕ)
    (ha : fieldHilbertThreshold I hI K ≤ a) (hb : fieldHilbertThreshold I hI K ≤ b) :
    BiMonomialHilbert.biEval (fieldHilbertPolynomial I hI K) a b =
      (Module.finrank K (bicoordinatePiece (σ ⊕ τ) K sumBlock
        (extendedIdeal (K := K) I) a b) : ℚ) :=
  (exists_field_hilbert_polynomial I hI K).choose_spec.choose_spec a b ha hb

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Every actual bidegree has the same dimension after arbitrary field
base change. Torsion-freeness of the coordinate quotient is the sole
flatness input. -/
theorem extended_ideal_hilbert_values_equal
    (I : Ideal (MvPolynomial (σ ⊕ τ) R))
    [NoZeroSMulDivisors R (MvPolynomial (σ ⊕ τ) R ⧸ I)]
    (hI : IsBihomogeneous (σ ⊕ τ) R sumBlock I)
    (K L : Type*) [Field K] [Field L] [Algebra R K] [Algebra R L] (a b : ℕ) :
    Module.finrank K (bicoordinatePiece (σ ⊕ τ) K sumBlock (extendedIdeal I) a b) =
      Module.finrank L (bicoordinatePiece (σ ⊕ τ) L sumBlock (extendedIdeal I) a b) := by
  rw [bicoordinatePiece_finrank_eq_fibre K, bicoordinatePiece_finrank_eq_fibre L]
  exact fibre_bicoordinate_dimensions_equal (σ ⊕ τ) R sumBlock I hI K L a b

/-- Constancy of the constructed Hilbert polynomial over every field of
the base, including generic and special fields. -/
theorem fieldHilbertPolynomial_constant
    (I : Ideal (MvPolynomial (σ ⊕ τ) R))
    [NoZeroSMulDivisors R (MvPolynomial (σ ⊕ τ) R ⧸ I)]
    (hI : IsBihomogeneous (σ ⊕ τ) R sumBlock I)
    (K L : Type*) [Field K] [Field L] [Algebra R K] [Algebra R L] :
    fieldHilbertPolynomial I hI K = fieldHilbertPolynomial I hI L := by
  let N := max (fieldHilbertThreshold I hI K) (fieldHilbertThreshold I hI L)
  apply polynomial_eq_of_nat_grid_tail_eval_eq _ _ N N
  intro a b ha hb
  change BiMonomialHilbert.biEval (fieldHilbertPolynomial I hI K) a b =
    BiMonomialHilbert.biEval (fieldHilbertPolynomial I hI L) a b
  rw [fieldHilbertPolynomial_eval I hI K a b ((le_max_left _ _).trans ha)
      ((le_max_left _ _).trans hb),
    fieldHilbertPolynomial_eval I hI L a b ((le_max_right _ _).trans ha)
      ((le_max_right _ _).trans hb),
    extended_ideal_hilbert_values_equal I hI K L a b]

/-- The generic fibre constructs a single polynomial and a single
threshold valid simultaneously for every field fibre of the base. -/
theorem generic_polynomial_evaluates_every_fibre
    (I : Ideal (MvPolynomial (σ ⊕ τ) R))
    [NoZeroSMulDivisors R (MvPolynomial (σ ⊕ τ) R ⧸ I)]
    (hI : IsBihomogeneous (σ ⊕ τ) R sumBlock I)
    (K : Type*) [Field K] [Algebra R K] (a b : ℕ)
    (ha : fieldHilbertThreshold I hI (FractionRing R) ≤ a)
    (hb : fieldHilbertThreshold I hI (FractionRing R) ≤ b) :
    BiMonomialHilbert.biEval (fieldHilbertPolynomial I hI (FractionRing R)) a b =
      (Module.finrank K (bicoordinatePiece (σ ⊕ τ) K sumBlock
        (extendedIdeal (K := K) I) a b) : ℚ) := by
  rw [fieldHilbertPolynomial_eval I hI (FractionRing R) a b ha hb,
    extended_ideal_hilbert_values_equal I hI (FractionRing R) K a b]

/-- Consequently all literal coefficients are conserved. Their
intersection-theoretic interpretation is a separate geometric theorem. -/
theorem fieldHilbertPolynomial_coefficients_constant
    (I : Ideal (MvPolynomial (σ ⊕ τ) R))
    [NoZeroSMulDivisors R (MvPolynomial (σ ⊕ τ) R ⧸ I)]
    (hI : IsBihomogeneous (σ ⊕ τ) R sumBlock I)
    (K L : Type*) [Field K] [Field L] [Algebra R K] [Algebra R L] (i j : ℕ) :
    ((fieldHilbertPolynomial I hI K).coeff i).coeff j =
      ((fieldHilbertPolynomial I hI L).coeff i).coeff j := by
  rw [fieldHilbertPolynomial_constant I hI K L]

end Sheshadri.GeneralFlatHilbertPolynomial
