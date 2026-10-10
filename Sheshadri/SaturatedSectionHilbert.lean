/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.HomogeneousHilbertDegree
import Sheshadri.OrdinaryProjectiveHilbert

/-!
# Hilbert degree through actual regular cuts and ideal enlargements

This iteration applies to the concrete operation "cut, then saturate": the
ideal enlargement only uses its literal inclusion, and every section is
regular in the actual current coordinate quotient. Hilbert polynomials of
all intermediate quotients are constructed rather than assumed as data.
-/
noncomputable section
namespace Sheshadri.SaturatedSectionHilbert
open MvPolynomial FlatGradedHilbert HomogeneousQuotientExact
open HomogeneousHilbertDegree GenericHomogeneousSections

variable {Z K : Type*} [Fintype Z] [Field K]

/-- After `r` actual regular cuts, even with arbitrary homogeneous ideal
enlargement after each cut, the actual Hilbert degree drops by at least `r`.
This is a reusable algebraic induction, not a geometric count hypothesis. -/
theorem exists_hilbert_polynomial_of_cut_sequence
    (I : ℕ → Ideal (MvPolynomial Z K))
    (hI : ∀ j k f, f ∈ I j → homogeneousComponent k f ∈ I j)
    (g : ℕ → MvPolynomial Z K) (d : ℕ → ℕ) (r : ℕ)
    (hg : ∀ j < r, (g j).IsHomogeneous (d j))
    (hreg : ∀ j < r, IsRegular (Ideal.Quotient.mk (I j) (g j)))
    (hle : ∀ j < r, enlargedIdeal (I j) (g j) ≤ I (j+1))
    (P₀ : Polynomial ℚ) (N₀ : ℕ)
    (hP₀ : ∀ k : ℕ, N₀ ≤ k → P₀.eval (k : ℚ) =
      (Module.finrank K (coordinatePiece Z K (I 0) k) : ℚ)) :
    ∃ P : Polynomial ℚ, ∃ N : ℕ,
      (∀ k : ℕ, N ≤ k → P.eval (k : ℚ) =
        (Module.finrank K (coordinatePiece Z K (I r) k) : ℚ)) ∧
      P.natDegree ≤ P₀.natDegree - r := by
  induction r with
  | zero => exact ⟨P₀,N₀,hP₀,by simp⟩
  | succ r ih =>
    obtain ⟨P,N,hP,hdeg⟩ := ih (fun j hj => hg j (by omega))
      (fun j hj => hreg j (by omega)) (fun j hj => hle j (by omega))
    have hJ := enlargedIdeal_homogeneous (I r) (hI r) (g r) (hg r (by omega))
    obtain ⟨Q,M,hQ⟩ := HilbertPolynomialExistence.exists_coordinate_hilbert_polynomial
      (enlargedIdeal (I r) (g r)) hJ
    obtain ⟨T,L,hT⟩ := HilbertPolynomialExistence.exists_coordinate_hilbert_polynomial
      (I (r+1)) (hI (r+1))
    have hcut := regular_cut_natDegree_le (I r) (hI r) (g r) (hg r (by omega))
      (hreg r (by omega)) P Q N M hP hQ
    have hquot := quotient_hilbert_natDegree_le (enlargedIdeal (I r) (g r)) (I (r+1))
      (hle r (by omega)) hJ (hI (r+1)) Q T M L hQ hT
    exact ⟨T,L,hT,by omega⟩

/-- A degree-zero actual Hilbert polynomial gives an eventual constant
natural-number dimension, extracted from a real graded piece. -/
theorem eventually_constant_of_natDegree_eq_zero
    (I : Ideal (MvPolynomial Z K)) (P : Polynomial ℚ) (N : ℕ)
    (hP : ∀ k : ℕ, N ≤ k → P.eval (k : ℚ) =
      (Module.finrank K (coordinatePiece Z K I k) : ℚ))
    (hdeg : P.natDegree = 0) :
    ∃ D : ℕ, ∃ M : ℕ, ∀ k > M, Module.finrank K (coordinatePiece Z K I k) = D := by
  refine ⟨Module.finrank K (coordinatePiece Z K I N),N,?_⟩
  intro k hk
  have heq : P.eval (k : ℚ) = P.eval (N : ℚ) := by
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
    simp
  rw [hP k hk.le,hP N le_rfl] at heq
  exact_mod_cast heq

/-- Enough regular cuts force an eventual constant without any separately
assumed finite-section, dimension, or point-count certificate. -/
theorem eventually_constant_of_cut_sequence
    (I : ℕ → Ideal (MvPolynomial Z K))
    (hI : ∀ j k f, f ∈ I j → homogeneousComponent k f ∈ I j)
    (g : ℕ → MvPolynomial Z K) (d : ℕ → ℕ) (r : ℕ)
    (hg : ∀ j < r, (g j).IsHomogeneous (d j))
    (hreg : ∀ j < r, IsRegular (Ideal.Quotient.mk (I j) (g j)))
    (hle : ∀ j < r, enlargedIdeal (I j) (g j) ≤ I (j+1))
    (P₀ : Polynomial ℚ) (N₀ : ℕ)
    (hP₀ : ∀ k : ℕ, N₀ ≤ k → P₀.eval (k : ℚ) =
      (Module.finrank K (coordinatePiece Z K (I 0) k) : ℚ))
    (hdeg : P₀.natDegree ≤ r) :
    ∃ D : ℕ, ∃ M : ℕ, ∀ k > M, Module.finrank K (coordinatePiece Z K (I r) k) = D := by
  obtain ⟨P,N,hP,hdegree⟩ := exists_hilbert_polynomial_of_cut_sequence I hI g d r hg hreg
    hle P₀ N₀ hP₀
  exact eventually_constant_of_natDegree_eq_zero (I r) P N hP (by omega)

/-- A prescribed regular linear chart of the constructed final section is
finite-dimensional. In particular this applies to `x₀ = 1` when saturation
has already made `x₀` regular. Nilpotent multiplicities are retained. -/
theorem cut_sequence_chart_finite
    (I : ℕ → Ideal (MvPolynomial Z K))
    (hI : ∀ j k f, f ∈ I j → homogeneousComponent k f ∈ I j)
    (g : ℕ → MvPolynomial Z K) (d : ℕ → ℕ) (r : ℕ)
    (hg : ∀ j < r, (g j).IsHomogeneous (d j))
    (hreg : ∀ j < r, IsRegular (Ideal.Quotient.mk (I j) (g j)))
    (hle : ∀ j < r, enlargedIdeal (I j) (g j) ≤ I (j+1))
    (P₀ : Polynomial ℚ) (N₀ : ℕ)
    (hP₀ : ∀ k : ℕ, N₀ ≤ k → P₀.eval (k : ℚ) =
      (Module.finrank K (coordinatePiece Z K (I 0) k) : ℚ))
    (hdeg : P₀.natDegree ≤ r)
    (l : MvPolynomial Z K) (hl : l.IsHomogeneous 1)
    (hlreg : IsRegular (Ideal.Quotient.mk (I r) l)) :
    Module.Finite K (OrdinaryProjectiveHilbert.ChartAlgebra (I r) l) := by
  obtain ⟨D,M,hM⟩ := eventually_constant_of_cut_sequence I hI g d r hg hreg hle
    P₀ N₀ hP₀ hdeg
  exact OrdinaryProjectiveHilbert.chartAlgebra_finite (I r) l (hI r) hl D ⟨M,hM⟩
    (regular_filterRegular (I r) l hl hlreg)

/-- Version starting from a larger homogeneous coordinate quotient, such
as the literal determinant hypersurface before derivative saturation. -/
theorem cut_sequence_chart_finite_of_initial_enlargement
    (J : Ideal (MvPolynomial Z K))
    (hJ : ∀ k f, f ∈ J → homogeneousComponent k f ∈ J)
    (I : ℕ → Ideal (MvPolynomial Z K)) (hJI : J ≤ I 0)
    (hI : ∀ j k f, f ∈ I j → homogeneousComponent k f ∈ I j)
    (g : ℕ → MvPolynomial Z K) (d : ℕ → ℕ) (r : ℕ)
    (hg : ∀ j < r, (g j).IsHomogeneous (d j))
    (hreg : ∀ j < r, IsRegular (Ideal.Quotient.mk (I j) (g j)))
    (hle : ∀ j < r, enlargedIdeal (I j) (g j) ≤ I (j+1))
    (P : Polynomial ℚ) (N : ℕ)
    (hP : ∀ k : ℕ, N ≤ k → P.eval (k : ℚ) =
      (Module.finrank K (coordinatePiece Z K J k) : ℚ))
    (hdeg : P.natDegree ≤ r)
    (l : MvPolynomial Z K) (hl : l.IsHomogeneous 1)
    (hlreg : IsRegular (Ideal.Quotient.mk (I r) l)) :
    Module.Finite K (OrdinaryProjectiveHilbert.ChartAlgebra (I r) l) := by
  obtain ⟨Q,M,hQ⟩ := HilbertPolynomialExistence.exists_coordinate_hilbert_polynomial
    (I 0) (hI 0)
  have hdegree := quotient_hilbert_natDegree_le J (I 0) hJI hJ (hI 0) P Q N M hP hQ
  exact cut_sequence_chart_finite I hI g d r hg hreg hle Q M hQ
    (hdegree.trans hdeg) l hl hlreg

end Sheshadri.SaturatedSectionHilbert
