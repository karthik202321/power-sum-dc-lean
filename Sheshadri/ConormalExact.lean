/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628

Legacy interface: its module discussion predates the completed endpoints in
ConormalBorderMultiplicity; see README.md for the current verification scope.
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalIncidence
import Sheshadri.ConormalCone
import Sheshadri.BezoutWithExcess
import Sheshadri.Numerical
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The original exact route, with its unproved general geometry made explicit

`GaussDegreeTheory` is an interface, NOT a constructed intersection theory.
Its degree function is currently abstract: this file does not identify it
with the multidegree of an actual conormal scheme. Its two fields explicitly
request generic transverse section realization and the classical degree
formula for smooth homogeneous hypersurfaces. No instance or existence
theorem for this interface is supplied.

Conditional on that general geometry, using the proved excess-compatible Bezout theorem,
the actual determinant incidence proves the coefficient bounds and the
quadratic constants. The Fermat polynomial's homogeneity, nonvanishing, and
smoothness away from the cone vertex are proved. No explicit Fermat polar
slice is imported, constructed, or counted.
-/

noncomputable section
namespace Sheshadri.ConormalExact

open MvPolynomial Incidence PolynomialModel MultiProjective ConormalIncidence
open scoped BigOperators

variable {n m : ℕ}

/-- Actual equations and actual transverse roots realizing a proposed
Gauss degree. The dual flags include their unrestricted zero-th coefficients. -/
structure GenericGaussSection (f : MvPolynomial (Fin n) ℂ) (r : ℕ) where
  flags : Fin (n - 2) → Fin (n + 1) → ℂ
  primal : Fin (n + 1) → ℂ
  roots : TransverseGaussRootFamily f flags primal (Fin r)

/-- Missing general geometric infrastructure, stated as visible data.
This is not a definition of conormal multidegree and no inhabitant is claimed.
The section and degree laws concern arbitrary polynomials, rather than an
assumed target-specific lower bound or determinant count inequality. -/
structure GaussDegreeTheory (n : ℕ) where
  degree : MvPolynomial (Fin n) ℂ → ℕ
  generic_sections : ∀ f, Nonempty (GenericGaussSection f (degree f))
  smooth_homogeneous_degree : ∀ (d : ℕ) (f : MvPolynomial (Fin n) ℂ),
    3 ≤ n → 2 ≤ d → f.IsHomogeneous d → f ≠ 0 →
    (∀ x : Fin n → ℂ, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) →
    degree f = d * (d - 1) ^ (n - 2)

theorem fermat_isHomogeneous (n : ℕ) :
    (PolynomialModel.fermat n : MvPolynomial (Fin n) ℂ).IsHomogeneous n := by
  classical
  apply IsHomogeneous.sum
  intro i _
  exact isHomogeneous_X_pow i n

theorem fermat_ne_zero (n : ℕ) (hn : 0 < n) :
    (PolynomialModel.fermat n : MvPolynomial (Fin n) ℂ) ≠ 0 := by
  intro h
  have he := congrArg (eval (fun _ : Fin n => (1 : ℂ))) h
  simp only [PolynomialModel.fermat, map_sum, eval_pow, eval_X, one_pow,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    map_zero] at he
  exact (Nat.cast_ne_zero.mpr hn.ne') he

theorem fermat_smooth_away_from_vertex (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℂ) (hx : x ≠ 0) :
    ∃ i, eval x (pderiv i (PolynomialModel.fermat n)) ≠ 0 := by
  exact ConormalCone.powerSum_smooth_away_from_vertex n n hn x hx

/-- The general smooth-hypersurface degree law specializes to Fermat using
proved hypotheses, not a separate Fermat-degree assumption. -/
theorem fermat_degree (geometry : GaussDegreeTheory n) (hn : 3 ≤ n) :
    geometry.degree (PolynomialModel.fermat n) = fermatCount n := by
  apply geometry.smooth_homogeneous_degree n (PolynomialModel.fermat n) hn
    (by omega) (fermat_isHomogeneous n) (fermat_ne_zero n (by omega))
  intro x hx _
  exact fermat_smooth_away_from_vertex n (by omega) x hx

/-- For an arbitrary literal affine determinant, the general section law
and the proved kernel incidence bound its abstract Gauss degree. -/
theorem ordinary_degree_bound
    (geometry : GaussDegreeTheory n) (hn : 2 ≤ n) (hm : 0 < m)
    (A : PencilCoefficients n m ℂ) (f : MvPolynomial (Fin n) ℂ)
    (hrep : determinant A = f) : geometry.degree f ≤ ordinaryBezout m n := by
  obtain ⟨sectionData⟩ := geometry.generic_sections f
  have h := ConormalIncidence.ordinary_bound BezoutWithExcess.universal_simple_bezout hn hm A f hrep
    sectionData.flags sectionData.primal sectionData.roots
  simpa only [Fintype.card_fin] using h

theorem symmetric_degree_bound
    (geometry : GaussDegreeTheory n) (hn : 2 ≤ n) (hm : 0 < m)
    (A : PencilCoefficients n m ℂ) (hA : ∀ i, (A i).transpose = A i)
    (f : MvPolynomial (Fin n) ℂ) (hrep : determinant A = f) :
    geometry.degree f ≤ symmetricBezout m n := by
  obtain ⟨sectionData⟩ := geometry.generic_sections f
  have h := ConormalIncidence.symmetric_bound BezoutWithExcess.universal_bi_simple_bezout hn hm A hA f hrep
    sectionData.flags sectionData.primal sectionData.roots
  simpa only [Fintype.card_fin] using h

/-- The cone vertex is used only to exclude a size-zero determinant.
It is not used as a smooth point or as a polar-count point. -/
theorem fermat_representation_size_pos (A : PencilCoefficients n m ℂ)
    (hn : 0 < n) (hrep : determinant A = PolynomialModel.fermat n) : 0 < m := by
  apply matrix_size_pos_of_root A (fun _ => 0)
  rw [hrep]
  simp [PolynomialModel.fermat, hn.ne']

/-- Conditional ordinary exact coefficient bound through general conormal
section realization and the smooth-homogeneous degree formula. -/
theorem ordinary_exact_count
    (geometry : GaussDegreeTheory n) (hn : 3 ≤ n)
    (hrep : ExactRepresentation n m ℂ) : fermatCount n ≤ ordinaryBezout m n := by
  obtain ⟨A, hA⟩ := hrep
  rw [← fermat_degree geometry hn]
  exact ordinary_degree_bound geometry (by omega)
    (fermat_representation_size_pos A (by omega) hA) A _ hA

/-- The proved three-factor Bezout theorem supplies the symmetric
two-factor bound via the proved arity reduction. -/
theorem symmetric_exact_count
    (geometry : GaussDegreeTheory n) (hn : 3 ≤ n)
    (hrep : SymmetricExactRepresentation n m ℂ) :
    fermatCount n ≤ symmetricBezout m n := by
  obtain ⟨A, hsym, hA⟩ := hrep
  rw [← fermat_degree geometry hn]
  exact symmetric_degree_bound geometry (by omega) (fermat_representation_size_pos A (by omega) hA) A hsym _ hA

theorem ordinary_exact_quadratic
    (geometry : GaussDegreeTheory n) (hn : 3 ≤ n)
    (hrep : ExactRepresentation n m ℂ) :
    ((n : ℝ) - 1) ^ 2 / (4 * Real.exp 1) ≤ (m : ℝ) :=
  ordinary_quadratic_bound n m hn (ordinary_exact_count geometry hn hrep)

theorem symmetric_exact_quadratic
    (geometry : GaussDegreeTheory n) (hn : 3 ≤ n)
    (hrep : SymmetricExactRepresentation n m ℂ) :
    ((n : ℝ) - 1) ^ 2 / (2 * Real.exp 1) ≤ (m : ℝ) :=
  symmetric_quadratic_bound n m hn (symmetric_exact_count geometry hn hrep)

end Sheshadri.ConormalExact
