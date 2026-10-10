/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalGaussSection
import Sheshadri.IncidenceAffineEquations
import Sheshadri.KernelIncidenceLocalMultiplicity

/-! # The exact ideal of the constructed Gauss flags

Jacobi's identity identifies the determinant polar equations with the
trace-adjugate cuts in the normalized kernel quotient. The equality is
scheme theoretic and retains every local multiplicity.
-/

noncomputable section
namespace Sheshadri.ConormalPolarIdeal
open MvPolynomial Matrix PolynomialModel Incidence ConormalGaussSection
open IncidenceAffineEquations SmoothGaussPolars SmoothGaussDegree SmoothGaussSection
open SmoothGaussSectionLength KernelIncidenceLocalMultiplicity

variable {n m : ℕ}

theorem trace_flagMatrix_polar (A : PencilCoefficients n (m+1) ℂ)
    (ell : ℕ → Fin n → ℂ) (t : Fin (n-2)) :
    Matrix.trace ((affinePencil A).adjugate * flagMatrix A (polarFlags ell t)) =
      polar (determinant A) (ell t) := by
  have hH : flagMatrix A (polarFlags ell t) =
      ∑ i : Fin n, (C (ell t i) : MvPolynomial (Fin n) ℂ) • (A i.succ).map C := by
    ext a b
    simp [flagMatrix, Fin.sum_univ_succ, Matrix.sum_apply, polarFlags,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [hH, Matrix.mul_sum, Matrix.trace_sum]
  unfold polar
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  rw [determinant, pderiv_det]
  have hp : (affinePencil A).map (pderiv i) = (A i.succ).map C := by
    apply Matrix.ext
    intro a b
    exact pderiv_affinePencil A i a b
  rw [hp]

@[simp] theorem primalPolynomial_primalFlag (a : Fin n → ℂ) :
    primalPolynomial (primalFlag a) = linearPolynomial a - 1 := by
  simp only [primalPolynomial, primalFlag, Fin.cons_zero, Fin.cons_succ,
    map_neg, map_one, linearPolynomial]
  ring

/-- A useful exact conversion from indexed principal ideals to a finite
span; it does not pass through zero loci. -/
theorem iSup_span_singleton_eq_span_range {R E : Type*} [CommRing R] (g : E → R) :
    (⨆ e, Ideal.span {g e}) = Ideal.span (Set.range g) := by
  apply le_antisymm
  · apply iSup_le
    intro e
    apply Ideal.span_le.mpr
    exact Set.singleton_subset_iff.mpr (Ideal.subset_span ⟨e, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨e, rfl⟩
    exact (le_iSup (fun e => Ideal.span {g e}) e)
      (Ideal.subset_span (Set.mem_singleton _))

/-- The coefficient-local determinant polar ideal is exactly the literal
finite Gauss-polar chart ideal used in the constructed degree theorem. -/
theorem polarIntersectionIdeal_eq_polarChartIdeal
    (A : PencilCoefficients n (m+1) ℂ) (ell : ℕ → Fin n → ℂ) (a : Fin n → ℂ) :
    polarIntersectionIdeal (affinePencil A)
      (fun t : Fin (n-2) => flagMatrix A (polarFlags ell t))
      (Ideal.span {primalPolynomial (primalFlag a)}) =
        polarChartIdeal (determinant A) ell (n-2) a := by
  simp only [polarIntersectionIdeal, polarFlagIdeal, trace_flagMatrix_polar,
    primalPolynomial_primalFlag, iSup_span_singleton_eq_span_range]
  change Ideal.span {determinant A} ⊔
      (Ideal.span {linearPolynomial a - 1} ⊔
        Ideal.span (Set.range (fun t : Fin (n-2) => polar (determinant A) (ell t)))) =
    polarIdeal (determinant A) ell (n-2) ⊔ Ideal.span {linearPolynomial a - 1}
  rw [polarIdeal_eq_finite_span]
  ac_rfl

end Sheshadri.ConormalPolarIdeal
