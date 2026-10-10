/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SmoothGaussSection
import Sheshadri.OrdinaryProjectiveHilbert

/-!
# Constructed smooth Gauss section with its full local scheme length

The actual derivative-polar coefficients and the actual primal chart are
constructed from the original form. Their literal affine quotient is finite,
and the sum over all its local module lengths is the Gauss-polar degree.
-/

noncomputable section
namespace Sheshadri.SmoothGaussSectionLength
open MvPolynomial SmoothGaussPolars SmoothGaussDegree SmoothGaussSection
open OrdinaryProjectiveHilbert HomogeneousQuotientExact

variable {σ K : Type*} [Fintype σ] [Field K] [CharZero K] [IsAlgClosed K]

abbrev polarChartIdeal (f : MvPolynomial σ K) (ell : ℕ → σ → K)
    (r : ℕ) (a : σ → K) := chartIdeal (polarIdeal f ell r) (linearPolynomial a)

abbrev PolarChartAlgebra (f : MvPolynomial σ K) (ell : ℕ → σ → K)
    (r : ℕ) (a : σ → K) := ChartAlgebra (polarIdeal f ell r) (linearPolynomial a)

/-- A full section-length realization, with no numerical or geometric
realization certificate among its inputs. -/
theorem exists_polar_section_length (r : ℕ) (hcard : Fintype.card σ = r+2)
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    (hfn : f ≠ 0) (hd : 0 < d)
    (hsmooth : ∀ x : σ → K, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) :
    ∃ ell : ℕ → σ → K, ∃ a : σ → K,
      Module.Finite K (PolarChartAlgebra f ell r a) ∧
      Module.finrank K (PolarChartAlgebra f ell r a) = d*(d-1)^r ∧
      (∑ᶠ p : MaximalSpectrum (PolarChartAlgebra f ell r a),
        Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) =
          (d*(d-1)^r : ℕ) ∧
      ∀ i : σ, X i ∈ (enlargedIdeal (polarIdeal f ell r) (linearPolynomial a)).radical := by
  obtain ⟨ell, a, hconst, hreg, havoid⟩ :=
    exists_polar_section_and_chart r hcard hf hfn hd hsmooth
  have hI := polarIdeal_homogeneous hf ell r
  exact ⟨ell, a,
    chartAlgebra_finite _ _ hI (linearPolynomial_homogeneous a) _ hconst hreg,
    chartAlgebra_finrank _ _ hI (linearPolynomial_homogeneous a) _ hconst hreg,
    chart_sum_local_lengths _ _ hI (linearPolynomial_homogeneous a) _ hconst hreg,
    havoid⟩

/-- Every actual chart point is nonzero because the constructed primal
linear form is equal to one there. -/
theorem chart_zero_ne_zero (f : MvPolynomial σ K) (ell : ℕ → σ → K)
    (r : ℕ) (a x : σ → K)
    (hx : ∀ q ∈ polarChartIdeal f ell r a, eval x q = 0) : x ≠ 0 := by
  have hlin : linearPolynomial a - 1 ∈ polarChartIdeal f ell r a :=
    (show Ideal.span {linearPolynomial a - 1} ≤ polarChartIdeal f ell r a
      from le_sup_right) (Ideal.subset_span (Set.mem_singleton _))
  have he := hx _ hlin
  intro hz
  simp [hz, linearPolynomial] at he

/-- All chart support is in the actual smooth Gauss domain, including
nonreduced local sections. -/
theorem chart_zero_smooth {f : MvPolynomial σ K} (ell : ℕ → σ → K)
    (r : ℕ) (a x : σ → K)
    (hsmooth : ∀ x : σ → K, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0)
    (hx : ∀ q ∈ polarChartIdeal f ell r a, eval x q = 0) :
    ∃ i, eval x (pderiv i f) ≠ 0 := by
  apply hsmooth x (chart_zero_ne_zero f ell r a x hx)
  exact hx f ((show polarIdeal f ell r ≤ polarChartIdeal f ell r a from le_sup_left)
    ((polarIdeal_le_iff f ell r _).mp le_rfl).1)

end Sheshadri.SmoothGaussSectionLength
