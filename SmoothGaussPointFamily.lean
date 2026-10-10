/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SmoothGaussSectionLength
import Sheshadri.FiniteQuotientPointFamily

/-!
# A constructed finite smooth Gauss root family with its actual multiplicities

The polar coefficients, primal normalization, finite complete root list, and
local multiplicity sum are all conclusions from the original form's
homogeneity and smoothness. The local rings are the literal localized
equation quotients, not abstract intersection-number data.
-/

noncomputable section
namespace Sheshadri.SmoothGaussPointFamily
open MvPolynomial SmoothGaussPolars SmoothGaussDegree SmoothGaussSection
open SmoothGaussSectionLength IsolatedLocalMultiplicity

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000

variable {σ K : Type*} [Fintype σ] [Field K] [CharZero K] [IsAlgClosed K]

theorem chart_zero_hypersurface (f : MvPolynomial σ K) (ell : ℕ → σ → K)
    (r : ℕ) (a x : σ → K) (hx : polarChartIdeal f ell r a ≤ pointIdeal x) :
    eval x f = 0 :=
  hx ((show polarIdeal f ell r ≤ polarChartIdeal f ell r a from le_sup_left)
    ((polarIdeal_le_iff f ell r _).mp le_rfl).1)

theorem chart_zero_polar (f : MvPolynomial σ K) (ell : ℕ → σ → K)
    (r : ℕ) (a x : σ → K) (hx : polarChartIdeal f ell r a ≤ pointIdeal x)
    (j : ℕ) (hj : j < r) : eval x (polar f (ell j)) = 0 :=
  hx ((show polarIdeal f ell r ≤ polarChartIdeal f ell r a from le_sup_left)
    (((polarIdeal_le_iff f ell r _).mp le_rfl).2 j hj))

theorem chart_zero_primal (f : MvPolynomial σ K) (ell : ℕ → σ → K)
    (r : ℕ) (a x : σ → K) (hx : polarChartIdeal f ell r a ≤ pointIdeal x) :
    ∑ i, a i * x i = 1 := by
  have h : linearPolynomial a - 1 ∈ polarChartIdeal f ell r a :=
    (show Ideal.span {linearPolynomial a - 1} ≤ polarChartIdeal f ell r a
      from le_sup_right) (Ideal.subset_span (Set.mem_singleton _))
  have he : eval x (linearPolynomial a - 1) = 0 := hx h
  simpa only [map_sub, map_one, eval_linearPolynomial, sub_eq_zero] using he

/-- Actual finite smooth Gauss section roots with complete scheme lengths.
The exponent `r` is `number of homogeneous variables - 2`.
No chosen roots, genericity, finiteness, or numerical degree hypotheses occur. -/
theorem exists_smooth_gauss_root_family (r : ℕ) (hcard : Fintype.card σ = r + 2)
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    (hfn : f ≠ 0) (hd : 0 < d)
    (hsmooth : ∀ x : σ → K, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) :
    ∃ ell : ℕ → σ → K, ∃ a : σ → K, ∃ N : ℕ, ∃ points : Fin N → σ → K,
      ∃ hpoints : ∀ j, polarChartIdeal f ell r a ≤ pointIdeal (points j),
        Function.Injective points ∧
        (∀ x : σ → K, polarChartIdeal f ell r a ≤ pointIdeal x ↔
          ∃ j, points j = x) ∧
        (∀ j, points j ≠ 0) ∧
        (∀ j, eval (points j) f = 0) ∧
        (∀ j q, q < r → eval (points j) (polar f (ell q)) = 0) ∧
        (∀ j, ∑ i, a i * points j i = 1) ∧
        (∀ j, ∃ i, eval (points j) (pderiv i f) ≠ 0) ∧
        Module.Finite K (PolarChartAlgebra f ell r a) ∧
        (∀ j, IsArtinianRing (LocalIntersectionRing
          (polarChartIdeal f ell r a) (points j) (hpoints j))) ∧
        (∑ j, multiplicity (polarChartIdeal f ell r a) (points j) (hpoints j)) =
          (d * (d - 1) ^ r : ℕ) := by
  classical
  obtain ⟨ell, a, hfinite, hdim, _, _⟩ :=
    exists_polar_section_length r hcard hf hfn hd hsmooth
  let I := polarChartIdeal f ell r a
  let A := EquationQuotient I
  letI : Module.Finite K A := hfinite
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  letI := Fintype.ofFinite (MaximalSpectrum A)
  let N := Fintype.card (MaximalSpectrum A)
  let e : Fin N ≃ MaximalSpectrum A := (Fintype.equivFin (MaximalSpectrum A)).symm
  let points : Fin N → σ → K := fun j => FiniteQuotientPointFamily.point I (e j)
  have hp : ∀ j, I ≤ pointIdeal (points j) :=
    fun j => FiniteQuotientPointFamily.point_vanishes I (e j)
  refine ⟨ell, a, N, points, hp,
    (FiniteQuotientPointFamily.point_injective I).comp e.injective,
    ?_, ?_, ?_, ?_, ?_, ?_, hfinite, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨P, hP⟩ := FiniteQuotientPointFamily.point_complete I x hx
      exact ⟨e.symm P, by simpa [points] using hP⟩
    · rintro ⟨j, rfl⟩
      exact hp j
  · intro j
    exact chart_zero_ne_zero f ell r a (points j) (fun q hq => hp j hq)
  · intro j
    exact chart_zero_hypersurface f ell r a (points j) (hp j)
  · intro j q hq
    exact chart_zero_polar f ell r a (points j) (hp j) q hq
  · intro j
    exact chart_zero_primal f ell r a (points j) (hp j)
  · intro j
    exact chart_zero_smooth ell r a (points j) hsmooth (fun q hq => hp j hq)
  · intro j
    infer_instance
  · calc
      (∑ j, multiplicity I (points j) (hp j)) =
          ∑ P : MaximalSpectrum A,
            multiplicity I (FiniteQuotientPointFamily.point I P)
              (FiniteQuotientPointFamily.point_vanishes I P) := by
        exact e.sum_comp (fun P => multiplicity I (FiniteQuotientPointFamily.point I P)
          (FiniteQuotientPointFamily.point_vanishes I P))
      _ = (Module.finrank K A : ℕ∞) :=
        (FiniteQuotientPointFamily.finrank_eq_sum_point_multiplicity I).symm
      _ = (d * (d - 1) ^ r : ℕ) := congrArg Nat.cast hdim

end Sheshadri.SmoothGaussPointFamily
