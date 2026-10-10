/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SmoothGaussDegree
import Sheshadri.FiniteHomogeneousSection

/-! # Actual Gauss-polar section and an avoiding primal hyperplane

Both the dual polar coefficients and the primal linear coefficients are
constructed. The literal polar ideal has the expected eventual Hilbert
dimension, and the chosen chart covers its entire projective support.
-/

noncomputable section
namespace Sheshadri.SmoothGaussSection
open MvPolynomial SmoothGaussPolars SmoothGaussDegree GenericHomogeneousSections
open HomogeneousQuotientExact FlatGradedHilbert

variable {σ K : Type*} [Fintype σ] [Field K]

/-- The actual linear polynomial with the given primal coefficients. -/
def linearPolynomial (a : σ → K) : MvPolynomial σ K := ∑ i, C (a i) * X i

theorem linearPolynomial_homogeneous (a : σ → K) :
    (linearPolynomial a).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro i hi
  simpa using (isHomogeneous_C σ (a i)).mul (isHomogeneous_X K i)

@[simp] theorem eval_linearPolynomial (a x : σ → K) :
    eval x (linearPolynomial a) = ∑ i, a i * x i := by
  simp [linearPolynomial]

/-- Generic selection with its literal coefficients retained, so it can
be used as a primal projective hyperplane in the conormal incidence. -/
theorem exists_filterRegular_linearPolynomial [Infinite K]
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ d p, p ∈ I → homogeneousComponent d p ∈ I) :
    ∃ a : σ → K,
      FilterRegular I (linearPolynomial a) (linearPolynomial_homogeneous a) := by
  classical
  let fs := (Finset.univ.toList : List σ).map (fun i => (X i : MvPolynomial σ K))
  have hfs : {p | p ∈ fs} = Set.range (X : σ → MvPolynomial σ K) := by
    ext p
    simp only [fs, Set.mem_setOf_eq, List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and, Set.mem_range]
  have hh : ∀ p ∈ fs, p.IsHomogeneous 1 := by
    intro p hp
    obtain ⟨i, rfl⟩ := (show p ∈ Set.range (X : σ → MvPolynomial σ K) from hfs ▸ hp)
    exact isHomogeneous_X K i
  have hr : ∀ i : σ, X i ∈ (Ideal.ofList fs).radical := by
    intro i
    apply Ideal.le_radical
    apply Ideal.subset_span
    change X i ∈ {p | p ∈ fs}
    rw [hfs]
    exact ⟨i, rfl⟩
  obtain ⟨g, hspan, hg, hreg⟩ := exists_regular_homogeneous_of_radical
    (IrrelevantSaturation.saturation I) (IrrelevantSaturation.saturation_isSaturated I)
    fs 1 hh hr
  rw [hfs] at hspan
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hspan
  have he : linearPolynomial a = g := by
    simpa only [linearPolynomial, Algebra.smul_def, algebraMap_eq] using ha
  rw [← he] at hreg
  exact ⟨a, SaturationHilbertTail.filterRegular_of_regular_saturation I hI
    (linearPolynomial a) (linearPolynomial_homogeneous a) hreg⟩

/-- The sequential construction has exactly the stated finite generators. -/
theorem polarIdeal_le_iff (f : MvPolynomial σ K) (ell : ℕ → σ → K)
    (r : ℕ) (J : Ideal (MvPolynomial σ K)) :
    polarIdeal f ell r ≤ J ↔ f ∈ J ∧ ∀ j < r, polar f (ell j) ∈ J := by
  induction r with
  | zero => simp [polarIdeal, idealSequence, Ideal.span_le, Set.singleton_subset_iff]
  | succ r ih =>
    change enlargedIdeal (polarIdeal f ell r) (polar f (ell r)) ≤ J ↔ _
    rw [enlargedIdeal, sup_le_iff, Ideal.span_le, Set.singleton_subset_iff, ih]
    constructor
    · rintro ⟨⟨hf, hp⟩, hr⟩
      refine ⟨hf, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
      · exact hp j h
      · exact hr
    · rintro ⟨hf, hp⟩
      exact ⟨⟨hf, fun j hj => hp j (by omega)⟩, hp r (by omega)⟩

theorem polarIdeal_eq_finite_span (f : MvPolynomial σ K) (ell : ℕ → σ → K) (r : ℕ) :
    polarIdeal f ell r = Ideal.span {f} ⊔
      Ideal.span (Set.range (fun j : Fin r => polar f (ell j))) := by
  apply le_antisymm
  · apply (polarIdeal_le_iff f ell r _).mpr
    refine ⟨(show Ideal.span {f} ≤ Ideal.span {f} ⊔
      Ideal.span (Set.range (fun j : Fin r => polar f (ell j))) from le_sup_left)
        (Ideal.subset_span (Set.mem_singleton f)), ?_⟩
    intro j hj
    exact (show Ideal.span (Set.range (fun j : Fin r => polar f (ell j))) ≤
      Ideal.span {f} ⊔ Ideal.span (Set.range (fun j : Fin r => polar f (ell j)))
      from le_sup_right) (Ideal.subset_span ⟨⟨j, hj⟩, rfl⟩)
  · apply sup_le
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
        ((polarIdeal_le_iff f ell r _).mp le_rfl).1)
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact ((polarIdeal_le_iff f ell r _).mp le_rfl).2 j j.isLt

variable [CharZero K] [IsAlgClosed K]

/-- Complete actual flag selection for the smooth Gauss-polar degree:
the ideal, coefficients, Hilbert constant, and whole-support chart avoidance
are all conclusions from smoothness of the original homogeneous form. -/
theorem exists_polar_section_and_chart (r : ℕ) (hcard : Fintype.card σ = r+2)
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    (hfn : f ≠ 0) (hd : 0 < d)
    (hsmooth : ∀ x : σ → K, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) :
    ∃ ell : ℕ → σ → K, ∃ a : σ → K,
      (∃ N : ℕ, ∀ k > N,
        Module.finrank K (coordinatePiece σ K (polarIdeal f ell r) k) = d*(d-1)^r) ∧
      FilterRegular (polarIdeal f ell r) (linearPolynomial a)
        (linearPolynomial_homogeneous a) ∧
      ∀ i : σ, X i ∈ (enlargedIdeal (polarIdeal f ell r) (linearPolynomial a)).radical := by
  obtain ⟨ell, hconst⟩ := exists_polar_hilbert_constant r hcard hf hfn hd hsmooth
  have hI := polarIdeal_homogeneous hf ell r
  obtain ⟨a, hreg⟩ := exists_filterRegular_linearPolynomial (polarIdeal f ell r) hI
  exact ⟨ell, a, hconst, hreg,
    FiniteHomogeneousSection.coordinate_mem_radical_of_eventually_zero _
      (FiniteHomogeneousSection.eventually_zero_after_filterRegular_hyperplane
        _ hI (d*(d-1)^r) hconst _ (linearPolynomial_homogeneous a) hreg)⟩

end Sheshadri.SmoothGaussSection
