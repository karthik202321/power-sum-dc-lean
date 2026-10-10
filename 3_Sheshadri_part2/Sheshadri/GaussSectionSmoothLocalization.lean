/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FiniteQuotientPointFamily
import Sheshadri.CommonProjectiveChart
import Sheshadri.SmoothGaussSectionLength
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# A single smooth open containing an entire finite Gauss section

A finite actual equation quotient whose support lies in the smooth locus
admits one scalar combination of the derivatives that is a unit in that
quotient. Localizing at this combination preserves the entire section,
including all nilpotents. In any coefficient field, every point of the
localized family is smooth. No transversality or multiplicity premise is
used in the construction.
-/

noncomputable section
namespace Sheshadri.GaussSectionSmoothLocalization
open MvPolynomial IsolatedLocalMultiplicity SmoothGaussPolars

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 150000

section FiniteSection
variable {σ K : Type*} [Fintype σ] [Field K] [IsAlgClosed K] [Infinite K]
variable (I : Ideal (MvPolynomial σ K)) [Module.Finite K (EquationQuotient I)]

omit [Fintype σ] [Infinite K] in
/-- Avoiding every actual root is exactly the condition needed for a unit
in the full finite quotient, not just in its reduction. -/
theorem quotient_isUnit_of_nonvanishing (g : MvPolynomial σ K)
    (hg : ∀ p : σ → K, I ≤ pointIdeal p → eval p g ≠ 0) :
    IsUnit (Ideal.Quotient.mk I g) := by
  classical
  by_contra hu
  have hproper : Ideal.span {Ideal.Quotient.mk I g} ≠ ⊤ :=
    fun h => hu (Ideal.span_singleton_eq_top.mp h)
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hproper
  let q : MaximalSpectrum (EquationQuotient I) := ⟨P, hP⟩
  have hmem : Ideal.Quotient.mk I g ∈ P :=
    hle (Ideal.subset_span (Set.mem_singleton _))
  have hzero : FiniteQuotientPointFamily.residue I q (Ideal.Quotient.mk I g) = 0 := by
    change Ideal.Quotient.mk I g ∈ RingHom.ker (FiniteQuotientPointFamily.residue I q)
    rw [FiniteQuotientPointFamily.residue_kernel]
    exact hmem
  rw [FiniteQuotientPointFamily.residue_mk] at hzero
  exact hg (FiniteQuotientPointFamily.point I q)
    (FiniteQuotientPointFamily.point_vanishes I q) hzero

/-- One derivative combination is nonzero at every point of the full
finite section; it is therefore a unit on the original finite scheme. -/
theorem exists_unit_polar (f : MvPolynomial σ K)
    (hsmooth : ∀ p : σ → K, I ≤ pointIdeal p → ∃ i, eval p (pderiv i f) ≠ 0) :
    ∃ ell : σ → K,
      (∀ p : σ → K, I ≤ pointIdeal p → eval p (polar f ell) ≠ 0) ∧
      IsUnit (Ideal.Quotient.mk I (polar f ell)) := by
  classical
  letI : IsArtinianRing (EquationQuotient I) := IsArtinianRing.of_finite K _
  letI := Fintype.ofFinite (MaximalSpectrum (EquationQuotient I))
  obtain ⟨ell, hell⟩ := CommonProjectiveChart.exists_common_linear_form
    (fun P : MaximalSpectrum (EquationQuotient I) =>
      fun i => eval (FiniteQuotientPointFamily.point I P) (pderiv i f))
    (fun P => hsmooth _ (FiniteQuotientPointFamily.point_vanishes I P))
  have hnonzero : ∀ p : σ → K, I ≤ pointIdeal p → eval p (polar f ell) ≠ 0 := by
    intro p hp
    obtain ⟨P, rfl⟩ := FiniteQuotientPointFamily.point_complete I p hp
    simpa only [polar, map_sum, map_mul, eval_C] using hell P
  exact ⟨ell, hnonzero, quotient_isUnit_of_nonvanishing I _ hnonzero⟩

/-- This is an isomorphism of the actual nonreduced section algebra. -/
def localizationEquiv (g : MvPolynomial σ K)
    (hg : IsUnit (Ideal.Quotient.mk I g)) :
    EquationQuotient I ≃ₐ[K] Localization.Away (Ideal.Quotient.mk I g) :=
  (IsLocalization.atUnit (EquationQuotient I)
    (Localization.Away (Ideal.Quotient.mk I g)) _ hg).restrictScalars K

omit [Fintype σ] [IsAlgClosed K] [Infinite K] [Module.Finite K (EquationQuotient I)] in
theorem localization_finrank (g : MvPolynomial σ K)
    (hg : IsUnit (Ideal.Quotient.mk I g)) :
    Module.finrank K (Localization.Away (Ideal.Quotient.mk I g)) =
      Module.finrank K (EquationQuotient I) :=
  (localizationEquiv I g hg).toLinearEquiv.finrank_eq.symm

end FiniteSection

section SmoothChart
variable {σ K : Type*} [Fintype σ] [Field K] [IsAlgClosed K] [CharZero K]

/-- Application to the literal constructed polar-chart ideal. The smooth
open preserves the whole chart, not only the selected point list. -/
theorem exists_unit_polar_on_chart (f : MvPolynomial σ K)
    (ell : ℕ → σ → K) (r : ℕ) (a : σ → K)
    [Module.Finite K (SmoothGaussSectionLength.PolarChartAlgebra f ell r a)]
    (hsmooth : ∀ p : σ → K, p ≠ 0 → eval p f = 0 →
      ∃ i, eval p (pderiv i f) ≠ 0) :
    ∃ b : σ → K,
      IsUnit (Ideal.Quotient.mk (SmoothGaussSectionLength.polarChartIdeal f ell r a)
        (polar f b)) := by
  obtain ⟨b, _, hb⟩ := exists_unit_polar
    (SmoothGaussSectionLength.polarChartIdeal f ell r a) f (by
      intro p hp
      exact SmoothGaussSectionLength.chart_zero_smooth ell r a p hsmooth hp)
  exact ⟨b, hb⟩

end SmoothChart

section GenericSmoothness
variable {σ R L : Type*} [Fintype σ] [CommRing R] [Field L]

/-- A derivative combination can be evaluated after any coefficient
specialization. The source need not be a field or reduced. -/
def derivativeCombination (f : MvPolynomial σ R) (b : σ → R) : MvPolynomial σ R :=
  ∑ i, C (b i) * pderiv i f

theorem map_derivativeCombination (φ : R →+* L)
    (f : MvPolynomial σ R) (b : σ → R) :
    MvPolynomial.map φ (derivativeCombination f b) =
      derivativeCombination (MvPolynomial.map φ f) (fun i => φ (b i)) := by
  simp only [derivativeCombination, map_sum, map_mul, map_C, pderiv_map]

/-- Inverting the displayed derivative combination forces every field
valued point into the actual smooth Gauss domain. -/
theorem smooth_of_combination_ne_zero (f : MvPolynomial σ L) (b p : σ → L)
    (h : eval p (derivativeCombination f b) ≠ 0) :
    ∃ i, eval p (pderiv i f) ≠ 0 := by
  classical
  by_contra hh
  push_neg at hh
  apply h
  simp only [derivativeCombination, map_sum, map_mul, eval_C, hh,
    mul_zero, Finset.sum_const_zero]

/-- A literal inverse-coordinate equation suffices; no assertion about
the generic derivative rank is being assumed. -/
theorem smooth_of_inverse_equation (f : MvPolynomial σ L) (b p : σ → L)
    (z : L) (h : z * eval p (derivativeCombination f b) = 1) :
    ∃ i, eval p (pderiv i f) ≠ 0 :=
  smooth_of_combination_ne_zero f b p (by intro hz; rw [hz, mul_zero] at h; exact zero_ne_one h)

end GenericSmoothness

section ResidueLift
variable {σ R K : Type*} [Fintype σ] [CommRing R] [Field K] [IsAlgClosed K] [Infinite K]

/-- The avoiding derivative combination lifts to any surjective residue
map. Its reduction is a unit on the actual finite special section. -/
theorem exists_lifted_unit_combination (ε : R →+* K) (hε : Function.Surjective ε)
    (F : MvPolynomial σ R) (I : Ideal (MvPolynomial σ K))
    [Module.Finite K (EquationQuotient I)]
    (hsmooth : ∀ p : σ → K, I ≤ pointIdeal p →
      ∃ i, eval p (pderiv i (MvPolynomial.map ε F)) ≠ 0) :
    ∃ b : σ → R,
      IsUnit (Ideal.Quotient.mk I (MvPolynomial.map ε (derivativeCombination F b))) := by
  obtain ⟨b, _, hb⟩ := exists_unit_polar I (MvPolynomial.map ε F) hsmooth
  choose c hc using fun i => hε (b i)
  refine ⟨c, ?_⟩
  rw [map_derivativeCombination]
  simpa only [hc, derivativeCombination, polar] using hb

end ResidueLift

section LocalizedPoint
variable {σ K : Type*} [Fintype σ] [Field K]

/-- The spatial coordinates of an actual field-valued point of a
derivative-open equation quotient. -/
def localizedPoint (I : Ideal (MvPolynomial σ K)) (f : MvPolynomial σ K) (b : σ → K)
    (ψ : Localization.Away (Ideal.Quotient.mk I (derivativeCombination f b)) →ₐ[K] K) :
    σ → K := fun i => ψ (algebraMap _ _ (Ideal.Quotient.mk I (X i)))

theorem localizedPoint_evaluation (I : Ideal (MvPolynomial σ K))
    (f : MvPolynomial σ K) (b : σ → K)
    (ψ : Localization.Away (Ideal.Quotient.mk I (derivativeCombination f b)) →ₐ[K] K)
    (q : MvPolynomial σ K) :
    eval (localizedPoint I f b ψ) q = ψ (algebraMap _ _ (Ideal.Quotient.mk I q)) := by
  let χ : MvPolynomial σ K →ₐ[K] K := ψ.comp
    ((IsScalarTower.toAlgHom K (EquationQuotient I) _).comp (Ideal.Quotient.mkₐ K I))
  have he : aeval (localizedPoint I f b ψ) = χ := by
    ext i
    simp only [aeval_X]
    rfl
  exact DFunLike.congr_fun he q

/-- Every actual rational point of the localized generic equation scheme
has a nonzero gradient. Smoothness is derived from the inverted element. -/
theorem localizedPoint_smooth (I : Ideal (MvPolynomial σ K))
    (f : MvPolynomial σ K) (b : σ → K)
    (ψ : Localization.Away (Ideal.Quotient.mk I (derivativeCombination f b)) →ₐ[K] K) :
    ∃ i, eval (localizedPoint I f b ψ) (pderiv i f) ≠ 0 := by
  apply smooth_of_combination_ne_zero f b
  rw [localizedPoint_evaluation]
  exact (IsUnit.map ψ (IsLocalization.Away.algebraMap_isUnit
    (Ideal.Quotient.mk I (derivativeCombination f b)))).ne_zero

theorem localizedPoint_vanishes (I : Ideal (MvPolynomial σ K))
    (f : MvPolynomial σ K) (b : σ → K)
    (ψ : Localization.Away (Ideal.Quotient.mk I (derivativeCombination f b)) →ₐ[K] K) :
    I ≤ pointIdeal (localizedPoint I f b ψ) := by
  intro q hq
  change eval (localizedPoint I f b ψ) q = 0
  rw [localizedPoint_evaluation, Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero, map_zero]

end LocalizedPoint
end Sheshadri.GaussSectionSmoothLocalization
