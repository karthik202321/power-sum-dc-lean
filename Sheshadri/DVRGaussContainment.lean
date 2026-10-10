/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.GeneralConormalFlatFamily
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Sheshadri.SmoothGaussPolars
import Sheshadri.ConormalZariski

/-!
# Algebraic smooth-Gauss containment over a DVR

The actual relative hypersurface is torsion-free when its special equation
is nonzero. Its derivative-open scaled Gauss graph therefore embeds in its
generic base localization. Contracted generic graph equations vanish at the
special smooth Gauss points, without analytic accumulation hypotheses.
-/

noncomputable section
namespace Sheshadri.DVRGaussContainment
open MvPolynomial
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 150000

section Hypersurface
variable {R k Z : Type*} [CommRing R] [IsDomain R] [Field k]
    (ε : R →+* k) (π : R) (hπ : π ≠ 0)
    (hker : RingHom.ker ε = Ideal.span {π})
    (F : MvPolynomial Z R) (hF : MvPolynomial.map ε F ≠ 0)

include hker in
theorem residue_zero_iff_dvd (r : R) : ε r = 0 ↔ π ∣ r := by
  change r ∈ RingHom.ker ε ↔ _
  rw [hker, Ideal.mem_span_singleton]

include ε hπ hker hF in
/-- The uniformizer cancels in the actual principal equation ideal. -/
theorem parameter_saturation (g : MvPolynomial Z R)
    (hg : C π * g ∈ Ideal.span {F}) : g ∈ Ideal.span {F} := by
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hg
  have hπzero : ε π = 0 := (residue_zero_iff_dvd ε π hker π).mpr dvd_rfl
  have hmap : MvPolynomial.map ε q = 0 := by
    have h := congrArg (MvPolynomial.map ε) hq
    simp only [map_mul, map_C, hπzero, C_0, zero_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hF
  obtain ⟨q', hq'⟩ := (C_dvd_iff_map_hom_eq_zero ε π
    (residue_zero_iff_dvd ε π hker) q).mpr hmap
  apply Ideal.mem_span_singleton.mpr
  refine ⟨q', ?_⟩
  apply mul_left_cancel₀ (C_ne_zero.mpr hπ)
  calc
    C π*g = F * (C π*q') := by rw [← hq']; exact hq
    _ = C π * (F*q') := by ring

include ε hπ hker hF in
theorem parameter_power_saturation (n : ℕ) (g : MvPolynomial Z R)
    (hg : C π ^ n * g ∈ Ideal.span {F}) : g ∈ Ideal.span {F} := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    apply ih
    apply parameter_saturation ε π hπ hker F hF
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hg

variable [IsDiscreteValuationRing R]

include ε hπ hker hF in
/-- Every nonzero scalar cancels, by the DVR factorization into a unit
and a power of the uniformizer. -/
theorem scalar_saturation (hπirr : Irreducible π) (r : R) (hr : r ≠ 0)
    (g : MvPolynomial Z R) (hg : r • g ∈ Ideal.span {F}) : g ∈ Ideal.span {F} := by
  obtain ⟨n,u,rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hπirr
  apply parameter_power_saturation ε π hπ hker F hF n
  have h := (Ideal.span {F}).mul_mem_left (C (↑(u⁻¹) : R)) hg
  simpa only [Algebra.smul_def, algebraMap_eq, map_mul, map_pow,
    ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] using h

include ε hπ hker hF in
/-- Torsion-freeness is proved for the literal hypersurface quotient,
including when the hypersurface has several or nonreduced components. -/
theorem hypersurface_torsionfree (hπirr : Irreducible π) :
    NoZeroSMulDivisors R (MvPolynomial Z R ⧸ Ideal.span {F}) :=
  SaturatedFlatFamily.quotient_torsionfree_of_saturated _
    (scalar_saturation ε π hπ hker F hF hπirr)

end Hypersurface

section Graph
variable {R k Z : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field k] [Fintype Z]

abbrev SourceVariables (Z : Type*) := Option (Option Z)
abbrev GraphVariables (Z : Type*) := Option Z ⊕ Option Z

def spatialVariable (i : Z) : SourceVariables Z := some (some i)

def sourceEquation (F : MvPolynomial Z R) : MvPolynomial (SourceVariables Z) R :=
  rename spatialVariable F

def sourceGradient (F : MvPolynomial Z R) (j : Z) : MvPolynomial (SourceVariables Z) R :=
  rename spatialVariable (pderiv j F)

def sourceDenominator (F : MvPolynomial Z R) (j : Z) :
    MvPolynomial (SourceVariables Z) R := X none * X (some none) * sourceGradient F j

abbrev SourceRing (F : MvPolynomial Z R) :=
  MvPolynomial (SourceVariables Z) R ⧸ Ideal.span {sourceEquation F}

abbrev GraphChart (F : MvPolynomial Z R) (j : Z) :=
  Localization.Away (Ideal.Quotient.mk (Ideal.span {sourceEquation F}) (sourceDenominator F j))

/-- Literal graph coordinates with independent primal and dual scalings. -/
def graphCoordinates (F : MvPolynomial Z R) :
    GraphVariables Z → MvPolynomial (SourceVariables Z) R :=
  Sum.elim
    (fun i => X none * i.elim 1 (fun j => X (spatialVariable j)))
    (fun i => X (some none) * i.elim
      (-∑ j, X (spatialVariable j) * sourceGradient F j) (sourceGradient F))

def sourceChartMap (F : MvPolynomial Z R) (j : Z) :
    MvPolynomial (SourceVariables Z) R →ₐ[R] GraphChart F j :=
  (IsScalarTower.toAlgHom R (SourceRing F) (GraphChart F j)).comp
    (Ideal.Quotient.mkₐ R (Ideal.span {sourceEquation F}))

def graphChartMap (F : MvPolynomial Z R) (j : Z) :
    MvPolynomial (GraphVariables Z) R →ₐ[R] GraphChart F j :=
  (sourceChartMap F j).comp (aeval (graphCoordinates F))

/-- The actual generic base open: every nonzero element of the DVR is
inverted, in the literal derivative-open graph coordinate algebra. -/
abbrev GenericChart (F : MvPolynomial Z R) (j : Z) :=
  Localization (Algebra.algebraMapSubmonoid (GraphChart F j) (nonZeroDivisors R))

def genericGraphMap (F : MvPolynomial Z R) (j : Z) :
    MvPolynomial (GraphVariables Z) R →+* GenericChart F j :=
  (algebraMap (GraphChart F j) (GenericChart F j)).comp (graphChartMap F j).toRingHom

/-- Contraction of the reduced generic smooth graph, taking all derivative
charts. The affine ambient coordinates include both scaling directions. -/
def horizontalGaussIdeal (F : MvPolynomial Z R) : Ideal (MvPolynomial (GraphVariables Z) R) :=
  ⨅ j : Z, (RingHom.ker (genericGraphMap F j)).radical

section GenericField
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The generic graph chart has its canonical fraction-field coefficients. -/
def genericCoefficientMap (F : MvPolynomial Z R) (j : Z) : K →+* GenericChart F j :=
  IsLocalization.lift (M := nonZeroDivisors R) (S := K)
    (g := algebraMap R (GenericChart F j)) (by
      intro r
      have h := IsLocalization.map_units (GenericChart F j)
        (⟨algebraMap R (GraphChart F j) r,
          ⟨r, r.property, rfl⟩⟩ :
          Algebra.algebraMapSubmonoid (GraphChart F j) (nonZeroDivisors R))
      simpa only [IsScalarTower.algebraMap_apply] using h)

@[simp] theorem genericCoefficientMap_base (F : MvPolynomial Z R) (j : Z) (r : R) :
    genericCoefficientMap K F j (algebraMap R K r) = algebraMap R (GenericChart F j) r :=
  IsLocalization.lift_eq _ _

/-- Literal generic graph map defined on polynomials over the fraction field. -/
def genericFieldGraphMap (F : MvPolynomial Z R) (j : Z) :
    MvPolynomial (GraphVariables Z) K →+* GenericChart F j :=
  eval₂Hom (genericCoefficientMap K F j) (fun v => genericGraphMap F j (X v))

theorem genericFieldGraphMap_comp (F : MvPolynomial Z R) (j : Z) :
    (genericFieldGraphMap K F j).comp (MvPolynomial.map (algebraMap R K)) =
      genericGraphMap F j := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, map_C, genericFieldGraphMap, eval₂Hom_C,
      genericCoefficientMap_base, genericGraphMap]
    change algebraMap R (GenericChart F j) r =
      algebraMap (GraphChart F j) (GenericChart F j) (graphChartMap F j (C r))
    rw [show graphChartMap F j (C r) = algebraMap R (GraphChart F j) r from
      (graphChartMap F j).commutes r, ← IsScalarTower.algebraMap_apply]
  · intro v
    simp only [RingHom.comp_apply, map_X, genericFieldGraphMap, MvPolynomial.eval₂Hom_X']

/-- The actual reduced generic scaled Gauss-image ideal over the fraction
field is the intersection of the radicals of the derivative-chart kernels. -/
def genericGaussIdeal (F : MvPolynomial Z R) : Ideal (MvPolynomial (GraphVariables Z) K) :=
  ⨅ j : Z, (RingHom.ker (genericFieldGraphMap K F j)).radical

theorem genericGaussIdeal_isRadical (F : MvPolynomial Z R) :
    (genericGaussIdeal K F).IsRadical :=
  Ideal.isRadical_iInf _ (fun j => Ideal.radical_isRadical _)

/-- The generic ideal has exactly the closure of the genuine scheme
images of the smooth derivative charts as support. -/
theorem genericGauss_zeroLocus_eq_closure (F : MvPolynomial Z R) :
    PrimeSpectrum.zeroLocus (genericGaussIdeal K F) =
      closure (⋃ j : Z, Set.range (PrimeSpectrum.comap (genericFieldGraphMap K F j))) := by
  simp only [genericGaussIdeal, ← PrimeSpectrum.vanishingIdeal_range_comap]
  rw [← PrimeSpectrum.vanishingIdeal_iUnion, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]

/-- The previously constructed horizontal ideal is literally contraction
from the fraction-field generic Gauss-image ideal. -/
theorem horizontalGaussIdeal_eq_comap (F : MvPolynomial Z R) :
    horizontalGaussIdeal F =
      (genericGaussIdeal K F).comap (MvPolynomial.map (algebraMap R K)) := by
  simp only [genericGaussIdeal, horizontalGaussIdeal, Ideal.comap_iInf, Ideal.comap_radical]
  apply iInf_congr
  intro j
  congr 1
  change RingHom.ker (genericGraphMap F j) =
    RingHom.ker ((genericFieldGraphMap K F j).comp (MvPolynomial.map (algebraMap R K)))
  rw [genericFieldGraphMap_comp]

/-- Agreement with the existing canonical flat horizontal construction. -/
theorem horizontalGaussIdeal_eq_horizontalIdeal (F : MvPolynomial Z R) :
    horizontalGaussIdeal F = SaturatedFlatFamily.horizontalIdeal R K (genericGaussIdeal K F) := by
  rw [SaturatedFlatFamily.horizontalIdeal_eq_comap,
    (genericGaussIdeal_isRadical K F).radical]
  exact horizontalGaussIdeal_eq_comap K F

/-- The horizontal support is literally the closure of the constructed
generic Gauss support under the coefficient specialization map. -/
theorem horizontalGauss_zeroLocus_eq_closure (F : MvPolynomial Z R) :
    PrimeSpectrum.zeroLocus (horizontalGaussIdeal F) =
      closure (PrimeSpectrum.comap (MvPolynomial.map (σ := GraphVariables Z) (algebraMap R K)) ''
        PrimeSpectrum.zeroLocus (genericGaussIdeal K F : Set (MvPolynomial (GraphVariables Z) K))) := by
  rw [horizontalGaussIdeal_eq_horizontalIdeal K F]
  exact SaturatedFlatFamily.horizontal_zeroLocus_eq_closure R K _

include K in
/-- Flatness of the actual horizontal Gauss coordinate ring. -/
theorem horizontalGaussRing_flat (F : MvPolynomial Z R) :
    Module.Flat R (MvPolynomial (GraphVariables Z) R ⧸ horizontalGaussIdeal F) := by
  rw [horizontalGaussIdeal_eq_horizontalIdeal K F]
  exact SaturatedFlatFamily.horizontalRing_flat R K _

end GenericField

theorem sourceEquation_special_ne_zero (ε : R →+* k) (F : MvPolynomial Z R)
    (hF : MvPolynomial.map ε F ≠ 0) :
    MvPolynomial.map ε (sourceEquation F) ≠ 0 := by
  rw [sourceEquation, map_rename]
  exact fun h => hF ((rename_injective _ (fun _ _ h => Option.some.inj (Option.some.inj h)))
    (by simpa using h))

theorem graphChart_torsionfree (ε : R →+* k) (π : R) (hπirr : Irreducible π)
    (hker : RingHom.ker ε = Ideal.span {π}) (F : MvPolynomial Z R)
    (hF : MvPolynomial.map ε F ≠ 0) : NoZeroSMulDivisors R (GraphChart F j) := by
  letI : NoZeroSMulDivisors R (SourceRing F) :=
    hypersurface_torsionfree ε π hπirr.ne_zero hker (sourceEquation F)
      (sourceEquation_special_ne_zero ε F hF) hπirr
  exact GeneralConormalFlatFamily.localization_torsionfree
    (R := R) (Q := SourceRing F) (L := GraphChart F j)
    (Submonoid.powers (Ideal.Quotient.mk (Ideal.span {sourceEquation F}) (sourceDenominator F j)))

theorem genericChart_injective (ε : R →+* k) (π : R) (hπirr : Irreducible π)
    (hker : RingHom.ker ε = Ideal.span {π}) (F : MvPolynomial Z R)
    (hF : MvPolynomial.map ε F ≠ 0) (j : Z) :
    Function.Injective (algebraMap (GraphChart F j) (GenericChart F j)) := by
  letI := graphChart_torsionfree ε π hπirr hker F hF (j := j)
  apply IsLocalization.injective (M := Algebra.algebraMapSubmonoid (GraphChart F j)
    (nonZeroDivisors R)) (GenericChart F j)
  rintro y ⟨r,hr,rfl⟩
  rw [mem_nonZeroDivisors_iff]
  intro x hx
  have h : r • x = 0 := by simpa only [Algebra.smul_def, mul_comm] using hx
  exact (smul_eq_zero.mp h).resolve_left (nonZeroDivisors.ne_zero hr)

def sourcePoint (z : Z → k) (μ ν : k) : SourceVariables Z → k :=
  fun i => i.elim μ (fun i => i.elim ν z)

/-- Actual independently scaled affine Gauss representatives over the
residue field, including the homogeneous zeroth dual coordinate. -/
def specialGaussPoint (ε : R →+* k) (F : MvPolynomial Z R) (z : Z → k) (μ ν : k) :
    GraphVariables Z → k :=
  Sum.elim (fun i => μ * i.elim 1 z)
    (fun i => ν * i.elim (-∑ j, z j * eval₂ ε z (pderiv j F))
      (fun j => eval₂ ε z (pderiv j F)))

theorem sourceEquation_eval (ε : R →+* k) (F : MvPolynomial Z R)
    (z : Z → k) (μ ν : k) :
    eval₂ ε (sourcePoint z μ ν) (sourceEquation F) = eval₂ ε z F := by
  simp only [sourceEquation, eval₂_rename, Function.comp_def, spatialVariable,
    sourcePoint, Option.elim_some]

theorem sourceGradient_eval (ε : R →+* k) (F : MvPolynomial Z R)
    (z : Z → k) (μ ν : k) (j : Z) :
    eval₂ ε (sourcePoint z μ ν) (sourceGradient F j) = eval₂ ε z (pderiv j F) := by
  exact sourceEquation_eval ε (pderiv j F) z μ ν

theorem sourceDenominator_eval (ε : R →+* k) (F : MvPolynomial Z R)
    (z : Z → k) (μ ν : k) (j : Z) :
    eval₂ ε (sourcePoint z μ ν) (sourceDenominator F j) =
      μ * ν * eval₂ ε z (pderiv j F) := by
  simp only [sourceDenominator, eval₂_mul, eval₂_X, sourceGradient_eval,
    sourcePoint, Option.elim_none, Option.elim_some]

theorem graphCoordinates_eval (ε : R →+* k) (F : MvPolynomial Z R)
    (z : Z → k) (μ ν : k) (v : GraphVariables Z) :
    eval₂ ε (sourcePoint z μ ν) (graphCoordinates F v) = specialGaussPoint ε F z μ ν v := by
  rcases v with (_ | j) | (_ | j) <;>
    simp [graphCoordinates, specialGaussPoint, sourcePoint, spatialVariable,
      sourceGradient_eval, eval₂_sum]

def sourceEvaluation (ε : R →+* k) (F : MvPolynomial Z R)
    (z : Z → k) (μ ν : k) (hz : eval₂ ε z F = 0) : SourceRing F →+* k :=
  Ideal.Quotient.lift (Ideal.span {sourceEquation F}) (eval₂Hom ε (sourcePoint z μ ν))
    (by
      change Ideal.span {sourceEquation F} ≤ RingHom.ker (eval₂Hom ε (sourcePoint z μ ν))
      apply Ideal.span_le.mpr
      intro f hf
      rcases Set.mem_singleton_iff.mp hf with rfl
      change eval₂ ε (sourcePoint z μ ν) (sourceEquation F) = 0
      rw [sourceEquation_eval, hz])

def chartEvaluation (ε : R →+* k) (F : MvPolynomial Z R)
    (z : Z → k) (μ ν : k) (hz : eval₂ ε z F = 0) (j : Z)
    (hμ : μ ≠ 0) (hν : ν ≠ 0) (hj : eval₂ ε z (pderiv j F) ≠ 0) :
    GraphChart F j →+* k :=
  IsLocalization.Away.lift (Ideal.Quotient.mk (Ideal.span {sourceEquation F})
    (sourceDenominator F j)) (g := sourceEvaluation ε F z μ ν hz)
    (by
      apply isUnit_iff_ne_zero.mpr
      change eval₂ ε (sourcePoint z μ ν) (sourceDenominator F j) ≠ 0
      rw [sourceDenominator_eval]
      exact mul_ne_zero (mul_ne_zero hμ hν) hj)

theorem chartEvaluation_sourceChartMap (ε : R →+* k) (F : MvPolynomial Z R)
    (z : Z → k) (μ ν : k) (hz : eval₂ ε z F = 0) (j : Z)
    (hμ : μ ≠ 0) (hν : ν ≠ 0) (hj : eval₂ ε z (pderiv j F) ≠ 0)
    (f : MvPolynomial (SourceVariables Z) R) :
    chartEvaluation ε F z μ ν hz j hμ hν hj (sourceChartMap F j f) =
      eval₂ ε (sourcePoint z μ ν) f := by
  apply IsLocalization.Away.lift_eq

theorem chartEvaluation_graphChartMap (ε : R →+* k) (F : MvPolynomial Z R)
    (z : Z → k) (μ ν : k) (hz : eval₂ ε z F = 0) (j : Z)
    (hμ : μ ≠ 0) (hν : ν ≠ 0) (hj : eval₂ ε z (pderiv j F) ≠ 0)
    (q : MvPolynomial (GraphVariables Z) R) :
    chartEvaluation ε F z μ ν hz j hμ hν hj (graphChartMap F j q) =
      eval₂ ε (specialGaussPoint ε F z μ ν) q := by
  have h : (chartEvaluation ε F z μ ν hz j hμ hν hj).comp (graphChartMap F j) =
      eval₂Hom ε (specialGaussPoint ε F z μ ν) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, eval₂Hom_C]
      change chartEvaluation ε F z μ ν hz j hμ hν hj
        (sourceChartMap F j (aeval (graphCoordinates F) (C r))) = ε r
      rw [aeval_C]
      change chartEvaluation ε F z μ ν hz j hμ hν hj (sourceChartMap F j (C r)) = ε r
      rw [chartEvaluation_sourceChartMap, eval₂_C]
    · intro v
      change chartEvaluation ε F z μ ν hz j hμ hν hj
        (sourceChartMap F j (aeval (graphCoordinates F) (X v))) = _
      rw [aeval_X, chartEvaluation_sourceChartMap]
      rw [MvPolynomial.eval₂Hom_X']
      exact graphCoordinates_eval ε F z μ ν v
  exact congrArg (fun φ : MvPolynomial (GraphVariables Z) R →+* k => φ q) h

/-- Algebraic specialization of the actual generic scaled Gauss closure.
Every contracted generic equation vanishes at every special smooth scaled
Gauss representative. No curve parametrization or analytic density premise
is required, and the generic source is the genuine DVR generic base open. -/
theorem specialGaussPoint_annihilates_horizontal
    (ε : R →+* k) (π : R) (hπirr : Irreducible π)
    (hker : RingHom.ker ε = Ideal.span {π}) (F : MvPolynomial Z R)
    (hF : MvPolynomial.map ε F ≠ 0)
    (z : Z → k) (hz : eval₂ ε z F = 0) (j : Z)
    (hj : eval₂ ε z (pderiv j F) ≠ 0) (μ ν : k) (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (q : MvPolynomial (GraphVariables Z) R) (hq : q ∈ horizontalGaussIdeal F) :
    eval₂ ε (specialGaussPoint ε F z μ ν) q = 0 := by
  have hqj : q ∈ (RingHom.ker (genericGraphMap F j)).radical :=
    (show horizontalGaussIdeal F ≤ (RingHom.ker (genericGraphMap F j)).radical
      from iInf_le _ j) hq
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hqj
  have hzero : graphChartMap F j (q^n) = 0 := by
    apply genericChart_injective ε π hπirr hker F hF j
    exact hn.trans (map_zero _).symm
  have h := congrArg (chartEvaluation ε F z μ ν hz j hμ hν hj) hzero
  rw [chartEvaluation_graphChartMap, eval₂_pow, map_zero] at h
  exact pow_eq_zero h

/-- The literal scheme-theoretic special-fibre ideal, with no radical
inserted after specialization. -/
def specialFibreIdeal (ε : R →+* k) (F : MvPolynomial Z R) :
    Ideal (MvPolynomial (GraphVariables Z) k) :=
  (horizontalGaussIdeal F).map (MvPolynomial.map ε)

theorem specialGaussPoint_mem_specialFibre
    (ε : R →+* k) (π : R) (hπirr : Irreducible π)
    (hker : RingHom.ker ε = Ideal.span {π}) (F : MvPolynomial Z R)
    (hF : MvPolynomial.map ε F ≠ 0)
    (z : Z → k) (hz : eval₂ ε z F = 0) (j : Z)
    (hj : eval₂ ε z (pderiv j F) ≠ 0) (μ ν : k) (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    specialGaussPoint ε F z μ ν ∈ MvPolynomial.zeroLocus (specialFibreIdeal ε F) := by
  have hle : specialFibreIdeal ε F ≤ RingHom.ker (eval (specialGaussPoint ε F z μ ν)) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro q hq
    change eval (specialGaussPoint ε F z μ ν) (MvPolynomial.map ε q) = 0
    rw [eval_map]
    exact specialGaussPoint_annihilates_horizontal ε π hπirr hker F hF z hz j hj μ ν hμ hν q hq
  exact fun q hq => hle hq

end Graph

section OriginalConormal
open ConormalPersistence ConormalZariski
variable {R A Z : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Fintype A] [Fintype Z]

theorem specialGaussPoint_eq_original (ε : R →+* ℂ) (F : MvPolynomial Z R)
    (G : MvPolynomial (A ⊕ Z) ℂ) (a : A → ℂ)
    (hsp : specialize a G = MvPolynomial.map ε F) (z : Z → ℂ) (μ ν : ℂ) :
    specialGaussPoint ε F z μ ν = gaussPoint G a z μ ν := by
  have hg (j : Z) : eval₂ ε z (pderiv j F) = gradient G a z j := by
    rw [← eval_map, ← pderiv_map, ← hsp, ← specialize_pderiv, eval_specialize]
    rfl
  funext v
  rcases v with (_ | j) | (_ | j) <;>
    simp [specialGaussPoint, gaussPoint, gaussCovector, hg]

/-- Containment of the exact conormal closure used by the original proof
in the scheme-theoretic special fibre of the constructed DVR horizontal
Gauss family. The curve may be nonrational; no analytic closure hypothesis
or family certificate is an input. -/
theorem original_conormalClosure_subset_specialFibre
    (ε : R →+* ℂ) (π : R) (hπirr : Irreducible π)
    (hker : RingHom.ker ε = Ideal.span {π}) (F : MvPolynomial Z R)
    (hF : MvPolynomial.map ε F ≠ 0)
    (G : MvPolynomial (A ⊕ Z) ℂ) (a : A → ℂ)
    (hsp : specialize a G = MvPolynomial.map ε F) :
    conormalClosure G a ⊆ MvPolynomial.zeroLocus (specialFibreIdeal ε F) := by
  intro p hp q hq
  apply hp q
  intro y hy
  obtain ⟨z,μ,ν,hz,⟨j,hj⟩,hμ,hν,rfl⟩ := hy
  have hz' : eval₂ ε z F = 0 := by
    rw [← eval_map, ← hsp, eval_specialize]
    exact hz
  have hj' : eval₂ ε z (pderiv j F) ≠ 0 := by
    rw [← eval_map, ← pderiv_map, ← hsp, ← specialize_pderiv, eval_specialize]
    exact hj
  have h := specialGaussPoint_mem_specialFibre ε π hπirr hker F hF z hz' j hj' μ ν hμ hν q hq
  rwa [specialGaussPoint_eq_original ε F G a hsp z μ ν] at h

end OriginalConormal
end Sheshadri.DVRGaussContainment
