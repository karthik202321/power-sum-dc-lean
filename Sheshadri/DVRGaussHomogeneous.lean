/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.DVRGaussContainment
import Sheshadri.HomogeneousVanishing
import Sheshadri.SaturatedFlatHilbert
import Sheshadri.RadicalKernelFieldPoints

/-! # Bihomogeneity of the actual DVR Gauss closure

Independent scaling of the two graph representatives preserves the actual
smooth derivative charts. Testing in residue fraction fields then proves
bihomogeneity of the radical generic graph ideal and its horizontal contraction.
-/
noncomputable section
namespace Sheshadri.DVRGaussHomogeneous
open MvPolynomial DVRGaussContainment
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 150000

variable {R Z E : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Fintype Z] [Field E]

/-- Any field-valued smooth graph point extends to the generic chart when
its coefficient map is injective. -/
def genericChartEvaluation (ε : R →+* E) (hε : Function.Injective ε)
    (F : MvPolynomial Z R) (z : Z → E) (μ ν : E)
    (hz : eval₂ ε z F = 0) (j : Z) (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hj : eval₂ ε z (pderiv j F) ≠ 0) : GenericChart F j →+* E :=
  IsLocalization.lift (M := Algebra.algebraMapSubmonoid (GraphChart F j)
    (nonZeroDivisors R)) (S := GenericChart F j)
    (g := chartEvaluation ε F z μ ν hz j hμ hν hj) (by
      rintro ⟨x, r, hr, rfl⟩
      apply isUnit_iff_ne_zero.mpr
      have heq : chartEvaluation ε F z μ ν hz j hμ hν hj
          (algebraMap R (GraphChart F j) r) = ε r := by
        simpa only [map_C, eval₂_C] using
          chartEvaluation_sourceChartMap ε F z μ ν hz j hμ hν hj (C r)
      rw [heq]
      exact fun h => nonZeroDivisors.ne_zero hr (hε (h.trans (map_zero ε).symm)))

@[simp] theorem genericChartEvaluation_base (ε : R →+* E) (hε : Function.Injective ε)
    (F : MvPolynomial Z R) (z : Z → E) (μ ν : E)
    (hz : eval₂ ε z F = 0) (j : Z) (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hj : eval₂ ε z (pderiv j F) ≠ 0) (x : GraphChart F j) :
    genericChartEvaluation ε hε F z μ ν hz j hμ hν hj
      (algebraMap (GraphChart F j) (GenericChart F j) x) =
      chartEvaluation ε F z μ ν hz j hμ hν hj x :=
  IsLocalization.lift_eq _ _

section FractionField
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The extension respects the specified fraction-field coefficient map. -/
theorem genericChartEvaluation_coeff (τ : K →+* E)
    (F : MvPolynomial Z R) (z : Z → E) (μ ν : E)
    (hz : eval₂ (τ.comp (algebraMap R K)) z F = 0) (j : Z)
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hj : eval₂ (τ.comp (algebraMap R K)) z (pderiv j F) ≠ 0) (c : K) :
    genericChartEvaluation (τ.comp (algebraMap R K))
      (τ.injective.comp (IsFractionRing.injective R K)) F z μ ν hz j hμ hν hj
      (genericCoefficientMap K F j c) = τ c := by
  let ψ := genericChartEvaluation (τ.comp (algebraMap R K))
    (τ.injective.comp (IsFractionRing.injective R K)) F z μ ν hz j hμ hν hj
  have heq : ψ.comp (genericCoefficientMap K F j) = τ := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    ext r
    simp only [RingHom.comp_apply, genericCoefficientMap_base,
      IsScalarTower.algebraMap_apply R (GraphChart F j) (GenericChart F j),
      ψ, genericChartEvaluation_base]
    simpa only [map_C, eval₂_C] using
      chartEvaluation_sourceChartMap (τ.comp (algebraMap R K)) F z μ ν hz j hμ hν hj (C r)
  exact congrArg (fun f : K →+* E => f c) heq

/-- Evaluating the genuine generic chart recovers the literal scaled
Gauss coordinates over every extension field. -/
theorem genericChartEvaluation_graph (τ : K →+* E)
    (F : MvPolynomial Z R) (z : Z → E) (μ ν : E)
    (hz : eval₂ (τ.comp (algebraMap R K)) z F = 0) (j : Z)
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hj : eval₂ (τ.comp (algebraMap R K)) z (pderiv j F) ≠ 0)
    (q : MvPolynomial (GraphVariables Z) K) :
    genericChartEvaluation (τ.comp (algebraMap R K))
      (τ.injective.comp (IsFractionRing.injective R K)) F z μ ν hz j hμ hν hj
      (genericFieldGraphMap K F j q) =
      eval₂ τ (specialGaussPoint (τ.comp (algebraMap R K)) F z μ ν) q := by
  let ψ := genericChartEvaluation (τ.comp (algebraMap R K))
    (τ.injective.comp (IsFractionRing.injective R K)) F z μ ν hz j hμ hν hj
  have heq : ψ.comp (genericFieldGraphMap K F j) =
      eval₂Hom τ (specialGaussPoint (τ.comp (algebraMap R K)) F z μ ν) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simpa only [RingHom.comp_apply, genericFieldGraphMap, eval₂Hom_C, ψ] using
        genericChartEvaluation_coeff K τ F z μ ν hz j hμ hν hj c
    · intro v
      simp only [RingHom.comp_apply, genericFieldGraphMap, eval₂Hom_X',
        genericGraphMap, ψ, genericChartEvaluation_base]
      change chartEvaluation (τ.comp (algebraMap R K)) F z μ ν hz j hμ hν hj
        (graphChartMap F j (X v)) = _
      rw [chartEvaluation_graphChartMap]
      exact eval₂_X _ _ _
  exact congrArg (fun f : MvPolynomial (GraphVariables Z) K →+* E => f q) heq


/-- Every field-valued point of a generic derivative chart is a literal
smooth scaled Gauss point. This is a statement about the chart algebra,
not a density or genericity hypothesis. -/
theorem genericChart_fieldPoint (F : MvPolynomial Z R) (j : Z)
    (χ : GenericChart F j →+* E) :
    ∃ (z : Z → E) (μ ν : E),
      eval₂ ((χ.comp (genericCoefficientMap K F j)).comp (algebraMap R K)) z F = 0 ∧
      μ ≠ 0 ∧ ν ≠ 0 ∧
      eval₂ ((χ.comp (genericCoefficientMap K F j)).comp (algebraMap R K)) z
        (pderiv j F) ≠ 0 ∧
      ∀ q : MvPolynomial (GraphVariables Z) K,
        χ (genericFieldGraphMap K F j q) =
          eval₂ (χ.comp (genericCoefficientMap K F j))
            (specialGaussPoint ((χ.comp (genericCoefficientMap K F j)).comp
              (algebraMap R K)) F z μ ν) q := by
  let τ := χ.comp (genericCoefficientMap K F j)
  let ε := τ.comp (algebraMap R K)
  let η : GraphChart F j →+* E :=
    χ.comp (algebraMap (GraphChart F j) (GenericChart F j))
  let φ : MvPolynomial (SourceVariables Z) R →+* E :=
    η.comp (sourceChartMap F j).toRingHom
  let z : Z → E := fun i => φ (X (spatialVariable i))
  let μ : E := φ (X none)
  let ν : E := φ (X (some none))
  have hφ : φ = eval₂Hom ε (sourcePoint z μ ν) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [φ, η, ε, τ, RingHom.comp_apply, eval₂Hom_C,
        genericCoefficientMap_base]
      rw [show (sourceChartMap F j).toRingHom (C r) =
        algebraMap R (GraphChart F j) r from (sourceChartMap F j).commutes r,
        ← IsScalarTower.algebraMap_apply]
    · intro v
      rcases v with _ | (_ | i) <;>
        simp only [eval₂Hom_X', sourcePoint, Option.elim_none, Option.elim_some,
          z, μ, ν, spatialVariable]
  have hz : eval₂ ε z F = 0 := by
    rw [← sourceEquation_eval ε F z μ ν]
    change (eval₂Hom ε (sourcePoint z μ ν)) (sourceEquation F) = 0
    rw [← hφ]
    change η (sourceChartMap F j (sourceEquation F)) = 0
    have heq : sourceChartMap F j (sourceEquation F) = 0 := by
      change algebraMap (SourceRing F) (GraphChart F j)
        (Ideal.Quotient.mk _ (sourceEquation F)) = 0
      rw [(Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton _)),
        map_zero]
    rw [heq, map_zero]
  have hden : μ * ν * eval₂ ε z (pderiv j F) ≠ 0 := by
    rw [← sourceDenominator_eval ε F z μ ν]
    change (eval₂Hom ε (sourcePoint z μ ν)) (sourceDenominator F j) ≠ 0
    rw [← hφ]
    exact (IsLocalization.Away.algebraMap_isUnit
      (S := GraphChart F j) (Ideal.Quotient.mk (Ideal.span {sourceEquation F})
        (sourceDenominator F j))).map η |>.ne_zero
  obtain ⟨hmn,hj⟩ := mul_ne_zero_iff.mp hden
  obtain ⟨hμ,hν⟩ := mul_ne_zero_iff.mp hmn
  refine ⟨z,μ,ν,hz,hμ,hν,hj,?_⟩
  intro q
  have heq : χ.comp (genericFieldGraphMap K F j) =
      eval₂Hom τ (specialGaussPoint ε F z μ ν) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, genericFieldGraphMap, eval₂Hom_C, τ]
    · intro v
      simp only [RingHom.comp_apply, genericFieldGraphMap, eval₂Hom_X', genericGraphMap]
      change η (sourceChartMap F j (aeval (graphCoordinates F) (X v))) = _
      rw [aeval_X]
      change φ (graphCoordinates F v) = _
      rw [hφ]
      exact graphCoordinates_eval ε F z μ ν v
  exact congrArg (fun f : MvPolynomial (GraphVariables Z) K →+* E => f q) heq


/-- Equations of the actual generic Gauss closure vanish on every smooth
scaled Gauss point over every fraction-field extension. -/
theorem genericGaussIdeal_eval_zero (τ : K →+* E)
    (F : MvPolynomial Z R) (z : Z → E) (μ ν : E)
    (hz : eval₂ (τ.comp (algebraMap R K)) z F = 0) (j : Z)
    (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (hj : eval₂ (τ.comp (algebraMap R K)) z (pderiv j F) ≠ 0)
    (q : MvPolynomial (GraphVariables Z) K) (hq : q ∈ genericGaussIdeal K F) :
    eval₂ τ (specialGaussPoint (τ.comp (algebraMap R K)) F z μ ν) q = 0 := by
  have hqj : q ∈ (RingHom.ker (genericFieldGraphMap K F j)).radical :=
    (show genericGaussIdeal K F ≤ (RingHom.ker (genericFieldGraphMap K F j)).radical
      from iInf_le _ j) hq
  obtain ⟨n,hn⟩ := Ideal.mem_radical_iff.mp hqj
  change genericFieldGraphMap K F j (q^n) = 0 at hn
  have h := congrArg (genericChartEvaluation (τ.comp (algebraMap R K))
    (τ.injective.comp (IsFractionRing.injective R K)) F z μ ν hz j hμ hν hj) hn
  rw [genericChartEvaluation_graph, eval₂_pow, map_zero] at h
  exact pow_eq_zero h

/-- Bihomogeneity is proved from independent scaling of the actual
field-valued graph charts, with radical kernels detected at all primes. -/
theorem genericGaussIdeal_bihomogeneous [Infinite K] (F : MvPolynomial Z R) :
    FlatGradedHilbert.IsBihomogeneous (GraphVariables Z) K
      HilbertPolynomialExistence.sumBlock (genericGaussIdeal K F) := by
  classical
  intro a b q hq
  apply Ideal.mem_iInf.mpr
  intro j
  apply (RadicalKernelFieldPoints.mem_radical_ker_iff_fieldPoints
    (genericFieldGraphMap K F j) _).mpr
  intro P
  let E := FractionRing (GenericChart F j ⧸ P.asIdeal)
  let χ : GenericChart F j →+* E := RadicalKernelFieldPoints.fieldPoint P
  let τ : K →+* E := χ.comp (genericCoefficientMap K F j)
  letI : Infinite E := Infinite.of_injective τ τ.injective
  obtain ⟨z,μ,ν,hz,hμ,hν,hj,heval⟩ := genericChart_fieldPoint K F j χ
  rw [heval]
  apply HomogeneousVanishing.biweightedComponent_eval_zero
  intro s t hs ht
  have hscale : (fun i => s ^ (FlatGradedHilbert.twoBlockWeight
      (GraphVariables Z) HilbertPolynomialExistence.sumBlock i).1 *
      (t ^ (FlatGradedHilbert.twoBlockWeight (GraphVariables Z)
        HilbertPolynomialExistence.sumBlock i).2 *
        specialGaussPoint (τ.comp (algebraMap R K)) F z μ ν i)) =
      specialGaussPoint (τ.comp (algebraMap R K)) F z (s*μ) (t*ν) := by
    funext v
    rcases v with v | v <;>
      simp [FlatGradedHilbert.twoBlockWeight, HilbertPolynomialExistence.sumBlock,
        specialGaussPoint, mul_assoc]
  rw [hscale]
  exact genericGaussIdeal_eval_zero K τ F z (s*μ) (t*ν) hz j
    (mul_ne_zero hs hμ) (mul_ne_zero ht hν) hj q hq

/-- The actual horizontal DVR Gauss ideal is bihomogeneous; this is a
consequence of the constructed generic charts, not a family assumption. -/
theorem horizontalGaussIdeal_bihomogeneous [Infinite K] (F : MvPolynomial Z R) :
    FlatGradedHilbert.IsBihomogeneous (GraphVariables Z) R
      HilbertPolynomialExistence.sumBlock (horizontalGaussIdeal F) := by
  rw [horizontalGaussIdeal_eq_horizontalIdeal K F]
  exact SaturatedFlatHilbert.horizontalIdeal_bihomogeneous
    HilbertPolynomialExistence.sumBlock (genericGaussIdeal K F)
    (genericGaussIdeal_isRadical K F) (genericGaussIdeal_bihomogeneous K F)


include K in
/-- Every literal field fibre, including the nonreduced special fibre,
retains the proved two-block grading. -/
theorem specialFibreIdeal_bihomogeneous [Infinite K] (ε : R →+* E)
    (F : MvPolynomial Z R) :
    FlatGradedHilbert.IsBihomogeneous (GraphVariables Z) E
      HilbertPolynomialExistence.sumBlock (specialFibreIdeal ε F) :=
  GeneralHomogeneousBaseChange.bihomogeneous_map ε _ _
    (horizontalGaussIdeal_bihomogeneous K F)

/-- The actual special-fibre equations and the actual generic Gauss closure
have equal vector-space dimensions in every bidegree. Nilpotents in the
special fibre are preserved. -/
theorem specialFibre_bicoordinate_dimensions [Infinite K] (ε : R →+* E)
    (F : MvPolynomial Z R) (a b : ℕ) :
    Module.finrank E (FlatGradedHilbert.bicoordinatePiece (GraphVariables Z) E
      HilbertPolynomialExistence.sumBlock (specialFibreIdeal ε F) a b) =
    Module.finrank K (FlatGradedHilbert.bicoordinatePiece (GraphVariables Z) K
      HilbertPolynomialExistence.sumBlock (genericGaussIdeal K F) a b) := by
  letI : Algebra R E := ε.toAlgebra
  rw [specialFibreIdeal, horizontalGaussIdeal_eq_horizontalIdeal K F]
  exact SaturatedFlatHilbert.horizontal_fibre_dimensions_eq_generic
    (genericGaussIdeal K F) (genericGaussIdeal_isRadical K F)
    (genericGaussIdeal_bihomogeneous K F) E a b

/-- A common eventual bivariate Hilbert polynomial exists for the actual
generic Gauss ideal and literal special fibre; it is not supplied as data. -/
theorem exists_common_gaussHilbertPolynomial [Infinite K] (ε : R →+* E)
    (F : MvPolynomial Z R) :
    ∃ H : Polynomial (Polynomial ℚ), ∃ N : ℕ, ∀ a b : ℕ, N ≤ a → N ≤ b →
      BiMonomialHilbert.biEval H a b =
        (Module.finrank K (FlatGradedHilbert.bicoordinatePiece (GraphVariables Z) K
          HilbertPolynomialExistence.sumBlock (genericGaussIdeal K F) a b) : ℚ) ∧
      BiMonomialHilbert.biEval H a b =
        (Module.finrank E (FlatGradedHilbert.bicoordinatePiece (GraphVariables Z) E
          HilbertPolynomialExistence.sumBlock (specialFibreIdeal ε F) a b) : ℚ) := by
  obtain ⟨H,N,hH⟩ := HilbertPolynomialExistence.exists_bicoordinate_hilbert_polynomial
    (genericGaussIdeal K F) (genericGaussIdeal_bihomogeneous K F)
  refine ⟨H,N,?_⟩
  intro a b ha hb
  exact ⟨hH a b ha hb, by rw [specialFibre_bicoordinate_dimensions K ε F]; exact hH a b ha hb⟩

end FractionField
end Sheshadri.DVRGaussHomogeneous
