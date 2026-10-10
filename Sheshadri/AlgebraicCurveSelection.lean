/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ZariskiBridge
import Sheshadri.ConormalTopology
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# The algebraic image needed before curve selection

For an actual polynomial map between finite complex affine spaces we construct
its image coordinate ring. Its defining ideal is proved to be exactly the
polynomials vanishing on the literal complex image. A point of the Zariski
closure therefore gives an actual complex point of this quotient ring.

The quotient is a finite-type domain and admits a finite injective Noether
normalization. The induced spectrum image is constructible by Chevalley.
These are genuine constructions without extra geometric hypotheses.

The subsequent `CurveThroughBoundary` module uses these constructions to
produce a dimension-one curve through any omitted image-closure point, with
only finitely many exceptional points outside the literal complex image.
Normalizing that curve, lifting matrix representations, and proving analytic
accumulation remain separate obligations.
-/

noncomputable section
namespace Sheshadri.AlgebraicCurveSelection

open MvPolynomial ZariskiBridge Topology

variable {X Y : Type*} (F : Y → MvPolynomial X ℂ)

/-- Pullback of polynomial functions along the literal polynomial map. -/
def pullback : MvPolynomial Y ℂ →ₐ[ℂ] MvPolynomial X ℂ := aeval F

theorem eval_pullback (x : X → ℂ) (q : MvPolynomial Y ℂ) :
    eval x (pullback F q) = eval (polynomialMap F x) q := by
  simpa only [pullback, polynomialMap, coe_aeval_eq_eval] using
    MvPolynomial.comp_aeval_apply F (aeval x) q

/-- The defining ideal of the algebraic image, computed by substitution. -/
def imageIdeal : Ideal (MvPolynomial Y ℂ) := RingHom.ker (pullback F)

theorem mem_imageIdeal_iff (q : MvPolynomial Y ℂ) :
    q ∈ imageIdeal F ↔ ∀ y ∈ Set.range (polynomialMap F), eval y q = 0 := by
  change pullback F q = 0 ↔ _
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := hy
    rw [← eval_pullback, h, map_zero]
  · intro h
    apply MvPolynomial.funext
    intro x
    rw [map_zero, eval_pullback]
    exact h _ ⟨x, rfl⟩

theorem mem_zariskiClosure_iff (y : Y → ℂ) :
    y ∈ zariskiClosure (Set.range (polynomialMap F)) ↔
      ∀ q ∈ imageIdeal F, eval y q = 0 := by
  constructor
  · intro hy q hq
    exact hy q ((mem_imageIdeal_iff F q).mp hq)
  · intro hy q hq
    exact hy q ((mem_imageIdeal_iff F q).mpr hq)

instance imageIdeal_isPrime : (imageIdeal F).IsPrime := RingHom.ker_isPrime _

/-- Actual coordinate ring of the irreducible algebraic image. -/
abbrev ImageRing := MvPolynomial Y ℂ ⧸ imageIdeal F

instance imageRing_isDomain : IsDomain (ImageRing F) := inferInstance

theorem spectrum_polynomialMap (x : X → ℂ) :
    PrimeSpectrum.comap (pullback F).toRingHom (MvPolynomial.pointToPoint x) =
      MvPolynomial.pointToPoint (polynomialMap F x) := by
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro q
  change pullback F q ∈ MvPolynomial.vanishingIdeal {x} ↔
    q ∈ MvPolynomial.vanishingIdeal {polynomialMap F x}
  rw [MvPolynomial.mem_vanishingIdeal_singleton_iff,
    MvPolynomial.mem_vanishingIdeal_singleton_iff, eval_pullback]

theorem pointToPoint_preimage_zeroLocus (I : Ideal (MvPolynomial Y ℂ)) :
    MvPolynomial.pointToPoint ⁻¹' PrimeSpectrum.zeroLocus (I : Set (MvPolynomial Y ℂ)) =
      MvPolynomial.zeroLocus I := by
  ext y
  change (∀ q ∈ I, q ∈ MvPolynomial.vanishingIdeal {y}) ↔ _
  simp only [MvPolynomial.mem_vanishingIdeal_singleton_iff,
    MvPolynomial.mem_zeroLocus_iff]

theorem zeroLocus_algebraic_isClosed (I : Ideal (MvPolynomial Y ℂ)) :
    @IsClosed (Y → ℂ) (ConormalTopology.algebraicTopology Y)
      (MvPolynomial.zeroLocus I) := by
  apply (ConormalTopology.isClosed_algebraicTopology_iff _).mpr
  apply Set.Subset.antisymm
  · intro y hy q hq
    exact hy q (fun x hx => hx q hq)
  · exact ConormalTopology.subset_zariskiClosure _

/-- The algebraic topology already used by the conormal development is
the topology induced by the genuine complex-point embedding into Spec. -/
theorem pointToPoint_isInducing :
    @Topology.IsInducing (Y → ℂ) (PrimeSpectrum (MvPolynomial Y ℂ))
      (ConormalTopology.algebraicTopology Y) inferInstance MvPolynomial.pointToPoint := by
  letI : TopologicalSpace (Y → ℂ) := ConormalTopology.algebraicTopology Y
  refine ⟨TopologicalSpace.ext_isClosed fun s => ?_⟩
  rw [isClosed_induced_iff, ConormalTopology.isClosed_algebraicTopology_iff]
  constructor
  · intro hs
    refine ⟨PrimeSpectrum.zeroLocus (MvPolynomial.vanishingIdeal s),
      PrimeSpectrum.isClosed_zeroLocus _, ?_⟩
    rw [pointToPoint_preimage_zeroLocus]
    exact hs
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨I, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal t).mp ht
    rw [pointToPoint_preimage_zeroLocus]
    exact (ConormalTopology.isClosed_algebraicTopology_iff _).mp
      (zeroLocus_algebraic_isClosed I)

/-- A closure point becomes a complex-valued point of the image ring. -/
def closurePoint (y : Y → ℂ)
    (hy : y ∈ zariskiClosure (Set.range (polynomialMap F))) :
    ImageRing F →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ (imageIdeal F) (aeval y) (by
    intro q hq
    exact (mem_zariskiClosure_iff F y).mp hy q hq)

@[simp] theorem closurePoint_coordinate (y : Y → ℂ)
    (hy : y ∈ zariskiClosure (Set.range (polynomialMap F))) (i : Y) :
    closurePoint F y hy (Ideal.Quotient.mk (imageIdeal F) (MvPolynomial.X i)) = y i := by
  simp [closurePoint]

section Finite
variable [Finite X] [Finite Y]

instance imageRing_finiteType : Algebra.FiniteType ℂ (ImageRing F) := by
  letI : Algebra.FiniteType ℂ (MvPolynomial Y ℂ) := Algebra.FiniteType.mvPolynomial ℂ Y
  infer_instance

omit [Finite X] in
/-- A finite injective normalization map is constructed for the actual
image ring. The integer `d` is not yet identified with Krull dimension. -/
theorem imageRing_noether_normalization :
    ∃ d, ∃ g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] ImageRing F,
      Function.Injective g ∧ g.Finite :=
  exists_finite_inj_algHom_of_fg ℂ (ImageRing F)

theorem pullback_finitePresentation : (pullback F).toRingHom.FinitePresentation := by
  apply RingHom.FinitePresentation.of_finiteType.mp
  apply RingHom.FiniteType.of_comp_finiteType
    (f := algebraMap ℂ (MvPolynomial Y ℂ))
  have hcomp : (pullback F).toRingHom.comp (algebraMap ℂ (MvPolynomial Y ℂ)) =
      algebraMap ℂ (MvPolynomial X ℂ) := by
    apply RingHom.ext
    intro z
    exact (pullback F).commutes z
  rw [hcomp]
  exact algebraMap_finiteType_iff_algebra_finiteType.mpr inferInstance

/-- Chevalley's theorem applies to the actual polynomial substitution map.
This is a statement about spectrum points, not an assumed complex-point
curve-selection or analytic-density theorem. -/
theorem polynomial_spectrum_image_constructible :
    IsConstructible (Set.range (PrimeSpectrum.comap (pullback F).toRingHom)) :=
  PrimeSpectrum.isConstructible_range_comap (pullback_finitePresentation F)

omit [Finite Y] in
/-- The literal complex image is exactly the closed-point part of the
constructible spectrum image. No equality of Euclidean and Zariski closures
is used in this theorem. -/
theorem mem_image_iff_pointToPoint_mem_spectrum_image (y : Y → ℂ) :
    y ∈ Set.range (polynomialMap F) ↔
      MvPolynomial.pointToPoint y ∈
        Set.range (PrimeSpectrum.comap (pullback F).toRingHom) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨MvPolynomial.pointToPoint x, spectrum_polynomialMap F x⟩
  · rintro ⟨P, hP⟩
    obtain ⟨M, hM, hPM⟩ := P.asIdeal.exists_le_maximal P.isPrime.ne_top
    obtain ⟨x, hMx⟩ :=
      (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton M).mp hM
    refine ⟨x, ?_⟩
    funext i
    have hq : MvPolynomial.X i - C (y i) ∈
        (PrimeSpectrum.comap (pullback F).toRingHom P).asIdeal := by
      rw [hP]
      change MvPolynomial.X i - C (y i) ∈ MvPolynomial.vanishingIdeal {y}
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    have hroot := hPM hq
    rw [hMx, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hroot
    change eval x (pullback F (MvPolynomial.X i - C (y i))) = 0 at hroot
    rw [eval_pullback] at hroot
    simpa only [map_sub, eval_X, eval_C, sub_eq_zero] using hroot

omit [Finite Y] in
theorem image_eq_pointToPoint_preimage :
    Set.range (polynomialMap F) = MvPolynomial.pointToPoint ⁻¹'
      Set.range (PrimeSpectrum.comap (pullback F).toRingHom) := by
  ext y
  exact mem_image_iff_pointToPoint_mem_spectrum_image F y

/-- Chevalley for the literal complex polynomial image in the explicitly
defined algebraic topology. This closes the spectrum/closed-point bridge. -/
theorem polynomial_image_constructible :
    @IsConstructible (Y → ℂ) (ConormalTopology.algebraicTopology Y)
      (Set.range (polynomialMap F)) := by
  letI : TopologicalSpace (Y → ℂ) := ConormalTopology.algebraicTopology Y
  have hi := pointToPoint_isInducing (Y := Y)
  letI : TopologicalSpace.NoetherianSpace (Y → ℂ) := hi.noetherianSpace
  rw [image_eq_pointToPoint_preimage F]
  apply (polynomial_spectrum_image_constructible F).preimage hi.continuous
  intro s _ _ V _ _
  exact TopologicalSpace.NoetherianSpace.isCompact _

omit [Finite X] [Finite Y] in
theorem polynomial_spectrum_image_closure :
    closure (Set.range (PrimeSpectrum.comap (pullback F).toRingHom)) =
      PrimeSpectrum.zeroLocus (imageIdeal F) :=
  PrimeSpectrum.closure_range_comap _

end Finite
end Sheshadri.AlgebraicCurveSelection
