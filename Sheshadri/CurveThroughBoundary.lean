/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.AlgebraicCurveSelection
import Sheshadri.NormalGoingDown
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Curves through boundary points by finite projections

This file constructs affine lines through specified points which avoid a
given nonzero polynomial. It then lifts such a line through a specified
point of a finite integral extension whenever the extension has going down.
The resulting prime quotient is finite over a polynomial ring in one variable.

Normal-base going down is proved in `NormalGoingDown`, so Noether
normalization yields an actual dimension-one prime through a boundary point.
The curve has a finite exceptional locus outside the polynomial image.
Normalization, lifting matrix representations, and analytic accumulation
are separate obligations and are not asserted by this module.
-/

noncomputable section
namespace Sheshadri.CurveThroughBoundary

open MvPolynomial Topology Filter
open scoped Polynomial Topology

variable {k I : Type*} [Field k]

section GenericOpen

variable {Z : Type*} [TopologicalSpace Z] {z : Z}

private theorem constructible_or_compl_mem_nhds
    (hz : IsGenericPoint z (Set.univ : Set Z)) {s : Set Z} (hs : IsConstructible s) :
    s ∈ 𝓝 z ∨ sᶜ ∈ 𝓝 z := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    by_cases hmem : z ∈ U
    · exact Or.inl (hU.mem_nhds hmem)
    · right
      have hempty : U = ∅ := by
        apply Set.eq_empty_iff_forall_not_mem.mpr
        intro x hx
        exact hmem ((hz.mem_open_set_iff hU).mpr ⟨x, Set.mem_univ _, hx⟩)
      simp [hempty]
  | union s hs t ht hs' ht' =>
    rcases hs' with hs' | hs'
    · exact Or.inl (Filter.mem_of_superset hs' Set.subset_union_left)
    · rcases ht' with ht' | ht'
      · exact Or.inl (Filter.mem_of_superset ht' Set.subset_union_right)
      · right
        rw [Set.compl_union]
        exact Filter.inter_mem hs' ht'
  | compl s hs hs' =>
    simpa only [compl_compl, or_comm] using hs'

/-- A constructible set containing the generic point contains an open
neighborhood of that point. No irreducibility certificate is assumed. -/
theorem constructible_mem_nhds_of_generic
    (hz : IsGenericPoint z (Set.univ : Set Z)) {s : Set Z}
    (hs : IsConstructible s) (hmem : z ∈ s) : s ∈ 𝓝 z := by
  rcases constructible_or_compl_mem_nhds hz hs with h | h
  · exact h
  · exact False.elim ((mem_of_mem_nhds h) hmem)

/-- Chevalley and the zero prime construct an actual principal open inside
the image of a dominant affine morphism of finite presentation. -/
theorem exists_nonzero_basicOpen_subset_image
    {R T : Type*} [CommRing R] [IsDomain R] [CommRing T] [IsDomain T]
    (φ : R →+* T) (hinj : Function.Injective φ) (hfp : φ.FinitePresentation) :
    ∃ r : R, r ≠ 0 ∧
      (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) ⊆
        Set.range (PrimeSpectrum.comap φ) := by
  let zR : PrimeSpectrum R := ⟨⊥, Ideal.bot_prime⟩
  let zT : PrimeSpectrum T := ⟨⊥, Ideal.bot_prime⟩
  have hgeneric : IsGenericPoint zR (Set.univ : Set (PrimeSpectrum R)) := by
    rw [IsGenericPoint, PrimeSpectrum.closure_singleton]
    exact PrimeSpectrum.zeroLocus_bot
  have hzero : PrimeSpectrum.comap φ zT = zR := by
    apply PrimeSpectrum.ext
    exact Ideal.comap_bot_of_injective φ hinj
  have hnbhd := constructible_mem_nhds_of_generic hgeneric
    (PrimeSpectrum.isConstructible_range_comap hfp) ⟨zT, hzero⟩
  obtain ⟨U, ⟨r, rfl⟩, hr, hU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff.mp hnbhd
  exact ⟨r, hr, hU⟩

end GenericOpen

/-- Pullback along the line joining `a` to `b`, with parameter zero at `a`. -/
def linePullback (a b : I → k) : MvPolynomial I k →ₐ[k] k[X] :=
  MvPolynomial.aeval (fun i => Polynomial.C (a i) +
    Polynomial.C (b i - a i) * Polynomial.X)

theorem eval_linePullback (a b : I → k) (p : MvPolynomial I k) (t : k) :
    Polynomial.eval t (linePullback a b p) =
      MvPolynomial.eval (fun i => a i + (b i - a i) * t) p := by
  change Polynomial.aeval t (MvPolynomial.aeval _ p) = MvPolynomial.aeval _ p
  rw [MvPolynomial.comp_aeval_apply]
  congr 1
  ext i
  simp

@[simp] theorem eval_zero_linePullback (a b : I → k) (p : MvPolynomial I k) :
    Polynomial.eval 0 (linePullback a b p) = MvPolynomial.eval a p := by
  simp [eval_linePullback]

@[simp] theorem eval_one_linePullback (a b : I → k) (p : MvPolynomial I k) :
    Polynomial.eval 1 (linePullback a b p) = MvPolynomial.eval b p := by
  simp [eval_linePullback]

/-- A nonconstant line really has the polynomial ring `k[t]` as its
coordinate ring: the pullback is surjective. -/
theorem linePullback_surjective (a b : I → k) (hab : a ≠ b) :
    Function.Surjective (linePullback a b) := by
  obtain ⟨i, hi⟩ : ∃ i, b i - a i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hab
    funext i
    exact (sub_eq_zero.mp (h i)).symm
  let back : k[X] →ₐ[k] MvPolynomial I k := Polynomial.aeval
    (MvPolynomial.C ((b i - a i)⁻¹) * (MvPolynomial.X i - MvPolynomial.C (a i)))
  have hback : (linePullback a b).comp back = AlgHom.id k k[X] := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, back, Polynomial.aeval_X, map_mul, map_sub,
      linePullback, MvPolynomial.aeval_C, MvPolynomial.aeval_X, AlgHom.id_apply]
    rw [← Polynomial.C_sub]
    change Polynomial.C ((b i - a i)⁻¹) *
      (Polynomial.C (a i) + Polynomial.C (b i - a i) * Polynomial.X - Polynomial.C (a i)) = _
    rw [add_sub_cancel_left, ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hi]
    simp
  intro p
  exact ⟨back p, DFunLike.congr_fun hback p⟩

/-- The actual coordinate quotient of a nonconstant affine line. -/
def lineQuotientEquiv (a b : I → k) (hab : a ≠ b) :
    (MvPolynomial I k ⧸ RingHom.ker (linePullback a b)) ≃ₐ[k] k[X] :=
  Ideal.quotientKerAlgEquivOfSurjective (linePullback_surjective a b hab)

/-- If a nonzero polynomial vanishes at the prescribed point, some
nonconstant line through that point is not contained in its zero locus. -/
theorem exists_line_avoiding [Infinite k] (a : I → k) (h : MvPolynomial I k)
    (hne : h ≠ 0) (ha : MvPolynomial.eval a h = 0) :
    ∃ b : I → k, a ≠ b ∧ linePullback a b h ≠ 0 := by
  obtain ⟨b, hb⟩ : ∃ b : I → k, MvPolynomial.eval b h ≠ 0 := by
    by_contra h'
    push_neg at h'
    apply hne
    exact MvPolynomial.funext (fun x => by simpa using h' x)
  refine ⟨b, ?_, ?_⟩
  · intro heq
    subst b
    exact hb ha
  · intro heq
    have := congrArg (Polynomial.eval 1) heq
    simpa using hb (by simpa using this)

theorem lineKernel_le_pointKernel (a b : I → k) :
    RingHom.ker (linePullback a b) ≤ RingHom.ker (MvPolynomial.eval a) := by
  intro p hp
  change MvPolynomial.eval a p = 0
  change linePullback a b p = 0 at hp
  have := congrArg (Polynomial.eval 0) hp
  simpa using this

section IntegralLift

variable {S : Type*} [CommRing S] [IsDomain S]
variable [Algebra k S] [Algebra (MvPolynomial I k) S]
variable [IsScalarTower k (MvPolynomial I k) S]

/-- The image of a specified point under the finite projection. -/
def normalizedPoint (point : S →ₐ[k] k) : I → k :=
  fun i => point (algebraMap (MvPolynomial I k) S (MvPolynomial.X i))

omit [IsDomain S] in
theorem eval_normalizedPoint (point : S →ₐ[k] k) (p : MvPolynomial I k) :
    MvPolynomial.eval (normalizedPoint point) p =
      point (algebraMap (MvPolynomial I k) S p) := by
  have he : point.comp (IsScalarTower.toAlgHom k (MvPolynomial I k) S) =
      MvPolynomial.aeval (normalizedPoint point) := by
    ext i
    simp [normalizedPoint]
  exact (DFunLike.congr_fun he p).symm

omit [IsDomain S] in
theorem pointKernel_under (point : S →ₐ[k] k) :
    (RingHom.ker point).under (MvPolynomial I k) =
      RingHom.ker (MvPolynomial.eval (normalizedPoint point)) := by
  ext p
  change point (algebraMap (MvPolynomial I k) S p) = 0 ↔
    MvPolynomial.eval (normalizedPoint point) p = 0
  rw [eval_normalizedPoint]

/-- A finite projection with going down lifts a suitable actual affine line
through the prescribed point to an irreducible component through that point,
and the lifted component avoids the specified nonzero element generically.

The displayed contracted prime is a line kernel, not an arbitrary prime
assumed to have the dimension one property. -/
theorem exists_prime_curve_over_line [Infinite k]
    [Algebra.IsIntegral (MvPolynomial I k) S]
    [Algebra.HasGoingDown (MvPolynomial I k) S]
    (point : S →ₐ[k] k) (f : S) (hf : f ≠ 0) (hpoint : point f = 0) :
    ∃ (b : I → k) (P : Ideal S),
      normalizedPoint point ≠ b ∧ P.IsPrime ∧ P ≤ RingHom.ker point ∧ f ∉ P ∧
      P.under (MvPolynomial I k) = RingHom.ker (linePullback (normalizedPoint point) b) := by
  let J : Ideal S := Ideal.span {f}
  have hJ : J.under (MvPolynomial I k) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hf (Ideal.subset_span (Set.mem_singleton f))
      (Algebra.IsIntegral.isIntegral f)
  obtain ⟨h, hh, hhne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hJpoint : J ≤ RingHom.ker point := by
    apply Ideal.span_le.mpr
    intro z hz
    simpa only [Set.mem_singleton_iff.mp hz, RingHom.mem_ker] using hpoint
  have hzero : MvPolynomial.eval (normalizedPoint point) h = 0 := by
    rw [eval_normalizedPoint]
    exact hJpoint hh
  obtain ⟨b, hab, hb⟩ := exists_line_avoiding (normalizedPoint point) h hhne hzero
  let p : Ideal (MvPolynomial I k) := RingHom.ker (linePullback (normalizedPoint point) b)
  let M : Ideal S := RingHom.ker point
  letI : p.IsPrime := RingHom.ker_isPrime _
  letI : M.IsPrime := RingHom.ker_isPrime _
  have hle : p ≤ M.under (MvPolynomial I k) := by
    rw [pointKernel_under]
    exact lineKernel_le_pointKernel _ _
  obtain ⟨P, hPM, hprime, hlies⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := p) (q := M.under (MvPolynomial I k)) M hle
  letI := hprime
  letI := hlies
  have hover : P.under (MvPolynomial I k) = p := (P.over_def p).symm
  refine ⟨b, P, hab, hprime, hPM, ?_, hover⟩
  intro hfP
  have hJP : J ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfP)
  have hhP : h ∈ P.under (MvPolynomial I k) := hJP hh
  rw [hover] at hhP
  exact hb hhP

omit [IsDomain S] in
/-- The prime quotient constructed over a line is a finite algebra over
that line's actual coordinate ring. -/
theorem finite_line_embedding [Module.Finite (MvPolynomial I k) S]
    (a b : I → k) (hab : a ≠ b) (P : Ideal S)
    (hover : P.under (MvPolynomial I k) = RingHom.ker (linePullback a b)) :
    ∃ g : k[X] →ₐ[k] (S ⧸ P), Function.Injective g ∧ g.Finite := by
  let p : Ideal (MvPolynomial I k) := RingHom.ker (linePullback a b)
  letI : P.LiesOver p := ⟨hover.symm⟩
  letI : Module.Finite (MvPolynomial I k ⧸ p) (S ⧸ P) :=
    Module.Finite.of_restrictScalars_finite (MvPolynomial I k) (MvPolynomial I k ⧸ p) (S ⧸ P)
  let φ : (MvPolynomial I k ⧸ p) →ₐ[k] (S ⧸ P) :=
    IsScalarTower.toAlgHom k (MvPolynomial I k ⧸ p) (S ⧸ P)
  have hφinj : Function.Injective φ :=
    FaithfulSMul.algebraMap_injective (MvPolynomial I k ⧸ p) (S ⧸ P)
  have hφfin : φ.Finite := by
    change (algebraMap (MvPolynomial I k ⧸ p) (S ⧸ P)).Finite
    have he : (algebraMap (MvPolynomial I k ⧸ p) (S ⧸ P)).toAlgebra =
        (inferInstance : Algebra (MvPolynomial I k ⧸ p) (S ⧸ P)) :=
      Algebra.algebra_ext _ _ (fun _ => rfl)
    simp only [RingHom.Finite, he]
    infer_instance
  let e : (MvPolynomial I k ⧸ p) ≃ₐ[k] k[X] := lineQuotientEquiv a b hab
  refine ⟨φ.comp e.symm.toAlgHom, hφinj.comp e.symm.injective,
    hφfin.comp (AlgHom.Finite.of_surjective _ e.symm.surjective)⟩

/-- The quotient is a genuine algebraic curve in the ring-theoretic sense:
it is an integral finite extension of `k[t]`, not a zero-dimensional quotient. -/
theorem exists_finite_curve_quotient [Infinite k]
    [Module.Finite (MvPolynomial I k) S]
    [Algebra.HasGoingDown (MvPolynomial I k) S]
    (point : S →ₐ[k] k) (f : S) (hf : f ≠ 0) (hpoint : point f = 0) :
    ∃ P : Ideal S, P.IsPrime ∧ P ≤ RingHom.ker point ∧ f ∉ P ∧
      ∃ g : k[X] →ₐ[k] (S ⧸ P), Function.Injective g ∧ g.Finite := by
  obtain ⟨b, P, hab, hP, hPM, hfP, hover⟩ :=
    exists_prime_curve_over_line (I := I) point f hf hpoint
  obtain ⟨g, hginj, hgfin⟩ := finite_line_embedding (normalizedPoint point) b hab P hover
  exact ⟨P, hP, hPM, hfP, g, hginj, hgfin⟩

end IntegralLift

section CurveDimension

variable {T : Type*} [CommRing T] [IsDomain T] [Algebra k T]

theorem curve_quotient_dimension_le_one (g : k[X] →ₐ[k] T) (hg : g.Finite) :
    Ring.KrullDimLE 1 T := by
  letI : Algebra k[X] T := g.toRingHom.toAlgebra
  letI : Module.Finite k[X] T := hg
  apply Ring.KrullDimLE.mk₁'
  intro J hJ hprime
  letI := hprime
  have hcomap : J.under k[X] ≠ ⊥ := by
    intro heq
    exact hJ (Ideal.eq_bot_of_comap_eq_bot heq)
  have hmax : (J.under k[X]).IsMaximal := IsPrime.to_maximal_ideal hcomap
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap J hmax

omit [IsDomain T] in
theorem curve_quotient_not_isField (g : k[X] →ₐ[k] T)
    (hinj : Function.Injective g) (hg : g.Finite) : ¬ IsField T := by
  letI : Algebra k[X] T := g.toRingHom.toAlgebra
  letI : Module.Finite k[X] T := hg
  intro hfield
  exact Polynomial.not_isField k (isField_of_isIntegral_of_isField hinj hfield)

/-- The finite injective polynomial parameter proves dimension exactly one. -/
theorem curve_quotient_dimension_eq_one (g : k[X] →ₐ[k] T)
    (hinj : Function.Injective g) (hg : g.Finite) : ringKrullDim T = 1 := by
  letI : Ring.KrullDimLE 1 T := curve_quotient_dimension_le_one g hg
  apply le_antisymm
  · exact Order.KrullDimLE.krullDim_le (n := 1)
  · rw [WithBot.one_le_iff_pos]
    apply lt_of_not_ge
    intro hzero
    letI : Ring.KrullDimLE 0 T := ⟨hzero⟩
    letI : (⊥ : Ideal T).IsPrime := Ideal.bot_prime
    have hm : (⊥ : Ideal T).IsMaximal := Ideal.isMaximal_of_isPrime (⊥ : Ideal T)
    exact (Ring.ne_bot_of_isMaximal_of_not_isField hm
      (curve_quotient_not_isField g hinj hg)) rfl

/-- A nonzero function on a Noetherian integral curve has only finitely
many zeroes, including scheme-theoretic spectrum points. -/
theorem finite_zeroLocus_of_nonzero [IsNoetherianRing T] [Ring.KrullDimLE 1 T]
    (f : T) (hf : f ≠ 0) : (PrimeSpectrum.zeroLocus ({f} : Set T)).Finite := by
  have hsub : PrimeSpectrum.zeroLocus ({f} : Set T) ⊆
      PrimeSpectrum.asIdeal ⁻¹' (Ideal.span ({f} : Set T)).minimalPrimes := by
    intro P hP
    have hfP : f ∈ P.asIdeal := hP (Set.mem_singleton f)
    have hle : Ideal.span ({f} : Set T) ≤ P.asIdeal :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfP)
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hle
    have hQne : Q ≠ ⊥ := by
      intro he
      have hmem := hQ.1.2 (Ideal.subset_span (Set.mem_singleton f))
      rw [he, Ideal.mem_bot] at hmem
      exact hf hmem
    have hmax : Q.IsMaximal :=
      Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance Q hQne hQ.1.1
    have heq : Q = P.asIdeal := hmax.eq_of_le P.isPrime.ne_top hQP
    simpa only [Set.mem_preimage, ← heq] using hQ
  exact ((Ideal.finite_minimalPrimes_of_isNoetherianRing T (Ideal.span ({f} : Set T))).preimage
    (fun _ _ _ _ h => PrimeSpectrum.ext h)).subset hsub

end CurveDimension

/-- An actual dimension-one irreducible closed subscheme through the
specified point, meeting the basic open `D(f)`, for finite maps with going down. -/
theorem exists_dimension_one_prime_through_point {S : Type*}
    [CommRing S] [IsDomain S] [Algebra k S] [Algebra (MvPolynomial I k) S]
    [IsScalarTower k (MvPolynomial I k) S] [Infinite k]
    [Module.Finite (MvPolynomial I k) S]
    [Algebra.HasGoingDown (MvPolynomial I k) S]
    (point : S →ₐ[k] k) (f : S) (hf : f ≠ 0) (hpoint : point f = 0) :
    ∃ P : Ideal S, P.IsPrime ∧ P ≤ RingHom.ker point ∧ f ∉ P ∧
      ringKrullDim (S ⧸ P) = 1 ∧
      ∃ g : k[X] →ₐ[k] (S ⧸ P), Function.Injective g ∧ g.Finite := by
  obtain ⟨P, hP, hPM, hfP, g, hginj, hgfin⟩ :=
    exists_finite_curve_quotient (I := I) point f hf hpoint
  letI := hP
  exact ⟨P, hP, hPM, hfP, curve_quotient_dimension_eq_one g hginj hgfin,
    g, hginj, hgfin⟩

/-- Noether normalization and proved normal-base going down construct an
irreducible curve through a prescribed zero of a nonzero function on an
arbitrary finite-type integral variety over a characteristic-zero field. -/
theorem exists_curve_through_point {S : Type*} [CharZero k] [Infinite k]
    [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S]
    (point : S →ₐ[k] k) (f : S) (hf : f ≠ 0) (hpoint : point f = 0) :
    ∃ P : Ideal S, P.IsPrime ∧ P ≤ RingHom.ker point ∧ f ∉ P ∧
      ringKrullDim (S ⧸ P) = 1 ∧
      ∃ g : k[X] →ₐ[k] (S ⧸ P), Function.Injective g ∧ g.Finite := by
  obtain ⟨d, g, hginj, hgfin⟩ := exists_finite_inj_algHom_of_fg k S
  letI : Algebra (MvPolynomial (Fin d) k) S := g.toRingHom.toAlgebra
  letI : IsScalarTower k (MvPolynomial (Fin d) k) S := IsScalarTower.of_algHom g
  letI : Module.Finite (MvPolynomial (Fin d) k) S := hgfin
  letI : IsIntegrallyClosed (MvPolynomial (Fin d) k) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  letI : Algebra.HasGoingDown (MvPolynomial (Fin d) k) S :=
    NormalGoingDown.finite_of_integrallyClosed (MvPolynomial (Fin d) k) S hginj
  exact exists_dimension_one_prime_through_point (I := Fin d) point f hf hpoint

section PolynomialBoundary

open AlgebraicCurveSelection ZariskiBridge
variable {X Y : Type*} [Finite X] [Finite Y]
variable (F : Y → MvPolynomial X ℂ)

/-- The image coordinate ring embeds in the source polynomial ring. -/
def imageEmbedding : ImageRing F →ₐ[ℂ] MvPolynomial X ℂ :=
  Ideal.kerLiftAlg (pullback F)

omit [Finite X] [Finite Y] in
theorem imageEmbedding_injective : Function.Injective (imageEmbedding F) :=
  Ideal.kerLiftAlg_injective _

theorem imageEmbedding_finitePresentation :
    (imageEmbedding F).toRingHom.FinitePresentation := by
  apply RingHom.FinitePresentation.of_finiteType.mp
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (ImageRing F))
  have hcomp : (imageEmbedding F).toRingHom.comp (algebraMap ℂ (ImageRing F)) =
      algebraMap ℂ (MvPolynomial X ℂ) := by
    apply RingHom.ext
    intro z
    exact (imageEmbedding F).commutes z
  rw [hcomp]
  exact algebraMap_finiteType_iff_algebra_finiteType.mpr inferInstance

/-- The specified closure point, regarded as a prime of the image ring. -/
def closurePrime (y : Y → ℂ)
    (hy : y ∈ zariskiClosure (Set.range (polynomialMap F))) : PrimeSpectrum (ImageRing F) :=
  ⟨RingHom.ker (closurePoint F y hy), RingHom.ker_isPrime _⟩

omit [Finite X] [Finite Y] in
theorem closurePrime_comap (y : Y → ℂ)
    (hy : y ∈ zariskiClosure (Set.range (polynomialMap F))) :
    PrimeSpectrum.comap (Ideal.Quotient.mk (imageIdeal F)) (closurePrime F y hy) =
      MvPolynomial.pointToPoint y := by
  apply PrimeSpectrum.ext
  ext p
  change closurePoint F y hy (Ideal.Quotient.mk (imageIdeal F) p) = 0 ↔
    p ∈ MvPolynomial.vanishingIdeal {y}
  simp [closurePoint, MvPolynomial.mem_vanishingIdeal_singleton_iff]

omit [Finite Y] in
/-- Every spectrum preimage of a complex closure point gives a literal
complex preimage under the original polynomial map. -/
theorem closurePrime_mem_image_iff (y : Y → ℂ)
    (hy : y ∈ zariskiClosure (Set.range (polynomialMap F))) :
    closurePrime F y hy ∈ Set.range (PrimeSpectrum.comap (imageEmbedding F).toRingHom) ↔
      y ∈ Set.range (polynomialMap F) := by
  constructor
  · rintro ⟨P, hP⟩
    apply (mem_image_iff_pointToPoint_mem_spectrum_image F y).mpr
    refine ⟨P, ?_⟩
    rw [← closurePrime_comap F y hy, ← hP]
    apply PrimeSpectrum.ext
    ext q
    change imageEmbedding F (Ideal.Quotient.mk (imageIdeal F) q) ∈ P.asIdeal ↔ _
    rfl
  · rintro ⟨x, rfl⟩
    refine ⟨MvPolynomial.pointToPoint x, ?_⟩
    apply PrimeSpectrum.ext
    ext q
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective q
    change pullback F q ∈ MvPolynomial.vanishingIdeal {x} ↔
      closurePoint F (polynomialMap F x) hy (Ideal.Quotient.mk (imageIdeal F) q) = 0
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff, eval_pullback]
    rfl

/-- An actual nonzero function cuts away all omitted image points. In
particular, it vanishes at the chosen boundary point, while its principal
open is contained in the genuine spectrum image. -/
theorem exists_image_open_vanishing_at_boundary (y : Y → ℂ)
    (hy : y ∈ zariskiClosure (Set.range (polynomialMap F)))
    (hout : y ∉ Set.range (polynomialMap F)) :
    ∃ f : ImageRing F, f ≠ 0 ∧ closurePoint F y hy f = 0 ∧
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (ImageRing F))) ⊆
        Set.range (PrimeSpectrum.comap (imageEmbedding F).toRingHom) := by
  obtain ⟨f, hf, hopen⟩ := exists_nonzero_basicOpen_subset_image
    (imageEmbedding F).toRingHom (imageEmbedding_injective F)
    (imageEmbedding_finitePresentation F)
  refine ⟨f, hf, ?_, hopen⟩
  by_contra hne
  exact hout ((closurePrime_mem_image_iff F y hy).mp (hopen hne))

/-- Actual algebraic curve selection in the image closure: the prime
quotient has dimension exactly one, contains the prescribed boundary point,
and has only finitely many exceptional spectrum points outside a principal
open that lies in the original polynomial image.

This constructs a curve in coefficient space. It does not assert a rational
parameterization, a lifted matrix family, or analytic accumulation. -/
theorem exists_curve_in_imageClosure_through_boundary (y : Y → ℂ)
    (hy : y ∈ zariskiClosure (Set.range (polynomialMap F)))
    (hout : y ∉ Set.range (polynomialMap F)) :
    ∃ (f : ImageRing F) (P : Ideal (ImageRing F)),
      P.IsPrime ∧ P ≤ RingHom.ker (closurePoint F y hy) ∧
      f ≠ 0 ∧ closurePoint F y hy f = 0 ∧ f ∉ P ∧
      ringKrullDim (ImageRing F ⧸ P) = 1 ∧
      (∃ g : ℂ[X] →ₐ[ℂ] (ImageRing F ⧸ P), Function.Injective g ∧ g.Finite) ∧
      (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (ImageRing F))) ⊆
        Set.range (PrimeSpectrum.comap (imageEmbedding F).toRingHom) ∧
      (PrimeSpectrum.zeroLocus ({Ideal.Quotient.mk P f} : Set (ImageRing F ⧸ P))).Finite := by
  obtain ⟨f, hf, hfy, hopen⟩ := exists_image_open_vanishing_at_boundary F y hy hout
  obtain ⟨P, hP, hPy, hfP, hdim, g, hginj, hgfin⟩ :=
    exists_curve_through_point (closurePoint F y hy) f hf hfy
  letI := hP
  letI : Ring.KrullDimLE 1 (ImageRing F ⧸ P) := curve_quotient_dimension_le_one g hgfin
  have hq : Ideal.Quotient.mk P f ≠ 0 := fun h => hfP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  exact ⟨f, P, hP, hPy, hf, hfy, hfP, hdim, ⟨g, hginj, hgfin⟩, hopen,
    finite_zeroLocus_of_nonzero (Ideal.Quotient.mk P f) hq⟩

omit [Finite Y] in
/-- The principal open in the selected curve contains literal complex
image points: no replacement of complex points by arbitrary spectrum
points is needed when the curve is used later. -/
theorem closurePoint_mem_image_of_nonzero
    (f : ImageRing F)
    (hopen : (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum (ImageRing F))) ⊆
      Set.range (PrimeSpectrum.comap (imageEmbedding F).toRingHom))
    (y : Y → ℂ) (hy : y ∈ zariskiClosure (Set.range (polynomialMap F)))
    (hne : closurePoint F y hy f ≠ 0) : y ∈ Set.range (polynomialMap F) :=
  (closurePrime_mem_image_iff F y hy).mp (hopen hne)

end PolynomialBoundary

end Sheshadri.CurveThroughBoundary
