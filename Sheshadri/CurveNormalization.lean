/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.CurveThroughBoundary
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Normalizing the selected curve

The normalization is the literal integral closure in the selected curve's
fraction field. Its finiteness follows from the trace theorem over the
polynomial PID, and its localization over the prescribed point is a DVR.
-/

noncomputable section
namespace Sheshadri.CurveNormalization
open scoped Polynomial nonZeroDivisors
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

section FractionExtension
variable (R T : Type*) [CommRing R] [IsDomain R] [CommRing T] [IsDomain T]
    [Algebra R T] [FaithfulSMul R T] [Algebra.IsAlgebraic R T]

/-- Nonzero base denominators already give the entire fraction field of
an algebraic domain extension. -/
theorem fractionRing_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid T R⁰) (FractionRing T) := by
  apply (IsLocalization.iff_of_le_of_exists_dvd
    (M := Algebra.algebraMapSubmonoid T R⁰) (S := FractionRing T) T⁰ ?_ ?_).mpr
  · infer_instance
  · rintro _ ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R T)).mpr
      (nonZeroDivisors.ne_zero hr)
  · intro t ht
    obtain ⟨r, hr, hd⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := R) t).exists_nonzero_dvd ht
    exact ⟨algebraMap R T r, ⟨r, mem_nonZeroDivisors_of_ne_zero hr, rfl⟩, hd⟩

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The finite parameter map proves finiteness of the fraction-field
extension; it is not an extra normalization hypothesis. -/
theorem fractionRing_finite [Module.Finite R T] :
    FiniteDimensional (FractionRing R) (FractionRing T) := by
  letI := fractionRing_isLocalization R T
  exact Module.Finite_of_isLocalization R T _ _ R⁰

end FractionExtension

section Normalization
variable {k : Type*} [Field k] [CharZero k]
variable (T : Type*) [CommRing T] [IsDomain T] [Algebra k[X] T]
    [FaithfulSMul k[X] T] [Module.Finite k[X] T]

/-- Actual normalization, retaining the original curve's function field. -/
abbrev Normalization := integralClosure T (FractionRing T)

instance normalization_isIntegralClosure :
    IsIntegralClosure (Normalization T) k[X] (FractionRing T) := by
  refine ⟨Subtype.val_injective, ?_⟩
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx.tower_top (A := T)⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact isIntegral_trans (R := k[X]) _ y.property

instance normalization_scalarTower :
    IsScalarTower k[X] (Normalization T) (FractionRing T) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

include k in
/-- Trace duality over the polynomial PID proves finite normalization. -/
theorem normalization_finite : Module.Finite k[X] (Normalization T) := by
  letI := fractionRing_finite k[X] T
  exact IsIntegralClosure.finite k[X] (FractionRing k[X]) (FractionRing T) (Normalization T)

include k in
/-- The actual normalization is Dedekind. -/
theorem normalization_dedekind : IsDedekindDomain (Normalization T) := by
  letI := fractionRing_finite k[X] T
  exact IsIntegralClosure.isDedekindDomain k[X] (FractionRing k[X])
    (FractionRing T) (Normalization T)

end Normalization

section ClosedPoint
variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
variable (T : Type*) [CommRing T] [IsDomain T] [Algebra k T] [Algebra k[X] T]
    [IsScalarTower k k[X] T] [FaithfulSMul k[X] T] [Module.Finite k[X] T]

instance normalization_base_scalarTower : IsScalarTower k k[X] (Normalization T) :=
  IsScalarTower.of_algebraMap_eq (fun c => by
    apply Subtype.ext
    change algebraMap T (FractionRing T) (algebraMap k T c) =
      algebraMap T (FractionRing T) (algebraMap k[X] T (algebraMap k k[X] c))
    rw [← IsScalarTower.algebraMap_apply k k[X] T])

/-- A rational point of the selected curve lifts to an actual nonzero
maximal ideal of its finite normalization. -/
theorem exists_normalization_point (point : T →ₐ[k] k) :
    ∃ (P : Ideal (Normalization T)) (hP : P.IsMaximal),
      P.comap (algebraMap T (Normalization T)) = RingHom.ker point ∧ P ≠ ⊥ ∧
      ∃ pointN : Normalization T →ₐ[k] k,
        RingHom.ker pointN = P ∧
        ∀ a : T, pointN (algebraMap T (Normalization T) a) = point a := by
  letI : (RingHom.ker point).IsMaximal := RingHom.ker_isMaximal_of_surjective point
    (fun c => ⟨algebraMap k T c, point.commutes c⟩)
  have hinj : Function.Injective (algebraMap T (Normalization T)) := by
    intro a b h
    exact IsFractionRing.injective T (FractionRing T) (congrArg Subtype.val h)
  obtain ⟨P, hP, hover⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := Normalization T) (RingHom.ker point)
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  letI := hP
  have hker : RingHom.ker point ≠ ⊥ := by
    let a : T := algebraMap k[X] T Polynomial.X
    let c : k := point a
    have hz : algebraMap k[X] T (Polynomial.X - Polynomial.C c) ∈ RingHom.ker point := by
      change point (algebraMap k[X] T (Polynomial.X - Polynomial.C c)) = 0
      rw [map_sub, map_sub]
      rw [show algebraMap k[X] T (Polynomial.C c) = algebraMap k T c from
        (IsScalarTower.algebraMap_apply k k[X] T c).symm, point.commutes]
      exact sub_self _
    have hn : algebraMap k[X] T (Polynomial.X - Polynomial.C c) ≠ 0 := by
      exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective k[X] T)).mpr
        (Polynomial.X_sub_C_ne_zero c)
    intro he
    exact hn (by simpa [he] using hz)
  have hPne : P ≠ ⊥ := by
    intro he
    apply hker
    rw [← hover, he, Ideal.comap_bot_of_injective _ hinj]
  letI := normalization_finite (k := k) T
  letI : Algebra.FiniteType k (Normalization T) :=
    Algebra.FiniteType.trans (R := k) (S := k[X]) (A := Normalization T)
      inferInstance inferInstance
  letI := Ideal.Quotient.field P
  letI : Module.Finite k (Normalization T ⧸ P) :=
    finite_of_finite_type_of_isJacobsonRing k (Normalization T ⧸ P)
  let e : k ≃ₐ[k] (Normalization T ⧸ P) :=
    AlgEquiv.ofBijective (Algebra.ofId k _)
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  let pointN : Normalization T →ₐ[k] k := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k P)
  have hNker : RingHom.ker pointN = P := by
    ext z
    change e.symm (Ideal.Quotient.mk P z) = 0 ↔ z ∈ P
    rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨P, hP, hover, hPne, pointN, hNker, ?_⟩
  intro a
  have hz : a - algebraMap k T (point a) ∈ RingHom.ker point := by
    change point (a - algebraMap k T (point a)) = 0
    simp
  rw [← hover] at hz
  have hn : algebraMap T (Normalization T) (a - algebraMap k T (point a)) ∈
      RingHom.ker pointN := by rw [hNker]; exact hz
  change pointN (algebraMap T (Normalization T) (a - algebraMap k T (point a))) = 0 at hn
  rw [map_sub, map_sub, ← IsScalarTower.algebraMap_apply k T (Normalization T),
    pointN.commutes, sub_eq_zero] at hn
  exact hn

/-- The selected curve has an actual local normalized branch at the
prescribed point. Its residue field is the base field, and an actual
uniformizer generates its maximal ideal. -/
theorem exists_normalized_dvr (point : T →ₐ[k] k) :
    ∃ P : PrimeSpectrum (Normalization T), P.asIdeal ≠ ⊥ ∧
      P.asIdeal.comap (algebraMap T (Normalization T)) = RingHom.ker point ∧
      IsDiscreteValuationRing (Localization.AtPrime P.asIdeal) ∧
      ∃ ρ : Localization.AtPrime P.asIdeal →ₐ[k] k,
        (∀ a : T, ρ (algebraMap T (Localization.AtPrime P.asIdeal) a) = point a) ∧
        RingHom.ker ρ = IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ∧
        Nonempty (IsLocalRing.ResidueField (Localization.AtPrime P.asIdeal) ≃ₐ[k] k) ∧
        ∃ π : Localization.AtPrime P.asIdeal, Irreducible π ∧
          IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) = Ideal.span {π} := by
  obtain ⟨P, hP, hover, hPne, pointN, hNker, hpoint⟩ := exists_normalization_point T point
  letI := hP
  letI := normalization_dedekind (k := k) T
  letI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Normalization T) hPne _
  have hunits (y : P.primeCompl) : IsUnit (pointN y) := by
    apply isUnit_iff_ne_zero.mpr
    intro hy
    apply y.property
    simpa only [hNker] using (show (y : Normalization T) ∈ RingHom.ker pointN from hy)
  let ρ : Localization.AtPrime P →ₐ[k] k := IsLocalization.liftAlgHom hunits
  have hρ (a : Normalization T) : ρ (algebraMap _ (Localization.AtPrime P) a) = pointN a :=
    IsLocalization.lift_eq hunits a
  have hρsurj : Function.Surjective ρ := fun c =>
    ⟨algebraMap k (Localization.AtPrime P) c, ρ.commutes c⟩
  have hρker : RingHom.ker ρ = IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    IsLocalRing.ker_eq_maximalIdeal (R := Localization.AtPrime P) ρ.toRingHom hρsurj
  let e : IsLocalRing.ResidueField (Localization.AtPrime P) ≃ₐ[k] k :=
    (Ideal.quotientEquivAlgOfEq k hρker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hρsurj)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  refine ⟨⟨P, hP.isPrime⟩, hPne, hover, inferInstance, ρ, ?_, hρker, ⟨e⟩, π, hπ, ?_⟩
  · intro a
    rw [IsScalarTower.algebraMap_apply T (Normalization T) (Localization.AtPrime P), hρ, hpoint]
  · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ

end ClosedPoint
section ParameterMap
variable {k T : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing T] [IsDomain T] [Algebra k T]

/-- The original curve embeds in every normalized local branch, so every
nonzero generic function remains nonzero after passing to the DVR. -/
theorem normalization_local_injective (P : PrimeSpectrum (Normalization T)) :
    Function.Injective (algebraMap T (Localization.AtPrime P.asIdeal)) := by
  rw [IsScalarTower.algebraMap_eq T (Normalization T) (Localization.AtPrime P.asIdeal)]
  apply (IsLocalization.injective (Localization.AtPrime P.asIdeal)
    P.asIdeal.primeCompl_le_nonZeroDivisors).comp
  intro a b h
  exact IsFractionRing.injective T (FractionRing T) (congrArg Subtype.val h)

/-- Direct interface for the actual finite parameter map produced by curve
selection. Neither normalization finiteness nor a DVR model is assumed. -/
theorem exists_normalized_dvr_of_finite_parameter
    (g : k[X] →ₐ[k] T) (hinj : Function.Injective g) (hfinite : g.Finite)
    (point : T →ₐ[k] k) :
    ∃ P : PrimeSpectrum (Normalization T), P.asIdeal ≠ ⊥ ∧
      P.asIdeal.comap (algebraMap T (Normalization T)) = RingHom.ker point ∧
      IsDiscreteValuationRing (Localization.AtPrime P.asIdeal) ∧
      ∃ ρ : Localization.AtPrime P.asIdeal →ₐ[k] k,
        (∀ a : T, ρ (algebraMap T (Localization.AtPrime P.asIdeal) a) = point a) ∧
        RingHom.ker ρ = IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ∧
        Nonempty (IsLocalRing.ResidueField (Localization.AtPrime P.asIdeal) ≃ₐ[k] k) ∧
        ∃ π : Localization.AtPrime P.asIdeal, Irreducible π ∧
          IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) = Ideal.span {π} := by
  letI : Algebra k[X] T := g.toRingHom.toAlgebra
  letI : IsScalarTower k k[X] T := IsScalarTower.of_algHom g
  letI : FaithfulSMul k[X] T := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  letI : Module.Finite k[X] T := hfinite
  exact exists_normalized_dvr T point

end ParameterMap
section SelectedCurve
variable {k S : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing S] [IsDomain S] [Algebra k S] [Algebra.FiniteType k S]

/-- Noether normalization, curve selection and finite normalization are
applied to the original affine variety. The nonzero function stays nonzero
on the resulting local branch and specializes to its prescribed value. -/
theorem exists_dvr_curve_through_point (point : S →ₐ[k] k)
    (f : S) (hf : f ≠ 0) (hpoint : point f = 0) :
    ∃ Q : PrimeSpectrum S, Q.asIdeal ≤ RingHom.ker point ∧ f ∉ Q.asIdeal ∧
      ringKrullDim (S ⧸ Q.asIdeal) = 1 ∧
      ∃ P : PrimeSpectrum (Normalization (S ⧸ Q.asIdeal)),
        IsDiscreteValuationRing (Localization.AtPrime P.asIdeal) ∧
        ∃ ρ : Localization.AtPrime P.asIdeal →ₐ[k] k,
          (∀ a : S, ρ (algebraMap (S ⧸ Q.asIdeal) (Localization.AtPrime P.asIdeal)
            (Ideal.Quotient.mk Q.asIdeal a)) = point a) ∧
          algebraMap (S ⧸ Q.asIdeal) (Localization.AtPrime P.asIdeal)
            (Ideal.Quotient.mk Q.asIdeal f) ≠ 0 ∧
          RingHom.ker ρ = IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ∧
          Nonempty (IsLocalRing.ResidueField (Localization.AtPrime P.asIdeal) ≃ₐ[k] k) ∧
          ∃ π : Localization.AtPrime P.asIdeal, Irreducible π ∧
            IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) = Ideal.span {π} := by
  obtain ⟨Q, hQ, hQpoint, hfQ, hdim, g, hginj, hgfinite⟩ :=
    CurveThroughBoundary.exists_curve_through_point point f hf hpoint
  letI := hQ
  let pointQ : (S ⧸ Q) →ₐ[k] k := Ideal.Quotient.liftₐ Q point hQpoint
  obtain ⟨P, hPne, hover, hDVR, ρ, hρ, hker, hresidue, π, hπ, hπgen⟩ :=
    exists_normalized_dvr_of_finite_parameter g hginj hgfinite pointQ
  refine ⟨⟨Q, hQ⟩, hQpoint, hfQ, hdim, P, hDVR, ρ, ?_, ?_, hker,
    hresidue, π, hπ, hπgen⟩
  · intro a
    exact hρ (Ideal.Quotient.mk Q a)
  · exact (map_ne_zero_iff _ (normalization_local_injective P)).mpr
      (fun hz => hfQ (Ideal.Quotient.eq_zero_iff_mem.mp hz))

end SelectedCurve
section PolynomialBoundary
open AlgebraicCurveSelection CurveThroughBoundary ZariskiBridge
variable {X Y : Type*} [Finite X] [Finite Y]
    (F : Y → MvPolynomial X ℂ)

/-- The normalized DVR belongs to the actual coefficient-image curve.
Its coefficient functions specialize to the requested boundary point, and
the curve's generic point has a preimage under the original polynomial map.
This is an algebraic branch statement, without an analytic closure assertion. -/
theorem exists_boundary_dvr (y : Y → ℂ)
    (hy : y ∈ zariskiClosure (Set.range (polynomialMap F)))
    (hout : y ∉ Set.range (polynomialMap F)) :
    ∃ (f : ImageRing F) (Q : PrimeSpectrum (ImageRing F)),
      f ∉ Q.asIdeal ∧
      Q ∈ Set.range (PrimeSpectrum.comap (imageEmbedding F).toRingHom) ∧
      ringKrullDim (ImageRing F ⧸ Q.asIdeal) = 1 ∧
      ∃ P : PrimeSpectrum (Normalization (ImageRing F ⧸ Q.asIdeal)),
        IsDiscreteValuationRing (Localization.AtPrime P.asIdeal) ∧
        ∃ ρ : Localization.AtPrime P.asIdeal →ₐ[ℂ] ℂ,
          (∀ i : Y, ρ (algebraMap (ImageRing F ⧸ Q.asIdeal) (Localization.AtPrime P.asIdeal)
            (Ideal.Quotient.mk Q.asIdeal
              (Ideal.Quotient.mk (imageIdeal F) (MvPolynomial.X i)))) = y i) ∧
          algebraMap (ImageRing F ⧸ Q.asIdeal) (Localization.AtPrime P.asIdeal)
            (Ideal.Quotient.mk Q.asIdeal f) ≠ 0 ∧
          ρ (algebraMap (ImageRing F ⧸ Q.asIdeal) (Localization.AtPrime P.asIdeal)
            (Ideal.Quotient.mk Q.asIdeal f)) = 0 ∧
          RingHom.ker ρ = IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ∧
          Nonempty (IsLocalRing.ResidueField (Localization.AtPrime P.asIdeal) ≃ₐ[ℂ] ℂ) ∧
          ∃ π : Localization.AtPrime P.asIdeal, Irreducible π ∧
            IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) = Ideal.span {π} := by
  obtain ⟨f, hf, hfy, hopen⟩ := exists_image_open_vanishing_at_boundary F y hy hout
  obtain ⟨Q, hQpoint, hfQ, hdim, P, hDVR, ρ, hρ, hnonzero, hker, hresidue, π, hπ, hπgen⟩ :=
    exists_dvr_curve_through_point (closurePoint F y hy) f hf hfy
  refine ⟨f, Q, hfQ, hopen hfQ, hdim, P, hDVR, ρ, ?_, hnonzero,
    (hρ f).trans hfy, hker, hresidue, π, hπ, hπgen⟩
  intro i
  exact (hρ _).trans (closurePoint_coordinate F y hy i)

end PolynomialBoundary
end Sheshadri.CurveNormalization
