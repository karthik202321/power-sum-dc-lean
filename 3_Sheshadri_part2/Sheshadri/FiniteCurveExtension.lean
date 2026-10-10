/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.CurveNormalization
import Mathlib.RingTheory.Localization.AsSubring

/-!
# Normalized branches after finite extension of the curve's function field

The extension can carry a coherent rational representation. Only coefficient
functions are asserted regular at the special point; representation coordinates
in the function field are allowed poles.
-/
noncomputable section
namespace Sheshadri.FiniteCurveExtension
open scoped Polynomial nonZeroDivisors
open CurveNormalization
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

variable {k : Type*} [Field k] [CharZero k]
variable (T L : Type*) [CommRing T] [IsDomain T] [Field L]
    [Algebra k[X] T] [FaithfulSMul k[X] T] [Module.Finite k[X] T]
    [Algebra T L] [Algebra (FractionRing T) L] [IsScalarTower T (FractionRing T) L]
    [FiniteDimensional (FractionRing T) L]
    [Algebra k[X] L] [IsScalarTower k[X] T L]

abbrev ExtensionNormalization := integralClosure T L

instance extension_faithful : FaithfulSMul T L := by
  apply (faithfulSMul_iff_algebraMap_injective T L).mpr
  rw [IsScalarTower.algebraMap_eq T (FractionRing T) L]
  exact (algebraMap (FractionRing T) L).injective.comp (IsFractionRing.injective T _)

instance extension_isIntegralClosure :
    IsIntegralClosure (ExtensionNormalization T L) k[X] L := by
  refine ⟨Subtype.val_injective, ?_⟩
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx.tower_top (A := T)⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact isIntegral_trans (R := k[X]) _ y.property

instance extension_scalarTower : IsScalarTower k[X] (ExtensionNormalization T L) L :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

include k in
/-- Both finiteness and the Dedekind property follow from the actual finite
function-field extension and trace duality over the parameter polynomial PID. -/
theorem extensionNormalization_finite_dedekind :
    Module.Finite k[X] (ExtensionNormalization T L) ∧
      IsDedekindDomain (ExtensionNormalization T L) := by
  letI : Algebra (FractionRing k[X]) (FractionRing T) := FractionRing.liftAlgebra k[X] _
  letI : IsScalarTower k[X] (FractionRing k[X]) (FractionRing T) :=
    FractionRing.isScalarTower_liftAlgebra k[X] _
  letI : Algebra (FractionRing k[X]) L :=
    ((algebraMap (FractionRing T) L).comp
      (algebraMap (FractionRing k[X]) (FractionRing T))).toAlgebra
  letI : IsScalarTower (FractionRing k[X]) (FractionRing T) L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower k[X] (FractionRing k[X]) L :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      change algebraMap k[X] L r = algebraMap (FractionRing T) L
        (algebraMap (FractionRing k[X]) (FractionRing T) (algebraMap k[X] (FractionRing k[X]) r))
      rw [← IsScalarTower.algebraMap_apply k[X] (FractionRing k[X]) (FractionRing T),
        IsScalarTower.algebraMap_apply k[X] T (FractionRing T),
        ← IsScalarTower.algebraMap_apply T (FractionRing T) L,
        ← IsScalarTower.algebraMap_apply k[X] T L])
  letI : FiniteDimensional (FractionRing k[X]) (FractionRing T) := fractionRing_finite k[X] T
  letI : FiniteDimensional (FractionRing k[X]) L := Module.Finite.trans (FractionRing T) L
  exact ⟨IsIntegralClosure.finite k[X] (FractionRing k[X]) L (ExtensionNormalization T L),
    IsIntegralClosure.isDedekindDomain k[X] (FractionRing k[X]) L (ExtensionNormalization T L)⟩

include k in
theorem extensionNormalization_finite : Module.Finite k[X] (ExtensionNormalization T L) :=
  (extensionNormalization_finite_dedekind (k := k) T L).1

include k in
theorem extensionNormalization_dedekind : IsDedekindDomain (ExtensionNormalization T L) :=
  (extensionNormalization_finite_dedekind (k := k) T L).2

instance extension_fractionRing : IsFractionRing (ExtensionNormalization T L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension T (FractionRing T) L
    (ExtensionNormalization T L)

section ClosedPoint
variable [IsAlgClosed k] [Algebra k T] [IsScalarTower k k[X] T]
    [Algebra k L] [IsScalarTower k T L]

instance extension_base_scalarTower : IsScalarTower k k[X] (ExtensionNormalization T L) :=
  IsScalarTower.of_algebraMap_eq (fun c => by
    apply Subtype.ext
    change algebraMap k L c = algebraMap k[X] L (algebraMap k k[X] c)
    rw [IsScalarTower.algebraMap_apply k T L, IsScalarTower.algebraMap_apply k[X] T L,
      ← IsScalarTower.algebraMap_apply k k[X] T])

instance extension_coefficient_scalarTower : IsScalarTower k (ExtensionNormalization T L) L :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/-- The actual branch embeds in the field carrying the generic representation. -/
def fractionEmbedding (P : PrimeSpectrum (ExtensionNormalization T L)) :
    Localization.AtPrime P.asIdeal →ₐ[k] L :=
  (Localization.mapToFractionRing L P.asIdeal.primeCompl
    (Localization.AtPrime P.asIdeal) P.asIdeal.primeCompl_le_nonZeroDivisors).restrictScalars k

@[simp] theorem fractionEmbedding_coefficient
    (P : PrimeSpectrum (ExtensionNormalization T L)) (a : T) :
    fractionEmbedding (k := k) T L P (algebraMap T (Localization.AtPrime P.asIdeal) a) =
      algebraMap T L a := by
  rw [IsScalarTower.algebraMap_apply T (ExtensionNormalization T L) (Localization.AtPrime P.asIdeal)]
  change IsLocalization.lift _ (algebraMap (ExtensionNormalization T L)
    (Localization.AtPrime P.asIdeal) (algebraMap T (ExtensionNormalization T L) a)) = _
  rw [IsLocalization.lift_eq, ← IsScalarTower.algebraMap_apply T (ExtensionNormalization T L) L]

theorem fractionEmbedding_injective (P : PrimeSpectrum (ExtensionNormalization T L)) :
    Function.Injective (fractionEmbedding (k := k) T L P) := by
  apply (IsLocalization.lift_injective_iff _).mpr
  intro a b
  constructor
  · intro h
    exact congrArg (algebraMap (ExtensionNormalization T L) L)
      (IsLocalization.injective (Localization.AtPrime P.asIdeal)
        P.asIdeal.primeCompl_le_nonZeroDivisors h)
  · intro h
    exact congrArg (algebraMap (ExtensionNormalization T L) (Localization.AtPrime P.asIdeal))
      (IsFractionRing.injective (ExtensionNormalization T L) L h)

/-- Every generic representation entry is an actual rational function on
the normalized local branch; no regularity of that entry is asserted. -/
theorem fractionEmbedding_div_surjective
    (P : PrimeSpectrum (ExtensionNormalization T L)) (z : L) :
    ∃ a b : Localization.AtPrime P.asIdeal, b ≠ 0 ∧
      z = fractionEmbedding (k := k) T L P a / fractionEmbedding (k := k) T L P b := by
  obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective (A := ExtensionNormalization T L) z
  refine ⟨algebraMap _ _ a, algebraMap _ _ b, ?_, ?_⟩
  · exact (map_ne_zero_iff _ (IsLocalization.injective (Localization.AtPrime P.asIdeal)
      P.asIdeal.primeCompl_le_nonZeroDivisors)).mpr (nonZeroDivisors.ne_zero hb)
  · change z = IsLocalization.lift _ (algebraMap (ExtensionNormalization T L)
      (Localization.AtPrime P.asIdeal) a) / IsLocalization.lift _
      (algebraMap (ExtensionNormalization T L) (Localization.AtPrime P.asIdeal) b)
    simpa only [IsLocalization.lift_eq] using hz.symm

/-- A rational point of the selected curve lifts to an actual nonzero
maximal ideal of its finite normalization. -/
theorem exists_extension_normalization_point (point : T →ₐ[k] k) :
    ∃ (P : Ideal (ExtensionNormalization T L)) (hP : P.IsMaximal),
      P.comap (algebraMap T (ExtensionNormalization T L)) = RingHom.ker point ∧ P ≠ ⊥ ∧
      ∃ pointN : ExtensionNormalization T L →ₐ[k] k,
        RingHom.ker pointN = P ∧
        ∀ a : T, pointN (algebraMap T (ExtensionNormalization T L) a) = point a := by
  letI : (RingHom.ker point).IsMaximal := RingHom.ker_isMaximal_of_surjective point
    (fun c => ⟨algebraMap k T c, point.commutes c⟩)
  have hinj : Function.Injective (algebraMap T (ExtensionNormalization T L)) := by
    intro a b h
    exact FaithfulSMul.algebraMap_injective T L (congrArg Subtype.val h)
  obtain ⟨P, hP, hover⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := ExtensionNormalization T L) (RingHom.ker point)
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
  letI := extensionNormalization_finite (k := k) T L
  letI : Algebra.FiniteType k (ExtensionNormalization T L) :=
    Algebra.FiniteType.trans (R := k) (S := k[X]) (A := ExtensionNormalization T L)
      inferInstance inferInstance
  letI := Ideal.Quotient.field P
  letI : Module.Finite k (ExtensionNormalization T L ⧸ P) :=
    finite_of_finite_type_of_isJacobsonRing k (ExtensionNormalization T L ⧸ P)
  let e : k ≃ₐ[k] (ExtensionNormalization T L ⧸ P) :=
    AlgEquiv.ofBijective (Algebra.ofId k _)
      IsAlgClosed.algebraMap_bijective_of_isIntegral
  let pointN : ExtensionNormalization T L →ₐ[k] k := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k P)
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
  have hn : algebraMap T (ExtensionNormalization T L) (a - algebraMap k T (point a)) ∈
      RingHom.ker pointN := by rw [hNker]; exact hz
  change pointN (algebraMap T (ExtensionNormalization T L) (a - algebraMap k T (point a))) = 0 at hn
  rw [map_sub, map_sub, ← IsScalarTower.algebraMap_apply k T (ExtensionNormalization T L),
    pointN.commutes, sub_eq_zero] at hn
  exact hn

/-- The selected curve has an actual local normalized branch at the
prescribed point. Its residue field is the base field, and an actual
uniformizer generates its maximal ideal. -/
theorem exists_extension_dvr (point : T →ₐ[k] k) :
    ∃ P : PrimeSpectrum (ExtensionNormalization T L), P.asIdeal ≠ ⊥ ∧
      P.asIdeal.comap (algebraMap T (ExtensionNormalization T L)) = RingHom.ker point ∧
      IsDiscreteValuationRing (Localization.AtPrime P.asIdeal) ∧
      ∃ ρ : Localization.AtPrime P.asIdeal →ₐ[k] k,
        (∀ a : T, ρ (algebraMap T (Localization.AtPrime P.asIdeal) a) = point a) ∧
        RingHom.ker ρ = IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) ∧
        Nonempty (IsLocalRing.ResidueField (Localization.AtPrime P.asIdeal) ≃ₐ[k] k) ∧
        ∃ π : Localization.AtPrime P.asIdeal, Irreducible π ∧
          IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) = Ideal.span {π} := by
  obtain ⟨P, hP, hover, hPne, pointN, hNker, hpoint⟩ := exists_extension_normalization_point T L point
  letI := hP
  letI := extensionNormalization_dedekind (k := k) T L
  letI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (ExtensionNormalization T L) hPne _
  have hunits (y : P.primeCompl) : IsUnit (pointN y) := by
    apply isUnit_iff_ne_zero.mpr
    intro hy
    apply y.property
    simpa only [hNker] using (show (y : ExtensionNormalization T L) ∈ RingHom.ker pointN from hy)
  let ρ : Localization.AtPrime P →ₐ[k] k := IsLocalization.liftAlgHom hunits
  have hρ (a : ExtensionNormalization T L) : ρ (algebraMap _ (Localization.AtPrime P) a) = pointN a :=
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
    rw [IsScalarTower.algebraMap_apply T (ExtensionNormalization T L) (Localization.AtPrime P), hρ, hpoint]
  · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ


end ClosedPoint
end Sheshadri.FiniteCurveExtension
