/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Invariant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Going down over normal domains in characteristic zero

Finite injective extensions of characteristic-zero domains satisfy going
down when the base is integrally closed. We construct a finite Galois
overfield from the fraction fields, use prime transitivity for its integral
closure, and contract the resulting prime chain. No going-down hypothesis
or normality assumption on the upper domain is imposed.
-/

noncomputable section
namespace Sheshadri.NormalGoingDown

open scoped Pointwise

theorem of_finite_invariant
    (R S G : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
    [Algebra.IsInvariant R S G] (hinj : Function.Injective (algebraMap R S)) :
    Algebra.HasGoingDown R S := by
  letI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral R S G
  constructor
  intro p hp Q hQ hpQ
  have hker : RingHom.ker (algebraMap R S) ≤ p := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨P, _, hP, hPp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S) p ⊥ hker
  letI := hP
  obtain ⟨Q', hPQ', hQ', hQ'Q⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := S) (Q.under R) P (hPp.le.trans hpQ.le)
  letI := hQ'
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq R S G Q' Q hQ'Q
  refine ⟨g • P, ?_, inferInstance, ⟨?_⟩⟩
  · rw [hg]
    exact smul_mono_right g hPQ'
  · rw [Ideal.under_smul]
    exact hPp.symm

/-- An integral injective overring with going down supplies going down for
the original extension by contracting the lifted prime chain. -/
theorem descend_integral_overring
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.IsIntegral S T] [Algebra.HasGoingDown R T]
    (hinj : Function.Injective (algebraMap S T)) : Algebra.HasGoingDown R S := by
  constructor
  intro p hp Q hQ hpQ
  have hker : RingHom.ker (algebraMap S T) ≤ Q := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨Q', _, hQ', hQ'Q⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := T) Q ⊥ hker
  letI := hQ'
  have hQ'R : Q'.under R = Q.under R := by
    rw [← Ideal.under_under (A := R) (B := S) Q']
    exact congrArg (Ideal.under R) hQ'Q
  obtain ⟨P', hPQ', hP', hP'p⟩ :=
    Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt Q' (hQ'R.symm ▸ hpQ)
  letI := hP'
  refine ⟨P'.under S, ?_, inferInstance, ⟨?_⟩⟩
  · rw [← hQ'Q]
    exact Ideal.comap_mono hPQ'
  · rw [Ideal.under_under]
    exact hP'p.over

/-- A finite algebra of domains induces a finite extension of fraction fields.
This argument transports a finite module spanning set, without requiring the
upper domain to be integrally closed. -/
theorem fractionField_finite
    (R S K L : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Field K] [Field L] [Algebra R S] [Algebra R K] [Algebra R L]
    [Algebra S L] [Algebra K L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsFractionRing S L] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R L)) : FiniteDimensional K L := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := R) (M := S))
  refine ⟨⟨s.image (algebraMap S L), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  intro x _
  apply IsFractionRing.ideal_span_singleton_map_subset (R := R) (K := K)
    (a := (1 : S)) (b := (s : Set S)) hinj
  · rw [hs]
    exact Set.subset_univ _
  · simp

/-- The integral closure of a normal domain in a finite Galois extension
of its fraction field satisfies going down. -/
theorem integralClosure_of_galois
    (R K L B : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Field L] [CommRing B] [IsDomain B]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [Algebra R B] [Algebra B L] [IsScalarTower R B L]
    [IsIntegralClosure B R L] [FiniteDimensional K L] [IsGalois K L] :
    Algebra.HasGoingDown R B := by
  letI : IsFractionRing B L := IsIntegralClosure.isFractionRing_of_finite_extension R K L B
  letI : Finite (B ≃ₐ[R] B) :=
    Finite.of_equiv (L ≃ₐ[K] L) (galRestrict R K L B).toEquiv
  letI := Algebra.isInvariant_of_isGalois' R K L B
  apply of_finite_invariant R B (B ≃ₐ[R] B)
  intro r s hrs
  apply (IsFractionRing.injective R K)
  apply (algebraMap K L).injective
  simpa only [← IsScalarTower.algebraMap_apply R K L,
    IsScalarTower.algebraMap_apply R B L] using congrArg (algebraMap B L) hrs

/-- A finite Galois overfield supplies the normal-base going-down theorem
for any integral domain embedded in it. -/
theorem of_galois_overfield
    (R S K L : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [Field K] [Field L]
    [Algebra R S] [Algebra R K] [IsFractionRing R K]
    [Algebra R L] [Algebra K L] [Algebra S L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    [Algebra.IsIntegral R S] [FiniteDimensional K L] [IsGalois K L]
    (hinj : Function.Injective (algebraMap S L)) : Algebra.HasGoingDown R S := by
  let C := integralClosure R L
  let f : S →ₐ[R] C := (IsScalarTower.toAlgHom R S L).codRestrict C
    (fun s => (Algebra.IsIntegral.isIntegral (R := R) s).map
      (IsScalarTower.toAlgHom R S L))
  letI : Algebra S C := f.toRingHom.toAlgebra
  letI : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq (fun r => (f.commutes r).symm)
  letI : Algebra.IsIntegral S C := Algebra.IsIntegral.tower_top (R := R)
  letI : Algebra.HasGoingDown R C := integralClosure_of_galois R K L C
  apply descend_integral_overring R S C
  intro s t hst
  apply hinj
  exact congrArg (fun c : C => (c : L)) hst

/-- A finite injective extension of characteristic-zero domains has going
down when the base is integrally closed. The finite Galois overfield is
constructed, rather than assumed. -/
theorem finite_of_integrallyClosed
    (R S : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (hinj : Function.Injective (algebraMap R S)) : Algebra.HasGoingDown R S := by
  let K := FractionRing R
  let E := FractionRing S
  letI : NoZeroSMulDivisors R S := (NoZeroSMulDivisors.iff_algebraMap_injective).mpr hinj
  letI : NoZeroSMulDivisors R E := NoZeroSMulDivisors.trans_faithfulSMul R S E
  letI : Algebra K E := FractionRing.liftAlgebra R E
  letI : IsScalarTower R K E := FractionRing.isScalarTower_liftAlgebra R E
  have hinjRE : Function.Injective (algebraMap R E) :=
    FaithfulSMul.algebraMap_injective R E
  letI : FiniteDimensional K E := fractionField_finite R S K E hinjRE
  let L := AlgebraicClosure K
  let f : E →ₐ[K] L := IsAlgClosed.lift
  letI : Algebra E L := f.toRingHom.toAlgebra
  letI : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq (fun k => (f.commutes k).symm)
  let N := IntermediateField.normalClosure K E L
  letI : Algebra R N := ((algebraMap K N).comp (algebraMap R K)).toAlgebra
  letI : IsScalarTower R K N := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra S N := ((algebraMap E N).comp (algebraMap S E)).toAlgebra
  letI : IsScalarTower S E N := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R S N := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap K N (algebraMap R K r) =
      algebraMap E N (algebraMap S E (algebraMap R S r))
    rw [← IsScalarTower.algebraMap_apply R S E,
      IsScalarTower.algebraMap_apply R K E,
      ← IsScalarTower.algebraMap_apply K E N])
  exact of_galois_overfield R S K N
    ((algebraMap E N).injective.comp (IsFractionRing.injective S E))

end Sheshadri.NormalGoingDown
