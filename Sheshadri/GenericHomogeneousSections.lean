/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.RegularPrimeAvoidance
import Sheshadri.HomogeneousQuotientExact
import Sheshadri.HilbertPolynomialExistence
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Generic homogeneous sections and actual Hilbert differences

A finite homogeneous linear system whose common annihilator in the actual
coordinate quotient is zero has a regular scalar combination. The exceptional
scalar parameters form a finite set, proved using associated primes. In
particular this applies to hyperplanes on an irrelevant-saturated quotient.

The Hilbert-polynomial difference theorem below only requires injectivity in
sufficiently high homogeneous degrees, allowing irrelevant torsion in the
original quotient. It is proved from the actual multiplication exact sequence.
-/

noncomputable section
namespace Sheshadri.GenericHomogeneousSections
open MvPolynomial FlatGradedHilbert HomogeneousQuotientExact

variable {Z K : Type*} [Field K]

/-- An explicit one-parameter scalar combination of a finite linear system. -/
def combination (fs : List (MvPolynomial Z K)) (a : K) : MvPolynomial Z K :=
  Polynomial.eval (C a) (RegularPrimeAvoidance.listPolynomial fs)

@[simp] theorem combination_nil (a : K) : combination ([] : List (MvPolynomial Z K)) a = 0 := by
  simp [combination, RegularPrimeAvoidance.listPolynomial]

@[simp] theorem combination_cons (f : MvPolynomial Z K) (fs : List (MvPolynomial Z K))
    (a : K) : combination (f :: fs) a = f + a • combination fs a := by
  simp [combination, RegularPrimeAvoidance.listPolynomial, Algebra.smul_def]

theorem combination_homogeneous (fs : List (MvPolynomial Z K)) (d : ℕ)
    (hfs : ∀ f ∈ fs, f.IsHomogeneous d) (a : K) :
    (combination fs a).IsHomogeneous d := by
  induction fs with
  | nil => simp only [combination_nil]; exact isHomogeneous_zero Z K d
  | cons f fs ih =>
    rw [combination_cons]
    apply (hfs f (by simp)).add
    simpa only [Algebra.smul_def, MvPolynomial.algebraMap_eq, zero_add] using
      (isHomogeneous_C Z a).mul (ih (fun g hg => hfs g (by simp [hg])))

theorem combination_mem_linearSpan (fs : List (MvPolynomial Z K)) (a : K) :
    combination fs a ∈ Submodule.span K {f | f ∈ fs} := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    rw [combination_cons]
    apply Submodule.add_mem
    · exact Submodule.subset_span (by simp)
    · exact Submodule.smul_mem _ _
        ((Submodule.span_mono (by intro g hg; simp_all)) ih)

/-- Saturation by the displayed linear system means its common annihilator
in the actual quotient is zero. This is the usual ideal-colon condition. -/
def IsSystemSaturated (I : Ideal (MvPolynomial Z K)) (fs : List (MvPolynomial Z K)) : Prop :=
  ∀ q, (∀ f ∈ fs, f * q ∈ I) → q ∈ I

/-- No associated prime can contain a linear system with zero common
annihilator. This implication is proved on the literal equation quotient. -/
theorem associatedPrime_avoids_system (I : Ideal (MvPolynomial Z K))
    (fs : List (MvPolynomial Z K)) (hsat : IsSystemSaturated I fs)
    (p : Ideal (MvPolynomial Z K)) (hp : p ∈ associatedPrimes _ (QuotientRing I)) :
    ¬ Ideal.ofList fs ≤ p := by
  intro hle
  obtain ⟨z, hz⟩ := hp.2
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hq : q ∈ I := hsat q (by
    intro f hf
    have hfp := hle (Ideal.subset_span hf)
    rw [hz, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hfp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk I f * Ideal.Quotient.mk I q = 0 at hfp
    simpa only [map_mul] using hfp)
  have hzero : Ideal.Quotient.mk I q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hq
  apply hp.isPrime.ne_top
  simpa [hzero] using hz

variable [Finite Z]

/-- The bad scalar combinations are a finite set. This is an actual generic
selection result, not a supplied regular-section certificate. -/
theorem finite_nonregular_parameters_of_avoid (I : Ideal (MvPolynomial Z K))
    (fs : List (MvPolynomial Z K))
    (havoid : ∀ p ∈ associatedPrimes _ (QuotientRing I), ¬ Ideal.ofList fs ≤ p) :
    {a : K | ¬ IsSMulRegular (QuotientRing I) (combination fs a)}.Finite := by
  classical
  let bad (p : Ideal (MvPolynomial Z K)) : Set K :=
    {a | combination fs a ∈ p}
  have hbad : (⋃ p ∈ associatedPrimes _ (QuotientRing I), bad p).Finite :=
    (RegularPrimeAvoidance.finite_associatedPrimes (R := MvPolynomial Z K)
      (M := QuotientRing I)).biUnion fun p hp =>
        RegularPrimeAvoidance.finite_bad_scalars K p hp.isPrime fs
          (havoid p hp)
  apply hbad.subset
  intro a ha
  have hh : combination fs a ∈ ⋃ p ∈ associatedPrimes (MvPolynomial Z K) (QuotientRing I),
      (p : Set (MvPolynomial Z K)) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact ha
  obtain ⟨p, hp, hmem⟩ := Set.mem_iUnion₂.mp hh
  exact Set.mem_iUnion₂.mpr ⟨p, hp, hmem⟩

theorem finite_nonregular_parameters (I : Ideal (MvPolynomial Z K))
    (fs : List (MvPolynomial Z K)) (hsat : IsSystemSaturated I fs) :
    {a : K | ¬ IsSMulRegular (QuotientRing I) (combination fs a)}.Finite :=
  finite_nonregular_parameters_of_avoid I fs (associatedPrime_avoids_system I fs hsat)

omit [Finite Z] in
theorem quotient_regular_of_smulRegular (I : Ideal (MvPolynomial Z K))
    (g : MvPolynomial Z K) (hg : IsSMulRegular (QuotientRing I) g) :
    IsRegular (Ideal.Quotient.mk I g) := by
  apply (Commute.isRegular_iff (fun _ => Commute.all _ _)).mpr
  exact hg

/-- Over an infinite field a saturated homogeneous linear system contains
an actual regular homogeneous polynomial in its coefficient-field span. -/
theorem exists_regular_homogeneous_combination [Infinite K]
    (I : Ideal (MvPolynomial Z K)) (fs : List (MvPolynomial Z K)) (d : ℕ)
    (hfs : ∀ f ∈ fs, f.IsHomogeneous d) (hsat : IsSystemSaturated I fs) :
    ∃ g : MvPolynomial Z K, g ∈ Submodule.span K {f | f ∈ fs} ∧
      g.IsHomogeneous d ∧ IsRegular (Ideal.Quotient.mk I g) := by
  obtain ⟨a, ha⟩ := (finite_nonregular_parameters I fs hsat).exists_not_mem
  exact ⟨combination fs a, combination_mem_linearSpan fs a,
    combination_homogeneous fs d hfs a, quotient_regular_of_smulRegular I _ (not_not.mp ha)⟩

theorem exists_regular_homogeneous_combination_of_avoid [Infinite K]
    (I : Ideal (MvPolynomial Z K)) (fs : List (MvPolynomial Z K)) (d : ℕ)
    (hfs : ∀ f ∈ fs, f.IsHomogeneous d)
    (havoid : ∀ p ∈ associatedPrimes _ (QuotientRing I), ¬ Ideal.ofList fs ≤ p) :
    ∃ g : MvPolynomial Z K, g ∈ Submodule.span K {f | f ∈ fs} ∧
      g.IsHomogeneous d ∧ IsRegular (Ideal.Quotient.mk I g) := by
  obtain ⟨a, ha⟩ := (finite_nonregular_parameters_of_avoid I fs havoid).exists_not_mem
  exact ⟨combination fs a, combination_mem_linearSpan fs a,
    combination_homogeneous fs d hfs a, quotient_regular_of_smulRegular I _ (not_not.mp ha)⟩

/-- The ordinary irrelevant-saturation condition, stated directly in
coordinates, without a geometric or numerical certificate. -/
def IsIrrelevantSaturated (I : Ideal (MvPolynomial Z K)) : Prop :=
  ∀ q, (∀ i, X i * q ∈ I) → q ∈ I

omit [Finite Z] in
/-- An associated prime of an irrelevant-saturated quotient omits at least
one coordinate. The vertex therefore cannot be an associated component. -/
theorem associatedPrime_omits_coordinate (I : Ideal (MvPolynomial Z K))
    (hsat : IsIrrelevantSaturated I) (p : Ideal (MvPolynomial Z K))
    (hp : p ∈ associatedPrimes _ (QuotientRing I)) : ∃ i, X i ∉ p := by
  classical
  by_contra h
  have hall : ∀ i, X i ∈ p := by simpa using h
  obtain ⟨z, hz⟩ := hp.2
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hq : q ∈ I := hsat q (by
    intro i
    have hi := hall i
    rw [hz, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hi
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk I (X i) * Ideal.Quotient.mk I q = 0 at hi
    simpa only [map_mul] using hi)
  have hzero : Ideal.Quotient.mk I q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hq
  exact hp.isPrime.ne_top (by simpa [hzero] using hz)

/-- A homogeneous system whose radical contains all coordinates has a
generic regular member on every irrelevant-saturated equation quotient.
This applies to the derivative system of a smooth homogeneous hypersurface. -/
theorem exists_regular_homogeneous_of_radical [Infinite K]
    (I : Ideal (MvPolynomial Z K)) (hsat : IsIrrelevantSaturated I)
    (fs : List (MvPolynomial Z K)) (d : ℕ)
    (hfs : ∀ f ∈ fs, f.IsHomogeneous d)
    (hrad : ∀ i, X i ∈ (Ideal.ofList fs).radical) :
    ∃ g : MvPolynomial Z K, g ∈ Submodule.span K {f | f ∈ fs} ∧
      g.IsHomogeneous d ∧ IsRegular (Ideal.Quotient.mk I g) := by
  apply exists_regular_homogeneous_combination_of_avoid I fs d hfs
  intro p hp hle
  obtain ⟨i, hi⟩ := associatedPrime_omits_coordinate I hsat p hp
  apply hi
  have hr : (Ideal.ofList fs).radical ≤ p := by
    simpa only [hp.isPrime.isRadical.radical] using Ideal.radical_mono hle
  exact hr (hrad i)

theorem exists_regular_hyperplane [Infinite K]
    (I : Ideal (MvPolynomial Z K)) (hsat : IsIrrelevantSaturated I) :
    ∃ g : MvPolynomial Z K, g.IsHomogeneous 1 ∧ IsRegular (Ideal.Quotient.mk I g) := by
  classical
  letI : Fintype Z := Fintype.ofFinite Z
  let fs := (Finset.univ.toList : List Z).map (fun i => (X i : MvPolynomial Z K))
  have hfs : ∀ f ∈ fs, f.IsHomogeneous 1 := by
    intro f hf
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
    exact isHomogeneous_X K i
  have hsys : IsSystemSaturated I fs := by
    intro q hq
    apply hsat q
    intro i
    exact hq (X i) (List.mem_map.mpr ⟨i, by simp, rfl⟩)
  obtain ⟨g, _, hg, hreg⟩ := exists_regular_homogeneous_combination I fs 1 hfs hsys
  exact ⟨g, hg, hreg⟩

/-- Filter regularity: the actual multiplication maps are injective in all
sufficiently large degrees. Torsion in low degrees is permitted. -/
def FilterRegular (I : Ideal (MvPolynomial Z K)) (g : MvPolynomial Z K)
    {d : ℕ} (hg : g.IsHomogeneous d) : Prop :=
  ∃ N : ℕ, ∀ k, N ≤ k → Function.Injective (pieceMultiplication I g hg k)

theorem regular_filterRegular (I : Ideal (MvPolynomial Z K)) (g : MvPolynomial Z K)
    {d : ℕ} (hg : g.IsHomogeneous d) (hreg : IsRegular (Ideal.Quotient.mk I g)) :
    FilterRegular I g hg :=
  ⟨0, fun k _ => pieceMultiplication_injective I g hg hreg k⟩

theorem coordinate_finrank_difference_of_piece_injective
    (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I)
    (g : MvPolynomial Z K) {d : ℕ} (hg : g.IsHomogeneous d) (k : ℕ)
    (hinj : Function.Injective (pieceMultiplication I g hg k)) :
    Module.finrank K (coordinatePiece Z K (enlargedIdeal I g) (d + k)) +
      Module.finrank K (coordinatePiece Z K I k) =
        Module.finrank K (coordinatePiece Z K I (d + k)) := by
  have h := (pieceProjection I g (d + k)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (pieceProjection_surjective I g (d + k)),
    finrank_top, piece_kernel_eq_range I hI g hg k,
    LinearMap.finrank_range_of_inj hinj] at h
  exact h

/-- The actual Hilbert-polynomial difference law remains valid for
filter-regular sections. No global regular sequence is required. -/
theorem hilbert_polynomial_difference_of_filterRegular
    (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I)
    (g : MvPolynomial Z K) {d : ℕ} (hg : g.IsHomogeneous d)
    (hreg : FilterRegular I g hg)
    (P Q : Polynomial ℚ)
    (hP : ∃ N : ℕ, ∀ k > N,
      (Module.finrank K (coordinatePiece Z K I k) : ℚ) = P.eval (k : ℚ))
    (hQ : ∃ N : ℕ, ∀ k > N,
      (Module.finrank K (coordinatePiece Z K (enlargedIdeal I g) k) : ℚ) = Q.eval (k : ℚ)) :
    Q = P - P.comp (Polynomial.X - Polynomial.C (d : ℚ)) := by
  obtain ⟨N, hP⟩ := hP
  obtain ⟨M, hQ⟩ := hQ
  obtain ⟨B, hB⟩ := hreg
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Ioi_infinite (max (max N M) B + d)).image
    (Nat.cast_injective (R := ℚ)).injOn).mono
  rintro x ⟨k, hk, rfl⟩
  change max (max N M) B + d < k at hk
  have hdk : d ≤ k := by omega
  have hrec := coordinate_finrank_difference_of_piece_injective I hI g hg (k-d)
    (hB (k-d) (by omega))
  rw [Nat.add_sub_of_le hdk] at hrec
  have heq : (Module.finrank K (coordinatePiece Z K (enlargedIdeal I g) k) : ℚ) +
      (Module.finrank K (coordinatePiece Z K I (k-d)) : ℚ) =
        (Module.finrank K (coordinatePiece Z K I k) : ℚ) := by exact_mod_cast hrec
  rw [hQ k (by omega), hP (k-d) (by omega), hP k (by omega), Nat.cast_sub hdk] at heq
  simpa only [Set.mem_setOf_eq, Polynomial.eval_sub, Polynomial.eval_comp,
    Polynomial.eval_X, Polynomial.eval_C] using (eq_sub_iff_add_eq.mpr heq)

end Sheshadri.GenericHomogeneousSections
