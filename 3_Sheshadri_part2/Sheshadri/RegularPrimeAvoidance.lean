/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Scalar prime avoidance for regular elements

The associated primes of a finite Noetherian module form a finite set.  Over an
infinite coefficient field this makes it possible to adjust the first member of
a generating list by a scalar combination of the remaining members, obtaining
a regular element whenever their ideal contains one.
-/

namespace Sheshadri.RegularPrimeAvoidance

open LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Finiteness of associated primes, proved by Noetherian induction on
submodules and a prime cyclic submodule of each nonzero quotient. -/
theorem finite_associatedPrimes [IsNoetherianRing R] [IsNoetherian R M] :
    (associatedPrimes R M).Finite := by
  have h : ∀ N : Submodule R M, (associatedPrimes R (M ⧸ N)).Finite := by
    apply IsNoetherian.induction
    intro N ih
    by_cases hN : N = ⊤
    · subst N
      rw [associatedPrimes.eq_empty_of_subsingleton]
      exact Set.finite_empty
    haveI : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_of_lt_top N (lt_top_iff_ne_top.mpr hN)
    obtain ⟨p, hp⟩ := associatedPrimes.nonempty R (M ⧸ N)
    obtain ⟨hpp, f, hf⟩ := (isAssociatedPrime_iff_exists_injective_linearMap p (M ⧸ N)).mp hp
    letI : p.IsPrime := hpp
    let T : Submodule R M := (LinearMap.range f).comap N.mkQ
    have hNT : N ≤ T := Submodule.le_comap_mkQ _ _
    have hstrict : N < T := by
      refine lt_of_le_of_ne hNT ?_
      intro heq
      have hfbot : LinearMap.range f = ⊥ := by
        have hh := congrArg (Submodule.map N.mkQ) heq
        simp only [T, Submodule.map_comap_eq, N.range_mkQ, inf_top_eq, top_inf_eq,
          Submodule.mkQ_map_self] at hh
        exact hh.symm
      have hz : f 1 = f 0 := by
        rw [f.map_zero]
        simp [LinearMap.range_eq_bot.mp hfbot]
      exact one_ne_zero (hf hz)
    have hfin := ih T hstrict
    let g : (M ⧸ N) →ₗ[R] M ⧸ T := Submodule.factor hNT
    have hfg : Function.Exact f g := by
      rw [Function.Exact]
      intro x
      obtain ⟨y, rfl⟩ := N.mkQ_surjective x
      change T.mkQ y = 0 ↔ ∃ a, f a = N.mkQ y
      change Submodule.Quotient.mk y = (0 : M ⧸ T) ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      rfl
    have hassoc : associatedPrimes R (R ⧸ p) = {p} := by
      simpa [hpp.isRadical.radical] using (associatedPrimes.eq_singleton_of_isPrimary hpp.isPrimary)
    exact (Set.Finite.union (hassoc ▸ Set.finite_singleton p) hfin).subset
      (associatedPrimes.subset_union_of_exact hf hfg)
  have he := LinearEquiv.AssociatedPrimes.eq ((⊥ : Submodule R M).quotEquivOfEqBot rfl)
  exact he ▸ h ⊥

open Polynomial

/-- A generating list regarded as the coefficients of a polynomial. -/
noncomputable def listPolynomial : List R → R[X]
  | [] => 0
  | x :: xs => C x + X * listPolynomial xs

lemma listPolynomial_map {S : Type*} [CommRing S] (φ : R →+* S) (xs : List R) :
    (listPolynomial xs).map φ = listPolynomial (xs.map φ) := by
  induction xs with
  | nil => simp [listPolynomial]
  | cons x xs ih => simp [listPolynomial, ih]

lemma listPolynomial_eq_zero_iff (xs : List R) :
    listPolynomial xs = 0 ↔ ∀ x ∈ xs, x = 0 := by
  induction xs with
  | nil => simp [listPolynomial]
  | cons x xs ih =>
    constructor
    · intro h
      have hx : x = 0 := by
        simpa [listPolynomial] using congrArg (fun p : R[X] => p.coeff 0) h
      have ht : listPolynomial xs = 0 := by
        ext n
        have hh := congrArg (fun p : R[X] => p.coeff (n + 1)) h
        simpa [listPolynomial, hx, Polynomial.coeff_X_mul] using hh
      simpa [hx] using ih.mp ht
    · intro h
      have hx : x = 0 := h x (by simp)
      have ht : listPolynomial xs = 0 := ih.mpr (fun a ha => h a (by simp [ha]))
      simp [listPolynomial, hx, ht]

lemma eval_listPolynomial_mem (xs : List R) (a : R) :
    Polynomial.eval a (listPolynomial xs) ∈ Ideal.ofList xs := by
  induction xs with
  | nil => simp [listPolynomial]
  | cons x xs ih =>
    simp only [listPolynomial, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, Ideal.ofList_cons]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.subset_span (by simp)))
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ ih))

variable (K : Type*) [Field K] [Infinite K] [Algebra K R]

omit [Infinite K] in
/-- A polynomial with coefficients not all in a proper prime has only finitely
many coefficient-field parameters whose value belongs to that prime. -/
lemma finite_bad_scalars (p : Ideal R) (hp : p.IsPrime) (xs : List R)
    (hxs : ¬ Ideal.ofList xs ≤ p) :
    {a : K | Polynomial.eval (algebraMap K R a) (listPolynomial xs) ∈ p}.Finite := by
  letI : p.IsPrime := hp
  let q : (R ⧸ p)[X] := (listPolynomial xs).map (Ideal.Quotient.mk p)
  have hq : q ≠ 0 := by
    intro hz
    have hall : ∀ x ∈ xs, x ∈ p := by
      have hh := (listPolynomial_eq_zero_iff (xs.map (Ideal.Quotient.mk p))).mp
        ((listPolynomial_map (Ideal.Quotient.mk p) xs) ▸ hz)
      intro x hx
      exact Ideal.Quotient.eq_zero_iff_mem.mp (hh _ (List.mem_map.mpr ⟨x, hx, rfl⟩))
    exact hxs (Ideal.span_le.mpr hall)
  have hinj : Function.Injective (algebraMap K (R ⧸ p)) :=
    (algebraMap K (R ⧸ p)).injective
  have hfin := Set.Finite.preimage hinj.injOn (Polynomial.finite_setOf_isRoot hq)
  convert hfin using 1
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Polynomial.IsRoot, q]
  rw [Polynomial.eval_map, ← Ideal.Quotient.eq_zero_iff_mem]
  rw [IsScalarTower.algebraMap_apply K R (R ⧸ p)]
  change _ ↔ Polynomial.eval₂ (Ideal.Quotient.mk p)
    (Ideal.Quotient.mk p (algebraMap K R a)) (listPolynomial xs) = 0
  rw [Polynomial.eval₂_at_apply]


include K

/-- Over an infinite coefficient field, if the generators avoid being contained
in any associated prime, their first member can be made regular by adding an
element of the ideal of the remaining members. The construction uses an actual
scalar specialization of the list's coefficient polynomial. -/
theorem exists_regular_head_mod_tail [IsNoetherianRing R] [IsNoetherian R M]
    (x : R) (xs : List R)
    (havoid : ∀ p ∈ associatedPrimes R M, ¬ Ideal.ofList (x :: xs) ≤ p) :
    ∃ h : R, h - x ∈ Ideal.ofList xs ∧ IsSMulRegular M h := by
  classical
  let bad (p : Ideal R) : Set K :=
    {a | Polynomial.eval (algebraMap K R a) (listPolynomial (x :: xs)) ∈ p}
  have hbad : (⋃ p ∈ associatedPrimes R M, bad p).Finite :=
    (finite_associatedPrimes (R := R) (M := M)).biUnion fun p hp =>
      finite_bad_scalars K p hp.isPrime (x :: xs) (havoid p hp)
  obtain ⟨a, ha⟩ := Set.Finite.exists_not_mem hbad
  let h := Polynomial.eval (algebraMap K R a) (listPolynomial (x :: xs))
  refine ⟨h, ?_, ?_⟩
  · simp only [h, listPolynomial, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, add_sub_cancel_left]
    exact Ideal.mul_mem_left _ _ (eval_listPolynomial_mem xs _)
  · by_contra hh
    have hin : h ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
      rw [biUnion_associatedPrimes_eq_compl_regular]
      exact hh
    obtain ⟨p, hp, hh⟩ := Set.mem_iUnion₂.mp hin
    exact ha (Set.mem_iUnion₂.mpr ⟨p, hp, hh⟩)


/-- The regular-element version of scalar prime avoidance. Membership is allowed
modulo the module annihilator, so the statement applies directly to successive
quotient modules without changing the coefficient ring. -/
theorem exists_regular_head_mod_tail_of_regular_mem [IsNoetherianRing R]
    [IsNoetherian R M] (x : R) (xs : List R) (g : R)
    (hg : IsSMulRegular M g)
    (hmem : g ∈ Ideal.ofList (x :: xs) ⊔ Module.annihilator R M) :
    ∃ h : R, h - x ∈ Ideal.ofList xs ∧ IsSMulRegular M h := by
  apply exists_regular_head_mod_tail K x xs
  intro p hp hle
  have hann : Module.annihilator R M ≤ p := by
    simpa only [Submodule.annihilator_top] using hp.annihilator_le
  have hgp : g ∈ p := (sup_le hle hann) hmem
  have hin : g ∈ ⋃ q ∈ associatedPrimes R M, (q : Set R) :=
    Set.mem_iUnion₂.mpr ⟨p, hp, hgp⟩
  rw [biUnion_associatedPrimes_eq_compl_regular] at hin
  exact hin hg

end Sheshadri.RegularPrimeAvoidance
