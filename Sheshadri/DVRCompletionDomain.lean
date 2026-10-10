/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # The actual completion of a DVR is a domain

A product of nonzero compatible residues is detected in a finite quotient:
bounded uniformizer valuations add. No domain or field property of the
completion is assumed.
-/

noncomputable section
namespace Sheshadri.DVRCompletionDomain
open scoped Pointwise
open AdicCompletion
set_option maxHeartbeats 800000

variable {D : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    (π : D) (hπ : Irreducible π)

include hπ in
theorem not_dvd_product {a b : D} {r s : ℕ}
    (ha : ¬ π ^ r ∣ a) (hb : ¬ π ^ s ∣ b) : ¬ π ^ (r+s) ∣ a*b := by
  have hval (x : D) (n : ℕ) : π ^ n ∣ x ↔ (n : WithTop ℕ) ≤ IsDiscreteValuationRing.addVal D x := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hπ.addVal_pow]
  have hra := lt_of_not_ge ((hval a r).not.mp ha)
  have hsb := lt_of_not_ge ((hval b s).not.mp hb)
  intro hab
  have hge := (hval (a*b) (r+s)).mp hab
  rw [IsDiscreteValuationRing.addVal_mul] at hge
  obtain ⟨i, hi⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hra)
  obtain ⟨j, hj⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hsb)
  rw [← hi] at hra hge
  rw [← hj] at hsb hge
  have hi' : i < r := WithTop.coe_lt_coe.mp hra
  have hj' : j < s := WithTop.coe_lt_coe.mp hsb
  have hij : r+s ≤ i+j := WithTop.coe_le_coe.mp (by simpa using hge)
  omega

private theorem exists_nonzero_component {I : Ideal D} (x : AdicCauchySequence I D)
    (hx : AdicCompletion.mk I D x ≠ 0) : ∃ n, Ideal.Quotient.mk (I^n) (x n) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hx
  apply AdicCompletion.ext
  intro n
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change x n ∈ I^n • (⊤ : Ideal D)
  simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using
    (Ideal.Quotient.eq_zero_iff_mem.mp (h n))

include hπ in
/-- Nonzero elements of the actual inverse-limit completion have nonzero product. -/
theorem completion_mul_ne_zero (x y : AdicCompletion (Ideal.span {π}) D)
    (hx : x ≠ 0) (hy : y ≠ 0) : x*y ≠ 0 := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {π}) D x
  obtain ⟨b, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {π}) D y
  obtain ⟨r, hr⟩ := exists_nonzero_component a hx
  obtain ⟨s, hs⟩ := exists_nonzero_component b hy
  have ha : ¬ π^r ∣ a (r+s) := by
    intro ha
    apply hr
    rw [← AdicCompletion.Ideal.mk_eq_mk (Ideal.span {π}) (Nat.le_add_right r s) a]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact ha
  have hb : ¬ π^s ∣ b (r+s) := by
    intro hb
    apply hs
    rw [← AdicCompletion.Ideal.mk_eq_mk (Ideal.span {π}) (Nat.le_add_left s r) b]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact hb
  intro hxy
  have h := congrArg (AdicCompletion.evalₐ (Ideal.span {π}) (r+s)) hxy
  rw [map_mul, map_zero, AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk,
    ← map_mul] at h
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp h
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
  exact not_dvd_product π hπ ha hb hmem

include hπ in
theorem completion_isDomain : IsDomain (AdicCompletion (Ideal.span {π}) D) := by
  let I : Ideal D := Ideal.span {π}
  have hI : I ≠ ⊤ := by
    exact fun h => hπ.not_isUnit (Ideal.span_singleton_eq_top.mp h)
  letI : Nontrivial (D ⧸ I) := Ideal.Quotient.nontrivial hI
  have hsurj : Function.Surjective (AdicCompletion.evalₐ I 1) := by
    intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨algebraMap D _ a, rfl⟩
  letI : Nontrivial (D ⧸ I^1) := by simpa only [pow_one] using
    (inferInstance : Nontrivial (D ⧸ I))
  letI : Nontrivial (AdicCompletion I D) := hsurj.nontrivial
  letI : NoZeroDivisors (AdicCompletion (Ideal.span {π}) D) :=
    ⟨fun {x y} h => by
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr (Classical.byContradiction (fun hy => completion_mul_ne_zero π hπ x y hx hy h))⟩
  exact NoZeroDivisors.to_isDomain _

end Sheshadri.DVRCompletionDomain
