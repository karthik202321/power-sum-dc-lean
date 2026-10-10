/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.GenericHomogeneousSections
import Sheshadri.ProjectiveChartHilbertBound
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Ideal.Colon

/-! # The actual irrelevant saturation

The ideal below is the intersection of contractions from the standard
coordinate opens. Membership, idempotence, homogeneous closure, and a
uniform coordinate-power annihilator are proved for this actual ideal.
-/

noncomputable section
namespace Sheshadri.IrrelevantSaturation
open MvPolynomial GenericHomogeneousSections

variable {σ K : Type*} [Finite σ] [Field K]

lemma pow_mul_mem_mono (I : Ideal (MvPolynomial σ K)) (i : σ)
    {q : MvPolynomial σ K} {n m : ℕ} (hnm : n ≤ m)
    (hq : X i ^ n * q ∈ I) : X i ^ m * q ∈ I := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using
    I.mul_mem_left (X i ^ k) hq

/-- Contraction from every coordinate open, hence saturation by the
irrelevant ideal. The existential exponents may initially depend on i. -/
def saturation (I : Ideal (MvPolynomial σ K)) : Ideal (MvPolynomial σ K) where
  carrier := {q | ∀ i : σ, ∃ n : ℕ, X i ^ n * q ∈ I}
  zero_mem' := by intro i; exact ⟨0, by simp⟩
  add_mem' := by
    intro p q hp hq i
    obtain ⟨n, hn⟩ := hp i
    obtain ⟨m, hm⟩ := hq i
    refine ⟨max n m, ?_⟩
    simpa [mul_add] using I.add_mem
      (pow_mul_mem_mono I i (le_max_left _ _) hn)
      (pow_mul_mem_mono I i (le_max_right _ _) hm)
  smul_mem' := by
    intro r q hq i
    obtain ⟨n, hn⟩ := hq i
    refine ⟨n, ?_⟩
    simpa [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using I.mul_mem_left r hn

@[simp] theorem mem_saturation (I : Ideal (MvPolynomial σ K)) (q) :
    q ∈ saturation I ↔ ∀ i : σ, ∃ n : ℕ, X i ^ n * q ∈ I := Iff.rfl

theorem le_saturation (I : Ideal (MvPolynomial σ K)) : I ≤ saturation I := by
  intro q hq i
  exact ⟨0, by simpa using hq⟩

theorem saturation_mono {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J) :
    saturation I ≤ saturation J := by
  intro q hq i
  obtain ⟨n, hn⟩ := hq i
  exact ⟨n, h hn⟩

theorem saturation_isSaturated (I : Ideal (MvPolynomial σ K)) :
    IsIrrelevantSaturated (saturation I) := by
  intro q hq i
  obtain ⟨n, hn⟩ := hq i i
  exact ⟨n+1, by simpa [pow_succ, mul_assoc] using hn⟩

@[simp] theorem saturation_idempotent (I : Ideal (MvPolynomial σ K)) :
    saturation (saturation I) = saturation I := by
  apply le_antisymm _ (le_saturation _)
  intro q hq i
  obtain ⟨n, hn⟩ := hq i
  obtain ⟨m, hm⟩ := hn i
  exact ⟨m+n, by simpa [pow_add, mul_assoc] using hm⟩

/-- Every homogeneous component belongs to the same actual saturation. -/
theorem saturation_homogeneous (I : Ideal (MvPolynomial σ K))
    (hI : ∀ d p, p ∈ I → homogeneousComponent d p ∈ I) :
    ∀ d p, p ∈ saturation I → homogeneousComponent d p ∈ saturation I := by
  intro d p hp i
  obtain ⟨n, hn⟩ := hp i
  refine ⟨n, ?_⟩
  have hx : (X i ^ n : MvPolynomial σ K).IsHomogeneous n := by
    simpa using (isHomogeneous_X K i).pow n
  have hc := hI (n+d) (X i ^ n * p) hn
  change weightedHomogeneousComponent (fun _ : σ => (1 : ℕ)) (n+d) (X i ^ n * p) ∈ I at hc
  rw [ProjectiveChartHilbertBound.component_mul_left (fun _ : σ => (1 : ℕ)) hx] at hc
  exact hc

/-- A single exponent works for every element of the saturation at a
fixed coordinate; this uses finite generation of the actual ideal. -/
theorem exists_uniform_coordinate_power (I : Ideal (MvPolynomial σ K)) (i : σ) :
    ∃ N : ℕ, ∀ q ∈ saturation I, X i ^ N * q ∈ I := by
  classical
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (saturation I)
  have hg : ∀ q ∈ s, ∃ n : ℕ, X i ^ n * q ∈ I := by
    intro q hq
    exact (show q ∈ saturation I from hs ▸ Ideal.subset_span hq) i
  choose n hn using hg
  let N := s.sup (fun q => if hq : q ∈ s then n q hq else 0)
  refine ⟨N, ?_⟩
  intro q hq
  rw [← hs] at hq
  induction hq using Submodule.span_induction with
  | mem q hq =>
    apply pow_mul_mem_mono I i _ (hn q hq)
    have hqs : q ∈ s := hq
    have := Finset.le_sup (f := fun q => if hq : q ∈ s then n q hq else 0) hqs
    simpa only [dif_pos hqs] using this
  | zero => simp
  | add p q hp hq ihp ihq => simpa [mul_add] using I.add_mem ihp ihq
  | smul r q hq ih =>
    simpa [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using I.mul_mem_left r ih

/-- One exponent works simultaneously for every coordinate and every
element of the actual saturated ideal. -/
theorem exists_uniform_power (I : Ideal (MvPolynomial σ K)) :
    ∃ N : ℕ, ∀ i : σ, ∀ q ∈ saturation I, X i ^ N * q ∈ I := by
  classical
  letI : Fintype σ := Fintype.ofFinite σ
  choose n hn using exists_uniform_coordinate_power I
  refine ⟨Finset.univ.sup n, ?_⟩
  intro i q hq
  exact pow_mul_mem_mono I i (Finset.le_sup (Finset.mem_univ i)) (hn i q hq)

/-- The irrelevant ideal is the literal ideal generated by all coordinates. -/
def irrelevantIdeal : Ideal (MvPolynomial σ K) := Ideal.span (Set.range X)

/-- A fixed power of the entire irrelevant ideal annihilates sat(I)/I. -/
theorem exists_irrelevant_power_annihilates (I : Ideal (MvPolynomial σ K)) :
    ∃ N : ℕ, ∀ a ∈ (irrelevantIdeal (σ := σ) (K := K)) ^ N,
      ∀ q ∈ saturation I, a * q ∈ I := by
  have hr : irrelevantIdeal (σ := σ) (K := K) ≤ (I.colon (saturation I)).radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨N, hN⟩ := exists_uniform_coordinate_power I i
    exact ⟨N, Submodule.mem_colon.mpr (fun q hq => hN q hq)⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hr
    (IsNoetherian.noetherian _)
  exact ⟨N, fun a ha q hq => Submodule.mem_colon.mp (hN ha) q hq⟩

end Sheshadri.IrrelevantSaturation
