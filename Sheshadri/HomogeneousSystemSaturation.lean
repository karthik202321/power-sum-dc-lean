/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.IrrelevantSaturation
import Sheshadri.SingularSpecialFiber

/-!
# Saturation by an actual homogeneous linear system

This is the contraction from the union of the displayed principal opens.
It removes only components supported where the entire system vanishes.
The construction is scheme-theoretic, and its localization at every point
where one displayed polynomial is nonzero equals the original ideal.
-/

noncomputable section
namespace Sheshadri.HomogeneousSystemSaturation
open MvPolynomial GenericHomogeneousSections

section Basic
variable {A E : Type*} [CommRing A]

lemma pow_mul_mem_mono (I : Ideal A) (f : A) {q : A} {n m : ℕ}
    (hnm : n ≤ m) (hq : f ^ n * q ∈ I) : f ^ m * q ∈ I := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hnm
  simpa [pow_add, mul_assoc, mul_comm, mul_left_comm] using I.mul_mem_left (f ^ r) hq

def saturation (I : Ideal A) (fs : E → A) : Ideal A where
  carrier := {q | ∀ i, ∃ n : ℕ, fs i ^ n * q ∈ I}
  zero_mem' := by intro i; exact ⟨0, by simp⟩
  add_mem' := by
    intro p q hp hq i
    obtain ⟨n, hn⟩ := hp i
    obtain ⟨m, hm⟩ := hq i
    refine ⟨max n m, ?_⟩
    simpa [mul_add] using I.add_mem
      (pow_mul_mem_mono I (fs i) (le_max_left _ _) hn)
      (pow_mul_mem_mono I (fs i) (le_max_right _ _) hm)
  smul_mem' := by
    intro r q hq i
    obtain ⟨n, hn⟩ := hq i
    exact ⟨n, by simpa [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
      using I.mul_mem_left r hn⟩

@[simp] theorem mem_saturation (I : Ideal A) (fs : E → A) (q : A) :
    q ∈ saturation I fs ↔ ∀ i, ∃ n : ℕ, fs i ^ n * q ∈ I := Iff.rfl

theorem le_saturation (I : Ideal A) (fs : E → A) : I ≤ saturation I fs := by
  intro q hq i
  exact ⟨0, by simpa using hq⟩

theorem saturation_mono {I J : Ideal A} (h : I ≤ J) (fs : E → A) :
    saturation I fs ≤ saturation J fs := by
  intro q hq i
  obtain ⟨n, hn⟩ := hq i
  exact ⟨n, h hn⟩

theorem system_saturated (I : Ideal A) (fs : E → A) (q : A)
    (hq : ∀ i, fs i * q ∈ saturation I fs) : q ∈ saturation I fs := by
  intro i
  obtain ⟨n, hn⟩ := hq i i
  exact ⟨n+1, by simpa [pow_succ, mul_assoc] using hn⟩

@[simp] theorem saturation_idempotent (I : Ideal A) (fs : E → A) :
    saturation (saturation I fs) fs = saturation I fs := by
  apply le_antisymm _ (le_saturation _ _)
  intro q hq i
  obtain ⟨n, hn⟩ := hq i
  obtain ⟨m, hm⟩ := hn i
  exact ⟨m+n, by simpa [pow_add, mul_assoc] using hm⟩

theorem saturation_sup_left (I J : Ideal A) (fs : E → A) :
    saturation (saturation I fs ⊔ J) fs = saturation (I ⊔ J) fs := by
  apply le_antisymm
  · have hle : saturation I fs ⊔ J ≤ saturation (I ⊔ J) fs := by
      apply sup_le
      · exact saturation_mono le_sup_left fs
      · exact le_trans le_sup_right (le_saturation _ fs)
    simpa only [saturation_idempotent] using saturation_mono hle fs
  · exact saturation_mono (sup_le_sup (le_saturation I fs) le_rfl) fs

/-- Mapping a saturation can only add equations already in the
saturation of the mapped ideal. No flatness or surjectivity is required. -/
theorem map_saturation_le {B : Type*} [CommRing B]
    (I : Ideal A) (fs : E → A) (φ : A →+* B) :
    (saturation I fs).map φ ≤ saturation (I.map φ) (fun i => φ (fs i)) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro q hq i
  obtain ⟨n, hn⟩ := hq i
  refine ⟨n, ?_⟩
  simpa only [map_mul, map_pow] using Ideal.mem_map_of_mem φ hn

/-- If the displayed open system spans a unit in a target quotient, every
power-saturated equation already vanishes in that full quotient. -/
theorem saturation_le_ker_of_unit_span {B : Type*} [CommRing B]
    (I : Ideal A) (fs : E → A) (φ : A →+* B) (hI : I ≤ RingHom.ker φ)
    (u : B) (hu : IsUnit u)
    (hspan : u ∈ Ideal.span (Set.range (fun i => φ (fs i)))) :
    saturation I fs ≤ RingHom.ker φ := by
  intro q hq
  let J : Ideal B := (Submodule.span B {φ q}).annihilator
  have hmem : ∀ i, φ (fs i) ∈ J.radical := by
    intro i
    obtain ⟨n, hn⟩ := hq i
    refine ⟨n, ?_⟩
    apply (Submodule.mem_annihilator_span_singleton (φ q) _).mpr
    change φ (fs i) ^ n * φ q = 0
    have hh := hI hn
    change φ (fs i ^ n * q) = 0 at hh
    simpa only [map_mul, map_pow] using hh
  have hle : Ideal.span (Set.range (fun i => φ (fs i))) ≤ J.radical :=
    Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)
  have htop : J = ⊤ := Ideal.radical_eq_top.mp (J.radical.eq_top_of_isUnit_mem (hle hspan) hu)
  have hone : (1 : B) ∈ J := htop ▸ Submodule.mem_top
  have hz := (Submodule.mem_annihilator_span_singleton (φ q) (1 : B)).mp hone
  simpa only [one_smul] using hz

/-- Bounds by the original ideal and its saturation become an equality
once the open system covers the intermediate quotient scheme. -/
theorem eq_saturation_of_unit_span (I J : Ideal A) (fs : E → A)
    (hIJ : I ≤ J) (hJ : J ≤ saturation I fs)
    (u : A ⧸ J) (hu : IsUnit u)
    (hspan : u ∈ Ideal.span (Set.range (fun i => Ideal.Quotient.mk J (fs i)))) :
    J = saturation I fs := by
  apply le_antisymm hJ
  have h := saturation_le_ker_of_unit_span I fs (Ideal.Quotient.mk J)
    (by simpa only [Ideal.mk_ker] using hIJ) u hu hspan
  simpa only [Ideal.mk_ker] using h

/-- Saturation does not change an equation ideal after a displayed member
of the linear system is inverted. Nilpotents are retained. -/
theorem map_saturation_eq_of_unit {B : Type*} [CommRing B]
    (I : Ideal A) (fs : E → A) (φ : A →+* B)
    (i : E) (hi : IsUnit (φ (fs i))) :
    (saturation I fs).map φ = I.map φ := by
  apply le_antisymm _ (Ideal.map_mono (le_saturation I fs))
  apply Ideal.map_le_iff_le_comap.mpr
  intro q hq
  obtain ⟨n, hn⟩ := hq i
  have hh := Ideal.mem_map_of_mem φ hn
  rw [map_mul, map_pow] at hh
  obtain ⟨u, hu⟩ := hi.pow n
  rw [← hu] at hh
  have h := (I.map φ).mul_mem_left (↑(u⁻¹) : B) hh
  simpa only [← mul_assoc, Units.inv_mul, one_mul] using h

end Basic

section Homogeneous
variable {σ E K : Type*} [Finite σ] [Field K]

/-- Each actual associated component meets one of the displayed opens. -/
theorem associatedPrime_omits_member (I : Ideal (MvPolynomial σ K))
    (fs : E → MvPolynomial σ K) (p : Ideal (MvPolynomial σ K))
    (hp : p ∈ associatedPrimes _ (MvPolynomial σ K ⧸ saturation I fs)) :
    ∃ i, fs i ∉ p := by
  classical
  by_contra hh
  push_neg at hh
  obtain ⟨z, hz⟩ := hp.2
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hq : q ∈ saturation I fs := by
    apply system_saturated I fs
    intro i
    have hi := hh i
    rw [hz, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at hi
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change Ideal.Quotient.mk (saturation I fs) (fs i) *
      Ideal.Quotient.mk (saturation I fs) q = 0 at hi
    simpa only [map_mul] using hi
  have hzero : Ideal.Quotient.mk (saturation I fs) q = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hq
  exact hp.isPrime.ne_top (by simpa [hzero] using hz)

/-- Saturating by a fixed open coordinate times the derivative system
also forces every associated component to avoid that open boundary. -/
theorem associatedPrime_omits_common_factor (I : Ideal (MvPolynomial σ K))
    (f : MvPolynomial σ K) (fs : E → MvPolynomial σ K)
    (p : Ideal (MvPolynomial σ K))
    (hp : p ∈ associatedPrimes _ (MvPolynomial σ K ⧸ saturation I (fun i => f * fs i))) :
    f ∉ p := by
  obtain ⟨i, hi⟩ := associatedPrime_omits_member I (fun i => f * fs i) p hp
  exact fun hf => hi (p.mul_mem_right _ hf)

theorem associatedPrime_omits_system_factor (I : Ideal (MvPolynomial σ K))
    (f : MvPolynomial σ K) (fs : E → MvPolynomial σ K)
    (p : Ideal (MvPolynomial σ K))
    (hp : p ∈ associatedPrimes _ (MvPolynomial σ K ⧸ saturation I (fun i => f * fs i))) :
    ∃ i, fs i ∉ p := by
  obtain ⟨i, hi⟩ := associatedPrime_omits_member I (fun i => f * fs i) p hp
  exact ⟨i, fun hf => hi (p.mul_mem_left _ hf)⟩

/-- The common factor inverted by the construction is actually regular
on the saturated quotient, including its nilpotents. -/
theorem common_factor_regular (I : Ideal (MvPolynomial σ K))
    (f : MvPolynomial σ K) (fs : E → MvPolynomial σ K) :
    IsRegular (Ideal.Quotient.mk (saturation I (fun i => f * fs i)) f) := by
  apply quotient_regular_of_smulRegular
  by_contra hh
  have hin : f ∈ ⋃ p ∈ associatedPrimes (MvPolynomial σ K)
      (MvPolynomial σ K ⧸ saturation I (fun i => f * fs i)),
      (p : Set (MvPolynomial σ K)) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact hh
  obtain ⟨p, hp, hh⟩ := Set.mem_iUnion₂.mp hin
  exact associatedPrime_omits_common_factor I f fs p hp hh

omit [Finite σ] in
theorem saturation_homogeneous (I : Ideal (MvPolynomial σ K))
    (fs : E → MvPolynomial σ K) (ds : E → ℕ)
    (hfs : ∀ i, (fs i).IsHomogeneous (ds i))
    (hI : ∀ d p, p ∈ I → homogeneousComponent d p ∈ I) :
    ∀ d p, p ∈ saturation I fs → homogeneousComponent d p ∈ saturation I fs := by
  intro d p hp i
  obtain ⟨n, hn⟩ := hp i
  refine ⟨n, ?_⟩
  have hx : (fs i ^ n).IsHomogeneous (ds i*n) := (hfs i).pow n
  have hc := hI (ds i*n+d) (fs i ^ n*p) hn
  change weightedHomogeneousComponent (fun _ : σ => (1 : ℕ)) (ds i*n+d)
    (fs i ^ n*p) ∈ I at hc
  rw [ProjectiveChartHilbertBound.component_mul_left (fun _ : σ => (1 : ℕ)) hx] at hc
  exact hc

omit [Finite σ] in
theorem list_system_saturated (I : Ideal (MvPolynomial σ K))
    (fs : List (MvPolynomial σ K)) :
    IsSystemSaturated (saturation I (fun i : Fin fs.length => fs[i])) fs := by
  intro q hq
  apply system_saturated I (fun i : Fin fs.length => fs[i])
  intro i
  exact hq _ (List.getElem_mem i.isLt)

/-- Every saturated linear system has a genuine regular member selected
from its scalar span. There is no genericity premise. -/
theorem exists_regular_section [Infinite K]
    (I : Ideal (MvPolynomial σ K)) (fs : List (MvPolynomial σ K)) (d : ℕ)
    (hfs : ∀ f ∈ fs, f.IsHomogeneous d) :
    ∃ g : MvPolynomial σ K, g ∈ Submodule.span K {f | f ∈ fs} ∧
      g.IsHomogeneous d ∧
      IsRegular (Ideal.Quotient.mk (saturation I (fun i : Fin fs.length => fs[i])) g) :=
  exists_regular_homogeneous_combination _ fs d hfs (list_system_saturated I fs)

end Homogeneous
end Sheshadri.HomogeneousSystemSaturation
