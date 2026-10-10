/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Uniform pole bounds for finite rational families over a DVR

A single power of the actual uniformizer clears every entry of a finite
rational representation. The entries themselves need not specialize.
-/

noncomputable section
namespace Sheshadri.DvrRationalEntries
set_option maxHeartbeats 600000

variable {D L : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Field L] (ι : D →+* L) (hinj : Function.Injective ι)
    (hfrac : ∀ z : L, ∃ a b : D, b ≠ 0 ∧ z = ι a / ι b)
    {π : D} (hπ : Irreducible π)

include hinj hfrac hπ

omit hfrac in
/-- A rational function has finite pole order at the selected branch. -/
theorem exists_pole_order_of_fraction (z : L)
    (hz : ∃ a b : D, b ≠ 0 ∧ z = ι a / ι b) : ∃ n : ℕ, ∃ a : D, ι a = ι π ^ n * z := by
  obtain ⟨a, b, hb, rfl⟩ := hz
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hπ
  refine ⟨n, a * ↑u⁻¹, ?_⟩
  have hd : ι (↑u : D) * ι π ^ n ≠ 0 := by
    rw [← map_pow, ← map_mul]
    exact (map_ne_zero_iff _ hinj).mpr hb
  simp only [map_mul, map_pow]
  rw [← mul_div_assoc]
  apply (eq_div_iff hd).mpr
  calc
    (ι a * ι (↑u⁻¹ : D)) * (ι ↑u * ι π ^ n) =
        (ι ↑u * ι (↑u⁻¹ : D)) * (ι π ^ n * ι a) := by ring
    _ = ι π ^ n * ι a := by rw [← map_mul]; simp

theorem exists_pole_order (z : L) : ∃ n : ℕ, ∃ a : D, ι a = ι π ^ n * z :=
  exists_pole_order_of_fraction ι hinj hπ z (hfrac z)

/-- One actual uniformizer power simultaneously clears every entry. -/
theorem common_pole_order {J : Type*} [Finite J] (x : J → L) :
    ∃ n : ℕ, ∃ a : J → D, ∀ j, ι (a j) = ι π ^ n * x j := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  choose m a ha using fun j => exists_pole_order ι hinj hfrac hπ (x j)
  let n := Finset.univ.sup m
  refine ⟨n, fun j => π ^ (n - m j) * a j, ?_⟩
  intro j
  have hle : m j ≤ n := Finset.le_sup (Finset.mem_univ j)
  rw [map_mul, map_pow, ha, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

omit hfrac in
/-- One actual uniformizer power simultaneously clears every entry. -/
theorem common_pole_order_of_fractions {J : Type*} [Finite J] (x : J → L)
    (hx : ∀ j, ∃ a b : D, b ≠ 0 ∧ x j = ι a / ι b) :
    ∃ n : ℕ, ∃ a : J → D, ∀ j, ι (a j) = ι π ^ n * x j := by
  classical
  letI : Fintype J := Fintype.ofFinite J
  choose m a ha using fun j => exists_pole_order_of_fraction ι hinj hπ (x j) (hx j)
  let n := Finset.univ.sup m
  refine ⟨n, fun j => π ^ (n - m j) * a j, ?_⟩
  intro j
  have hle : m j ≤ n := Finset.le_sup (Finset.mem_univ j)
  rw [map_mul, map_pow, ha, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

end Sheshadri.DvrRationalEntries
