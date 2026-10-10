/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SingularDeformation
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.List.Nodup
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Flat.Localization

/-!
# Coordinate powers are regular, including after localization

The proof uses the actual monomial ideal membership criterion: multiplying by
a power of a fresh coordinate cannot introduce divisibility by a power of a
previous coordinate. Translation and flat base change then give the regular
coordinate-difference powers in local polynomial rings.
-/

noncomputable section
namespace Sheshadri.CoordinatePowerRegular
open MvPolynomial RingTheory.Sequence
open scoped Pointwise TensorProduct

section Monomials
variable {σ K : Type*} [CommRing K]

def powerIdeal (s : Set σ) (N : σ → ℕ) : Ideal (MvPolynomial σ K) :=
  Ideal.span ((fun i => (X i : MvPolynomial σ K)^N i) '' s)

theorem mem_powerIdeal_iff (s : Set σ) (N : σ → ℕ) (p : MvPolynomial σ K) :
    p ∈ powerIdeal s N ↔ ∀ d ∈ p.support, ∃ i ∈ s, N i ≤ d i := by
  classical
  have hs : ((fun i => (X i : MvPolynomial σ K)^N i) '' s) =
      (fun d => monomial d (1 : K)) '' ((fun i => Finsupp.single i (N i)) '' s) := by
    rw [Set.image_image]
    simp only [Function.comp_def, X_pow_eq_monomial]
  rw [powerIdeal, hs, mem_ideal_span_monomial_image]
  simp only [Set.mem_image, exists_exists_and_eq_and, Finsupp.single_le_iff]

theorem cancel_fresh_coordinate_power (s : Set σ) (N : σ → ℕ)
    (i : σ) (hi : i ∉ s) (n : ℕ) (p : MvPolynomial σ K)
    (hp : (X i)^n * p ∈ powerIdeal s N) : p ∈ powerIdeal s N := by
  classical
  rw [mem_powerIdeal_iff] at hp ⊢
  intro d hd
  have hshift : Finsupp.single i n + d ∈ ((X i)^n * p).support := by
    rw [mem_support_iff, X_pow_eq_monomial, coeff_monomial_mul, one_mul]
    exact mem_support_iff.mp hd
  obtain ⟨j,hj,hNj⟩ := hp _ hshift
  refine ⟨j,hj,?_⟩
  have hji : i ≠ j := by rintro rfl; exact hi hj
  simpa [Finsupp.single_apply, hji] using hNj

theorem fresh_coordinate_power_regular (s : Set σ) (N : σ → ℕ)
    (i : σ) (hi : i ∉ s) (n : ℕ) :
    IsSMulRegular (MvPolynomial σ K ⧸ powerIdeal s N) ((X i)^n : MvPolynomial σ K) := by
  apply isSMulRegular_of_smul_eq_zero_imp_eq_zero
  intro x hx
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply cancel_fresh_coordinate_power s N i hi n p
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact hx

theorem ofList_powers (l : List σ) (N : σ → ℕ) :
    Ideal.ofList (l.map (fun i => (X i : MvPolynomial σ K)^N i)) =
      powerIdeal {i | i ∈ l} N := by
  unfold Ideal.ofList powerIdeal
  congr 1
  ext p
  simp only [List.mem_map, Set.mem_image, Set.mem_setOf_eq]

/-- Powers of distinct polynomial coordinates form a weak regular sequence,
over an arbitrary coefficient ring and for arbitrary exponents. -/
theorem coordinate_powers_weakly_regular (l : List σ) (hl : l.Nodup) (N : σ → ℕ) :
    IsWeaklyRegular (MvPolynomial σ K) (l.map (fun i => (X i : MvPolynomial σ K)^N i)) := by
  constructor
  intro j hj
  have hj' : j < l.length := by simpa using hj
  have hn : l[j] ∉ l.take j := by
    intro h
    obtain ⟨k,hk,he⟩ := List.mem_take_iff_getElem.mp h
    have hkj : k = j := hl.getElem_inj_iff.mp he
    omega
  have hreg := fresh_coordinate_power_regular (K := K) {i | i ∈ l.take j} N l[j] hn (N l[j])
  have hI : Ideal.ofList ((l.map (fun i => (X i : MvPolynomial σ K)^N i)).take j) •
      (⊤ : Submodule (MvPolynomial σ K) (MvPolynomial σ K)) =
      powerIdeal {i | i ∈ l.take j} N := by
    rw [← List.map_take, Ideal.smul_eq_mul, Ideal.mul_top, ofList_powers]
  rw [hI]
  simpa only [List.getElem_map] using hreg

end Monomials

section Translation
variable {σ K : Type*} [CommRing K]

/-- The explicit coordinate translation taking `Xi` to `Xi-pi`. -/
def translation (p : σ → K) : MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofAlgHom (aeval (fun i => X i - C (p i))) (aeval (fun i => X i + C (p i)))
    (by ext i; simp) (by ext i; simp)

@[simp] theorem translation_X (p : σ → K) (i : σ) :
    translation p (X i) = X i - C (p i) := by simp [translation]

theorem coordinate_difference_powers_weakly_regular
    (p : σ → K) (l : List σ) (hl : l.Nodup) (N : σ → ℕ) :
    IsWeaklyRegular (MvPolynomial σ K) (l.map (fun i => (X i - C (p i))^N i)) := by
  have h := coordinate_powers_weakly_regular (K := K) l hl N
  have he : IsWeaklyRegular (MvPolynomial σ K) (l.map (fun i => (X i)^N i)) ↔
      IsWeaklyRegular (MvPolynomial σ K)
        ((l.map (fun i => (X i)^N i)).map (translation p)) :=
    (translation p).toAddEquiv.isWeaklyRegular_congr
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr (fun r _ x => by
        exact map_mul (translation p) r x)))
  simpa only [List.map_map, Function.comp_def, map_pow, translation_X] using he.mp h

end Translation

section Flat
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- Flat extension preserves the actual scalar regular sequence, with the
scalars explicitly mapped into the extension ring. -/
theorem weakly_regular_map_of_flat (fs : List R) (hf : IsWeaklyRegular R fs) :
    IsWeaklyRegular S (fs.map (algebraMap R S)) := by
  apply (isWeaklyRegular_map_algebraMap_iff S S fs).mpr
  exact ((TensorProduct.rid R S).isWeaklyRegular_congr fs).mp hf.isWeaklyRegular_lTensor

end Flat

section Local
variable {σ K S : Type*} [CommRing K] [CommRing S]
    [Algebra (MvPolynomial σ K) S] [Module.Flat (MvPolynomial σ K) S]
    [IsLocalRing S] [Nontrivial S]

/-- In every flat local polynomial algebra, positive powers of coordinate
differences in the maximal ideal form an actual regular sequence. In
particular this applies to the localization at the chosen affine point. -/
theorem local_coordinate_difference_powers_regular
    (p : σ → K) (l : List σ) (hl : l.Nodup) (N : σ → ℕ)
    (hN : ∀ i ∈ l, 0 < N i)
    (hp : ∀ i ∈ l, algebraMap (MvPolynomial σ K) S (X i-C (p i)) ∈
      IsLocalRing.maximalIdeal S) :
    IsRegular S (l.map (fun i => (algebraMap (MvPolynomial σ K) S (X i-C (p i)))^N i)) := by
  have hw := weakly_regular_map_of_flat (S := S) _
    (coordinate_difference_powers_weakly_regular p l hl N)
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal ?_).mpr
  · simpa only [List.map_map, Function.comp_def, map_pow] using hw
  · intro r hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    exact (IsLocalRing.maximalIdeal S).pow_mem_of_mem (hp i hi) (N i) (hN i hi)

end Local

section PointLocalization
variable {σ K : Type*} [Field K]

/-- The actual maximal ideal of evaluation at the selected affine point. -/
def pointIdeal (p : σ → K) : Ideal (MvPolynomial σ K) := RingHom.ker (eval p)

instance pointIdeal_maximal (p : σ → K) : (pointIdeal p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (eval p) (fun c => ⟨C c, by simp⟩)

abbrev PointLocalRing (p : σ → K) := Localization.AtPrime (pointIdeal p)

/-- Positive powers of all distinct coordinate differences form a regular
sequence in the actual local polynomial ring at the chosen point. All
locality, flatness and maximal-ideal membership facts are constructed. -/
theorem coordinate_powers_at_point (p : σ → K) (l : List σ) (hl : l.Nodup)
    (N : σ → ℕ) (hN : ∀ i ∈ l, 0 < N i) :
    IsRegular (PointLocalRing p)
      (l.map (fun i => (algebraMap (MvPolynomial σ K) (PointLocalRing p)
        (X i-C (p i)))^N i)) := by
  apply local_coordinate_difference_powers_regular p l hl N hN
  intro i hi
  apply (IsLocalization.AtPrime.to_map_mem_maximal_iff (PointLocalRing p) (pointIdeal p) _).mpr
  change eval p (X i-C (p i)) = 0
  simp

end PointLocalization
end Sheshadri.CoordinatePowerRegular
