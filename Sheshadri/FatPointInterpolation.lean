/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ProjectivePointInterpolation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Sheshadri.SplitBranchHilbert
import Sheshadri.FlatMultiGradedHilbert
import Sheshadri.IsolatedLocalMultiplicity

/-!
# Interpolation onto actual finite quotient algebras

Explicit multihomogenization proves that every sufficiently high diagonal
coordinate piece surjects onto an actual finite-dimensional quotient algebra
in a common projective chart. Chinese remaindering then applies this to finite
families of pairwise-comaximal fat-point ideals. The lower bound counts their
full quotient dimensions, not just their reduced supports.
-/

noncomputable section
namespace Sheshadri.FatPointInterpolation
open MvPolynomial MultiProjective ProjectivePointInterpolation
set_option synthInstance.maxHeartbeats 200000

section Homogenization
variable {σ K : Type*} [CommRing K]

def degreeBound (w : σ → Degree) (f : MvPolynomial σ K) : ℕ :=
  f.support.sup (fun e => max (Finsupp.weight w e).1
    (max (Finsupp.weight w e).2.1 (Finsupp.weight w e).2.2))

def homogenizeForms (w : σ → Degree) (lx lu lv : MvPolynomial σ K)
    (f : MvPolynomial σ K) (n : ℕ) : MvPolynomial σ K :=
  ∑ e ∈ f.support, monomial e (coeff e f) *
    lx ^ (n - (Finsupp.weight w e).1) *
    lu ^ (n - (Finsupp.weight w e).2.1) *
    lv ^ (n - (Finsupp.weight w e).2.2)

def homogenize (w : σ → Degree) (ix iu iv : σ)
    (f : MvPolynomial σ K) (n : ℕ) : MvPolynomial σ K :=
  homogenizeForms w (X ix) (X iu) (X iv) f n

theorem support_degrees_le (w : σ → Degree) (f : MvPolynomial σ K)
    (n : ℕ) (hn : degreeBound w f ≤ n) (e : σ →₀ ℕ) (he : e ∈ f.support) :
    (Finsupp.weight w e).1 ≤ n ∧ (Finsupp.weight w e).2.1 ≤ n ∧
      (Finsupp.weight w e).2.2 ≤ n := by
  have h : max (Finsupp.weight w e).1
      (max (Finsupp.weight w e).2.1 (Finsupp.weight w e).2.2) ≤ degreeBound w f := by
    exact Finset.le_sup (f := fun e => max (Finsupp.weight w e).1
      (max (Finsupp.weight w e).2.1 (Finsupp.weight w e).2.2)) he
  exact ⟨(le_max_left _ _).trans (h.trans hn),
    (le_max_left _ _).trans ((le_max_right _ _).trans (h.trans hn)),
    (le_max_right _ _).trans ((le_max_right _ _).trans (h.trans hn))⟩

theorem homogenizeForms_homogeneous (w : σ → Degree) (lx lu lv : MvPolynomial σ K)
    (hx : IsWeightedHomogeneous w lx (1, 0, 0))
    (hu : IsWeightedHomogeneous w lu (0, 1, 0))
    (hv : IsWeightedHomogeneous w lv (0, 0, 1))
    (f : MvPolynomial σ K) (n : ℕ) (hn : degreeBound w f ≤ n) :
    IsWeightedHomogeneous w (homogenizeForms w lx lu lv f n) (n, n, n) := by
  classical
  apply IsWeightedHomogeneous.sum
  intro e he
  obtain ⟨he1, he2, he3⟩ := support_degrees_le w f n hn e he
  have hh := (((isWeightedHomogeneous_monomial w e (coeff e f) rfl).mul
    (hx.pow (n - (Finsupp.weight w e).1))).mul
    (hu.pow (n - (Finsupp.weight w e).2.1))).mul
    (hv.pow (n - (Finsupp.weight w e).2.2))
  have hd : Finsupp.weight w e + (n - (Finsupp.weight w e).1) • (1, 0, 0) +
      (n - (Finsupp.weight w e).2.1) • (0, 1, 0) +
      (n - (Finsupp.weight w e).2.2) • (0, 0, 1) = (n, n, n) := by
    ext <;> simp <;> omega
  rw [hd] at hh
  exact hh

theorem map_homogenizeForms {A : Type*} [CommRing A] [Algebra K A]
    (w : σ → Degree) (lx lu lv : MvPolynomial σ K) (φ : MvPolynomial σ K →ₐ[K] A)
    (hx : φ lx = 1) (hu : φ lu = 1) (hv : φ lv = 1)
    (f : MvPolynomial σ K) (n : ℕ) :
    φ (homogenizeForms w lx lu lv f n) = φ f := by
  classical
  simp only [homogenizeForms, map_sum, map_mul, map_pow, hx, hu, hv, one_pow, mul_one]
  rw [← map_sum, f.support_sum_monomial_coeff]

theorem homogenize_homogeneous (w : σ → Degree) (ix iu iv : σ)
    (hx : w ix = (1, 0, 0)) (hu : w iu = (0, 1, 0)) (hv : w iv = (0, 0, 1))
    (f : MvPolynomial σ K) (n : ℕ) (hn : degreeBound w f ≤ n) :
    IsWeightedHomogeneous w (homogenize w ix iu iv f n) (n, n, n) := by
  exact homogenizeForms_homogeneous w (X ix) (X iu) (X iv)
    (hx ▸ isWeightedHomogeneous_X K w ix)
    (hu ▸ isWeightedHomogeneous_X K w iu)
    (hv ▸ isWeightedHomogeneous_X K w iv) f n hn

theorem map_homogenize {A : Type*} [CommRing A] [Algebra K A]
    (w : σ → Degree) (ix iu iv : σ) (φ : MvPolynomial σ K →ₐ[K] A)
    (hx : φ (X ix) = 1) (hu : φ (X iu) = 1) (hv : φ (X iv) = 1)
    (f : MvPolynomial σ K) (n : ℕ) :
    φ (homogenize w ix iu iv f n) = φ f :=
  map_homogenizeForms w (X ix) (X iu) (X iv) φ hx hu hv f n

end Homogenization

section FiniteQuotient
variable {σ K A : Type*} [Field K] [CommRing A] [Algebra K A] [Module.Finite K A]

/-- Actual finite-dimensionality supplies a finite basis of preimages;
explicitly homogenizing those preimages proves eventual surjectivity. -/
theorem eventually_homogeneous_surjective_forms
    (w : σ → Degree) (lx lu lv : MvPolynomial σ K)
    (hwx : IsWeightedHomogeneous w lx (1, 0, 0))
    (hwu : IsWeightedHomogeneous w lu (0, 1, 0))
    (hwv : IsWeightedHomogeneous w lv (0, 0, 1))
    (φ : MvPolynomial σ K →ₐ[K] A) (hφ : Function.Surjective φ)
    (hx : φ lx = 1) (hu : φ lu = 1) (hv : φ lv = 1) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ y : A, ∃ f : MvPolynomial σ K,
      IsWeightedHomogeneous w f (n, n, n) ∧ φ f = y := by
  classical
  let b := Module.finBasis K A
  choose pre hpre using fun i => hφ (b i)
  let N := Finset.univ.sup (fun i => degreeBound w (pre i))
  refine ⟨N, fun n hn => ?_⟩
  let W := (weightedHomogeneousSubmodule K w (n, n, n)).map φ.toLinearMap
  have hb : ∀ i, b i ∈ W := by
    intro i
    have hi : degreeBound w (pre i) ≤ n := (Finset.le_sup (Finset.mem_univ i)).trans hn
    exact ⟨homogenizeForms w lx lu lv (pre i) n,
      homogenizeForms_homogeneous w lx lu lv hwx hwu hwv (pre i) n hi,
      (map_homogenizeForms w lx lu lv φ hx hu hv (pre i) n).trans (hpre i)⟩
  have htop : W = ⊤ := by
    apply top_unique
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro y ⟨i, rfl⟩; exact hb i)
  intro y
  have hy : y ∈ W := by rw [htop]; trivial
  exact hy

theorem eventually_homogeneous_surjective
    (w : σ → Degree) (ix iu iv : σ)
    (hwx : w ix = (1, 0, 0)) (hwu : w iu = (0, 1, 0)) (hwv : w iv = (0, 0, 1))
    (φ : MvPolynomial σ K →ₐ[K] A) (hφ : Function.Surjective φ)
    (hx : φ (X ix) = 1) (hu : φ (X iu) = 1) (hv : φ (X iv) = 1) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ y : A, ∃ f : MvPolynomial σ K,
      IsWeightedHomogeneous w f (n, n, n) ∧ φ f = y :=
  eventually_homogeneous_surjective_forms w (X ix) (X iu) (X iv)
    (hwx ▸ isWeightedHomogeneous_X K w ix)
    (hwu ▸ isWeightedHomogeneous_X K w iu)
    (hwv ▸ isWeightedHomogeneous_X K w iv) φ hφ hx hu hv

/-- The actual induced evaluation map from a coordinate-ring piece. -/
def quotientPieceMap (w : σ → Degree) (I : Ideal (MvPolynomial σ K))
    (φ : MvPolynomial σ K →ₐ[K] A) (hI : ∀ f ∈ I, φ f = 0) (d : Degree) :
    coordinatePiece w I d →ₗ[K] A :=
  (Ideal.Quotient.liftₐ I φ hI).toLinearMap.comp (coordinatePiece w I d).subtype

theorem eventually_quotientPieceMap_surjective_forms
    (w : σ → Degree) (lx lu lv : MvPolynomial σ K)
    (hwx : IsWeightedHomogeneous w lx (1, 0, 0))
    (hwu : IsWeightedHomogeneous w lu (0, 1, 0))
    (hwv : IsWeightedHomogeneous w lv (0, 0, 1))
    (I : Ideal (MvPolynomial σ K))
    (φ : MvPolynomial σ K →ₐ[K] A) (hφ : Function.Surjective φ)
    (hI : ∀ f ∈ I, φ f = 0)
    (hx : φ lx = 1) (hu : φ lu = 1) (hv : φ lv = 1) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      Function.Surjective (quotientPieceMap w I φ hI (n, n, n)) := by
  obtain ⟨N, hN⟩ := eventually_homogeneous_surjective_forms w lx lu lv hwx hwu hwv φ hφ hx hu hv
  refine ⟨N, fun n hn y => ?_⟩
  obtain ⟨f, hf, hfy⟩ := hN n hn y
  exact ⟨⟨Ideal.Quotient.mk I f, f, hf, rfl⟩, hfy⟩

theorem eventually_finrank_le_coordinatePiece_forms
    (w : σ → Degree) (lx lu lv : MvPolynomial σ K)
    (hwx : IsWeightedHomogeneous w lx (1, 0, 0))
    (hwu : IsWeightedHomogeneous w lu (0, 1, 0))
    (hwv : IsWeightedHomogeneous w lv (0, 0, 1))
    (I : Ideal (MvPolynomial σ K))
    (φ : MvPolynomial σ K →ₐ[K] A) (hφ : Function.Surjective φ)
    (hI : ∀ f ∈ I, φ f = 0)
    (hx : φ lx = 1) (hu : φ lu = 1) (hv : φ lv = 1)
    [∀ n, Module.Finite K (coordinatePiece w I (n, n, n))] :
    ∃ N : ℕ, ∀ n, N ≤ n →
      Module.finrank K A ≤ Module.finrank K (coordinatePiece w I (n, n, n)) := by
  obtain ⟨N, hN⟩ := eventually_quotientPieceMap_surjective_forms w lx lu lv hwx hwu hwv I
    φ hφ hI hx hu hv
  refine ⟨N, fun n hn => ?_⟩
  have h := (quotientPieceMap w I φ hI (n, n, n)).finrank_range_le
  rw [LinearMap.range_eq_top.mpr (hN n hn), finrank_top] at h
  exact h

theorem eventually_quotientPieceMap_surjective
    (w : σ → Degree) (ix iu iv : σ)
    (hwx : w ix = (1, 0, 0)) (hwu : w iu = (0, 1, 0)) (hwv : w iv = (0, 0, 1))
    (I : Ideal (MvPolynomial σ K))
    (φ : MvPolynomial σ K →ₐ[K] A) (hφ : Function.Surjective φ)
    (hI : ∀ f ∈ I, φ f = 0)
    (hx : φ (X ix) = 1) (hu : φ (X iu) = 1) (hv : φ (X iv) = 1) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      Function.Surjective (quotientPieceMap w I φ hI (n, n, n)) := by
  obtain ⟨N, hN⟩ := eventually_homogeneous_surjective w ix iu iv hwx hwu hwv φ hφ hx hu hv
  refine ⟨N, fun n hn y => ?_⟩
  obtain ⟨f, hf, hfy⟩ := hN n hn y
  exact ⟨⟨Ideal.Quotient.mk I f, f, hf, rfl⟩, hfy⟩

theorem eventually_finrank_le_coordinatePiece
    (w : σ → Degree) (ix iu iv : σ)
    (hwx : w ix = (1, 0, 0)) (hwu : w iu = (0, 1, 0)) (hwv : w iv = (0, 0, 1))
    (I : Ideal (MvPolynomial σ K))
    (φ : MvPolynomial σ K →ₐ[K] A) (hφ : Function.Surjective φ)
    (hI : ∀ f ∈ I, φ f = 0)
    (hx : φ (X ix) = 1) (hu : φ (X iu) = 1) (hv : φ (X iv) = 1)
    [∀ n, Module.Finite K (coordinatePiece w I (n, n, n))] :
    ∃ N : ℕ, ∀ n, N ≤ n →
      Module.finrank K A ≤ Module.finrank K (coordinatePiece w I (n, n, n)) := by
  obtain ⟨N, hN⟩ := eventually_quotientPieceMap_surjective w ix iu iv hwx hwu hwv I
    φ hφ hI hx hu hv
  refine ⟨N, fun n hn => ?_⟩
  have h := (quotientPieceMap w I φ hI (n, n, n)).finrank_range_le
  rw [LinearMap.range_eq_top.mpr (hN n hn), finrank_top] at h
  exact h

end FiniteQuotient

section Normalization
variable {σ β K A : Type*} [Field K] [CommRing A] [Algebra K A]
  [Module.Finite K A]

/-- A finite-dimensional subalgebra contains the inverse of each of its
elements which is a unit in the ambient algebra. Nilpotents are allowed. -/
theorem unit_inverse_mem_subalgebra (B : Subalgebra K A) (u : Aˣ)
    (hu : (u : A) ∈ B) : (↑(u⁻¹) : A) ∈ B := by
  let v : B := ⟨u, hu⟩
  let m : B →ₗ[K] B := LinearMap.mulLeft K v
  have hm : Function.Injective m := by
    intro x y h
    apply Subtype.ext
    exact u.isUnit.mul_left_cancel (congrArg Subtype.val h)
  obtain ⟨z, hz⟩ := LinearMap.surjective_of_injective hm 1
  have hval : (u : A) * (z : A) = 1 := congrArg Subtype.val hz
  have heq : (z : A) = (↑(u⁻¹) : A) := by
    apply u.isUnit.mul_left_cancel
    simpa using hval
  exact heq ▸ z.property

/-- Block normalization acts on actual polynomial images by units in the
target algebra. -/
def normalizedMap (φ : MvPolynomial σ K →ₐ[K] A)
    (block : σ → β) (u : β → Aˣ) : MvPolynomial σ K →ₐ[K] A :=
  aeval (fun i => φ (X i) * (↑((u (block i))⁻¹) : A))

omit [Module.Finite K A] in
@[simp] theorem normalizedMap_X (φ : MvPolynomial σ K →ₐ[K] A)
    (block : σ → β) (u : β → Aˣ) (i : σ) :
    normalizedMap φ block u (X i) = φ (X i) * (↑((u (block i))⁻¹) : A) := by
  simp [normalizedMap]

/-- Normalizing a finite quotient does not lose any infinitesimal functions.
The old chart coordinates, which are nonzero scalars, recover every block
unit inside the new image algebra. -/
theorem normalizedMap_surjective (φ : MvPolynomial σ K →ₐ[K] A)
    (hφ : Function.Surjective φ) (block : σ → β) (u : β → Aˣ)
    (representative : β → σ) (hrep : ∀ j, block (representative j) = j)
    (c : β → K) (hc : ∀ j, c j ≠ 0)
    (hchart : ∀ j, φ (X (representative j)) = algebraMap K A (c j)) :
    Function.Surjective (normalizedMap φ block u) := by
  let ψ := normalizedMap φ block u
  let B := ψ.range
  have hinv : ∀ j, (↑((u j)⁻¹) : A) ∈ B := by
    intro j
    have hx : ψ (X (representative j)) ∈ B := ⟨_, rfl⟩
    have h := B.mul_mem (B.algebraMap_mem ((c j)⁻¹)) hx
    simpa [ψ, normalizedMap_X, hrep, hchart, ← mul_assoc,
      ← map_mul, inv_mul_cancel₀ (hc j)] using h
  have hu : ∀ j, (u j : A) ∈ B := by
    intro j
    simpa using unit_inverse_mem_subalgebra B ((u j)⁻¹) (hinv j)
  have hcoords : ∀ i, φ (X i) ∈ B := by
    intro i
    have h := B.mul_mem (show ψ (X i) ∈ B from ⟨_, rfl⟩) (hu (block i))
    simpa [ψ, normalizedMap_X, mul_assoc] using h
  have hall : ∀ f, φ f ∈ B := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C c => simpa using B.algebraMap_mem c
    | add f g hf hg => simpa using B.add_mem hf hg
    | mul_X f i hf => simpa using B.mul_mem hf (hcoords i)
  intro y
  obtain ⟨f, rfl⟩ := hφ y
  exact hall f

end Normalization

section HomogeneousNormalization
variable {σ D K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [AddCommMonoid D]

/-- Weighted scaling works over arbitrary quotient algebras, including
nonreduced local intersection algebras. -/
theorem aeval_scaled_character (w : σ → D) (χ : Multiplicative D →* A)
    (c : σ → A) (f : MvPolynomial σ K) (d : D)
    (hf : IsWeightedHomogeneous w f d) :
    aeval (fun i => c i * χ (Multiplicative.ofAdd (w i))) f =
      aeval c f * χ (Multiplicative.ofAdd d) := by
  classical
  have hprod (e : σ →₀ ℕ) :
      e.prod (fun i n => (c i * χ (Multiplicative.ofAdd (w i))) ^ n) =
      e.prod (fun i n => c i ^ n) *
        χ (Multiplicative.ofAdd (Finsupp.weight w e)) := by
    rw [SplitBranchHilbert.character_weight]
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  rw [← f.support_sum_monomial_coeff, map_sum, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  have hd := hf (mem_support_iff.mp he)
  simp only [aeval_def, eval₂_monomial]
  rw [hprod, hd, mul_assoc]

end HomogeneousNormalization

section ThreeBlockNormalization
variable {X U V K A : Type*} [Field K] [CommRing A] [Algebra K A]

def blockIndex : Variables X U V → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

def normalizationCharacter (u : Fin 3 → Aˣ) : Multiplicative Degree →* A :=
  SplitBranchHilbert.threeCharacter (↑((u 0)⁻¹) : A)
    (↑((u 1)⁻¹) : A) (↑((u 2)⁻¹) : A)

theorem normalizedMap_homogeneous (φ : MvPolynomial (Variables X U V) K →ₐ[K] A)
    (u : Fin 3 → Aˣ) (f : MvPolynomial (Variables X U V) K) (d : Degree)
    (hf : IsWeightedHomogeneous (weight X U V) f d) :
    normalizedMap φ blockIndex u f = φ f * normalizationCharacter u (Multiplicative.ofAdd d) := by
  have hφ : φ = aeval (fun i => φ (MvPolynomial.X i)) := by ext i; simp
  have hψ : normalizedMap φ blockIndex u =
      aeval (fun i => φ (MvPolynomial.X i) *
        normalizationCharacter u (Multiplicative.ofAdd (weight X U V i))) := by
    ext (i | (i | i)) <;>
      simp [normalizedMap_X, blockIndex, normalizationCharacter,
        SplitBranchHilbert.threeCharacter, weight]
  rw [hψ]
  have h := aeval_scaled_character (weight X U V) (normalizationCharacter u)
    (fun i => φ (MvPolynomial.X i)) f d hf
  rwa [← hφ] at h

/-- Block normalization preserves every equation of an actual homogeneous
ideal, by decomposing it into its homogeneous components. -/
theorem normalizedMap_kills_homogeneous_ideal
    (φ : MvPolynomial (Variables X U V) K →ₐ[K] A) (u : Fin 3 → Aˣ)
    (I : Ideal (MvPolynomial (Variables X U V) K))
    (hI : FlatMultiGradedHilbert.IsHomogeneous (weight X U V) I)
    (hφ : ∀ f ∈ I, φ f = 0) :
    ∀ f ∈ I, normalizedMap φ blockIndex u f = 0 := by
  classical
  intro f hf
  conv_lhs => rw [← sum_weightedHomogeneousComponent (weight X U V) f]
  rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  rw [normalizedMap_homogeneous φ u _ d (weightedHomogeneousComponent_mem _ f d),
    hφ _ (hI d f hf), zero_mul]

theorem normalizedMap_first_form
    (φ : MvPolynomial (Variables X U V) K →ₐ[K] A) (u : Fin 3 → Aˣ)
    (l : MvPolynomial (Variables X U V) K)
    (hl : IsWeightedHomogeneous (weight X U V) l (1, 0, 0))
    (hval : φ l = (u 0 : A)) : normalizedMap φ blockIndex u l = 1 := by
  rw [normalizedMap_homogeneous φ u l (1, 0, 0) hl, hval]
  simp [normalizationCharacter, SplitBranchHilbert.threeCharacter]

theorem normalizedMap_second_form
    (φ : MvPolynomial (Variables X U V) K →ₐ[K] A) (u : Fin 3 → Aˣ)
    (l : MvPolynomial (Variables X U V) K)
    (hl : IsWeightedHomogeneous (weight X U V) l (0, 1, 0))
    (hval : φ l = (u 1 : A)) : normalizedMap φ blockIndex u l = 1 := by
  rw [normalizedMap_homogeneous φ u l (0, 1, 0) hl, hval]
  simp [normalizationCharacter, SplitBranchHilbert.threeCharacter]

theorem normalizedMap_third_form
    (φ : MvPolynomial (Variables X U V) K →ₐ[K] A) (u : Fin 3 → Aˣ)
    (l : MvPolynomial (Variables X U V) K)
    (hl : IsWeightedHomogeneous (weight X U V) l (0, 0, 1))
    (hval : φ l = (u 2 : A)) : normalizedMap φ blockIndex u l = 1 := by
  rw [normalizedMap_homogeneous φ u l (0, 0, 1) hl, hval]
  simp [normalizationCharacter, SplitBranchHilbert.threeCharacter]

end ThreeBlockNormalization

section LocalLengthProduct
variable {σ K P : Type*} [Field K] [Fintype P]

theorem sum_local_length_eq_finrank_product
    (A : P → Type*) [∀ p, CommRing (A p)] [∀ p, Algebra K (A p)]
    [∀ p, IsLocalRing (A p)] [∀ p, Module.Finite K (A p)]
    (ε : ∀ p, A p →ₐ[K] K) :
    (∑ p, Module.length (A p) (A p)) = (Module.finrank K (∀ p, A p) : ℕ∞) := by
  simp_rw [LocalLengthDimension.length_eq_finrank (ε _) (A _)]
  rw [Module.finrank_pi_fintype, Nat.cast_sum]

/-- Interpolation bounds the sum of the actual lengths of distinct finite
local quotient algebras. The maps retain their nilpotents; no reducedness or
transversality assumption appears. -/
theorem eventually_sum_local_length_le_coordinatePiece_forms
    (w : σ → Degree) (lx lu lv : MvPolynomial σ K)
    (hwx : IsWeightedHomogeneous w lx (1, 0, 0))
    (hwu : IsWeightedHomogeneous w lu (0, 1, 0))
    (hwv : IsWeightedHomogeneous w lv (0, 0, 1))
    (I : Ideal (MvPolynomial σ K))
    (A : P → Type*) [∀ p, CommRing (A p)] [∀ p, Algebra K (A p)]
    [∀ p, IsLocalRing (A p)] [∀ p, IsArtinianRing (A p)]
    [∀ p, Module.Finite K (A p)]
    (φ : ∀ p, MvPolynomial σ K →ₐ[K] A p)
    (hφ : ∀ p, Function.Surjective (φ p)) (ε : ∀ p, A p →ₐ[K] K)
    (hp : Function.Injective (fun p => IsolatedLocalMultiplicity.residuePoint (φ p) (ε p)))
    (hI : ∀ p f, f ∈ I → φ p f = 0)
    (hx : ∀ p, φ p lx = 1) (hu : ∀ p, φ p lu = 1) (hv : ∀ p, φ p lv = 1)
    [∀ n, Module.Finite K (coordinatePiece w I (n, n, n))] :
    ∃ N : ℕ, ∀ n, N ≤ n →
      (∑ p, (Module.length (A p) (A p)).toNat) ≤
        Module.finrank K (coordinatePiece w I (n, n, n)) := by
  have hsurj := IsolatedLocalMultiplicity.piAlgHom_surjective_of_distinctResidues
    A φ hφ ε hp
  have hker : ∀ f ∈ I, (Pi.algHom K _ φ) f = 0 := by
    intro f hf
    exact funext (fun p => hI p f hf)
  have hx' : (Pi.algHom K _ φ) lx = 1 := funext hx
  have hu' : (Pi.algHom K _ φ) lu = 1 := funext hu
  have hv' : (Pi.algHom K _ φ) lv = 1 := funext hv
  obtain ⟨N, hN⟩ := eventually_finrank_le_coordinatePiece_forms
    w lx lu lv hwx hwu hwv I (Pi.algHom K _ φ) hsurj hker hx' hu' hv'
  refine ⟨N, fun n hn => ?_⟩
  have hlen (p : P) : (Module.length (A p) (A p)).toNat = Module.finrank K (A p) := by
    rw [LocalLengthDimension.length_eq_finrank (ε p) (A p)]
    simp
  simpa only [hlen, Module.finrank_pi_fintype] using hN n hn

end LocalLengthProduct

section ChineseRemainder
variable {σ K P : Type*} [Field K] [Fintype P]

/-- The actual simultaneous quotient map to all specified jets. -/
def jetMap (J : P → Ideal (MvPolynomial σ K)) :
    MvPolynomial σ K →ₐ[K] (∀ p, MvPolynomial σ K ⧸ J p) :=
  Pi.algHom K _ (fun p => Ideal.Quotient.mkₐ K (J p))

theorem jetMap_surjective (J : P → Ideal (MvPolynomial σ K))
    (hJ : Pairwise (fun p q => IsCoprime (J p) (J q))) :
    Function.Surjective (jetMap J) := by
  intro y
  obtain ⟨f, hf⟩ := Ideal.pi_quotient_surjective hJ y
  exact ⟨f, funext hf⟩

/-- Chinese remainder interpolation retains full dimensions of the
nonreduced quotient algebras. No reducedness hypothesis is used. -/
theorem eventually_sum_jet_finrank_le_coordinatePiece
    (w : σ → Degree) (ix iu iv : σ)
    (hwx : w ix = (1, 0, 0)) (hwu : w iu = (0, 1, 0)) (hwv : w iv = (0, 0, 1))
    (I : Ideal (MvPolynomial σ K)) (J : P → Ideal (MvPolynomial σ K))
    (hJ : Pairwise (fun p q => IsCoprime (J p) (J q)))
    (hI : ∀ p, I ≤ J p)
    (hx : ∀ p, X ix - 1 ∈ J p) (hu : ∀ p, X iu - 1 ∈ J p)
    (hv : ∀ p, X iv - 1 ∈ J p)
    [∀ p, Module.Finite K (MvPolynomial σ K ⧸ J p)]
    [∀ n, Module.Finite K (coordinatePiece w I (n, n, n))] :
    ∃ N : ℕ, ∀ n, N ≤ n →
      (∑ p, Module.finrank K (MvPolynomial σ K ⧸ J p)) ≤
        Module.finrank K (coordinatePiece w I (n, n, n)) := by
  have hker : ∀ f ∈ I, jetMap J f = 0 := by
    intro f hf
    funext p
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI p hf)
  have hx' : jetMap J (X ix) = 1 := by
    funext p
    exact Ideal.Quotient.eq.mpr (hx p)
  have hu' : jetMap J (X iu) = 1 := by
    funext p
    exact Ideal.Quotient.eq.mpr (hu p)
  have hv' : jetMap J (X iv) = 1 := by
    funext p
    exact Ideal.Quotient.eq.mpr (hv p)
  simpa only [Module.finrank_pi_fintype] using
    eventually_finrank_le_coordinatePiece w ix iu iv hwx hwu hwv I (jetMap J)
      (jetMap_surjective J hJ) hker hx' hu' hv'

/-- Enlarging pairwise-comaximal powers by any common ideal preserves
Chinese-remainder independence. This applies to actual fat-point truncations. -/
theorem pairwise_coprime_fatIdeals (I : Ideal (MvPolynomial σ K))
    (m : P → Ideal (MvPolynomial σ K))
    (hm : Pairwise (fun p q => IsCoprime (m p) (m q))) (N : P → ℕ) :
    Pairwise (fun p q => IsCoprime (I ⊔ m p ^ N p) (I ⊔ m q ^ N q)) := by
  intro p q hpq
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply top_unique
  have hpow : IsCoprime (m p ^ N p) (m q ^ N q) := (hm hpq).pow
  rw [← hpow.sup_eq]
  exact sup_le_sup le_sup_right le_sup_right

end ChineseRemainder

end Sheshadri.FatPointInterpolation
