/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FlatMultiGradedHilbert
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A product inequality for actual multigraded Hilbert functions

Splitting a product equation gives an upper bound on the actual homogeneous
quotient pieces even with excess components or zero divisors. Multiplication
need not be injective. The inequality is proved from explicit quotient maps
and their exact kernel, not a regular-sequence or geometric certificate.
-/

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section
namespace Sheshadri.ProjectiveChartHilbertBound

open MvPolynomial ProjectivePointInterpolation FlatMultiGradedHilbert

variable {σ K D : Type*} [Field K] [AddCancelCommMonoid D]
variable (w : σ → D)

/-- Projection of a homogeneous factor times an arbitrary polynomial. -/
theorem component_mul_left {a : MvPolynomial σ K} {da : D}
    (ha : a.IsWeightedHomogeneous w da) (p : MvPolynomial σ K) (k : D) :
    weightedHomogeneousComponent w (da + k) (a * p) =
      a * weightedHomogeneousComponent w k p := by
  classical
  ext e
  rw [coeff_weightedHomogeneousComponent, coeff_mul, coeff_mul]
  trans ∑ uv ∈ Finset.antidiagonal e,
    if Finsupp.weight w e = da + k then coeff uv.1 a * coeff uv.2 p else 0
  · split_ifs <;> simp
  apply Finset.sum_congr rfl
  intro uv huv
  have he : uv.1 + uv.2 = e := Finset.mem_antidiagonal.mp huv
  rw [coeff_weightedHomogeneousComponent]
  by_cases hua : coeff uv.1 a = 0
  · simp [hua]
  have hud : Finsupp.weight w uv.1 = da := ha hua
  have hdeg : Finsupp.weight w e = da + Finsupp.weight w uv.2 := by
    rw [← he, map_add, hud]
  simp only [hdeg, add_left_cancel_iff]
  split_ifs <;> simp_all

/-- A component below or outside the factor's translated degree cone is zero. -/
theorem component_mul_left_eq_zero {a : MvPolynomial σ K} {da k : D}
    (ha : a.IsWeightedHomogeneous w da) (hk : ¬ ∃ b, da + b = k)
    (p : MvPolynomial σ K) : weightedHomogeneousComponent w k (a * p) = 0 := by
  classical
  ext e
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with he
  · rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro uv huv
    by_cases hua : coeff uv.1 a = 0
    · simp [hua]
    exfalso
    apply hk
    refine ⟨Finsupp.weight w uv.2, ?_⟩
    rw [← ha hua, ← map_add, Finset.mem_antidiagonal.mp huv, he]
  · rfl

/-- Adjoining a genuinely homogeneous polynomial preserves actual ideal
homogeneity for any cancellative additive grading monoid. -/
theorem homogeneous_sup_span (I : Ideal (MvPolynomial σ K))
    (hI : IsHomogeneous w I) (a : MvPolynomial σ K) {da : D}
    (ha : a.IsWeightedHomogeneous w da) : IsHomogeneous w (I ⊔ Ideal.span {a}) := by
  intro k p hp
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hp
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hv
  rw [map_add]
  apply (I ⊔ Ideal.span {a}).add_mem
  · exact (show I ≤ I ⊔ Ideal.span {a} from le_sup_left) (hI _ _ hu)
  · by_cases hdk : ∃ b, da + b = k
    · obtain ⟨b, rfl⟩ := hdk
      rw [component_mul_left w ha]
      exact (I ⊔ Ideal.span {a}).mul_mem_right _
        ((show Ideal.span {a} ≤ I ⊔ Ideal.span {a} from le_sup_right)
          (Ideal.subset_span (Set.mem_singleton a)))
    · rw [component_mul_left_eq_zero w ha hdk]
      exact Ideal.zero_mem _

abbrev QuotientRing (I : Ideal (MvPolynomial σ K)) := MvPolynomial σ K ⧸ I

variable (I : Ideal (MvPolynomial σ K)) (a b : MvPolynomial σ K)

theorem productIdeal_le_factorIdeal :
    I ⊔ Ideal.span {a * b} ≤ I ⊔ Ideal.span {a} := by
  apply sup_le le_sup_left
  apply Ideal.span_le.mpr
  rintro p rfl
  exact (I ⊔ Ideal.span {a}).mul_mem_right _
    ((show Ideal.span {a} ≤ I ⊔ Ideal.span {a} from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton a)))

/-- Projection from the product equation to its first factor equation. -/
def productProjection :
    QuotientRing (I ⊔ Ideal.span {a * b}) →ₐ[K] QuotientRing (I ⊔ Ideal.span {a}) :=
  Ideal.quotientMapₐ (I ⊔ Ideal.span {a}) (AlgHom.id K _)
    (productIdeal_le_factorIdeal I a b)

@[simp] theorem productProjection_mk (p : MvPolynomial σ K) :
    productProjection I a b (Ideal.Quotient.mk (I ⊔ Ideal.span {a * b}) p) =
      Ideal.Quotient.mk (I ⊔ Ideal.span {a}) p := rfl

def pieceProjection (d : D) :
    coordinatePiece w (I ⊔ Ideal.span {a * b}) d →ₗ[K]
      coordinatePiece w (I ⊔ Ideal.span {a}) d :=
  (((productProjection I a b).toLinearMap.comp
    (coordinatePiece w (I ⊔ Ideal.span {a * b}) d).subtype).codRestrict _ (by
      rintro ⟨x, p, hp, hpx⟩
      refine ⟨p, hp, ?_⟩
      change Ideal.Quotient.mk (I ⊔ Ideal.span {a}) p = productProjection I a b x
      change Ideal.Quotient.mk (I ⊔ Ideal.span {a * b}) p = x at hpx
      rw [← hpx, productProjection_mk]))

theorem pieceProjection_surjective (d : D) :
    Function.Surjective (pieceProjection w I a b d) := by
  rintro ⟨x, p, hp, hpx⟩
  refine ⟨⟨Ideal.Quotient.mk (I ⊔ Ideal.span {a * b}) p, p, hp, rfl⟩, ?_⟩
  exact Subtype.ext hpx

/-- Multiplication by the first factor descends from the quotient by the
second factor, without any nonzerodivisor assumption. -/
def productMultiplication :
    QuotientRing (I ⊔ Ideal.span {b}) →ₗ[K] QuotientRing (I ⊔ Ideal.span {a * b}) := by
  let J := I ⊔ Ideal.span {a * b}
  let f : MvPolynomial σ K →ₗ[K] QuotientRing J :=
    (LinearMap.mulLeft K (Ideal.Quotient.mk J a)).comp (Ideal.Quotient.mkₐ K J).toLinearMap
  exact ((I ⊔ Ideal.span {b}).restrictScalars K).liftQ f (by
    intro p hp
    change Ideal.Quotient.mk J a * Ideal.Quotient.mk J p = 0
    rw [← map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hp
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hv
    rw [mul_add, ← mul_assoc]
    apply J.add_mem
    · exact J.mul_mem_left _ ((show I ≤ J from le_sup_left) hu)
    · exact J.mul_mem_right _ ((show Ideal.span {a * b} ≤ J from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton (a * b)))))

@[simp] theorem productMultiplication_mk (p : MvPolynomial σ K) :
    productMultiplication I a b (Ideal.Quotient.mk (I ⊔ Ideal.span {b}) p) =
      Ideal.Quotient.mk (I ⊔ Ideal.span {a * b}) (a * p) := rfl

def pieceMultiplication {da : D} (ha : a.IsWeightedHomogeneous w da) (k : D) :
    coordinatePiece w (I ⊔ Ideal.span {b}) k →ₗ[K]
      coordinatePiece w (I ⊔ Ideal.span {a * b}) (da + k) :=
  (((productMultiplication I a b).comp
    (coordinatePiece w (I ⊔ Ideal.span {b}) k).subtype).codRestrict _ (by
      rintro ⟨x, p, hp, hpx⟩
      refine ⟨a * p, ha.mul hp, ?_⟩
      change Ideal.Quotient.mk (I ⊔ Ideal.span {a * b}) (a * p) = productMultiplication I a b x
      change Ideal.Quotient.mk (I ⊔ Ideal.span {b}) p = x at hpx
      rw [← hpx, productMultiplication_mk]))

/-- The exact kernel of the displayed homogeneous projection. Multiplication
may have a nontrivial kernel; only its image is identified. -/
theorem piece_kernel_eq_range (hI : IsHomogeneous w I)
    {da : D} (ha : a.IsWeightedHomogeneous w da) (k : D) :
    LinearMap.ker (pieceProjection w I a b (da + k)) =
      LinearMap.range (pieceMultiplication w I a b ha k) := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hpx⟩ := x.property
    change Ideal.Quotient.mk (I ⊔ Ideal.span {a * b}) p = (x : QuotientRing _) at hpx
    have hpJ : p ∈ I ⊔ Ideal.span {a} := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hx0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      change productProjection I a b (x : QuotientRing _) = 0 at hx0
      rwa [← hpx, productProjection_mk] at hx0
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hpJ
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hv
    have he : p = weightedHomogeneousComponent w (da + k) u +
        a * weightedHomogeneousComponent w k q := by
      have hc := congrArg (weightedHomogeneousComponent w (da + k)) huv
      rw [map_add, hq, component_mul_left w ha,
        IsWeightedHomogeneous.weightedHomogeneousComponent_same hp] at hc
      exact hc.symm
    refine ⟨⟨Ideal.Quotient.mk (I ⊔ Ideal.span {b}) (weightedHomogeneousComponent w k q),
      weightedHomogeneousComponent w k q, weightedHomogeneousComponent_mem _ _ _, rfl⟩, ?_⟩
    apply Subtype.ext
    change productMultiplication I a b
      (Ideal.Quotient.mk (I ⊔ Ideal.span {b}) (weightedHomogeneousComponent w k q)) = x
    rw [productMultiplication_mk, ← hpx, he, map_add,
      Ideal.Quotient.eq_zero_iff_mem.mpr
        ((show I ≤ I ⊔ Ideal.span {a * b} from le_sup_left) (hI _ _ hu)), zero_add]
  · rintro ⟨y, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    obtain ⟨p, hp, hpy⟩ := y.property
    change Ideal.Quotient.mk (I ⊔ Ideal.span {b}) p = (y : QuotientRing _) at hpy
    change productProjection I a b (productMultiplication I a b (y : QuotientRing _)) = 0
    rw [← hpy, productMultiplication_mk, productProjection_mk]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (I ⊔ Ideal.span {a}).mul_mem_right _
      ((show Ideal.span {a} ≤ I ⊔ Ideal.span {a} from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton a)))

/-- Product splitting gives an inequality for the ACTUAL coordinate pieces.
There is no regularity, radicality, proper-intersection, or reducedness input. -/
theorem piece_finrank_mul_le (hI : IsHomogeneous w I)
    {da : D} (ha : a.IsWeightedHomogeneous w da) (k : D)
    [Module.Finite K (coordinatePiece w (I ⊔ Ideal.span {a * b}) (da + k))]
    [Module.Finite K (coordinatePiece w (I ⊔ Ideal.span {b}) k)] :
    Module.finrank K (coordinatePiece w (I ⊔ Ideal.span {a * b}) (da + k)) ≤
      Module.finrank K (coordinatePiece w (I ⊔ Ideal.span {a}) (da + k)) +
        Module.finrank K (coordinatePiece w (I ⊔ Ideal.span {b}) k) := by
  have h := (pieceProjection w I a b (da + k)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (pieceProjection_surjective w I a b (da + k)),
    finrank_top, piece_kernel_eq_range w I a b hI ha k] at h
  rw [← h]
  exact Nat.add_le_add_left (LinearMap.finrank_range_le (pieceMultiplication w I a b ha k)) _

end Sheshadri.ProjectiveChartHilbertBound
