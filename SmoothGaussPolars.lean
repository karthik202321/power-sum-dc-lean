/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalIncidence
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Homogeneous Gauss polars and their actual base ideal

Euler's identity makes the ordinary homogeneous polar system identical to
the unrestricted projective Gauss flags modulo the hypersurface equation.
Smoothness away from the cone vertex implies that the gradient system has
no other base point. Nullstellensatz then puts every coordinate into the
radical of the actual gradient ideal. No generic flag or degree formula is
assumed in these statements.
-/

noncomputable section
namespace Sheshadri.SmoothGaussPolars
open MvPolynomial
set_option maxHeartbeats 600000

section Algebra
variable {σ k : Type*} [Fintype σ] [Field k] [CharZero k]

def gradientIdeal (f : MvPolynomial σ k) : Ideal (MvPolynomial σ k) :=
  Ideal.span (Set.range (fun i => pderiv i f))

def polar (f : MvPolynomial σ k) (ell : σ → k) : MvPolynomial σ k :=
  ∑ i, C (ell i) * pderiv i f

def derivativeList (f : MvPolynomial σ k) : List (MvPolynomial σ k) :=
  (Finset.univ.toList : List σ).map (fun i => pderiv i f)

omit [CharZero k] in
theorem derivativeList_set (f : MvPolynomial σ k) :
    {g | g ∈ derivativeList f} = Set.range (fun i => pderiv i f) := by
  classical
  ext g
  simp [derivativeList]

omit [CharZero k] in
theorem derivativeList_ideal (f : MvPolynomial σ k) :
    Ideal.ofList (derivativeList f) = gradientIdeal f := by
  unfold Ideal.ofList gradientIdeal
  rw [derivativeList_set]

omit [CharZero k] in
theorem mem_polarSpan_iff (f g : MvPolynomial σ k) :
    g ∈ Submodule.span k (Set.range (fun i => pderiv i f)) ↔
      ∃ ell : σ → k, polar f ell = g := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  simp only [polar, Algebra.smul_def, MvPolynomial.algebraMap_eq]

omit [CharZero k] in
theorem polar_homogeneous {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (ell : σ → k) :
    (polar f ell).IsHomogeneous (d-1) := by
  apply IsHomogeneous.sum
  intro i hi
  simpa only [zero_add] using (isHomogeneous_C σ (ell i)).mul (hf.pderiv (i := i))

omit [CharZero k] in
theorem euler_polynomial {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) :
    ∑ i, X i * pderiv i f = C (d : k) * f := by
  simpa only [nsmul_eq_mul, map_natCast] using hf.sum_X_mul_pderiv

omit [CharZero k] in
theorem euler_evaluation {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (x : σ → k) :
    ∑ i, x i * eval x (pderiv i f) = (d : k) * eval x f := by
  have he := congrArg (eval x) (euler_polynomial hf)
  simpa only [map_sum, map_mul, eval_X, eval_C] using he

/-- In characteristic zero the hypersurface equation itself belongs to its
gradient ideal, as an actual ideal membership statement. -/
theorem self_mem_gradientIdeal {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 0 < d) : f ∈ gradientIdeal f := by
  have hd' : (d : k) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hsum : (∑ i, X i * pderiv i f) ∈ gradientIdeal f := by
    apply Ideal.sum_mem
    intro i hi
    exact (gradientIdeal f).mul_mem_left _ (Ideal.subset_span (Set.mem_range_self i))
  have h := (gradientIdeal f).mul_mem_left (C ((d : k)⁻¹)) hsum
  rw [euler_polynomial hf, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hd', map_one, one_mul] at h
  exact h

/-- Projective smoothness plus Euler eliminates every nonvertex common zero
of the gradient, even without assuming the point is on the hypersurface. -/
theorem gradient_nonzero_away_from_origin {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hsmooth : ∀ x : σ → k, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0)
    (x : σ → k) (hx : x ≠ 0) : ∃ i, eval x (pderiv i f) ≠ 0 := by
  by_contra h
  push_neg at h
  have he := euler_evaluation hf x
  simp only [h, mul_zero, Finset.sum_const_zero] at he
  have hz : eval x f = 0 :=
    (mul_eq_zero.mp he.symm).resolve_left (Nat.cast_ne_zero.mpr hd.ne')
  obtain ⟨i, hi⟩ := hsmooth x hx hz
  exact hi (h i)

theorem gradient_zeroLocus_subset_origin {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hsmooth : ∀ x : σ → k, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) :
    zeroLocus (gradientIdeal f) ⊆ {0} := by
  intro x hx
  by_contra hx0
  obtain ⟨i, hi⟩ := gradient_nonzero_away_from_origin hf hd hsmooth x
    (by simpa only [Set.mem_singleton_iff] using hx0)
  exact hi (hx _ (Ideal.subset_span (Set.mem_range_self i)))

variable [IsAlgClosed k]

/-- The projective gradient system is basepoint-free as an algebraic ideal
statement, suitable for actual generic-section construction. -/
theorem coordinate_mem_radical_gradient {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hsmooth : ∀ x : σ → k, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) (i : σ) :
    X i ∈ (gradientIdeal f).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical]
  intro x hx
  have hx0 := gradient_zeroLocus_subset_origin hf hd hsmooth hx
  simp only [Set.mem_singleton_iff] at hx0
  simp [hx0]

theorem coordinate_power_mem_gradient {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hsmooth : ∀ x : σ → k, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) (i : σ) :
    ∃ N : ℕ, (X i : MvPolynomial σ k)^N ∈ gradientIdeal f :=
  coordinate_mem_radical_gradient hf hd hsmooth i

end Algebra

section ProjectiveFlags
open ConormalIncidence
variable {n d : ℕ} {f : MvPolynomial (Fin n) ℂ}

/-- The unrestricted zeroth flag coefficient contributes only a multiple
of the homogeneous hypersurface equation. -/
theorem projectiveGradientFlag_eq_polar (hf : f.IsHomogeneous d)
    (ell : Fin (n+1) → ℂ) :
    projectiveGradientFlag f ell = polar f (fun i => ell i.succ) - C (ell 0) * C (d : ℂ) * f := by
  unfold projectiveGradientFlag polar
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc]
  rw [← Finset.mul_sum, euler_polynomial hf]

theorem projectiveGradientFlag_sub_polar_mem (hf : f.IsHomogeneous d)
    (ell : Fin (n+1) → ℂ) :
    projectiveGradientFlag f ell - polar f (fun i => ell i.succ) ∈ Ideal.span {f} := by
  rw [projectiveGradientFlag_eq_polar hf]
  have he : polar f (fun i => ell i.succ) - C (ell 0) * C (d : ℂ) * f -
      polar f (fun i => ell i.succ) = -(C (ell 0) * C (d : ℂ)) * f := by ring
  rw [he]
  exact (Ideal.span {f}).mul_mem_left _ (Ideal.subset_span rfl)

/-- Equality of the actual flag equation ideals, including all nilpotents. -/
theorem gaussFlag_ideal_eq_polar_ideal {T : Type*} (hf : f.IsHomogeneous d)
    (flags : T → Fin (n+1) → ℂ) :
    Ideal.span {f} ⊔ Ideal.span (Set.range (fun t => projectiveGradientFlag f (flags t))) =
      Ideal.span {f} ⊔ Ideal.span (Set.range (fun t => polar f (fun i => flags t i.succ))) := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    rintro q ⟨t, rfl⟩
    have hdiff := (show Ideal.span {f} ≤ Ideal.span {f} ⊔
      Ideal.span (Set.range (fun t => polar f (fun i => flags t i.succ))) from le_sup_left)
      (projectiveGradientFlag_sub_polar_mem hf (flags t))
    have hp := (show Ideal.span (Set.range (fun t => polar f (fun i => flags t i.succ))) ≤
      Ideal.span {f} ⊔ Ideal.span (Set.range (fun t => polar f (fun i => flags t i.succ))) from
        le_sup_right) (Ideal.subset_span (Set.mem_range_self t))
    simpa only [sub_add_cancel] using Ideal.add_mem _ hdiff hp
  · apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    rintro q ⟨t, rfl⟩
    have hdiff := (show Ideal.span {f} ≤ Ideal.span {f} ⊔
      Ideal.span (Set.range (fun t => projectiveGradientFlag f (flags t))) from le_sup_left)
      (projectiveGradientFlag_sub_polar_mem hf (flags t))
    have hp := (show Ideal.span (Set.range (fun t => projectiveGradientFlag f (flags t))) ≤
      Ideal.span {f} ⊔ Ideal.span (Set.range (fun t => projectiveGradientFlag f (flags t))) from
        le_sup_right) (Ideal.subset_span (Set.mem_range_self t))
    simpa only [sub_sub_cancel] using Ideal.sub_mem _ hp hdiff

end ProjectiveFlags
end Sheshadri.SmoothGaussPolars
