/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.PolynomialModel
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The original cone argument: smoothness and a hyperplane avoiding the vertex

These are the coordinate identities used in Sections 8 and 9 of the revised
manuscript. No particular polar fibre is chosen or counted. The section map
below is defined only through a hyperplane avoiding the cone vertex; it does
not assert a global bundle projection of the cone conormal across that vertex.

The classical degree of the dual hypersurface is NOT proved in this module.
-/

noncomputable section
namespace Sheshadri.ConormalCone

open MvPolynomial
open scoped BigOperators

variable {n : ℕ}

def powerSum (n d : ℕ) : MvPolynomial (Fin n) ℂ := ∑ i, X i ^ d

theorem powerSum_eq_fermat (n : ℕ) : powerSum n n = PolynomialModel.fermat n := rfl

theorem pderiv_powerSum (n d : ℕ) (i : Fin n) :
    pderiv i (powerSum n d) = C (d : ℂ) * X i ^ (d - 1) := by
  classical
  simp [powerSum, pderiv_pow, Pi.single_apply]

theorem eval_pderiv_powerSum (n d : ℕ) (x : Fin n → ℂ) (i : Fin n) :
    eval x (pderiv i (powerSum n d)) = (d : ℂ) * x i ^ (d - 1) := by
  simp [pderiv_powerSum]

/-- A nonzero representative on the Fermat cone is a smooth point.
The zero condition is not needed: its gradient vanishes only at the vertex. -/
theorem powerSum_smooth_away_from_vertex (n d : ℕ) (hd : 0 < d)
    (x : Fin n → ℂ) (hx : x ≠ 0) :
    ∃ i, eval x (pderiv i (powerSum n d)) ≠ 0 := by
  have hcoord : ∃ i, x i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := hcoord
  refine ⟨i, ?_⟩
  rw [eval_pderiv_powerSum]
  exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hd)) (pow_ne_zero _ hi)

/-- Euler's identity, including its exact scalar, for the actual power sum. -/
theorem powerSum_euler (n d : ℕ) (hd : 0 < d) (x : Fin n → ℂ) :
    ∑ i, x i * eval x (pderiv i (powerSum n d)) =
      (d : ℂ) * eval x (powerSum n d) := by
  simp_rw [eval_pderiv_powerSum]
  rw [show eval x (powerSum n d) = ∑ i, x i ^ d by simp [powerSum], Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hp : x i ^ d = x i ^ (d - 1) * x i := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega]
    exact pow_succ _ _
  rw [hp]
  ring

/-- Thus the homogenizing coordinate of the Gauss covector is zero at
an affine zero of the homogeneous target. -/
theorem powerSum_gauss_zero_coordinate (n d : ℕ) (hd : 0 < d)
    (x : Fin n → ℂ) (hx : eval x (powerSum n d) = 0) :
    -(∑ i, x i * eval x (pderiv i (powerSum n d))) = 0 := by
  rw [powerSum_euler n d hd, hx, mul_zero, neg_zero]

def linearForm (ell z : Fin n → ℂ) : ℂ := ∑ i, ell i * z i

/-- The hyperplane has equation a*x₀ + ell(x)=0. Its avoidance of the
vertex is exactly a≠0. This section picks its intersection with each ruling. -/
def sectionPoint (a : ℂ) (ell z : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.cons (-linearForm ell z / a) z

@[simp] theorem sectionPoint_zero (a : ℂ) (ell z : Fin n → ℂ) :
    sectionPoint a ell z 0 = -linearForm ell z / a := rfl

@[simp] theorem sectionPoint_succ (a : ℂ) (ell z : Fin n → ℂ) (i : Fin n) :
    sectionPoint a ell z i.succ = z i := rfl

theorem sectionPoint_mem_hyperplane (a : ℂ) (ha : a ≠ 0) (ell z : Fin n → ℂ) :
    a * sectionPoint a ell z 0 + linearForm ell z = 0 := by
  simp only [sectionPoint_zero]
  field_simp
  ring

theorem sectionPoint_unique (a : ℂ) (ha : a ≠ 0) (ell z : Fin n → ℂ)
    (t : ℂ) (ht : a * t + linearForm ell z = 0) :
    Fin.cons t z = sectionPoint a ell z := by
  have ht' : t = -linearForm ell z / a := by
    apply (eq_div_iff ha).2
    linear_combination ht
  rw [ht']
  rfl

theorem sectionPoint_injective (a : ℂ) (ell : Fin n → ℂ) :
    Function.Injective (sectionPoint a ell) := by
  intro z w h
  funext i
  exact congrFun h i.succ

theorem sectionPoint_ne_zero (a : ℂ) (ell z : Fin n → ℂ) (hz : z ≠ 0) :
    sectionPoint a ell z ≠ 0 := by
  intro h
  apply hz
  funext i
  exact congrFun h i.succ

/-- Scaling compatibility lets the section descend to projective points. -/
theorem sectionPoint_smul (a : ℂ) (ell z : Fin n → ℂ) (c : ℂ) :
    sectionPoint a ell (c • z) = c • sectionPoint a ell z := by
  have hs : linearForm ell (c • z) = c * linearForm ell z := by
    simp only [linearForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [sectionPoint_zero, Pi.smul_apply, smul_eq_mul, hs]
    ring
  · rfl

/-- A genuine bijection on representatives, with inverse radial projection.
Nonzero representatives correspond because the chosen hyperplane avoids
the vertex. The projective statement follows by scaling compatibility. -/
def hyperplaneSectionEquiv (a : ℂ) (ha : a ≠ 0) (ell : Fin n → ℂ) :
    (Fin n → ℂ) ≃ {x : Fin (n + 1) → ℂ |
      a * x 0 + linearForm ell (fun i => x i.succ) = 0} where
  toFun z := ⟨sectionPoint a ell z, sectionPoint_mem_hyperplane a ha ell z⟩
  invFun x := fun i => x.val i.succ
  left_inv z := rfl
  right_inv x := by
    apply Subtype.ext
    have h := sectionPoint_unique a ha ell (fun i => x.val i.succ) (x.val 0) x.property
    calc
      sectionPoint a ell (fun i => x.val i.succ) =
          Fin.cons (x.val 0) (fun i => x.val i.succ) := h.symm
      _ = x.val := by ext i; exact Fin.cases rfl (fun _ => rfl) i

end Sheshadri.ConormalCone
