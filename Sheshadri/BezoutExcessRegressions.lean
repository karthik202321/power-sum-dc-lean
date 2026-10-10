/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.MultiProjectiveBezout
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Regular.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Regression against a false Cox-ring complete-intersection shortcut

Three split equations of degree (1,1,1) in three projective lines need not
form a regular sequence in the full six-variable homogeneous coordinate ring.
The irrelevant coordinate block creates an explicit nonzero annihilator.
This does not contradict projective Bezout or affine-chart regularity.
-/

noncomputable section
namespace Sheshadri.BezoutExcessRegressions

open MvPolynomial MultiProjective

abbrev Variables := MultiProjective.Variables (Fin 2) (Fin 2) (Fin 2)
abbrev CoordinateRing := MvPolynomial Variables ℂ

def x (i : Fin 2) : CoordinateRing := X (.inl i)
def y (i : Fin 2) : CoordinateRing := X (.inr (.inl i))
def z (i : Fin 2) : CoordinateRing := X (.inr (.inr i))

def firstEquation : CoordinateRing := x 0 * y 0 * z 0
def secondEquation : CoordinateRing := x 1 * y 1 * z 1
def thirdEquation : CoordinateRing := (x 0 + x 1) * (y 0 + y 1) * (z 0 + z 1)
def firstTwoIdeal : Ideal CoordinateRing := Ideal.span {firstEquation, secondEquation}
def annihilator : CoordinateRing := y 0 * z 0 * y 1 * z 1

theorem equations_weightedHomogeneous :
    IsWeightedHomogeneous (weight (Fin 2) (Fin 2) (Fin 2)) firstEquation (1,1,1) ∧
    IsWeightedHomogeneous (weight (Fin 2) (Fin 2) (Fin 2)) secondEquation (1,1,1) ∧
    IsWeightedHomogeneous (weight (Fin 2) (Fin 2) (Fin 2)) thirdEquation (1,1,1) := by
  have hx (i : Fin 2) : IsWeightedHomogeneous (weight (Fin 2) (Fin 2) (Fin 2))
      (x i) (1,0,0) := isWeightedHomogeneous_X ℂ _ _
  have hy (i : Fin 2) : IsWeightedHomogeneous (weight (Fin 2) (Fin 2) (Fin 2))
      (y i) (0,1,0) := isWeightedHomogeneous_X ℂ _ _
  have hz (i : Fin 2) : IsWeightedHomogeneous (weight (Fin 2) (Fin 2) (Fin 2))
      (z i) (0,0,1) := isWeightedHomogeneous_X ℂ _ _
  exact ⟨(hx 0 |>.mul (hy 0)).mul (hz 0),
    (hx 1 |>.mul (hy 1)).mul (hz 1),
    ((hx 0 |>.add (hx 1)).mul (hy 0 |>.add (hy 1))).mul (hz 0 |>.add (hz 1))⟩

theorem annihilator_not_mem : annihilator ∉ firstTwoIdeal := by
  let point : Variables → ℂ := Sum.elim (fun _ => 0) (fun _ => 1)
  have hle : firstTwoIdeal ≤ RingHom.ker (eval point) := by
    apply Ideal.span_le.mpr
    intro p hp
    rcases hp with rfl | rfl
    · simp [firstEquation, x, y, z, point]
    · simp [secondEquation, x, y, z, point]
  intro h
  have hv : eval point annihilator = 0 := hle h
  simpa [annihilator, y, z, point] using hv

theorem third_mul_annihilator_mem : thirdEquation * annihilator ∈ firstTwoIdeal := by
  have h₁ : firstEquation ∈ firstTwoIdeal := Ideal.subset_span (by simp)
  have h₂ : secondEquation ∈ firstTwoIdeal := Ideal.subset_span (by simp)
  have h := firstTwoIdeal.add_mem
    (firstTwoIdeal.mul_mem_left ((y 1 * z 1) * (y 0 + y 1) * (z 0 + z 1)) h₁)
    (firstTwoIdeal.mul_mem_left ((y 0 * z 0) * (y 0 + y 1) * (z 0 + z 1)) h₂)
  convert h using 1
  dsimp [thirdEquation, annihilator, firstEquation, secondEquation]
  ring

/-- Even the square, trihomogeneous split system cannot justify invoking
a regular-sequence Hilbert formula in its full Cox coordinate ring. -/
theorem thirdEquation_not_regular_mod_first_two :
    ¬ IsRegular (Ideal.Quotient.mk firstTwoIdeal thirdEquation) := by
  intro hregular
  have hprod : Ideal.Quotient.mk firstTwoIdeal thirdEquation *
      Ideal.Quotient.mk firstTwoIdeal annihilator =
      Ideal.Quotient.mk firstTwoIdeal thirdEquation * 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr third_mul_annihilator_mem, mul_zero]
  exact annihilator_not_mem (Ideal.Quotient.eq_zero_iff_mem.mp (hregular.left hprod))

end Sheshadri.BezoutExcessRegressions
