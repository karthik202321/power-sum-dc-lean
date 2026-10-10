/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SmoothGaussPointFamily
import Sheshadri.ConormalIncidence
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Constructed Gauss sections in the actual conormal incidence chart

This packages the proved finite polar section and its full local lengths,
then constructs the actual normalized kernel lifts and the single common
ordinary reduction matrix. The data structure has a proved constructor
from the original smooth homogeneous form.
-/

noncomputable section
namespace Sheshadri.ConormalGaussSection
open MvPolynomial SmoothGaussPolars SmoothGaussDegree SmoothGaussSectionLength
open SmoothGaussPointFamily IsolatedLocalMultiplicity Incidence PolynomialModel ExactKernelLifts

variable {n m d : ℕ}

def conePoint (z : Fin n → ℂ) : Fin (n+1) → ℂ := Fin.cons 1 z

def polarFlags (ell : ℕ → Fin n → ℂ) : Fin (n-2) → Fin (n+1) → ℂ :=
  fun t => Fin.cons 0 (ell t)

def primalFlag (a : Fin n → ℂ) : Fin (n+1) → ℂ := Fin.cons (-1) a

@[simp] theorem conePoint_zero (z : Fin n → ℂ) : conePoint z 0 = 1 := rfl
@[simp] theorem conePoint_succ (z : Fin n → ℂ) (i : Fin n) : conePoint z i.succ = z i := rfl
@[simp] theorem polarFlags_zero (ell : ℕ → Fin n → ℂ) (t : Fin (n-2)) :
    polarFlags ell t 0 = 0 := rfl
@[simp] theorem polarFlags_succ (ell : ℕ → Fin n → ℂ) (t : Fin (n-2)) (i : Fin n) :
    polarFlags ell t i.succ = ell t i := rfl

@[simp] theorem projectiveFlag_eq_polar (f : MvPolynomial (Fin n) ℂ)
    (ell : ℕ → Fin n → ℂ) (t : Fin (n-2)) :
    ConormalIncidence.projectiveGradientFlag f (polarFlags ell t) = polar f (ell t) := by
  simp [ConormalIncidence.projectiveGradientFlag, polar]

theorem primalFlag_equation (a z : Fin n → ℂ) (hz : ∑ i, a i*z i = 1) :
    ∑ i, primalFlag a i * conePoint z i = 0 := by
  rw [Fin.sum_univ_succ]
  change (-1 : ℂ)*1 + (∑ i, a i*z i) = 0
  rw [hz]
  ring

/-- Actual finite section data; `exists_section` constructs every field.
In particular, the multiplicity is always the actual localized quotient. -/
structure Section (f : MvPolynomial (Fin n) ℂ) (d : ℕ) where
  ell : ℕ → Fin n → ℂ
  a : Fin n → ℂ
  count : ℕ
  point : Fin count → Fin n → ℂ
  vanishes : ∀ p, polarChartIdeal f ell (n-2) a ≤ pointIdeal (point p)
  injective : Function.Injective point
  root : ∀ p, eval (point p) f = 0
  polar_zero : ∀ p (t : Fin (n-2)), eval (point p) (polar f (ell t)) = 0
  primal_one : ∀ p, ∑ i, a i*point p i = 1
  smooth : ∀ p, ∃ i, eval (point p) (pderiv i f) ≠ 0
  finite : Module.Finite ℂ (PolarChartAlgebra f ell (n-2) a)
  artinian : ∀ p, IsArtinianRing
    (LocalIntersectionRing (polarChartIdeal f ell (n-2) a) (point p) (vanishes p))
  length_sum : (∑ p, multiplicity (polarChartIdeal f ell (n-2) a) (point p) (vanishes p)) =
    (d*(d-1)^(n-2) : ℕ)

/-- No section, transversality, or degree certificate is assumed. -/
theorem exists_section (hn : 2 ≤ n) {f : MvPolynomial (Fin n) ℂ}
    (hf : f.IsHomogeneous d) (hfn : f ≠ 0) (hd : 0 < d)
    (hsmooth : ∀ x : Fin n → ℂ, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) : Nonempty (Section f d) := by
  obtain ⟨ell, a, N, points, hp, hinj, _, _, hroot, hpol, hprim, hs,
      hfinite, hart, hlength⟩ :=
    exists_smooth_gauss_root_family (n-2) (by simpa using (Nat.sub_add_cancel hn).symm)
      hf hfn hd hsmooth
  exact ⟨⟨ell, a, N, points, hp, hinj, hroot,
    (fun p t => hpol p t t.isLt), hprim, hs, hfinite, hart, hlength⟩⟩

namespace Section
variable {f : MvPolynomial (Fin n) ℂ} (s : Section f d)

def projectivePoint (p : Fin s.count) : Fin (n+1) → ℂ := conePoint (s.point p)

theorem projectivePoint_injective : Function.Injective s.projectivePoint := by
  intro p q hpq
  apply s.injective
  funext i
  exact congrFun hpq i.succ

/-- The previously proved common-reduction construction applies to the
actual constructed finite Gauss section. -/
theorem ordinaryLiftFamily (A : PencilCoefficients n m ℂ) (hm : 0 < m)
    (hrep : determinant A = f) :
    Nonempty (OrdinaryLiftFamily A (polarFlags s.ell) (primalFlag s.a) s.projectivePoint) := by
  apply ConormalIncidence.exists_ordinary_lift_family A hm _ _ s.projectivePoint
    s.projectivePoint_injective (fun _ => rfl)
  · intro p
    simpa only [projectivePoint, conePoint_succ, hrep] using s.root p
  · intro p
    simpa only [projectivePoint, conePoint_succ, hrep] using s.smooth p
  · intro p t
    simpa only [projectivePoint, conePoint_succ, hrep, projectiveFlag_eq_polar] using
      s.polar_zero p t
  · intro p
    exact primalFlag_equation s.a (s.point p) (s.primal_one p)

theorem symmetricLiftFamily (A : PencilCoefficients n m ℂ) (hm : 0 < m)
    (hA : ∀ i, (A i).transpose = A i) (hrep : determinant A = f) :
    Nonempty (SymmetricLiftFamily A (polarFlags s.ell) (primalFlag s.a) s.projectivePoint) := by
  apply ConormalIncidence.exists_symmetric_lift_family A hm hA _ _ s.projectivePoint
    s.projectivePoint_injective (fun _ => rfl)
  · intro p
    simpa only [projectivePoint, conePoint_succ, hrep] using s.root p
  · intro p
    simpa only [projectivePoint, conePoint_succ, hrep] using s.smooth p
  · intro p t
    simpa only [projectivePoint, conePoint_succ, hrep, projectiveFlag_eq_polar] using
      s.polar_zero p t
  · intro p
    exact primalFlag_equation s.a (s.point p) (s.primal_one p)

end Section
end Sheshadri.ConormalGaussSection
