/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.HomogeneousDeterminant
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# A literal homogeneous lift over the coefficient ring

Every affine polynomial is lifted to a homogeneous polynomial by adding the
chart coordinate. The degree is a constructed finite bound on its support.
Both dehomogenization and all affine partial derivatives commute with arbitrary
coefficient specialization. Thus one lift over a DVR gives compatible generic
and special equations, without an assumed projective family.
-/

noncomputable section
namespace Sheshadri.HomogeneousPolynomialLift

open MvPolynomial HomogeneousDeterminant

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

theorem dehom_rename_succ (p : MvPolynomial (Fin n) R) :
    dehom (rename Fin.succ p) = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem dehom_map (φ : R →+* S) (p : MvPolynomial (Fin (n+1)) R) :
    dehom (map φ p) = map φ (dehom p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [hp]

/-- Evaluating the dehomogenized polynomial is evaluation at the literal
standard-chart point, also after extending the coefficient field. -/
theorem eval₂_dehom (φ : R →+* S) (x : Fin n → S)
    (p : MvPolynomial (Fin (n+1)) R) :
    eval₂ φ x (dehom p) = eval₂ φ (Fin.cons 1 x) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [hp]

theorem eval_dehom (x : Fin n → R) (p : MvPolynomial (Fin (n+1)) R) :
    eval x (dehom p) = eval (Fin.cons 1 x) p := eval₂_dehom (RingHom.id R) x p

def supportDegree (p : MvPolynomial (Fin n) R) : ℕ := p.support.sup Finsupp.degree

theorem degree_le_supportDegree (p : MvPolynomial (Fin n) R)
    {e : Fin n →₀ ℕ} (he : e ∈ p.support) : e.degree ≤ supportDegree p :=
  Finset.le_sup he

def lift (p : MvPolynomial (Fin n) R) : MvPolynomial (Fin (n+1)) R :=
  ∑ e ∈ p.support,
    C (coeff e p) * X 0 ^ (supportDegree p - e.degree) * rename Fin.succ (monomial e 1)

theorem lift_homogeneous (p : MvPolynomial (Fin n) R) :
    (lift p).IsHomogeneous (supportDegree p) := by
  classical
  apply IsHomogeneous.sum
  intro e he
  have hm : (monomial e (1 : R)).IsHomogeneous e.degree := isHomogeneous_monomial _ rfl
  have hmr : (rename Fin.succ (monomial e (1 : R))).IsHomogeneous e.degree :=
    hm.rename_isHomogeneous
  simpa only [Nat.sub_add_cancel (degree_le_supportDegree p he)] using
    (isHomogeneous_C_mul_X_pow (coeff e p) (0 : Fin (n+1))
      (supportDegree p - e.degree)).mul hmr

@[simp] theorem dehom_lift (p : MvPolynomial (Fin n) R) : dehom (lift p) = p := by
  classical
  simp only [lift, map_sum, map_mul, dehom_C, map_pow, dehom_X_zero, one_pow,
    mul_one, dehom_rename_succ, C_mul_monomial, mul_one]
  exact support_sum_monomial_coeff p

theorem dehom_map_lift (φ : R →+* S) (p : MvPolynomial (Fin n) R) :
    dehom (map φ (lift p)) = map φ p := by
  rw [dehom_map, dehom_lift]

theorem dehom_map_pderiv_lift (φ : R →+* S) (p : MvPolynomial (Fin n) R)
    (i : Fin n) :
    dehom (map φ (pderiv i.succ (lift p))) = pderiv i (map φ p) := by
  rw [← pderiv_map, dehom_pderiv_succ, dehom_map_lift]

theorem map_lift_homogeneous (φ : R →+* S) (p : MvPolynomial (Fin n) R) :
    (map φ (lift p)).IsHomogeneous (supportDegree p) :=
  (lift_homogeneous p).map φ

theorem pderiv_lift_homogeneous (p : MvPolynomial (Fin n) R) (i : Fin n) :
    (pderiv i.succ (lift p)).IsHomogeneous (supportDegree p - 1) :=
  (lift_homogeneous p).pderiv

theorem map_lift_ne_zero (φ : R →+* S) (p : MvPolynomial (Fin n) R)
    (hp : map φ p ≠ 0) : map φ (lift p) ≠ 0 := by
  intro h
  apply hp
  rw [← dehom_map_lift φ p, h, map_zero]

end Sheshadri.HomogeneousPolynomialLift
