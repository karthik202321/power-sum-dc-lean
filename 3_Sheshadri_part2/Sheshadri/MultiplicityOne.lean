/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Lean.Elab.Tactic.Omega

/-!
# Nonzero differential excludes repeated and crossing factors

These are statements about actual polynomial partial derivatives and actual
evaluation at a root. A nonzero gradient excludes every squared vanishing
factor. In a finite factorization with positive exponents and a prefactor
nonzero at the point, exactly one factor vanishes there, and its exponent
is one. This is the multiplicity-one implication used in Section 8.
-/

namespace Sheshadri.MultiplicityOne

open MvPolynomial
open scoped BigOperators

section Ring

variable {K σ : Type*} [CommRing K]

/-- At an intersection of two factors, every derivative of their product
vanishes, with no irreducibility or characteristic hypothesis. -/
theorem product_gradient_zero (g h : MvPolynomial σ K) (x : σ → K)
    (hg : eval x g = 0) (hh : eval x h = 0) (i : σ) :
    eval x (pderiv i (g * h)) = 0 := by
  simp only [pderiv_mul, map_add, map_mul, hg, hh, mul_zero, zero_mul, add_zero]

/-- A squared factor vanishing at a point kills the entire gradient. -/
theorem square_divisor_gradient_zero (f g : MvPolynomial σ K) (x : σ → K)
    (hdiv : g ^ 2 ∣ f) (hg : eval x g = 0) (i : σ) :
    eval x (pderiv i f) = 0 := by
  obtain ⟨h, rfl⟩ := hdiv
  simp only [pow_two, mul_assoc]
  apply product_gradient_zero g (g * h) x hg
  simp only [map_mul, hg, zero_mul]

/-- A concrete nonzero partial derivative rules out any squared vanishing
factor. This is the local multiplicity-one test, independent of schemes. -/
theorem no_square_divisor_at_smooth_point (f g : MvPolynomial σ K) (x : σ → K)
    (hg : eval x g = 0) (hsmooth : ∃ i, eval x (pderiv i f) ≠ 0) :
    ¬g ^ 2 ∣ f := by
  intro hdiv
  obtain ⟨i, hi⟩ := hsmooth
  exact hi (square_divisor_gradient_zero f g x hdiv hg i)

/-- A nonzero derivative of a vanishing power forces exponent exactly one. -/
theorem vanishing_power_exponent_one (g : MvPolynomial σ K) (e : ℕ) (x : σ → K)
    (hg : eval x g = 0) (hsmooth : ∃ i, eval x (pderiv i (g ^ e)) ≠ 0) : e = 1 := by
  have he0 : e ≠ 0 := by
    intro he
    obtain ⟨i, hi⟩ := hsmooth
    simp only [he, pow_zero, map_one, Derivation.map_one_eq_zero, map_zero] at hi
    exact hi rfl
  have he2 : ¬2 ≤ e := by
    intro he
    apply no_square_divisor_at_smooth_point (g ^ e) g x hg hsmooth
    exact pow_dvd_pow g he
  omega

end Ring

section Factorization

variable {K σ J : Type*} [CommRing K] [IsDomain K] [Fintype J] [DecidableEq J]

omit [IsDomain K] in
/-- If a product is smooth at a root of one factor, that factor is smooth
and every other factor is nonzero at that point. -/
theorem smooth_product_at_vanishing_factor
    (q : J → MvPolynomial σ K) (x : σ → K) (j : J)
    (hqj : eval x (q j) = 0)
    (hsmooth : ∃ i, eval x (pderiv i (∏ k, q k)) ≠ 0) :
    (∃ i, eval x (pderiv i (q j)) ≠ 0) ∧
      ∀ k, k ≠ j → eval x (q k) ≠ 0 := by
  obtain ⟨i, hi⟩ := hsmooth
  have hprod : (∏ k, q k) = q j * ∏ k ∈ Finset.univ.erase j, q k :=
    (Finset.mul_prod_erase Finset.univ q (Finset.mem_univ j)).symm
  rw [hprod, pderiv_mul, map_add, map_mul, map_mul, hqj, zero_mul, add_zero] at hi
  refine ⟨⟨i, ?_⟩, ?_⟩
  · intro hz
    exact hi (by rw [hz, zero_mul])
  · intro k hkj hk
    apply hi
    have hzero : eval x (∏ l ∈ Finset.univ.erase j, q l) = 0 := by
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩) hk
    rw [hzero, mul_zero]

/-- The finite-factorization form of multiplicity one. All exponents are
positive, so inactive factors of exponent zero cannot create fake branches. -/
theorem unique_vanishing_factor_exponent_one
    (q : J → MvPolynomial σ K) (e : J → ℕ) (he : ∀ j, 0 < e j)
    (x : σ → K)
    (hroot : eval x (∏ j, q j ^ e j) = 0)
    (hsmooth : ∃ i, eval x (pderiv i (∏ j, q j ^ e j)) ≠ 0) :
    ∃ j, eval x (q j) = 0 ∧ e j = 1 ∧
      ∀ k, k ≠ j → eval x (q k) ≠ 0 := by
  have hroot' : (∏ j, eval x (q j ^ e j)) = 0 := by simpa only [map_prod] using hroot
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hroot'
  have hqj : eval x (q j) = 0 := by
    rw [map_pow] at hj
    exact (pow_eq_zero hj)
  obtain ⟨hsj, hrest⟩ := smooth_product_at_vanishing_factor
    (fun j => q j ^ e j) x j hj hsmooth
  refine ⟨j, hqj, vanishing_power_exponent_one (q j) (e j) x hqj hsj, ?_⟩
  intro k hkj hk
  apply hrest k hkj
  simp only [map_pow, hk, zero_pow (Nat.ne_of_gt (he k))]

/-- A prefactor nonzero at the point does not affect the multiplicity-one
conclusion for a finite polynomial factorization. -/
theorem unique_vanishing_factor_of_factorization
    (f unitFactor : MvPolynomial σ K)
    (q : J → MvPolynomial σ K) (e : J → ℕ) (he : ∀ j, 0 < e j)
    (hfactor : f = unitFactor * ∏ j, q j ^ e j) (x : σ → K)
    (hunit : eval x unitFactor ≠ 0) (hroot : eval x f = 0)
    (hsmooth : ∃ i, eval x (pderiv i f) ≠ 0) :
    ∃ j, eval x (q j) = 0 ∧ e j = 1 ∧
      ∀ k, k ≠ j → eval x (q k) ≠ 0 := by
  have hprod : eval x (∏ j, q j ^ e j) = 0 := by
    rw [hfactor, map_mul] at hroot
    exact (mul_eq_zero.mp hroot).resolve_left hunit
  apply unique_vanishing_factor_exponent_one q e he x hprod
  obtain ⟨i, hi⟩ := hsmooth
  refine ⟨i, ?_⟩
  intro hz
  apply hi
  rw [hfactor, pderiv_mul, map_add, map_mul, map_mul, hprod, hz]
  simp

end Factorization
end Sheshadri.MultiplicityOne
