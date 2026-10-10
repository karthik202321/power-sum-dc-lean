/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FermatIrreducible
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! General algebraic foundations for the original Gauss-degree argument.
For every smooth homogeneous complex hypersurface, Euler's identity and
Nullstellensatz prove that the gradient ideal has finite-dimensional quotient.
These are actual ideal and quotient statements, with no generic-section or
degree hypothesis and no Fermat-specific slice. -/

noncomputable section
namespace Sheshadri.SmoothGradientIdeal
open MvPolynomial Set

variable {Z : Type*} [Fintype Z]

def gradientIdeal (f : MvPolynomial Z ℂ) : Ideal (MvPolynomial Z ℂ) :=
  Ideal.span (Set.range (fun i : Z => pderiv i f))

theorem pderiv_mem_gradientIdeal (f : MvPolynomial Z ℂ) (i : Z) :
    pderiv i f ∈ gradientIdeal f := Ideal.subset_span ⟨i, rfl⟩

/-- Euler's identity forces a common zero of all derivatives onto the
hypersurface itself. Characteristic zero and positive degree are explicit. -/
theorem eval_eq_zero_of_gradient_zero (f : MvPolynomial Z ℂ) {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 0 < d) (x : Z → ℂ)
    (hx : ∀ i, eval x (pderiv i f) = 0) : eval x f = 0 := by
  have he := congrArg (eval x) hf.sum_X_mul_pderiv
  have hz : (d : ℂ) * eval x f = 0 := by
    simpa only [map_sum, map_mul, eval_X, hx, mul_zero, Finset.sum_const_zero,
      map_nsmul, nsmul_eq_mul, map_natCast] using he.symm
  exact (mul_eq_zero.mp hz).resolve_left (Nat.cast_ne_zero.mpr hd.ne')

/-- A smooth projective hypersurface has no nonzero common zero of its
homogeneous partial derivatives. This is the base-locus exclusion needed
for its everywhere-defined Gauss morphism. -/
theorem gradient_zeroLocus_subset_origin (f : MvPolynomial Z ℂ) {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hsmooth : ∀ x : Z → ℂ, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) :
    MvPolynomial.zeroLocus (gradientIdeal f) ⊆ {0} := by
  intro x hx
  change x = 0
  by_contra hne
  have hg (i : Z) : eval x (pderiv i f) = 0 := hx _ (pderiv_mem_gradientIdeal f i)
  obtain ⟨i, hi⟩ := hsmooth x hne (eval_eq_zero_of_gradient_zero f hf hd x hg)
  exact hi (hg i)

/-- A version of affine Nullstellensatz with its concrete consequence:
if the only possible common zero is the origin, a positive power of every
coordinate lies in the literal defining ideal. -/
theorem exists_coordinate_power_mem (I : Ideal (MvPolynomial Z ℂ))
    (hI : MvPolynomial.zeroLocus I ⊆ {0}) (i : Z) :
    ∃ N : ℕ, 0 < N ∧ (X i : MvPolynomial Z ℂ) ^ N ∈ I := by
  have hx : (X i : MvPolynomial Z ℂ) ∈ I.radical := by
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical I]
    intro x hx
    have hx0 : x = 0 := hI hx
    simp [hx0]
  obtain ⟨N, hN⟩ := hx
  exact ⟨N + 1, by omega, by simpa only [pow_succ] using I.mul_mem_right (X i) hN⟩

/-- The quotient by any such ideal is finite dimensional. The proof uses
the actual nilpotent coordinate classes to show the finite-type quotient
is an integral complex algebra. -/
theorem quotient_finite_of_zeroLocus_subset_origin (I : Ideal (MvPolynomial Z ℂ))
    (hI : MvPolynomial.zeroLocus I ⊆ {0}) :
    Module.Finite ℂ (MvPolynomial Z ℂ ⧸ I) := by
  let Q := MvPolynomial Z ℂ ⧸ I
  let pi : MvPolynomial Z ℂ →ₐ[ℂ] Q := Ideal.Quotient.mkₐ ℂ I
  have hcoord (i : Z) : IsIntegral ℂ (pi (X i)) := by
    obtain ⟨N, hNpos, hN⟩ := exists_coordinate_power_mem I hI i
    have hpow : pi (X i) ^ N = 0 := by
      rw [← map_pow]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hN
    exact IsIntegral.of_pow hNpos (hpow ▸ isIntegral_zero)
  letI : Algebra.IsIntegral ℂ Q := ⟨fun q => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I q
    change IsIntegral ℂ (pi p)
    induction p using MvPolynomial.induction_on with
    | C a => exact isIntegral_algebraMap
    | add p q hp hq => simpa only [map_add] using hp.add hq
    | mul_X p i hp => simpa only [map_mul] using hp.mul (hcoord i)⟩
  letI : Algebra.FiniteType ℂ Q :=
    (Algebra.FiniteType.mvPolynomial ℂ Z).of_surjective pi (Ideal.Quotient.mkₐ_surjective ℂ I)
  exact Algebra.IsIntegral.finite

/-- The actual Jacobian ring of a smooth homogeneous complex hypersurface
is finite dimensional. No finite-dimensionality certificate is supplied. -/
theorem gradient_quotient_finite (f : MvPolynomial Z ℂ) {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hsmooth : ∀ x : Z → ℂ, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) :
    Module.Finite ℂ (MvPolynomial Z ℂ ⧸ gradientIdeal f) :=
  quotient_finite_of_zeroLocus_subset_origin _
    (gradient_zeroLocus_subset_origin f hf hd hsmooth)

end Sheshadri.SmoothGradientIdeal
