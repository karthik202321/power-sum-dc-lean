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
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Sheshadri.ConormalTopology
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Irreducibility of the literal homogeneous Fermat polynomial.  The proof uses
the classical Eisenstein argument in a multivariate polynomial coefficient ring;
it introduces no projective slice or counting hypothesis. -/

noncomputable section
namespace Sheshadri.FermatIrreducible
open MvPolynomial

variable {K : Type*} [Field K] [CharZero K]

def powerSum (k d : ℕ) : MvPolynomial (Fin k) K := ∑ i, X i ^ d

theorem eval_powerSum_basis (k d : ℕ) (hd : 0 < d) (j : Fin k) :
    eval (fun i => if i = j then (1 : K) else 0) (powerSum k d) = 1 := by
  classical
  simp [powerSum, hd.ne', apply_ite]

theorem powerSum_ne_zero (k d : ℕ) (hd : 0 < d) (j : Fin k) :
    (powerSum k d : MvPolynomial (Fin k) K) ≠ 0 := by
  intro h
  have he := eval_powerSum_basis (K := K) k d hd j
  rw [h, map_zero] at he
  exact zero_ne_one he

theorem powerSum_not_unit (k d : ℕ) (hd : 0 < d) :
    ¬ IsUnit (powerSum k d : MvPolynomial (Fin k) K) := by
  intro h
  have he := h.map (eval (fun _ => (0 : K)))
  simpa [powerSum, hd.ne'] using he

theorem pderiv_powerSum (k d : ℕ) (i : Fin k) :
    pderiv i (powerSum k d : MvPolynomial (Fin k) K) =
      C (d : K) * X i ^ (d - 1) := by
  classical
  simp [powerSum, pderiv_pow, Pi.single_apply, Finset.sum_ite_eq', map_natCast]

theorem irreducible_X_zero (k : ℕ) :
    Irreducible (X (0 : Fin (k + 1)) : MvPolynomial (Fin (k + 1)) K) := by
  apply (MulEquiv.irreducible_iff (finSuccEquiv K k).toMulEquiv).mp
  change Irreducible (finSuccEquiv K k (X 0))
  simpa only [finSuccEquiv_X_zero] using
    (Polynomial.irreducible_X : Irreducible (Polynomial.X : Polynomial (MvPolynomial (Fin k) K)))

theorem X_zero_not_dvd_powerSum (k d : ℕ) (hd : 0 < d) :
    ¬ (X (0 : Fin (k + 2)) : MvPolynomial (Fin (k + 2)) K) ∣ powerSum (k + 2) d := by
  intro h
  have he := map_dvd (eval (fun i : Fin (k + 2) => if i = 1 then (1 : K) else 0)) h
  have hsum := eval_powerSum_basis (K := K) (k + 2) d hd (1 : Fin (k + 2))
  simp only [hsum, eval_X] at he
  have h01 : (0 : Fin (k + 2)) ≠ 1 := by simp
  simp [h01] at he

theorem prime_square_not_dvd_powerSum (k d : ℕ) (hd : 0 < d)
    (p : MvPolynomial (Fin (k + 2)) K) (hp : Prime p) :
    ¬ p ^ 2 ∣ powerSum (k + 2) d := by
  intro hsq
  obtain ⟨q, hq⟩ := hsq
  have hpderiv : p ∣ pderiv (0 : Fin (k + 2)) (powerSum (k + 2) d) := by
    rw [hq, pderiv_mul, pderiv_pow]
    refine ⟨2 * pderiv (0 : Fin (k + 2)) p * q + p * pderiv (0 : Fin (k + 2)) q, ?_⟩
    simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
    ring
  rw [pderiv_powerSum] at hpderiv
  have hdu : IsUnit (C (d : K) : MvPolynomial (Fin (k + 2)) K) :=
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hd.ne')).map C
  have hpx : p ∣ X (0 : Fin (k + 2)) := by
    rcases hp.dvd_mul.mp hpderiv with hc | hx
    · exact False.elim (hp.not_unit (isUnit_of_dvd_unit hc hdu))
    · exact hp.dvd_of_dvd_pow hx
  have hxp : (X (0 : Fin (k + 2)) : MvPolynomial (Fin (k + 2)) K) ∣ p :=
    hp.irreducible.dvd_symm (irreducible_X_zero (K := K) (k + 1)) hpx
  apply X_zero_not_dvd_powerSum (K := K) k d hd
  exact dvd_trans hxp (dvd_trans (dvd_pow_self p (by decide : 2 ≠ 0)) ⟨q, hq⟩)

theorem irreducible_X_pow_add_powerSum (k d : ℕ) (hd : 0 < d) :
    Irreducible (Polynomial.X ^ d + Polynomial.C
      (powerSum (k + 2) d : MvPolynomial (Fin (k + 2)) K)) := by
  obtain ⟨p, hp, hpg⟩ := WfDvdMonoid.exists_irreducible_factor
    (powerSum_not_unit (K := K) (k + 2) d hd)
    (powerSum_ne_zero (K := K) (k + 2) d hd (0 : Fin (k + 2)))
  have hprime : Prime p := hp.prime
  have hP : (Ideal.span ({p} : Set (MvPolynomial (Fin (k + 2)) K))).IsPrime :=
    (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hmonic := Polynomial.monic_X_pow_add_C
    (powerSum (k + 2) d : MvPolynomial (Fin (k + 2)) K) hd.ne'
  have heis : (Polynomial.X ^ d + Polynomial.C
      (powerSum (k + 2) d : MvPolynomial (Fin (k + 2)) K)).IsEisensteinAt
      (Ideal.span {p}) := by
    apply hmonic.isEisensteinAt_of_mem_of_not_mem hP.ne_top
    · intro i hi
      simp only [Polynomial.natDegree_X_pow_add_C] at hi
      rw [Ideal.mem_span_singleton]
      by_cases hi0 : i = 0
      · subst i
        simpa [Polynomial.coeff_X_pow, hd.ne, hd.ne'] using hpg
      · simp [Polynomial.coeff_X_pow, Polynomial.coeff_C, hi.ne, hi.ne', hi0]
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      simpa [Polynomial.coeff_X_pow, hd.ne, hd.ne'] using
        prime_square_not_dvd_powerSum (K := K) k d hd p hprime
  apply heis.irreducible hP hmonic.isPrimitive
  simpa only [Polynomial.natDegree_X_pow_add_C] using hd

theorem powerSum_irreducible (k d : ℕ) (hd : 0 < d) :
    Irreducible (powerSum (k + 3) d : MvPolynomial (Fin (k + 3)) K) := by
  apply (MulEquiv.irreducible_iff (finSuccEquiv K (k + 2)).toMulEquiv).mp
  change Irreducible (finSuccEquiv K (k + 2) (powerSum (k + 3) d))
  have he : finSuccEquiv K (k + 2)
      (powerSum (k + 3) d : MvPolynomial (Fin (k + 3)) K) =
      Polynomial.X ^ d + Polynomial.C
        (powerSum (k + 2) d : MvPolynomial (Fin (k + 2)) K) := by
    rw [powerSum, Fin.sum_univ_succ]
    simp only [map_add, map_sum, map_pow, finSuccEquiv_X_zero, finSuccEquiv_X_succ]
    simp only [powerSum, map_sum, map_pow]
  rw [he]
  exact irreducible_X_pow_add_powerSum k d hd

/-- The homogeneous Fermat polynomial appearing in the manuscript is
irreducible over every characteristic-zero field as soon as `n ≥ 3`. -/
theorem fermat_irreducible {n : ℕ} (hn : 3 ≤ n) :
    Irreducible (PolynomialModel.fermat n : MvPolynomial (Fin n) K) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have hn' : n = k + 3 := by omega
  subst hn'
  simpa only [PolynomialModel.fermat, powerSum] using
    powerSum_irreducible (K := K) k (k + 3) (by omega)

theorem fermat_span_isPrime {n : ℕ} (hn : 3 ≤ n) :
    (Ideal.span ({PolynomialModel.fermat n} : Set (MvPolynomial (Fin n) K))).IsPrime := by
  have hp := (fermat_irreducible (K := K) hn).prime
  exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp

/-- Adding a genuinely free coordinate preserves primality. -/
theorem prime_rename_some {Y : Type*} {f : MvPolynomial Y K} (hf : Prime f) :
    Prime (rename (some : Y → Option Y) f) := by
  have he : optionEquivLeft K Y (rename (some : Y → Option Y) f) = Polynomial.C f := by
    clear hf
    induction f using MvPolynomial.induction_on with
    | C a => simp [optionEquivLeft_C]
    | add f g hf hg => simp [hf, hg]
    | mul_X f i hf => simp [hf, optionEquivLeft_X_some]
  apply (MulEquiv.prime_iff (optionEquivLeft K Y).toMulEquiv).mp
  change Prime (optionEquivLeft K Y (rename (some : Y → Option Y) f))
  rw [he]
  exact Polynomial.prime_C_iff.mpr hf

section AlgebraicTopology
open Set ConormalTopology

/-- The elementary prime-ideal criterion in the actual polynomial topology
used by the conormal development. -/
theorem isIrreducible_of_vanishingIdeal_isPrime {Y : Type*} (S : Set (Y → ℂ))
    (hprime : (MvPolynomial.vanishingIdeal S).IsPrime) :
    @IsIrreducible (Y → ℂ) (algebraicTopology Y) S := by
  letI := algebraicTopology Y
  have hne : S.Nonempty := by
    by_contra h
    have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    exact hprime.ne_top (by rw [he, MvPolynomial.vanishingIdeal_empty])
  refine ⟨hne, isPreirreducible_iff_isClosed_union_isClosed.mpr ?_⟩
  intro U V hU hV hcover
  by_contra h
  have hUS : ¬S ⊆ U := fun hs => h (Or.inl hs)
  have hVS : ¬S ⊆ V := fun hs => h (Or.inr hs)
  obtain ⟨x, hxS, hxU⟩ := Set.not_subset.mp hUS
  obtain ⟨y, hyS, hyV⟩ := Set.not_subset.mp hVS
  have hx : x ∉ ZariskiBridge.zariskiClosure U := by
    rwa [(isClosed_algebraicTopology_iff U).mp hU]
  have hy : y ∉ ZariskiBridge.zariskiClosure V := by
    rwa [(isClosed_algebraicTopology_iff V).mp hV]
  change ¬ (∀ p : MvPolynomial Y ℂ, (∀ z ∈ U, eval z p = 0) → eval x p = 0) at hx
  change ¬ (∀ p : MvPolynomial Y ℂ, (∀ z ∈ V, eval z p = 0) → eval y p = 0) at hy
  push_neg at hx hy
  obtain ⟨p, hpU, hpx⟩ := hx
  obtain ⟨q, hqV, hqy⟩ := hy
  have hpq : p * q ∈ MvPolynomial.vanishingIdeal S := by
    intro z hz
    rcases hcover hz with hzu | hzv
    · simp [hpU z hzu]
    · simp [hqV z hzv]
  rcases hprime.mem_or_mem hpq with hp | hq
  · exact hpx (hp x hxS)
  · exact hqy (hq y hyS)

/-- Nullstellensatz supplies irreducibility of complex closed points, not
merely irreducibility of the abstract prime spectrum. -/
theorem zeroLocus_isIrreducible {Y : Type*} [Finite Y]
    (I : Ideal (MvPolynomial Y ℂ)) (hI : I.IsPrime) :
    @IsIrreducible (Y → ℂ) (algebraicTopology Y) (MvPolynomial.zeroLocus I) := by
  apply isIrreducible_of_vanishingIdeal_isPrime
  rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, hI.radical]
  exact hI

/-- The actual complex affine Fermat zero set is irreducible. -/
theorem fermat_zeroLocus_isIrreducible {n : ℕ} (hn : 3 ≤ n) :
    @IsIrreducible (Fin n → ℂ) (algebraicTopology (Fin n))
      {x | MvPolynomial.eval x (PolynomialModel.fermat n : MvPolynomial (Fin n) ℂ) = 0} := by
  simpa [MvPolynomial.zeroLocus_span] using
    zeroLocus_isIrreducible
      (Ideal.span ({PolynomialModel.fermat n} : Set (MvPolynomial (Fin n) ℂ)))
      (fermat_span_isPrime hn)

end AlgebraicTopology

end Sheshadri.FermatIrreducible
