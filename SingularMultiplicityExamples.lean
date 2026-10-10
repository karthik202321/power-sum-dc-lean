/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.IsolatedLocalMultiplicity
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Singular multiplicity regression examples

The actual local intersection ring of `x^m = 0` at the origin has length `m`.
In particular, the double zero has multiplicity two even though its reduced
zero set consists of a single point.
-/

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section
namespace Sheshadri.SingularMultiplicityExamples

open IsolatedLocalMultiplicity MvPolynomial

variable (K : Type*) [Field K]

abbrev origin : PUnit → K := fun _ => 0

/-- The literal equation ideal `(x^m)` in a one-variable polynomial ring. -/
def powerIdeal (m : ℕ) : Ideal (MvPolynomial PUnit K) :=
  Ideal.span {X PUnit.unit ^ m}

theorem pointIdeal_origin : pointIdeal (origin K) = Ideal.span {X PUnit.unit} := by
  apply le_antisymm
  · intro f hf
    have hpoly : ∀ f : MvPolynomial PUnit K,
        f - C (eval (origin K) f) ∈ Ideal.span {X PUnit.unit} := by
      intro f
      induction f using MvPolynomial.induction_on with
      | C r => simp
      | add f g hf hg =>
        simpa only [map_add, add_sub_add_comm] using Ideal.add_mem _ hf hg
      | mul_X f i hf =>
        cases i
        simpa [origin] using
          (Ideal.mul_mem_left (Ideal.span {X PUnit.unit}) f
            (Ideal.mem_span_singleton_self (X PUnit.unit)))
    change eval (origin K) f = 0 at hf
    simpa only [hf, map_zero, sub_zero] using hpoly f
  · apply Ideal.span_le.mpr
    intro f hf
    rcases Set.mem_singleton_iff.mp hf with rfl
    simp [origin]

theorem powerIdeal_le_pointIdeal (m : ℕ) (hm : 0 < m) :
    powerIdeal K m ≤ pointIdeal (origin K) := by
  apply Ideal.span_le.mpr
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  simp [origin, Nat.ne_of_gt hm]

theorem pointIdeal_pow_origin (m : ℕ) :
    pointIdeal (origin K) ^ m = powerIdeal K m := by
  rw [pointIdeal_origin, Ideal.span_singleton_pow]
  rfl

/-- The actual equation quotient is the usual truncated polynomial algebra. -/
def quotientEquivAdjoinRoot (m : ℕ) :
    EquationQuotient (powerIdeal K m) ≃ₐ[K] AdjoinRoot (Polynomial.X ^ m : Polynomial K) :=
  Ideal.quotientEquivAlg (powerIdeal K m) (Ideal.span {Polynomial.X ^ m})
    (MvPolynomial.pUnitAlgEquiv K) (by
      simp [powerIdeal, Ideal.map_span, Set.image_singleton,
        MvPolynomial.pUnitAlgEquiv_apply])

theorem equation_finrank (m : ℕ) :
    Module.finrank K (EquationQuotient (powerIdeal K m)) = m := by
  rw [(quotientEquivAdjoinRoot K m).toLinearEquiv.finrank_eq]
  simpa using (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow m :
    (Polynomial.X ^ m : Polynomial K).Monic)).finrank

/-- The point maximal ideal vanishes to exactly the available truncation order
in the actual local intersection ring. -/
theorem pointPower_le_localKernel (m : ℕ) (hm : 0 < m) :
    pointIdeal (origin K) ^ m ≤ RingHom.ker
      (localPolynomialMap (powerIdeal K m) (origin K) (powerIdeal_le_pointIdeal K m hm)) := by
  rw [pointIdeal_pow_origin]
  intro f hf
  change algebraMap _ _ (Ideal.Quotient.mk (powerIdeal K m) f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]

/-- Localizing the actual fat point does not remove its nilpotent structure. -/
def localEquivEquation (m : ℕ) (hm : 0 < m) :
    LocalIntersectionRing (powerIdeal K m) (origin K) (powerIdeal_le_pointIdeal K m hm)
      ≃ₐ[K] EquationQuotient (powerIdeal K m) :=
  (localEquivFatPointOfPow (powerIdeal K m) (origin K)
    (powerIdeal_le_pointIdeal K m hm) m (pointPower_le_localKernel K m hm)).trans
    (Ideal.quotientEquivAlgOfEq K (by simp [fatPointIdeal, pointIdeal_pow_origin]))

/-- Transporting to any finite algebra establishes finite local length without
assuming its value. -/
theorem multiplicity_eq_of_equiv {σ A : Type*} [CommRing A] [Algebra K A]
    [Module.Finite K A] (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) (e : LocalIntersectionRing I p hI ≃ₐ[K] A) :
    multiplicity I p hI = (Module.finrank K A : ℕ∞) := by
  letI : Module.Finite K (LocalIntersectionRing I p hI) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  change Module.length (LocalIntersectionRing I p hI) (LocalIntersectionRing I p hI) = _
  rw [LocalLengthDimension.length_eq_finrank (localEvaluationAlg I p hI)
    (LocalIntersectionRing I p hI), e.toLinearEquiv.finrank_eq]

/-- An explicit finite algebra model proves isolatedness. -/
theorem local_artinian_of_equiv {σ A : Type*} [CommRing A] [Algebra K A]
    [Module.Finite K A] (I : Ideal (MvPolynomial σ K)) (p : σ → K)
    (hI : I ≤ pointIdeal p) (e : LocalIntersectionRing I p hI ≃ₐ[K] A) :
    IsArtinianRing (LocalIntersectionRing I p hI) := by
  letI : Module.Finite K (LocalIntersectionRing I p hI) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  exact isArtinian_of_tower K (inferInstance : IsArtinian K (LocalIntersectionRing I p hI))

/-- The literal root is algebraically isolated, proved using its truncation
algebra rather than assumed as a hypothesis. -/
theorem local_power_artinian (m : ℕ) (hm : 0 < m) :
    IsArtinianRing (LocalIntersectionRing (powerIdeal K m) (origin K)
      (powerIdeal_le_pointIdeal K m hm)) := by
  letI : Module.Finite K (AdjoinRoot (Polynomial.X ^ m : Polynomial K)) :=
    (Polynomial.monic_X_pow m).finite_adjoinRoot
  exact local_artinian_of_equiv K _ _ _
    ((localEquivEquation K m hm).trans (quotientEquivAdjoinRoot K m))

/-- A singular isolated root of `x^m` contributes `m`, not one. This uses the
literal localized quotient and its module length. -/
theorem power_multiplicity (m : ℕ) (hm : 0 < m) :
    multiplicity (powerIdeal K m) (origin K) (powerIdeal_le_pointIdeal K m hm) = (m : ℕ∞) := by
  letI : Module.Finite K (AdjoinRoot (Polynomial.X ^ m : Polynomial K)) :=
    (Polynomial.monic_X_pow m).finite_adjoinRoot
  rw [multiplicity_eq_of_equiv K _ _ _
    ((localEquivEquation K m hm).trans (quotientEquivAdjoinRoot K m))]
  congr 1
  simpa using (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow m :
    (Polynomial.X ^ m : Polynomial K).Monic)).finrank

/-- The underlying zero set has exactly one point for every positive exponent. -/
theorem power_zero_iff_origin (m : ℕ) (hm : 0 < m) (p : PUnit → K) :
    eval p (X PUnit.unit ^ m : MvPolynomial PUnit K) = 0 ↔ p = origin K := by
  simp only [map_pow, eval_X, pow_eq_zero_iff (Nat.ne_of_gt hm)]
  constructor
  · intro hp
    funext i
    cases i
    exact hp
  · intro hp
    rw [hp]

/-- The double root fails the derivative test for a simple zero. -/
theorem double_zero_derivative :
    eval (origin K) (pderiv PUnit.unit (X PUnit.unit ^ 2 : MvPolynomial PUnit K)) = 0 := by
  simp [origin, pderiv_pow]

theorem double_zero_multiplicity :
    multiplicity (powerIdeal K 2) (origin K) (powerIdeal_le_pointIdeal K 2 (by decide)) = 2 :=
  power_multiplicity K 2 (by decide)

end Sheshadri.SingularMultiplicityExamples
