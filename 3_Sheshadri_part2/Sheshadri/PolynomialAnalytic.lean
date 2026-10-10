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
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Ring

/-!
# The formal polynomial Jacobian is the analytic strict derivative

This bridge is proved by induction on actual multivariate polynomials.
It supplies the calculus input needed to apply the inverse function theorem
to explicit polynomial systems. There are no custom axioms.
-/

noncomputable section

namespace Sheshadri.PolynomialAnalytic

open MvPolynomial

variable {K σ : Type*} [NontriviallyNormedField K] [Fintype σ]

def derivative (p : MvPolynomial σ K) (a : σ → K) : (σ → K) →L[K] K :=
  ∑ i, eval a (pderiv i p) • ContinuousLinearMap.proj i

theorem derivative_apply (p : MvPolynomial σ K) (a v : σ → K) :
    derivative p a v = ∑ i, eval a (pderiv i p) * v i := by
  simp [derivative, smul_eq_mul]

@[simp] theorem derivative_C (c : K) (a : σ → K) : derivative (C c) a = 0 := by
  ext v
  simp [derivative_apply, pderiv_C]

@[simp] theorem derivative_X (j : σ) (a : σ → K) :
    derivative (X j) a = ContinuousLinearMap.proj j := by
  classical
  ext v
  simp [derivative_apply, Pi.single_apply]

@[simp] theorem derivative_add (p q : MvPolynomial σ K) (a : σ → K) :
    derivative (p + q) a = derivative p a + derivative q a := by
  ext v
  simp [derivative_apply, add_mul, Finset.sum_add_distrib]

theorem derivative_mul (p q : MvPolynomial σ K) (a : σ → K) :
    derivative (p * q) a = eval a p • derivative q a + eval a q • derivative p a := by
  ext v
  simp only [derivative_apply, pderiv_mul, map_add, map_mul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Formal partial differentiation agrees with the actual strict Fréchet
derivative of multivariate evaluation over any nontrivially normed field. -/
theorem hasStrictFDerivAt_eval (p : MvPolynomial σ K) (a : σ → K) :
    HasStrictFDerivAt (fun z => eval z p) (derivative p a) a := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using (hasStrictFDerivAt_const (𝕜 := K) c a)
  | add p q hp hq => simpa using hp.add hq
  | mul_X p j hp =>
    simpa [derivative_mul] using hp.mul (hasStrictFDerivAt_apply j a)

def systemDerivative {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ K) (a : σ → K) : (σ → K) →L[K] (ι → K) :=
  ContinuousLinearMap.pi (fun i => derivative (f i) a)

/-- The Jacobian matrix of a vector-valued polynomial system is its genuine
analytic strict derivative. -/
theorem hasStrictFDerivAt_system {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ K) (a : σ → K) :
    HasStrictFDerivAt (fun z i => eval z (f i)) (systemDerivative f a) a := by
  exact hasStrictFDerivAt_pi.mpr (fun i => hasStrictFDerivAt_eval (f i) a)

theorem systemDerivative_apply {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial σ K) (a v : σ → K) (i : ι) :
    systemDerivative f a v i = ∑ j, eval a (pderiv j (f i)) * v j :=
  derivative_apply (f i) a v

/-- A square polynomial system with trivial formal Jacobian kernel has the
invertible analytic strict derivative needed by the inverse function theorem. -/
theorem exists_equiv_strict_derivative [CompleteSpace K]
    (f : σ → MvPolynomial σ K) (a : σ → K)
    (hker : ∀ v : σ → K,
      (∀ i, (∑ j, eval a (pderiv j (f i)) * v j) = 0) → v = 0) :
    ∃ e : (σ → K) ≃L[K] (σ → K),
      HasStrictFDerivAt (fun z i => eval z (f i)) (e : (σ → K) →L[K] (σ → K)) a := by
  let D := systemDerivative f a
  have hD : LinearMap.ker D.toLinearMap = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply hker v
    intro i
    simpa [D, systemDerivative_apply] using congrFun hv i
  have hsurj : LinearMap.range D.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr
      (LinearMap.surjective_of_injective (LinearMap.ker_eq_bot.mp hD))
  refine ⟨ContinuousLinearEquiv.ofBijective D hD hsurj, ?_⟩
  rw [ContinuousLinearEquiv.coe_ofBijective]
  exact hasStrictFDerivAt_system f a

end Sheshadri.PolynomialAnalytic
