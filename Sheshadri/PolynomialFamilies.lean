/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.PolynomialAnalytic
import Sheshadri.StableFiniteFibres
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Finite simple roots persist in actual polynomial families

Parameters and unknowns are separate summands of the polynomial variable type.
The only nonsingularity hypothesis is that the displayed formal Jacobian in
the unknown variables has trivial kernel. The full invertible strict
derivative used by the inverse function theorem is constructed here.
-/

noncomputable section

namespace Sheshadri.PolynomialFamilies

open MvPolynomial Function Filter Matrix
open scoped Topology

variable {K A Z : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Fintype A] [Fintype Z]

def family (F : Z → MvPolynomial (A ⊕ Z) K) (p : A → K) (z : Z → K) : Z → K :=
  fun i => eval (Sum.elim p z) (F i)

def split : (A ⊕ Z → K) ≃L[K] ((A → K) × (Z → K)) :=
  ContinuousLinearEquiv.sumPiEquivProdPi K A Z (fun _ => K)

def familyDerivative (F : Z → MvPolynomial (A ⊕ Z) K)
    (p : A → K) (z : Z → K) : ((A → K) × (Z → K)) →L[K] (Z → K) :=
  (PolynomialAnalytic.systemDerivative F (Sum.elim p z)).comp split.symm.toContinuousLinearMap

def totalDerivative (F : Z → MvPolynomial (A ⊕ Z) K)
    (p : A → K) (z : Z → K) :
    ((A → K) × (Z → K)) →L[K] ((A → K) × (Z → K)) :=
  (ContinuousLinearMap.fst K (A → K) (Z → K)).prod (familyDerivative F p z)

omit [CompleteSpace K] in
theorem familyDerivative_apply (F : Z → MvPolynomial (A ⊕ Z) K)
    (p : A → K) (z : Z → K) (v : (A → K) × (Z → K)) (i : Z) :
    familyDerivative F p z v i =
      ∑ j, eval (Sum.elim p z) (pderiv j (F i)) * Sum.elim v.1 v.2 j := by
  exact PolynomialAnalytic.systemDerivative_apply F (Sum.elim p z) (Sum.elim v.1 v.2) i

omit [CompleteSpace K] in
theorem hasStrictFDerivAt_family (F : Z → MvPolynomial (A ⊕ Z) K)
    (p : A → K) (z : Z → K) :
    HasStrictFDerivAt (fun q : (A → K) × (Z → K) => family F q.1 q.2)
      (familyDerivative F p z) (p, z) := by
  exact (PolynomialAnalytic.hasStrictFDerivAt_system F (Sum.elim p z)).comp (p, z)
    (split.symm.hasStrictFDerivAt)

omit [CompleteSpace K] in
theorem hasStrictFDerivAt_total (F : Z → MvPolynomial (A ⊕ Z) K)
    (p : A → K) (z : Z → K) :
    HasStrictFDerivAt (StableFiniteFibres.totalMap (family F))
      (totalDerivative F p z) (p, z) := by
  exact (ContinuousLinearMap.fst K (A → K) (Z → K)).hasStrictFDerivAt.prodMk
    (hasStrictFDerivAt_family F p z)

/-- Nonsingularity in the unknown variables is an explicit formal-Jacobian
kernel statement, not an axiom asserting geometric transversality. -/
def Regular (F : Z → MvPolynomial (A ⊕ Z) K) (p : A → K) (z : Z → K) : Prop :=
  ∀ v : Z → K,
    (∀ i, (∑ j, eval (Sum.elim p z) (pderiv (Sum.inr j) (F i)) * v j) = 0) → v = 0

def unknownJacobian (F : Z → MvPolynomial (A ⊕ Z) K)
    (q : (A → K) × (Z → K)) : Matrix Z Z K :=
  fun i j => eval (Sum.elim q.1 q.2) (pderiv (Sum.inr j) (F i))

def regularityDet (F : Z → MvPolynomial (A ⊕ Z) K)
    (q : (A → K) × (Z → K)) : K := by
  classical
  exact (unknownJacobian F q).det

omit [CompleteSpace K] [Fintype A] in
theorem regularityDet_ne_zero_iff (F : Z → MvPolynomial (A ⊕ Z) K)
    (p : A → K) (z : Z → K) :
    regularityDet F (p, z) ≠ 0 ↔ Regular F p z := by
  classical
  constructor
  · intro hd v hv
    have hu : IsUnit (unknownJacobian F (p, z)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)
    apply (Matrix.mulVec_injective_iff_isUnit.mpr hu)
    rw [Matrix.mulVec_zero]
    funext i
    exact hv i
  · intro hreg
    have hk : LinearMap.ker (unknownJacobian F (p, z)).mulVecLin = ⊥ := by
      apply LinearMap.ker_eq_bot'.mpr
      intro v hv
      apply hreg v
      intro i
      exact congrFun hv i
    have hu : IsUnit (unknownJacobian F (p, z)) :=
      Matrix.mulVec_injective_iff_isUnit.mp (LinearMap.ker_eq_bot.mp hk)
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

omit [CompleteSpace K] in
theorem continuous_regularityDet (F : Z → MvPolynomial (A ⊕ Z) K) :
    Continuous (regularityDet F) := by
  classical
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply continuous_iff_continuousAt.mpr
  intro q
  have hin : ContinuousAt (fun r : (A → K) × (Z → K) => Sum.elim r.1 r.2) q :=
    split.symm.continuous.continuousAt
  exact ContinuousAt.comp (f := fun r : (A → K) × (Z → K) => Sum.elim r.1 r.2)
    (PolynomialAnalytic.hasStrictFDerivAt_eval (pderiv (Sum.inr j) (F i))
      (Sum.elim q.1 q.2)).continuousAt hin

omit [CompleteSpace K] in
theorem totalDerivative_ker_eq_bot (F : Z → MvPolynomial (A ⊕ Z) K)
    (p : A → K) (z : Z → K) (hreg : Regular F p z) :
    LinearMap.ker (totalDerivative F p z).toLinearMap = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hp : v.1 = 0 := congrArg Prod.fst hv
  have hz : v.2 = 0 := by
    apply hreg
    intro i
    have he := congrFun (congrArg Prod.snd hv) i
    change familyDerivative F p z v i = 0 at he
    rw [familyDerivative_apply, Fintype.sum_sum_type] at he
    simpa [hp] using he
  exact Prod.ext hp hz

/-- The inverse-function input is proved from the actual unknown-variable
Jacobian, including its finite-dimensional invertibility. -/
theorem exists_total_equiv_derivative (F : Z → MvPolynomial (A ⊕ Z) K)
    (p : A → K) (z : Z → K) (hreg : Regular F p z) :
    ∃ e : ((A → K) × (Z → K)) ≃L[K] ((A → K) × (Z → K)),
      HasStrictFDerivAt (StableFiniteFibres.totalMap (family F))
        (e : ((A → K) × (Z → K)) →L[K] ((A → K) × (Z → K))) (p, z) := by
  let D := totalDerivative F p z
  have hker : LinearMap.ker D.toLinearMap = ⊥ := totalDerivative_ker_eq_bot F p z hreg
  have hsurj : LinearMap.range D.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr
      (LinearMap.surjective_of_injective (LinearMap.ker_eq_bot.mp hker))
  refine ⟨ContinuousLinearEquiv.ofBijective D hker hsurj, ?_⟩
  rw [ContinuousLinearEquiv.coe_ofBijective]
  exact hasStrictFDerivAt_total F p z

/-- Finite simple roots of an actual polynomial family persist under small
parameter changes. No analytic differentiability hypothesis is supplied. -/
theorem finite_polynomial_roots_persist {I : Type*} [Finite I]
    (F : Z → MvPolynomial (A ⊕ Z) K) (p₀ : A → K) (z : I → Z → K)
    (hz : Injective z) (hroot : ∀ i, family F p₀ (z i) = 0)
    (hreg : ∀ i, Regular F p₀ (z i)) :
    ∃ b : I → (A → K) → (Z → K),
      (∀ i, b i p₀ = z i) ∧ (∀ i, ContinuousAt (b i) p₀) ∧
      ∀ᶠ p in 𝓝 p₀, Injective (fun i => b i p) ∧ ∀ i, family F p (b i p) = 0 := by
  choose e he using (fun i => exists_total_equiv_derivative F p₀ (z i) (hreg i))
  exact StableFiniteFibres.finite_simple_roots_persist (family F) p₀ z hz e hroot he

/-- A continuous scalar regularity certificate, such as the Jacobian
determinant, also remains nonzero on all nearby root branches. -/
theorem finite_polynomial_roots_persist_with_nonvanishing {I : Type*} [Finite I]
    (F : Z → MvPolynomial (A ⊕ Z) K) (p₀ : A → K) (z : I → Z → K)
    (hz : Injective z) (hroot : ∀ i, family F p₀ (z i) = 0)
    (hreg : ∀ i, Regular F p₀ (z i))
    (J : ((A → K) × (Z → K)) → K)
    (hJ : ∀ i, ContinuousAt J (p₀, z i)) (hJ0 : ∀ i, J (p₀, z i) ≠ 0) :
    ∃ b : I → (A → K) → (Z → K),
      (∀ i, b i p₀ = z i) ∧ (∀ i, ContinuousAt (b i) p₀) ∧
      ∀ᶠ p in 𝓝 p₀, Injective (fun i => b i p) ∧
        (∀ i, family F p (b i p) = 0) ∧ ∀ i, J (p, b i p) ≠ 0 := by
  choose e he using (fun i => exists_total_equiv_derivative F p₀ (z i) (hreg i))
  exact StableFiniteFibres.finite_regular_roots_persist (family F) p₀ z hz e hroot he J hJ hJ0

/-- Full polynomial-family persistence: finitely many distinct regular zeros
remain distinct regular zeros nearby. All differentiation, invertibility,
continuity, and root-branch construction are proved in Lean. -/
theorem finite_regular_polynomial_roots_persist {I : Type*} [Finite I]
    (F : Z → MvPolynomial (A ⊕ Z) K) (p₀ : A → K) (z : I → Z → K)
    (hz : Injective z) (hroot : ∀ i, family F p₀ (z i) = 0)
    (hreg : ∀ i, Regular F p₀ (z i)) :
    ∃ b : I → (A → K) → (Z → K),
      (∀ i, b i p₀ = z i) ∧ (∀ i, ContinuousAt (b i) p₀) ∧
      ∀ᶠ p in 𝓝 p₀, Injective (fun i => b i p) ∧
        (∀ i, family F p (b i p) = 0) ∧ ∀ i, Regular F p (b i p) := by
  obtain ⟨b, hb0, hbc, hb⟩ := finite_polynomial_roots_persist_with_nonvanishing
    F p₀ z hz hroot hreg (regularityDet F)
    (fun _ => (continuous_regularityDet F).continuousAt)
    (fun i => (regularityDet_ne_zero_iff F p₀ (z i)).mpr (hreg i))
  refine ⟨b, hb0, hbc, ?_⟩
  filter_upwards [hb] with p hp
  exact ⟨hp.1, hp.2.1, fun i => (regularityDet_ne_zero_iff F p (b i p)).mp (hp.2.2 i)⟩

end Sheshadri.PolynomialFamilies
