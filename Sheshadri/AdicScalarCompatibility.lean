/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Scalar-compatible principal-adic completions

The completion of an algebra as a module over the base ring agrees with
its completion as a ring at the extended principal ideal. These are literal
inverse-limit equivalences, preserving the canonical maps and scalars.
-/

noncomputable section
namespace Sheshadri.AdicScalarCompatibility
open scoped Pointwise
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 150000

variable {D B : Type*} [CommRing D] [CommRing B] [Algebra D B] (π : D)

abbrev baseIdeal : Ideal D := Ideal.span {π}
abbrev extendedIdeal : Ideal B := Ideal.span {algebraMap D B π}

/-- Principal-adic filtrations agree after restricting scalars. -/
theorem filtration_eq (n : ℕ) :
    (baseIdeal π ^ n • (⊤ : Submodule D B)) =
    ((extendedIdeal (B := B) π ^ n • (⊤ : Submodule B B))).restrictScalars D := by
  ext x
  change x ∈ (baseIdeal π ^ n • (⊤ : Submodule D B)) ↔
    x ∈ (extendedIdeal (B := B) π ^ n • (⊤ : Submodule B B))
  simp only [baseIdeal, extendedIdeal, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  simp only [Algebra.smul_def, map_pow, smul_eq_mul]
  rfl

def quotientEquiv (n : ℕ) :
    (B ⧸ (baseIdeal π ^ n • (⊤ : Submodule D B))) ≃ₗ[D]
    (B ⧸ (extendedIdeal (B := B) π ^ n • (⊤ : Submodule B B))) :=
  (Submodule.quotEquivOfEq _ _ (filtration_eq (B := B) π n)).trans
    (Submodule.Quotient.restrictScalarsEquiv D _)

@[simp] theorem quotientEquiv_mk (n : ℕ) (b : B) :
    quotientEquiv π n (Submodule.Quotient.mk b) = Submodule.Quotient.mk b := rfl

@[simp] theorem quotientEquiv_symm_mk (n : ℕ) (b : B) :
    (quotientEquiv π n).symm (Submodule.Quotient.mk b) = Submodule.Quotient.mk b := rfl

theorem quotientEquiv_transition {m n : ℕ} (h : m ≤ n)
    (x : B ⧸ (baseIdeal π ^ n • (⊤ : Submodule D B))) :
    quotientEquiv π m (AdicCompletion.transitionMap (baseIdeal π) B h x) =
    AdicCompletion.transitionMap (extendedIdeal (B := B) π) B h (quotientEquiv π n x) := by
  induction x using Submodule.Quotient.induction_on
  rfl

theorem quotientEquiv_symm_transition {m n : ℕ} (h : m ≤ n)
    (x : B ⧸ (extendedIdeal (B := B) π ^ n • (⊤ : Submodule B B))) :
    (quotientEquiv π m).symm (AdicCompletion.transitionMap (extendedIdeal (B := B) π) B h x) =
    AdicCompletion.transitionMap (baseIdeal π) B h ((quotientEquiv π n).symm x) := by
  induction x using Submodule.Quotient.induction_on
  rfl

/-- The canonical equivalence between base-module and algebra-ring completion. -/
def completionEquiv :
    AdicCompletion (baseIdeal π) B ≃ₗ[D] AdicCompletion (extendedIdeal (B := B) π) B where
  toFun x := ⟨fun n => quotientEquiv π n (x.val n), fun h => by
    rw [← quotientEquiv_transition, x.property h]⟩
  invFun x := ⟨fun n => (quotientEquiv π n).symm (x.val n), fun h => by
    rw [← quotientEquiv_symm_transition, x.property h]⟩
  left_inv x := AdicCompletion.ext (fun n => (quotientEquiv π n).symm_apply_apply _)
  right_inv x := AdicCompletion.ext (fun n => (quotientEquiv π n).apply_symm_apply _)
  map_add' x y := AdicCompletion.ext (fun n => (quotientEquiv π n).map_add _ _)
  map_smul' r x := AdicCompletion.ext (fun n => (quotientEquiv π n).map_smul r _)

@[simp] theorem completionEquiv_of (b : B) :
    completionEquiv π (AdicCompletion.of (baseIdeal π) B b) =
      algebraMap B (AdicCompletion (extendedIdeal (B := B) π) B) b := by
  apply AdicCompletion.ext
  intro n
  rfl

/-- Injective multiplication by a scalar remains injective on the actual
ring completion. This uses exactness over the Noetherian ring itself. -/
theorem ring_completion_scalar_regular [IsNoetherianRing B]
    (hπ : IsSMulRegular B π) :
    IsSMulRegular (AdicCompletion (extendedIdeal (B := B) π) B) π := by
  let f : B →ₗ[B] B := LinearMap.lsmul B B (algebraMap D B π)
  have hf : Function.Injective f := by
    intro x y h
    apply hπ
    simpa only [f, LinearMap.lsmul_apply, Algebra.smul_def] using h
  have hinj := AdicCompletion.map_injective (extendedIdeal (B := B) π) hf
  have he (x : AdicCompletion (extendedIdeal (B := B) π) B) :
      AdicCompletion.map (extendedIdeal (B := B) π) f x = π • x := by
    apply AdicCompletion.ext
    intro n
    change f.reduceModIdeal _ (x.val n) = π • x.val n
    induction x.val n using Submodule.Quotient.induction_on
    simp only [LinearMap.reduceModIdeal_apply, f, LinearMap.lsmul_apply,
      ← Submodule.Quotient.mk_smul, Algebra.smul_def]
    rfl
  intro x y h
  apply hinj
  simpa only [he] using h

/-- The same cancellation theorem in the base-module presentation used for
finite-free completion bases. -/
theorem module_completion_scalar_regular [IsNoetherianRing B]
    (hπ : IsSMulRegular B π) :
    IsSMulRegular (AdicCompletion (baseIdeal π) B) π := by
  intro x y h
  apply (completionEquiv (B := B) π).injective
  apply ring_completion_scalar_regular π hπ
  simpa only [map_smul] using congrArg (completionEquiv (B := B) π) h

end Sheshadri.AdicScalarCompatibility
