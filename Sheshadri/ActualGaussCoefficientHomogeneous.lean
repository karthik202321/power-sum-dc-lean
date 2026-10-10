/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ActualGaussCoefficientRing
import Sheshadri.FlatGradedHilbert
import Sheshadri.HomogeneousVanishing

/-!
# Bihomogeneity over the polynomial parameter ring

This bridges the actual scaled Gauss graph to its presentation over `ℂ[t]`.
The parameter is a coefficient, so each bihomogeneous coordinate module is
finite over the base. Its homogeneous projections preserve the actual ideal.
-/

noncomputable section
namespace Sheshadri.ActualGaussCoefficientRing

open MvPolynomial ActualGaussFamily

variable {Z : Type} [Fintype Z]

def spatialBlock : SpatialVariables Z → Bool := Sum.elim (fun _ => true) (fun _ => false)

/-- Evaluation is preserved when the parameter is repackaged as a coefficient. -/
theorem eval_coefficientEquiv (p : MvPolynomial (TotalCoordinates Unit Z) ℂ)
    (a : Unit → ℂ) (v : SpatialVariables Z → ℂ) :
    (coefficientEquiv p).eval₂ (Polynomial.evalRingHom (a ())) v =
      eval (Sum.elim a v) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, eval₂_mul, hp, map_mul]
    congr 1
    cases i with
    | inl i => cases i; simp
    | inr i => simp

theorem mem_coefficientIdeal_iff
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ))
    (p : MvPolynomial (SpatialVariables Z) (Polynomial ℂ)) :
    p ∈ coefficientIdeal F U ↔ coefficientEquiv.symm p ∈ totalIdeal F U := by
  change p ∈ (totalIdeal F U).map coefficientEquiv.toRingHom ↔ _
  rw [Ideal.mem_map_iff_of_surjective coefficientEquiv.toRingHom coefficientEquiv.surjective]
  constructor
  · rintro ⟨f, hf, hfp⟩
    change coefficientEquiv f = p at hfp
    rw [← hfp, AlgEquiv.symm_apply_apply]
    exact hf
  · intro hp
    exact ⟨coefficientEquiv.symm p, hp, coefficientEquiv.apply_symm_apply p⟩

/-- Actual bihomogeneity over the base PID, with no assumed homogeneous
ideal certificate. The proof uses literal independent graph rescalings. -/
theorem coefficientIdeal_bihomogeneous
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) :
    FlatGradedHilbert.IsBihomogeneous (SpatialVariables Z) (Polynomial ℂ)
      spatialBlock (coefficientIdeal F U) := by
  intro a b p hp
  rw [mem_coefficientIdeal_iff] at hp ⊢
  intro q hq
  let par : Unit → ℂ := fun _ => q (Sum.inl ())
  let v : SpatialVariables Z → ℂ := fun i => q (Sum.inr i)
  have hqsplit : Sum.elim par v = q := by
    funext i
    cases i with
    | inl i => cases i; rfl
    | inr i => rfl
  rw [← hqsplit, ← eval_coefficientEquiv, AlgEquiv.apply_symm_apply]
  apply HomogeneousVanishing.biweightedComponent_eval_zero
  intro s t hs ht
  rw [← coefficientEquiv.apply_symm_apply p, eval_coefficientEquiv]
  apply hp
  convert rescaleTotal_mem_totalGraph F U s t hs ht hq using 1
  funext i
  cases i with
  | inl i => cases i; simp [par, rescaleTotal]
  | inr i =>
    cases i <;> simp [FlatGradedHilbert.twoBlockWeight, spatialBlock, v, rescaleTotal]

end Sheshadri.ActualGaussCoefficientRing
