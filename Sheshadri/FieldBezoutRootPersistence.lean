/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldProjectiveMultiplicityInterpolation

noncomputable section
open Sheshadri.MultiProjective
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

namespace Sheshadri.FieldBezoutRootPersistence
variable {k₀ : Type*} [Field k₀] [CharZero k₀]
open MvPolynomial
section CoefficientPresentation
variable {Z : Type*}

def parameterCoordinates : Unit ⊕ Z ≃ Option Z where
  toFun := Sum.elim (fun _ => none) some
  invFun := fun i => Option.elim i (Sum.inl ()) Sum.inr
  left_inv := by rintro (⟨⟩ | i) <;> rfl
  right_inv := by rintro (⟨⟩ | i) <;> rfl

def coefficientEquiv : MvPolynomial (Unit ⊕ Z) k₀ ≃ₐ[k₀] MvPolynomial Z (Polynomial k₀) :=
  (renameEquiv k₀ parameterCoordinates).trans (optionEquivRight k₀ Z)

@[simp] theorem coefficientEquiv_C (c : k₀) :
    coefficientEquiv (Z := Z) (C c) = C (Polynomial.C c) := by
  simp [coefficientEquiv, optionEquivRight_C]

@[simp] theorem coefficientEquiv_parameter :
    coefficientEquiv (k₀ := k₀) (Z := Z) (X (Sum.inl ())) = C Polynomial.X := by
  simp [coefficientEquiv, parameterCoordinates, optionEquivRight_X_none]

@[simp] theorem coefficientEquiv_spatial (i : Z) :
    coefficientEquiv (k₀ := k₀) (X (Sum.inr i)) = X i := by
  simp [coefficientEquiv, parameterCoordinates, optionEquivRight_X_some]

theorem coefficientEquiv_rename (f : MvPolynomial Z k₀) :
    coefficientEquiv (rename Sum.inr f) = MvPolynomial.map Polynomial.C f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg]
  | mul_X f i hf => simp [hf]

theorem eval_coefficientEquiv (a : k₀) (z : Z → k₀) (G : MvPolynomial (Unit ⊕ Z) k₀) :
    eval₂ (Polynomial.evalRingHom a) z (coefficientEquiv G) =
      eval (Sum.elim (fun _ => a) z) G := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg]
  | mul_X f i hf =>
    cases i with
    | inl u => cases u; simp [hf]
    | inr i => simp [hf]

/-- Linear interpolation between the original and split systems, with an
actual coefficient variable rather than an abstract family certificate. -/
def interpolation (f g : MvPolynomial Z k₀) : MvPolynomial (Unit ⊕ Z) k₀ :=
  (1 - X (Sum.inl ())) * rename Sum.inr f + X (Sum.inl ()) * rename Sum.inr g

theorem coefficientEquiv_interpolation (f g : MvPolynomial Z k₀) :
    coefficientEquiv (interpolation f g) =
      C (1-Polynomial.X) * MvPolynomial.map Polynomial.C f +
        C Polynomial.X * MvPolynomial.map Polynomial.C g := by
  simp [interpolation, coefficientEquiv_rename]

/-- The coefficient interpolation has exactly the same multidegree as its
endpoints; the parameter is part of the coefficient ring and has degree zero. -/
theorem coefficient_interpolation_homogeneous {Γ : Type*} [AddCommMonoid Γ]
    (w : Z → Γ) (d : Γ) (f g : MvPolynomial Z k₀)
    (hf : f.IsWeightedHomogeneous w d) (hg : g.IsWeightedHomogeneous w d) :
    (coefficientEquiv (interpolation f g)).IsWeightedHomogeneous w d := by
  rw [coefficientEquiv_interpolation]
  have hf' := GeneralHomogeneousBaseChange.weightedHomogeneous_map Polynomial.C w hf
  have hg' := GeneralHomogeneousBaseChange.weightedHomogeneous_map Polynomial.C w hg
  have h₁ := (isWeightedHomogeneous_C w (1-Polynomial.X : Polynomial k₀)).mul hf'
  have h₂ := (isWeightedHomogeneous_C w (Polynomial.X : Polynomial k₀)).mul hg'
  simpa only [zero_add] using h₁.add h₂

end CoefficientPresentation


end Sheshadri.FieldBezoutRootPersistence
