/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ActualGaussFlatScheme
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Put the parameter in the coefficient ring

The actual total ideal was constructed in `ℂ[t, primal, dual]`.  The explicit
equivalence below rewrites it as an ideal in `ℂ[t][primal, dual]`, over the
base PID `ℂ[t]`.  This is essential for finite homogeneous coordinate pieces:
the parameter has degree zero and belongs to the coefficient ring.
-/

noncomputable section
namespace Sheshadri.ActualGaussCoefficientRing

open MvPolynomial ActualGaussFamily ActualGaussFlatness

variable {Z : Type} [Fintype Z]

abbrev SpatialVariables (Z : Type) := Option Z ⊕ Option Z

def coordinatesEquiv : TotalCoordinates Unit Z ≃ Option (SpatialVariables Z) where
  toFun := Sum.elim (fun _ => none) some
  invFun := fun i => Option.elim i (Sum.inl ()) Sum.inr
  left_inv := by rintro (⟨⟩ | i) <;> rfl
  right_inv := by rintro (⟨⟩ | i) <;> rfl

/-- The explicit equivalence that makes the base parameter a coefficient. -/
def coefficientEquiv :
    MvPolynomial (TotalCoordinates Unit Z) ℂ ≃ₐ[ℂ]
      MvPolynomial (SpatialVariables Z) (Polynomial ℂ) :=
  (renameEquiv ℂ coordinatesEquiv).trans (optionEquivRight ℂ (SpatialVariables Z))

@[simp] theorem coefficientEquiv_C (c : ℂ) :
    coefficientEquiv (Z := Z) (C c) = C (Polynomial.C c) := by
  simp [coefficientEquiv, optionEquivRight_C]

@[simp] theorem coefficientEquiv_parameter :
    coefficientEquiv (Z := Z) (X (Sum.inl ())) = C Polynomial.X := by
  simp [coefficientEquiv, coordinatesEquiv, optionEquivRight_X_none]

@[simp] theorem coefficientEquiv_spatial (i : SpatialVariables Z) :
    coefficientEquiv (X (Sum.inr i)) = X i := by
  simp [coefficientEquiv, coordinatesEquiv, optionEquivRight_X_some]

theorem coefficientEquiv_baseMap (p : Polynomial ℂ) :
    coefficientEquiv (Z := Z) (baseMap p) = C p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
    change coefficientEquiv ((Polynomial.monomial n c).eval₂ C (X (Sum.inl ()))) = _
    rw [Polynomial.eval₂_monomial, map_mul, map_pow,
      coefficientEquiv_C, coefficientEquiv_parameter]
    rw [← map_pow, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]

/-- The same equivalence is linear over the actual polynomial base. -/
def coefficientAlgEquiv :
    MvPolynomial (TotalCoordinates Unit Z) ℂ ≃ₐ[Polynomial ℂ]
      MvPolynomial (SpatialVariables Z) (Polynomial ℂ) :=
  { coefficientEquiv.toRingEquiv with
    commutes' := coefficientEquiv_baseMap }

def coefficientIdeal (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) :
    Ideal (MvPolynomial (SpatialVariables Z) (Polynomial ℂ)) :=
  (totalIdeal F U).map coefficientAlgEquiv.toRingHom

abbrev CoefficientRing (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) :=
  MvPolynomial (SpatialVariables Z) (Polynomial ℂ) ⧸ coefficientIdeal F U

/-- A base-algebra equivalence of the actual two coordinate presentations. -/
def quotientEquiv (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) :
    CoordinateRing F U ≃ₐ[Polynomial ℂ] CoefficientRing F U :=
  Ideal.quotientEquivAlg (totalIdeal F U) (coefficientIdeal F U) coefficientAlgEquiv rfl

/-- Base torsion-freeness transfers to the coefficient presentation. -/
theorem coefficientRing_torsionfree
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U) :
    NoZeroSMulDivisors (Polynomial ℂ) (CoefficientRing F U) := by
  letI := ActualGaussFlatScheme.coordinateRing_torsionfree F U hU
  exact (quotientEquiv F U).symm.injective.noZeroSMulDivisors _
    (map_zero _) (fun r x => (quotientEquiv F U).symm.toLinearEquiv.map_smul r x)

theorem coefficientRing_flat
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U) :
    Module.Flat (Polynomial ℂ) (CoefficientRing F U) := by
  letI := coefficientRing_torsionfree F U hU
  exact ConormalFlatness.flat_of_torsionfree_pid (Polynomial ℂ) (CoefficientRing F U)

end Sheshadri.ActualGaussCoefficientRing
