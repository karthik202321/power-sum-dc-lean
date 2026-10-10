/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.IncidenceClass
import Sheshadri.BezoutCoefficient
import Sheshadri.Numerical
import Lean.Elab.Tactic.Omega

/-!
# Applying the textbook Bezout principle to actual incidence polynomials

All multidegrees and equation counts are proved by `IncidenceSystem`, and the
class product by `IncidenceClass`. Remaining input here is the UNIVERSAL
Bezout principle and concrete selected zeros with trivial chart tangent kernel.
No paper-specific count-budget axiom is used or introduced.
-/

noncomputable section
namespace Sheshadri.Incidence
open Matrix MvPolynomial MultiProjective

theorem ordinary_incidence_coefficient_bound
    (bezout : UniversalSimpleBezout) {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m)
    {P : Type} [Fintype P]
    (A : PencilCoefficients n m ℂ) (Λ : Matrix (Fin (m - 1)) (Fin m) ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (points : P → OrdinaryVar n m → ℂ)
    (hzero : ∀ p e, eval (points p) (ordinarySystem A Λ flags M e) = 0)
    (hsimple : ∀ p, SimpleInCharts (ordinarySystem A Λ flags M) (points p))
    (hdistinct : ∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q) :
    Fintype.card P ≤ coefficientBudget (ordinaryDegree (n := n) (m := m))
      n (m - 1) (m - 1) := by
  letI : NeZero m := ⟨by omega⟩
  have hc : Fintype.card (OrdinaryEquationIndex n m) =
      (Fintype.card (Fin (n + 1)) - 1) + (Fintype.card (Fin m) - 1) +
        (Fintype.card (Fin m) - 1) := by
    rw [ordinarySystem_equation_count hn hm]
    simp only [Fintype.card_fin]
    omega
  have hd : ∀ e, IsWeightedHomogeneous (weight (Fin (n + 1)) (Fin m) (Fin m))
      (ordinarySystem A Λ flags M e) (ordinaryDegree e) := by
    have hw : weight (Fin (n + 1)) (Fin m) (Fin m) =
        ordinaryWeight (n := n) (m := m) := by
      funext i
      rcases i with i | (i | i) <;> rfl
    rw [hw]
    exact ordinarySystem_multidegree A Λ flags M
  simpa only [Fintype.card_fin, Nat.add_sub_cancel] using
    bezout (Fin (n + 1)) (Fin m) (Fin m) (OrdinaryEquationIndex n m) P
      (ordinarySystem A Λ flags M) ordinaryDegree points hc hd hzero hsimple hdistinct

theorem symmetric_incidence_coefficient_bound
    (bezout : UniversalBiSimpleBezout) {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m)
    {P : Type} [Fintype P]
    (A : PencilCoefficients n m ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (points : P → SymmetricVar n m → ℂ)
    (hzero : ∀ p e, eval (points p) (symmetricSystem A flags M e) = 0)
    (hsimple : ∀ p, BiSimpleInCharts (symmetricSystem A flags M) (points p))
    (hdistinct : ∀ p q, BiProjectivelyEquivalent (points p) (points q) → p = q) :
    Fintype.card P ≤ coefficientBudget (symmetricDegreeThree (n := n) (m := m))
      n (m - 1) 0 := by
  letI : NeZero m := ⟨by omega⟩
  have hc : Fintype.card (SymmetricEquationIndex n m) =
      (Fintype.card (Fin (n + 1)) - 1) + (Fintype.card (Fin m) - 1) := by
    rw [symmetricSystem_equation_count hn]
    simp only [Fintype.card_fin]
    omega
  have hd : ∀ e, IsWeightedHomogeneous (biWeight (Fin (n + 1)) (Fin m))
      (symmetricSystem A flags M e) (symmetricDegree e) := by
    have hw : biWeight (Fin (n + 1)) (Fin m) =
        symmetricWeight (n := n) (m := m) := by
      funext i
      cases i <;> rfl
    rw [hw]
    exact symmetricSystem_multidegree A flags M
  simpa only [Fintype.card_fin, Nat.add_sub_cancel, symmetricDegreeThree] using
    bezout (Fin (n + 1)) (Fin m) (SymmetricEquationIndex n m) P
      (symmetricSystem A flags M) symmetricDegree points hc hd hzero hsimple hdistinct

/-- Normalizing one primal coordinate to 1 makes distinct primal points
projectively distinct, regardless of the chosen kernel-vector representatives. -/
theorem ordinary_projective_distinct_of_primal
    {n m : ℕ} {P : Type} (x : P → Fin (n + 1) → ℂ)
    (u v : P → Fin m → ℂ) (hx : Function.Injective x)
    (hnorm : ∀ p, x p 0 = 1) :
    ∀ p q, ProjectivelyEquivalent (ordinaryAssignment (x p) (u p) (v p))
      (ordinaryAssignment (x q) (u q) (v q)) → p = q := by
  intro p q h
  obtain ⟨a, b, c, _, _, _, heq, _, _⟩ := h
  have ha : a = 1 := by
    have hz := heq 0
    simpa [ordinaryAssignment, hnorm] using hz.symm
  apply hx
  funext i
  simpa [ordinaryAssignment, ha] using heq i

theorem symmetric_projective_distinct_of_primal
    {n m : ℕ} {P : Type} (x : P → Fin (n + 1) → ℂ)
    (u : P → Fin m → ℂ) (hx : Function.Injective x)
    (hnorm : ∀ p, x p 0 = 1) :
    ∀ p q, BiProjectivelyEquivalent (symmetricAssignment (x p) (u p))
      (symmetricAssignment (x q) (u q)) → p = q := by
  intro p q h
  obtain ⟨a, b, _, _, heq, _⟩ := h
  have ha : a = 1 := by
    have hz := heq 0
    simpa [symmetricAssignment, hnorm] using hz.symm
  apply hx
  funext i
  simpa [symmetricAssignment, ha] using heq i

theorem ordinary_budget_eq (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) :
    coefficientBudget (ordinaryDegree (n := n) (m := m)) n (m - 1) (m - 1) =
      ordinaryBezout m n := by
  unfold coefficientBudget
  rw [ordinary_class_product]
  exact BezoutCoefficient.ordinary_coefficient m n hm hn

theorem symmetric_budget_eq (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) :
    coefficientBudget (symmetricDegreeThree (n := n) (m := m)) n (m - 1) 0 =
      symmetricBezout m n := by
  unfold coefficientBudget
  rw [symmetric_class_product]
  exact BezoutCoefficient.symmetric_coefficient m n hm hn

/-- Concrete incidence theorem: the only counting assumption is the universal
textbook principle; all degrees and coefficient formulas have been checked. -/
theorem ordinary_incidence_count_bound
    (bezout : UniversalSimpleBezout) {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m)
    {P : Type} [Fintype P]
    (A : PencilCoefficients n m ℂ) (Λ : Matrix (Fin (m - 1)) (Fin m) ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (points : P → OrdinaryVar n m → ℂ)
    (hzero : ∀ p e, eval (points p) (ordinarySystem A Λ flags M e) = 0)
    (hsimple : ∀ p, SimpleInCharts (ordinarySystem A Λ flags M) (points p))
    (hdistinct : ∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q) :
    Fintype.card P ≤ ordinaryBezout m n := by
  rw [← ordinary_budget_eq m n hm hn]
  exact ordinary_incidence_coefficient_bound bezout hn hm A Λ flags M points
    hzero hsimple hdistinct

theorem symmetric_incidence_count_bound
    (bezout : UniversalBiSimpleBezout) {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m)
    {P : Type} [Fintype P]
    (A : PencilCoefficients n m ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (points : P → SymmetricVar n m → ℂ)
    (hzero : ∀ p e, eval (points p) (symmetricSystem A flags M e) = 0)
    (hsimple : ∀ p, BiSimpleInCharts (symmetricSystem A flags M) (points p))
    (hdistinct : ∀ p q, BiProjectivelyEquivalent (points p) (points q) → p = q) :
    Fintype.card P ≤ symmetricBezout m n := by
  rw [← symmetric_budget_eq m n hm hn]
  exact symmetric_incidence_coefficient_bound bezout hn hm A flags M points
    hzero hsimple hdistinct

end Sheshadri.Incidence
