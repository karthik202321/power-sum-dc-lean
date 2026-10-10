/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Complex.Basic

/-!
# A precise, universal multiprojective Bezout input

This module does NOT prove Bezout. It states the standard simple-isolated-point
version as a proposition about actual complex polynomials, their multidegrees,
their derivatives, and projectively distinct zeros. Unlike the first version's
paper-specific count provider, this proposition mentions no determinants,
Fermat polynomials, conormals, or target count.

It is a hypothesis, not a declared axiom. The later incidence application must
prove homogeneity and exhibit its actual zero/simple/distinct-point data.
-/

noncomputable section
namespace Sheshadri.MultiProjective
open MvPolynomial

abbrev Variables (X U V : Type*) := X ⊕ (U ⊕ V)
abbrev Degree := ℕ × ℕ × ℕ

def weight (X U V : Type*) : Variables X U V → Degree
  | .inl _ => (1, 0, 0)
  | .inr (.inl _) => (0, 1, 0)
  | .inr (.inr _) => (0, 0, 1)

def HasNonzeroBlocks {X U V : Type*} (p : Variables X U V → ℂ) : Prop :=
  (∃ i, p (.inl i) ≠ 0) ∧
  (∃ i, p (.inr (.inl i)) ≠ 0) ∧
  (∃ i, p (.inr (.inr i)) ≠ 0)

def ProjectivelyEquivalent {X U V : Type*}
    (p q : Variables X U V → ℂ) : Prop :=
  ∃ a b c : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
    (∀ i, p (.inl i) = a * q (.inl i)) ∧
    (∀ i, p (.inr (.inl i)) = b * q (.inr (.inl i))) ∧
    (∀ i, p (.inr (.inr i)) = c * q (.inr (.inr i)))

def directional {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ ℂ) (p v : σ → ℂ) : ℂ :=
  ∑ i, eval p (pderiv i f) * v i

/-- The affine chart tangent kernel is trivial. This is an explicit simple
projective zero condition, not an abstract label for isolatedness. -/
def SimpleInCharts {X U V E : Type*} [Fintype X] [Fintype U] [Fintype V]
    (f : E → MvPolynomial (Variables X U V) ℂ)
    (p : Variables X U V → ℂ) : Prop :=
  ∃ ix : X, ∃ iu : U, ∃ iv : V,
    p (.inl ix) ≠ 0 ∧ p (.inr (.inl iu)) ≠ 0 ∧ p (.inr (.inr iv)) ≠ 0 ∧
    ∀ v : Variables X U V → ℂ,
      v (.inl ix) = 0 → v (.inr (.inl iu)) = 0 → v (.inr (.inr iv)) = 0 →
      (∀ e, directional (f e) p v = 0) → v = 0

def exponent (h u v : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 h + Finsupp.single 1 u + Finsupp.single 2 v

def classFactor (d : Degree) : MvPolynomial (Fin 3) ℕ :=
  C d.1 * X 0 + C d.2.1 * X 1 + C d.2.2 * X 2

def classPolynomial {E : Type*} [Fintype E] (degree : E → Degree) :
    MvPolynomial (Fin 3) ℕ := ∏ e, classFactor (degree e)

def coefficientBudget {E : Type*} [Fintype E]
    (degree : E → Degree) (a b c : ℕ) : ℕ :=
  coeff (exponent a b c) (classPolynomial degree)

/-- Standard multihomogeneous Bezout for a finite family of distinct simple
zeros; arbitrary additional components of the zero locus are permitted.

The complete universally quantified statement is deliberately exposed.
`BezoutWithExcess.universal_simple_bezout` proves it from actual polynomial
deformation, graded quotient modules, and a concrete split comparison system. -/
def UniversalSimpleBezout : Prop :=
  ∀ (X U V E P : Type) [Fintype X] [Fintype U] [Fintype V]
    [Fintype E] [Fintype P] [Nonempty X] [Nonempty U] [Nonempty V],
    ∀ (f : E → MvPolynomial (Variables X U V) ℂ) (degree : E → Degree)
      (points : P → Variables X U V → ℂ),
      Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
        (Fintype.card V - 1) →
      (∀ e, IsWeightedHomogeneous (weight X U V) (f e) (degree e)) →
      (∀ p e, eval (points p) (f e) = 0) →
      (∀ p, SimpleInCharts f (points p)) →
      (∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q) →
      Fintype.card P ≤ coefficientBudget degree
        (Fintype.card X - 1) (Fintype.card U - 1) (Fintype.card V - 1)

def biWeight (X U : Type*) : X ⊕ U → ℕ × ℕ
  | .inl _ => (1, 0)
  | .inr _ => (0, 1)

def BiProjectivelyEquivalent {X U : Type*} (p q : X ⊕ U → ℂ) : Prop :=
  ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧
    (∀ i, p (.inl i) = a * q (.inl i)) ∧
    (∀ i, p (.inr i) = b * q (.inr i))

def BiSimpleInCharts {X U E : Type*} [Fintype X] [Fintype U]
    (f : E → MvPolynomial (X ⊕ U) ℂ) (p : X ⊕ U → ℂ) : Prop :=
  ∃ ix : X, ∃ iu : U, p (.inl ix) ≠ 0 ∧ p (.inr iu) ≠ 0 ∧
    ∀ v : X ⊕ U → ℂ, v (.inl ix) = 0 → v (.inr iu) = 0 →
      (∀ e, directional (f e) p v = 0) → v = 0

/-- Two-factor version of exactly the same textbook principle. The unused
third formal class variable has target exponent zero. -/
def UniversalBiSimpleBezout : Prop :=
  ∀ (X U E P : Type) [Fintype X] [Fintype U] [Fintype E] [Fintype P]
    [Nonempty X] [Nonempty U],
    ∀ (f : E → MvPolynomial (X ⊕ U) ℂ) (degree : E → ℕ × ℕ)
      (points : P → X ⊕ U → ℂ),
      Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) →
      (∀ e, IsWeightedHomogeneous (biWeight X U) (f e) (degree e)) →
      (∀ p e, eval (points p) (f e) = 0) →
      (∀ p, BiSimpleInCharts f (points p)) →
      (∀ p q, BiProjectivelyEquivalent (points p) (points q) → p = q) →
      Fintype.card P ≤ coefficientBudget (fun e => ((degree e).1, (degree e).2, 0))
        (Fintype.card X - 1) (Fintype.card U - 1) 0

end Sheshadri.MultiProjective
