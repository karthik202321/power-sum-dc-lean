/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SingularBezoutWithExcess
import Sheshadri.CommonProjectiveChart

noncomputable section
open Sheshadri.MultiProjective
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

namespace Sheshadri.FieldMultiProjective
variable {k₀ : Type*} [Field k₀] [CharZero k₀]
open MvPolynomial

def HasNonzeroBlocks {X U V : Type*} (p : Variables X U V → k₀) : Prop :=
  (∃ i, p (.inl i) ≠ 0) ∧
  (∃ i, p (.inr (.inl i)) ≠ 0) ∧
  (∃ i, p (.inr (.inr i)) ≠ 0)

def ProjectivelyEquivalent {X U V : Type*}
    (p q : Variables X U V → k₀) : Prop :=
  ∃ a b c : k₀, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
    (∀ i, p (.inl i) = a * q (.inl i)) ∧
    (∀ i, p (.inr (.inl i)) = b * q (.inr (.inl i))) ∧
    (∀ i, p (.inr (.inr i)) = c * q (.inr (.inr i)))

def directional {σ : Type*} [Fintype σ]
    (f : MvPolynomial σ k₀) (p v : σ → k₀) : k₀ :=
  ∑ i, eval p (pderiv i f) * v i

/-- The affine chart tangent kernel is trivial. This is an explicit simple
projective zero condition, not an abstract label for isolatedness. -/
def SimpleInCharts {X U V E : Type*} [Fintype X] [Fintype U] [Fintype V]
    (f : E → MvPolynomial (Variables X U V) k₀)
    (p : Variables X U V → k₀) : Prop :=
  ∃ ix : X, ∃ iu : U, ∃ iv : V,
    p (.inl ix) ≠ 0 ∧ p (.inr (.inl iu)) ≠ 0 ∧ p (.inr (.inr iv)) ≠ 0 ∧
    ∀ v : Variables X U V → k₀,
      v (.inl ix) = 0 → v (.inr (.inl iu)) = 0 → v (.inr (.inr iv)) = 0 →
      (∀ e, directional (f e) p v = 0) → v = 0

/-- Standard multihomogeneous Bezout for a finite family of distinct simple
zeros; arbitrary additional components of the zero locus are permitted.

This auxiliary simple-zero proposition is retained for comparison. The
general-field proof below uses the stronger actual local-length formulation
proved by `FieldSingularBezoutWithExcess.universal_multiplicity_bezout`. -/
def UniversalSimpleBezout : Prop :=
  ∀ (X U V E P : Type) [Fintype X] [Fintype U] [Fintype V]
    [Fintype E] [Fintype P] [Nonempty X] [Nonempty U] [Nonempty V],
    ∀ (f : E → MvPolynomial (Variables X U V) k₀) (degree : E → Degree)
      (points : P → Variables X U V → k₀),
      Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
        (Fintype.card V - 1) →
      (∀ e, IsWeightedHomogeneous (weight X U V) (f e) (degree e)) →
      (∀ p e, eval (points p) (f e) = 0) →
      (∀ p, SimpleInCharts f (points p)) →
      (∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q) →
      Fintype.card P ≤ coefficientBudget degree
        (Fintype.card X - 1) (Fintype.card U - 1) (Fintype.card V - 1)

def BiProjectivelyEquivalent {X U : Type*} (p q : X ⊕ U → k₀) : Prop :=
  ∃ a b : k₀, a ≠ 0 ∧ b ≠ 0 ∧
    (∀ i, p (.inl i) = a * q (.inl i)) ∧
    (∀ i, p (.inr i) = b * q (.inr i))

def BiSimpleInCharts {X U E : Type*} [Fintype X] [Fintype U]
    (f : E → MvPolynomial (X ⊕ U) k₀) (p : X ⊕ U → k₀) : Prop :=
  ∃ ix : X, ∃ iu : U, p (.inl ix) ≠ 0 ∧ p (.inr iu) ≠ 0 ∧
    ∀ v : X ⊕ U → k₀, v (.inl ix) = 0 → v (.inr iu) = 0 →
      (∀ e, directional (f e) p v = 0) → v = 0

/-- Two-factor version of exactly the same textbook principle. The unused
third formal class variable has target exponent zero. -/
def UniversalBiSimpleBezout : Prop :=
  ∀ (X U E P : Type) [Fintype X] [Fintype U] [Fintype E] [Fintype P]
    [Nonempty X] [Nonempty U],
    ∀ (f : E → MvPolynomial (X ⊕ U) k₀) (degree : E → ℕ × ℕ)
      (points : P → X ⊕ U → k₀),
      Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) →
      (∀ e, IsWeightedHomogeneous (biWeight X U) (f e) (degree e)) →
      (∀ p e, eval (points p) (f e) = 0) →
      (∀ p, BiSimpleInCharts f (points p)) →
      (∀ p q, BiProjectivelyEquivalent (points p) (points q) → p = q) →
      Fintype.card P ≤ coefficientBudget (fun e => ((degree e).1, (degree e).2, 0))
        (Fintype.card X - 1) (Fintype.card U - 1) 0

end Sheshadri.FieldMultiProjective
