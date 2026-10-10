/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.Data.Finsupp.Order
import Mathlib.Topology.Irreducible
import Sheshadri.ConormalHilbert

/-!
# Effective fibre cycles and the conormal-component comparison

This is the cycle-bookkeeping part of the original conormal specialization
argument (Sections 7--8), not a replacement by a finite transverse slice.
An effective cycle is a finitely supported collection of natural multiplicities.
Its multidegree is the corresponding weighted sum of nonnegative component
multidegrees. Both additivity and the target-component inequality are proved.

The topological lemmas additionally prove that an irreducible subset of a finite
closed union lies in one member. A strict dimension-drop hypothesis then turns
containment of a target of the fibre dimension into equality with a component.
That dimension hypothesis is visible; this file does not construct scheme
fibres, their generic-length multiplicities, or their dimension theory. Nor does
it assert that an arbitrary labelled family is the Gauss-graph family.
-/

noncomputable section

namespace Sheshadri.ConormalCycles

open scoped BigOperators

/-- Effective cycles have finite support and nonnegative integral weights. -/
abbrev EffectiveCycle (Component : Type*) := Component →₀ ℕ

/-- One chosen multidegree of an effective cycle. The component degrees are
natural numbers, so nonnegativity is part of the data rather than an axiom. -/
def multidegree {Component : Type*} (degree : Component → ℕ)
    (cycle : EffectiveCycle Component) : ℕ :=
  cycle.sum fun component multiplicity => multiplicity * degree component

@[simp] theorem multidegree_zero {Component : Type*} (degree : Component → ℕ) :
    multidegree degree 0 = 0 := by
  simp [multidegree]

@[simp] theorem multidegree_single {Component : Type*} (degree : Component → ℕ)
    (component : Component) (multiplicity : ℕ) :
    multidegree degree (Finsupp.single component multiplicity) =
      multiplicity * degree component := by
  simp [multidegree]

theorem multidegree_add {Component : Type*} (degree : Component → ℕ)
    (first second : EffectiveCycle Component) :
    multidegree degree (first + second) =
      multidegree degree first + multidegree degree second := by
  classical
  exact Finsupp.sum_add_index' (by simp) (by intros; exact Nat.add_mul _ _ _)

theorem multidegree_mono {Component : Type*} (degree : Component → ℕ)
    {first second : EffectiveCycle Component} (h : first ≤ second) :
    multidegree degree first ≤ multidegree degree second := by
  classical
  apply Finsupp.sum_le_sum_index h
  · intro component _ a b hab
    exact Nat.mul_le_mul_right (degree component) hab
  · simp

/-- A component's full contribution is bounded by the effective total. -/
theorem contribution_le_multidegree {Component : Type*} (degree : Component → ℕ)
    (cycle : EffectiveCycle Component) (component : Component) :
    cycle component * degree component ≤ multidegree degree cycle := by
  classical
  have h : Finsupp.single component (cycle component) ≤ cycle :=
    Finsupp.single_le_iff.mpr le_rfl
  simpa using multidegree_mono degree h

/-- The coefficient-at-least-one step used when the target conormal appears
as an irreducible component of the scheme-theoretic special-fibre cycle. -/
theorem component_le_multidegree {Component : Type*} (degree : Component → ℕ)
    (cycle : EffectiveCycle Component) (component : Component)
    (hcoefficient : 1 ≤ cycle component) :
    degree component ≤ multidegree degree cycle := by
  calc
    degree component = 1 * degree component := (one_mul _).symm
    _ ≤ cycle component * degree component :=
      Nat.mul_le_mul_right _ hcoefficient
    _ ≤ multidegree degree cycle := contribution_le_multidegree degree cycle component

theorem component_le_multidegree_of_mem_support {Component : Type*}
    (degree : Component → ℕ) (cycle : EffectiveCycle Component) (component : Component)
    (hcomponent : component ∈ cycle.support) :
    degree component ≤ multidegree degree cycle := by
  apply component_le_multidegree degree cycle component
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hcomponent)

/-- The underlying finite union of an effective cycle's labelled components. -/
def supportSet {Component X : Type*} (componentSet : Component → Set X)
    (cycle : EffectiveCycle Component) : Set X :=
  ⋃ component ∈ cycle.support, componentSet component

/-- The irreducibility argument required before effectivity can be used:
containment in the support implies containment in one closed component. -/
theorem exists_component_containing_of_irreducible
    {Component X : Type*} [TopologicalSpace X]
    (componentSet : Component → Set X) (cycle : EffectiveCycle Component)
    {target : Set X} (htarget : IsIrreducible target)
    (hclosed : ∀ component ∈ cycle.support, IsClosed (componentSet component))
    (hcontain : target ⊆ supportSet componentSet cycle) :
    ∃ component ∈ cycle.support, target ⊆ componentSet component := by
  classical
  have hcover : target ⊆ ⋃₀ (↑(cycle.support.image componentSet) : Set (Set X)) := by
    intro x hx
    obtain ⟨component, hcomponent, hxcomponent⟩ :=
      Set.mem_iUnion₂.mp (hcontain hx)
    exact Set.mem_sUnion.mpr ⟨componentSet component,
      Finset.mem_image.mpr ⟨component, hcomponent, rfl⟩, hxcomponent⟩
  obtain ⟨z, hz, htz⟩ := isIrreducible_iff_sUnion_isClosed.mp htarget
    (cycle.support.image componentSet) (by
      intro z hz
      obtain ⟨component, hcomponent, rfl⟩ := Finset.mem_image.mp hz
      exact hclosed component hcomponent) hcover
  obtain ⟨component, hcomponent, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨component, hcomponent, htz⟩

/-- Equal dimension rules out a proper containment in a fibre component.
The visible strict-dimension-drop hypothesis is the standard geometric input
for irreducible closed algebraic sets; it is not asserted for arbitrary spaces. -/
theorem exists_component_eq_of_dimension
    {Component X : Type*} [TopologicalSpace X]
    (componentSet : Component → Set X) (cycle : EffectiveCycle Component)
    (dimension : Set X → ℕ) {target : Set X}
    (htarget : IsIrreducible target)
    (hclosed : ∀ component ∈ cycle.support, IsClosed (componentSet component))
    (hcontain : target ⊆ supportSet componentSet cycle)
    (hdimension : ∀ component ∈ cycle.support,
      dimension target = dimension (componentSet component))
    (hstrict : ∀ component ∈ cycle.support,
      target ⊂ componentSet component → dimension target < dimension (componentSet component)) :
    ∃ component ∈ cycle.support, target = componentSet component := by
  obtain ⟨component, hcomponent, hsub⟩ :=
    exists_component_containing_of_irreducible componentSet cycle htarget hclosed hcontain
  refine ⟨component, hcomponent, ?_⟩
  by_contra hne
  have hproper : target ⊂ componentSet component :=
    lt_of_le_of_ne hsub hne
  have hlt := hstrict component hcomponent hproper
  rw [hdimension component hcomponent] at hlt
  exact (lt_irrefl _) hlt

/-- Section 8's geometric containment and equal dimension imply the actual
positive coefficient needed for comparing the target multidegree. -/
theorem target_le_multidegree_of_support_containment
    {Component X : Type*} [TopologicalSpace X]
    (componentSet : Component → Set X) (cycle : EffectiveCycle Component)
    (degree dimension : Set X → ℕ) {target : Set X}
    (htarget : IsIrreducible target)
    (hclosed : ∀ component ∈ cycle.support, IsClosed (componentSet component))
    (hcontain : target ⊆ supportSet componentSet cycle)
    (hdimension : ∀ component ∈ cycle.support,
      dimension target = dimension (componentSet component))
    (hstrict : ∀ component ∈ cycle.support,
      target ⊂ componentSet component → dimension target < dimension (componentSet component)) :
    degree target ≤ multidegree (fun component => degree (componentSet component)) cycle := by
  obtain ⟨component, hcomponent, heq⟩ :=
    exists_component_eq_of_dimension componentSet cycle dimension htarget hclosed hcontain
      hdimension hstrict
  rw [heq]
  exact component_le_multidegree_of_mem_support
    (fun component => degree (componentSet component)) cycle component hcomponent

/-- Conservation transports the effective special-fibre comparison to the
generic cycle. The conservation equality must be proved separately, e.g. by
the Hilbert-coefficient argument in `ConormalHilbert`. -/
theorem component_le_generic_multidegree {Component : Type*}
    (degree : Component → ℕ) (special generic : EffectiveCycle Component)
    (target : Component) (hcoefficient : 1 ≤ special target)
    (hconservation : multidegree degree special = multidegree degree generic) :
    degree target ≤ multidegree degree generic := by
  rw [← hconservation]
  exact component_le_multidegree degree special target hcoefficient

/-- The factorial-normalized Hilbert profile of all multidegrees of a cycle.
Its geometric identification with the top part of a fibre Hilbert polynomial
is deliberately not built into the definition of an effective cycle. -/
def cycleHilbertPolynomial {Component : Type*} (d : ℕ)
    (degree : Fin (d + 1) → Component → ℕ) (cycle : EffectiveCycle Component) :
    Polynomial ℚ :=
  ConormalHilbert.topHilbertPolynomial d
    (fun k => (multidegree (degree k) cycle : ℚ))

/-- Equality of Hilbert profiles proves conservation, including when special
and generic fibres have different sets of component labels. -/
theorem multidegrees_eq_of_cycleHilbertPolynomial_eq
    {SpecialComponent GenericComponent : Type*} (d : ℕ)
    (specialDegree : Fin (d + 1) → SpecialComponent → ℕ)
    (genericDegree : Fin (d + 1) → GenericComponent → ℕ)
    (special : EffectiveCycle SpecialComponent) (generic : EffectiveCycle GenericComponent)
    (hHilbert : cycleHilbertPolynomial d specialDegree special =
      cycleHilbertPolynomial d genericDegree generic) :
    ∀ k, multidegree (specialDegree k) special = multidegree (genericDegree k) generic := by
  have hprofile := ConormalHilbert.multidegrees_eq_of_topHilbertPolynomial_eq d hHilbert
  intro k
  exact Nat.cast_injective (congrFun hprofile k)

/-- The original cycle-specialization inequality, proved from coefficient
positivity and Hilbert-polynomial equality rather than assumed as a bound. -/
theorem component_le_generic_of_cycleHilbertPolynomial_eq
    {SpecialComponent GenericComponent : Type*} (d : ℕ)
    (specialDegree : Fin (d + 1) → SpecialComponent → ℕ)
    (genericDegree : Fin (d + 1) → GenericComponent → ℕ)
    (special : EffectiveCycle SpecialComponent) (generic : EffectiveCycle GenericComponent)
    (target : SpecialComponent) (hcoefficient : 1 ≤ special target)
    (hHilbert : cycleHilbertPolynomial d specialDegree special =
      cycleHilbertPolynomial d genericDegree generic) (k : Fin (d + 1)) :
    specialDegree k target ≤ multidegree (genericDegree k) generic := by
  rw [← multidegrees_eq_of_cycleHilbertPolynomial_eq d specialDegree genericDegree
    special generic hHilbert k]
  exact component_le_multidegree (specialDegree k) special target hcoefficient

end Sheshadri.ConormalCycles
