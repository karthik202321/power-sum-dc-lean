/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalZariski
import Sheshadri.ConormalTopology
import Sheshadri.ConormalCycles
import Sheshadri.ConormalEulerHilbert

/-!
# Assembly of the original conormal-specialization inequality

The smooth Gauss containment is derived by the proved analytic argument.
Zariski irreducibility, equal dimensions, and effective finite support then
give an actual positive component coefficient. Independently supplied Euler
characteristics give conservation through polynomial identity and coefficient
extraction. This is the original route, without any chosen Fermat polar slice.

`FamilyCycleData` and the geometric premises are NOT constructed for schemes
here. In particular, existence of the reduced horizontal closure, its fibre
cycles, the intersection/Hilbert identification, and constancy of actual Euler
characteristics remain visible obligations. These are not hidden by declaring
the specialization inequality as an axiom.
-/

noncomputable section
namespace Sheshadri.ConormalSpecialization

open MvPolynomial ConormalZariski ConormalCycles ConormalTopology ConormalEulerHilbert
open scoped Topology

/-- A numerical model of an effective projective fibre cycle, with its
component supports represented as affine bi-cones. This record does not assert
that it comes from a scheme. `degree` refers to projective multidegrees;
`dimension` refers to the affine support, so the two dimensions must not be
silently identified (they differ by two for a nonempty bi-cone). -/
structure FamilyCycleData (Parameter Z : Type) (d : ℕ) where
  Component : Type
  componentSet : Component → Set (Ambient Z)
  cycle : Parameter → EffectiveCycle Component
  degree : Fin (d + 1) → Set (Ambient Z) → ℕ
  dimension : Set (Ambient Z) → ℕ
  hilbert : EulerHilbertData Parameter d
    (fun c k => (multidegree (fun i => degree k (componentSet i)) (cycle c) : ℚ))

namespace FamilyCycleData

def totalDegree {C Z : Type} {d : ℕ} (D : FamilyCycleData C Z d)
    (c : C) (k : Fin (d + 1)) : ℕ :=
  multidegree (fun i => D.degree k (D.componentSet i)) (D.cycle c)

/-- Euler-characteristic constancy is the input of the proper-flat theorem;
its numerical consequences, including multiplicity weights, are proved. -/
theorem totalDegree_constant {C Z : Type} {d : ℕ} (D : FamilyCycleData C Z d)
    (base : C)
    (hχ : ∀ c q t, D.hilbert.eulerCharacteristic c q t =
      D.hilbert.eulerCharacteristic base q t) :
    ∀ c k, D.totalDegree c k = D.totalDegree base k := by
  intro c k
  have h := multidegrees_constant_of_euler_characteristics_constant D.hilbert base hχ c k
  exact Nat.cast_injective h

end FamilyCycleData

variable {A Z C : Type} [Fintype A] [Fintype Z] [TopologicalSpace C]

/-- All the topology is explicit: Euclidean closure supplies limits;
algebraicTopology supplies irreducibility and the finite-component argument.
The containment of the target is a conclusion, not a hypothesis. -/
theorem target_degree_le_generic
    (F : MvPolynomial (A ⊕ Z) ℂ) (a : C → A → ℂ) (c₀ : C)
    (ha : ContinuousAt a c₀) (U : Set C) (hU : c₀ ∈ closure U)
    (W : Set (C × Ambient Z)) (hW : IsClosed W)
    (hgraph : ∀ c ∈ U, ∀ p ∈ smoothGaussRepresentatives F (a c), (c, p) ∈ W)
    (halgebraic : ZariskiBridge.zariskiClosure {p | (c₀, p) ∈ W} ⊆
      {p | (c₀, p) ∈ W})
    {d : ℕ} (D : FamilyCycleData C Z d)
    (hsupport : supportSet D.componentSet (D.cycle c₀) = {p | (c₀, p) ∈ W})
    (hirreducible : @IsIrreducible (Ambient Z)
      (algebraicTopology (Option Z ⊕ Option Z)) (conormalClosure F (a c₀)))
    (hclosed : ∀ i ∈ (D.cycle c₀).support,
      @IsClosed (Ambient Z) (algebraicTopology (Option Z ⊕ Option Z)) (D.componentSet i))
    (hdimension : ∀ i ∈ (D.cycle c₀).support,
      D.dimension (conormalClosure F (a c₀)) = D.dimension (D.componentSet i))
    (hstrict : ∀ i ∈ (D.cycle c₀).support,
      conormalClosure F (a c₀) ⊂ D.componentSet i →
      D.dimension (conormalClosure F (a c₀)) < D.dimension (D.componentSet i))
    (hχ : ∀ c q t, D.hilbert.eulerCharacteristic c q t =
      D.hilbert.eulerCharacteristic c₀ q t)
    (c : C) (k : Fin (d + 1)) :
    D.degree k (conormalClosure F (a c₀)) ≤ D.totalDegree c k := by
  have hcontain : conormalClosure F (a c₀) ⊆ supportSet D.componentSet (D.cycle c₀) := by
    rw [hsupport]
    exact conormalClosure_subset_special_fibre F a c₀ ha U hU W hW hgraph halgebraic
  have hspecial : D.degree k (conormalClosure F (a c₀)) ≤ D.totalDegree c₀ k := by
    letI : TopologicalSpace (Ambient Z) := algebraicTopology (Option Z ⊕ Option Z)
    exact target_le_multidegree_of_support_containment D.componentSet (D.cycle c₀)
      (D.degree k) D.dimension hirreducible hclosed hcontain hdimension hstrict
  rw [D.totalDegree_constant c₀ hχ c k]
  exact hspecial

end Sheshadri.ConormalSpecialization
