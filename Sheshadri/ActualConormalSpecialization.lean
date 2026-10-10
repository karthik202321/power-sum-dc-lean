/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ActualGaussFamily
import Sheshadri.ConormalSpecialization

/-!
# Specialization for the constructed total Gauss family

The total set, graph inclusion, closedness and algebraicity are no longer
independent inputs. The remaining cycle, dimension and Hilbert premises below
are still geometric obligations, not asserted to follow merely from closure.
-/

noncomputable section
namespace Sheshadri.ActualConormalSpecialization

open MvPolynomial ConormalZariski ConormalCycles ConormalTopology ConormalSpecialization
open scoped Topology

variable {A Z C : Type} [Fintype A] [Fintype Z] [TopologicalSpace C]

theorem target_degree_le_generic
    (F : MvPolynomial (A ⊕ Z) ℂ) (a : C → A → ℂ) (c₀ : C)
    (ha : ContinuousAt a c₀) (U : Set C) (hU : c₀ ∈ closure U)
    {d : ℕ} (D : FamilyCycleData C Z d)
    (hsupport : supportSet D.componentSet (D.cycle c₀) =
      ActualGaussFamily.fibre F (a '' U) (a c₀))
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
    exact ActualGaussFamily.conormalClosure_subset_fibre_of_curve F a c₀ ha U hU
  have hspecial : D.degree k (conormalClosure F (a c₀)) ≤ D.totalDegree c₀ k := by
    letI : TopologicalSpace (Ambient Z) := algebraicTopology (Option Z ⊕ Option Z)
    exact target_le_multidegree_of_support_containment D.componentSet (D.cycle c₀)
      (D.degree k) D.dimension hirreducible hclosed hcontain hdimension hstrict
  rw [D.totalDegree_constant c₀ hχ c k]
  exact hspecial

end Sheshadri.ActualConormalSpecialization
