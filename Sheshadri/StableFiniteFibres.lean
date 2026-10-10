/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Order.Filter.Finite

/-!
# Persistence of finitely many simple roots

This file proves a genuine perturbation theorem from Mathlib's inverse function
theorem. For `H(p,z)=0`, invertibility of the strict derivative of
`(p,z) ↦ (p,H(p,z))` constructs a continuous local root branch. A finite family
of distinct simple roots gives equally many distinct nearby roots.

There are no custom axioms. Applying the theorem to coefficient perturbations
of the paper's polar equations still requires the derivative calculation and
the link to the determinantal incidence budget.
-/

noncomputable section

namespace Sheshadri.StableFiniteFibres

open Filter Function
open scoped Topology

section Distinctness
variable {I P E : Type*} [Finite I] [TopologicalSpace P]
    [TopologicalSpace E] [T2Space E]

/-- Distinct continuous branches stay distinct on one common neighborhood. -/
theorem eventually_injective_branches (b : I → P → E) (p₀ : P)
    (hb : ∀ i, ContinuousAt (b i) p₀)
    (hinj : Injective (fun i => b i p₀)) :
    ∀ᶠ p in 𝓝 p₀, Injective (fun i => b i p) := by
  have hpairs : ∀ i j, ∀ᶠ p in 𝓝 p₀, b i p = b j p → i = j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (fun _ _ => hij)
    · have hne : b i p₀ ≠ b j p₀ := fun he => hij (hinj he)
      filter_upwards [((hb i).ne_iff_eventually_ne (hb j)).mp hne] with p hp
      exact fun he => False.elim (hp he)
  exact Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hpairs i))

end Distinctness

section Roots
variable {𝕜 P E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

def totalMap (H : P → E → E) : P × E → P × E :=
  fun q => (q.1, H q.1 q.2)

/-- Actual IFT construction of a continuous local zero branch. The derivative
hypothesis concerns the displayed function `totalMap H`, not an abstract
predicate asserting root persistence. -/
theorem exists_local_root_branch (H : P → E → E) (p₀ : P) (z₀ : E)
    (e : (P × E) ≃L[𝕜] (P × E))
    (hroot : H p₀ z₀ = 0)
    (hD : HasStrictFDerivAt (totalMap H) (e : (P × E) →L[𝕜] (P × E)) (p₀, z₀)) :
    ∃ b : P → E, b p₀ = z₀ ∧ ContinuousAt b p₀ ∧
      ∀ᶠ p in 𝓝 p₀, H p (b p) = 0 := by
  let g := hD.localInverse (totalMap H) e (p₀, z₀)
  let b : P → E := fun p => (g (p, 0)).2
  have hin : Tendsto (fun p : P => (p, (0 : E))) (𝓝 p₀)
      (𝓝 (totalMap H (p₀, z₀))) := by
    simpa [totalMap, hroot] using
      (continuousAt_id.prodMk (continuousAt_const (y := (0 : E)))).tendsto
  have hg0 : g (p₀, 0) = (p₀, z₀) := by
    simpa [g, totalMap, hroot] using hD.localInverse_apply_image
  have hb0 : b p₀ = z₀ := congrArg Prod.snd hg0
  have hgt : Tendsto (fun p => g (p, 0)) (𝓝 p₀) (𝓝 (p₀, z₀)) :=
    hD.localInverse_tendsto.comp hin
  have hbt : ContinuousAt b p₀ := by
    change Tendsto b (𝓝 p₀) (𝓝 (b p₀))
    rw [hb0]
    exact (continuous_snd.tendsto (p₀, z₀)).comp hgt
  refine ⟨b, hb0, hbt, ?_⟩
  filter_upwards [hin.eventually hD.eventually_right_inverse] with p hp
  have hp1 : (g (p, 0)).1 = p := congrArg Prod.fst hp
  have hp2 : H (g (p, 0)).1 (g (p, 0)).2 = 0 := congrArg Prod.snd hp
  rw [hp1] at hp2
  exact hp2

/-- A finite collection of distinct simple zeros persists simultaneously.
Thus the nearby zero set admits an injection from the original root index set. -/
theorem finite_simple_roots_persist {I : Type*} [Finite I]
    (H : P → E → E) (p₀ : P) (z : I → E) (hz : Injective z)
    (e : I → (P × E) ≃L[𝕜] (P × E))
    (hroot : ∀ i, H p₀ (z i) = 0)
    (hD : ∀ i, HasStrictFDerivAt (totalMap H)
      (e i : (P × E) →L[𝕜] (P × E)) (p₀, z i)) :
    ∃ b : I → P → E,
      (∀ i, b i p₀ = z i) ∧ (∀ i, ContinuousAt (b i) p₀) ∧
      ∀ᶠ p in 𝓝 p₀, Injective (fun i => b i p) ∧ ∀ i, H p (b i p) = 0 := by
  choose b hb0 hbcont hbroot using
    (fun i => exists_local_root_branch H p₀ (z i) (e i) (hroot i) (hD i))
  refine ⟨b, hb0, hbcont, ?_⟩
  have hbase : Injective (fun i => b i p₀) := by
    intro i j hij
    apply hz
    simpa only [hb0] using hij
  exact (eventually_injective_branches b p₀ hbcont hbase).and
    (Filter.eventually_all.mpr hbroot)

/-- A continuous scalar nonvanishing condition (for example a Jacobian
determinant) persists simultaneously along all of the constructed branches. -/
theorem finite_regular_roots_persist {I : Type*} [Finite I]
    (H : P → E → E) (p₀ : P) (z : I → E) (hz : Injective z)
    (e : I → (P × E) ≃L[𝕜] (P × E))
    (hroot : ∀ i, H p₀ (z i) = 0)
    (hD : ∀ i, HasStrictFDerivAt (totalMap H)
      (e i : (P × E) →L[𝕜] (P × E)) (p₀, z i))
    (J : P × E → 𝕜) (hJ : ∀ i, ContinuousAt J (p₀, z i))
    (hJ0 : ∀ i, J (p₀, z i) ≠ 0) :
    ∃ b : I → P → E,
      (∀ i, b i p₀ = z i) ∧ (∀ i, ContinuousAt (b i) p₀) ∧
      ∀ᶠ p in 𝓝 p₀, Injective (fun i => b i p) ∧
        (∀ i, H p (b i p) = 0) ∧ ∀ i, J (p, b i p) ≠ 0 := by
  obtain ⟨b, hb0, hbcont, hb⟩ := finite_simple_roots_persist H p₀ z hz e hroot hD
  refine ⟨b, hb0, hbcont, ?_⟩
  have hreg : ∀ i, ∀ᶠ p in 𝓝 p₀, J (p, b i p) ≠ 0 := by
    intro i
    have hpair : ContinuousAt (fun p => (p, b i p)) p₀ :=
      continuousAt_id.prodMk (hbcont i)
    have hc : ContinuousAt (fun p => J (p, b i p)) p₀ := by
      apply ContinuousAt.comp _ hpair
      simpa only [hb0] using hJ i
    exact hc.eventually_ne (by simpa only [hb0] using hJ0 i)
  filter_upwards [hb, Filter.eventually_all.mpr hreg] with p hp hj
  exact ⟨hp.1, hp.2, hj⟩

end Roots
end Sheshadri.StableFiniteFibres
