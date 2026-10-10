/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalPersistence
import Sheshadri.ZariskiBridge

/-!
# Actual Gauss representatives and containment in an algebraic special fibre

This is the set-theoretic containment step in Section 8. Both projective
coordinates are represented by nonzero vectors and arbitrary nonzero scalings.
Taking their affine Zariski closure records the cone over the projective
conormal closure. It also includes zero representatives on its boundary;
projectivization discards those, as usual.

The theorem proves containment for any closed total family which contains the
smooth Gauss graphs at the good parameters and whose special fibre is algebraic.
It does not assume the conormal containment it concludes. Construction,
flatness, purity and the cycle of that family are separate obligations.
-/

noncomputable section
namespace Sheshadri.ConormalZariski

open MvPolynomial Filter ConormalPersistence ZariskiBridge
open scoped Topology

variable {A Z : Type*} [Fintype A] [Fintype Z]

abbrev Ambient (Z : Type*) := Option Z ⊕ Option Z → ℂ

/-- A pair of homogeneous representatives, allowing independent nonzero
scalings of the primal point and its homogeneous tangent covector. -/
def gaussPoint (F : MvPolynomial (A ⊕ Z) ℂ) (a : A → ℂ) (z : Z → ℂ)
    (mu nu : ℂ) : Ambient Z :=
  Sum.elim (fun i => mu * Option.elim i 1 z)
    (fun i => nu * gaussCovector F a z i)

theorem continuous_gaussPoint (F : MvPolynomial (A ⊕ Z) ℂ) (mu nu : ℂ) :
    Continuous (fun q : (A → ℂ) × (Z → ℂ) => gaussPoint F q.1 q.2 mu nu) := by
  apply continuous_pi
  intro i
  cases i with
  | inl i =>
    cases i with
    | none =>
      change Continuous (fun _ : (A → ℂ) × (Z → ℂ) => mu * 1)
      exact continuous_const
    | some j => exact continuous_const.mul ((continuous_apply j).comp continuous_snd)
  | inr i =>
    exact continuous_const.mul ((continuous_apply i).comp (continuous_gaussCovector F))

def smoothGaussRepresentatives (F : MvPolynomial (A ⊕ Z) ℂ)
    (a : A → ℂ) : Set (Ambient Z) :=
  {p | ∃ z mu nu, value F a z = 0 ∧ (∃ j, gradient F a z j ≠ 0) ∧
    mu ≠ 0 ∧ nu ≠ 0 ∧ p = gaussPoint F a z mu nu}

/-- Concrete affine closure of the rescaled smooth affine Gauss graph.
Identification of its nonzero-block projectivization with the target's
projective conormal is a separate geometric bridge, not proved here. -/
def conormalClosure (F : MvPolynomial (A ⊕ Z) ℂ)
    (a : A → ℂ) : Set (Ambient Z) :=
  zariskiClosure (smoothGaussRepresentatives F a)

theorem zariskiClosure_mono {Y : Type*} {s t : Set (Y → ℂ)} (h : s ⊆ t) :
    zariskiClosure s ⊆ zariskiClosure t := by
  intro y hy q hq
  exact hy q (fun x hx => hq x (h hx))

theorem subset_zariskiClosure {Y : Type*} (s : Set (Y → ℂ)) :
    s ⊆ zariskiClosure s := by
  intro x hx q hq
  exact hq x hx

theorem zariskiClosure_idempotent {Y : Type*} (s : Set (Y → ℂ)) :
    zariskiClosure (zariskiClosure s) = zariskiClosure s := by
  apply Set.Subset.antisymm
  · intro x hx q hq
    exact hx q (fun y hy => hy q hq)
  · exact subset_zariskiClosure _

/-- Common zero loci are Euclidean closed. Only polynomial continuity is
used, not the stronger polynomial-image closure theorem. -/
theorem isClosed_zariskiClosure {Y : Type*} [Fintype Y] (s : Set (Y → ℂ)) :
    IsClosed (zariskiClosure s) := by
  have heq : zariskiClosure s =
      ⋂ q : {q : MvPolynomial Y ℂ // ∀ x ∈ s, eval x q = 0},
        {x | eval x q.val = 0} := by
    ext x
    simp only [zariskiClosure, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h q
      exact h q.val q.property
    · intro h q hq
      exact h ⟨q, hq⟩
  rw [heq]
  apply isClosed_iInter
  intro q
  apply isClosed_eq
  · apply continuous_iff_continuousAt.mpr
    intro x
    exact (PolynomialAnalytic.hasStrictFDerivAt_eval q.val x).continuousAt
  · exact continuous_const

section Family
variable {C : Type*} [TopologicalSpace C]

/-- The limiting point belongs to the special fibre, because actual nearby
smooth roots and their entire homogeneous covectors have been constructed. -/
theorem smooth_gauss_point_mem_special_fibre
    (F : MvPolynomial (A ⊕ Z) ℂ) (a : C → A → ℂ) (c₀ : C)
    (ha : ContinuousAt a c₀) (U : Set C) (hU : c₀ ∈ closure U)
    (W : Set (C × Ambient Z)) (hW : IsClosed W)
    (hgraph : ∀ c ∈ U, ∀ p ∈ smoothGaussRepresentatives F (a c), (c, p) ∈ W)
    (z : Z → ℂ) (j : Z) (hroot : value F (a c₀) z = 0)
    (hj : gradient F (a c₀) z j ≠ 0)
    (mu nu : ℂ) (hmu : mu ≠ 0) (hnu : nu ≠ 0) :
    (c₀, gaussPoint F (a c₀) z mu nu) ∈ W := by
  obtain ⟨b, hb0, hbc, hg, hG, hbranch⟩ :=
    smooth_zero_gauss_persistence F (a c₀) z j hroot hj
  have hp : ContinuousAt (fun c => (a c, b (a c))) c₀ :=
    ha.prodMk (hbc.comp ha)
  have hc : ContinuousAt (fun c => (c, gaussPoint F (a c) (b (a c)) mu nu)) c₀ :=
    continuousAt_id.prodMk ((continuous_gaussPoint F mu nu).continuousAt.comp hp)
  have ht : Tendsto (fun c => (c, gaussPoint F (a c) (b (a c)) mu nu))
      (𝓝[U] c₀) (𝓝 (c₀, gaussPoint F (a c₀) z mu nu)) := by
    simpa only [hb0] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ c in 𝓝[U] c₀,
      (c, gaussPoint F (a c) (b (a c)) mu nu) ∈ W := by
    filter_upwards [self_mem_nhdsWithin,
      (ha.tendsto.eventually hbranch).filter_mono nhdsWithin_le_nhds] with c hcU hcb
    apply hgraph c hcU
    exact ⟨b (a c), mu, nu, hcb.1, ⟨j, hcb.2.1⟩, hmu, hnu, rfl⟩
  letI : NeBot (𝓝[U] c₀) := mem_closure_iff_nhdsWithin_neBot.mp hU
  exact hW.mem_of_tendsto ht he

/-- The Zariski closure of the target's smooth Gauss graph lies in the
special fibre. This proves the containment part of Proposition 8.1 from
the construction properties of W, without an explicit polar slice. -/
theorem conormalClosure_subset_special_fibre
    (F : MvPolynomial (A ⊕ Z) ℂ) (a : C → A → ℂ) (c₀ : C)
    (ha : ContinuousAt a c₀) (U : Set C) (hU : c₀ ∈ closure U)
    (W : Set (C × Ambient Z)) (hW : IsClosed W)
    (hgraph : ∀ c ∈ U, ∀ p ∈ smoothGaussRepresentatives F (a c), (c, p) ∈ W)
    (halgebraic : zariskiClosure {p | (c₀, p) ∈ W} ⊆ {p | (c₀, p) ∈ W}) :
    conormalClosure F (a c₀) ⊆ {p | (c₀, p) ∈ W} := by
  apply Set.Subset.trans (zariskiClosure_mono ?_) halgebraic
  intro p hp
  obtain ⟨z, mu, nu, hz, ⟨j, hj⟩, hmu, hnu, rfl⟩ := hp
  exact smooth_gauss_point_mem_special_fibre F a c₀ ha U hU W hW hgraph
    z j hz hj mu nu hmu hnu

end Family
end Sheshadri.ConormalZariski
