/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ZariskiBridge
import Mathlib.Topology.Irreducible

/-!
# An explicit algebraic topology for the conormal argument

The ordinary topology on `Y → ℂ` remains the Euclidean product topology.
`algebraicTopology Y` is a separate, explicitly named topology, whose closed
sets are precisely the sets fixed by the polynomial-zero-locus operation
`ZariskiBridge.zariskiClosure`. It is deliberately NOT registered as a global
instance. Thus a limit argument can keep the ordinary topology, while an
irreducible-component argument uses `@IsIrreducible _ (algebraicTopology Y)`
(or an explicitly local `letI`).

The construction proves the Kuratowski closure identities directly, including
finite-union preservation by multiplying separating polynomials. The closure
in this topology is proved to equal the existing polynomial Zariski closure.
No closure-comparison or geometric irreducibility theorem is assumed here.
-/

noncomputable section

namespace Sheshadri.ConormalTopology

open MvPolynomial Set
open scoped Topology
open ZariskiBridge

theorem subset_zariskiClosure {Y : Type*} (s : Set (Y → ℂ)) :
    s ⊆ zariskiClosure s := by
  intro x hx q hq
  exact hq x hx

theorem zariskiClosure_mono {Y : Type*} {s t : Set (Y → ℂ)} (h : s ⊆ t) :
    zariskiClosure s ⊆ zariskiClosure t := by
  intro x hx q hq
  exact hx q (fun y hy => hq y (h hy))

@[simp] theorem zariskiClosure_idempotent {Y : Type*} (s : Set (Y → ℂ)) :
    zariskiClosure (zariskiClosure s) = zariskiClosure s := by
  apply Set.Subset.antisymm
  · intro x hx q hq
    exact hx q (fun y hy => hy q hq)
  · exact subset_zariskiClosure _

@[simp] theorem zariskiClosure_empty (Y : Type*) :
    zariskiClosure (∅ : Set (Y → ℂ)) = ∅ := by
  apply Set.eq_empty_iff_forall_not_mem.mpr
  intro x hx
  have h := hx (1 : MvPolynomial Y ℂ) (by simp)
  simp at h

/-- Finite unions of polynomial-closed sets are polynomial-closed: if a
point avoids both sets, the product of two separating polynomials separates
it from their union. -/
theorem zariskiClosure_union {Y : Type*} (s t : Set (Y → ℂ)) :
    zariskiClosure (s ∪ t) = zariskiClosure s ∪ zariskiClosure t := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hs : x ∈ zariskiClosure s
    · exact Or.inl hs
    apply Or.inr
    by_contra ht
    have hs' : ∃ p : MvPolynomial Y ℂ,
        (∀ y ∈ s, eval y p = 0) ∧ eval x p ≠ 0 := by
      by_contra h
      apply hs
      intro p hp
      by_contra hpx
      exact h ⟨p, hp, hpx⟩
    have ht' : ∃ q : MvPolynomial Y ℂ,
        (∀ y ∈ t, eval y q = 0) ∧ eval x q ≠ 0 := by
      by_contra h
      apply ht
      intro q hq
      by_contra hqx
      exact h ⟨q, hq, hqx⟩
    obtain ⟨p, hp, hpx⟩ := hs'
    obtain ⟨q, hq, hqx⟩ := ht'
    have hpq : ∀ y ∈ s ∪ t, eval y (p * q) = 0 := by
      intro y hy
      rcases hy with hy | hy
      · simp [map_mul, hp y hy]
      · simp [map_mul, hq y hy]
    exact mul_ne_zero hpx hqx (by simpa only [map_mul] using hx (p * q) hpq)
  · intro x hx
    rcases hx with hx | hx
    · exact zariskiClosure_mono Set.subset_union_left hx
    · exact zariskiClosure_mono Set.subset_union_right hx

theorem zariskiClosure_sInter_of_fixed {Y : Type*} (sets : Set (Set (Y → ℂ)))
    (hfixed : ∀ s ∈ sets, zariskiClosure s = s) :
    zariskiClosure (⋂₀ sets) = ⋂₀ sets := by
  apply Set.Subset.antisymm
  · intro x hx
    apply Set.mem_sInter.mpr
    intro s hs
    rw [← hfixed s hs]
    exact zariskiClosure_mono (Set.sInter_subset_of_mem hs) hx
  · exact subset_zariskiClosure _

/-- The Zariski topology, kept explicit to avoid changing the Euclidean
topology used by the analytic persistence theorems. -/
def algebraicTopology (Y : Type*) : TopologicalSpace (Y → ℂ) :=
  TopologicalSpace.ofClosed {s | zariskiClosure s = s}
    (zariskiClosure_empty Y)
    (fun sets hsets => zariskiClosure_sInter_of_fixed sets hsets)
    (fun s hs t ht => by
      change zariskiClosure (s ∪ t) = s ∪ t
      rw [zariskiClosure_union, hs, ht])

theorem isClosed_algebraicTopology_iff {Y : Type*} (s : Set (Y → ℂ)) :
    @IsClosed (Y → ℂ) (algebraicTopology Y) s ↔ zariskiClosure s = s := by
  constructor
  · intro h
    have h := h.isOpen_compl
    change zariskiClosure sᶜᶜ = sᶜᶜ at h
    simpa only [compl_compl] using h
  · intro h
    refine @IsClosed.mk (Y → ℂ) (algebraicTopology Y) s ?_
    change zariskiClosure sᶜᶜ = sᶜᶜ
    simpa only [compl_compl] using h

theorem isClosed_zariskiClosure {Y : Type*} (s : Set (Y → ℂ)) :
    @IsClosed (Y → ℂ) (algebraicTopology Y) (zariskiClosure s) :=
  (isClosed_algebraicTopology_iff _).mpr (zariskiClosure_idempotent s)

/-- The explicit topology realizes exactly the polynomial closure already
used in `ZariskiBridge`; no Euclidean closure is changed by this statement. -/
theorem closure_algebraicTopology_eq {Y : Type*} (s : Set (Y → ℂ)) :
    @closure (Y → ℂ) (algebraicTopology Y) s = zariskiClosure s := by
  letI := algebraicTopology Y
  apply Set.Subset.antisymm
  · exact closure_minimal (subset_zariskiClosure s) (isClosed_zariskiClosure s)
  · have hclosed : zariskiClosure (closure s) = closure s :=
      (isClosed_algebraicTopology_iff _).mp isClosed_closure
    rw [← hclosed]
    exact zariskiClosure_mono subset_closure

/-- A convenience theorem for passing a polynomial-closure support to a
closed-component argument with the explicitly algebraic topology. -/
theorem isClosed_of_zariskiClosure_eq {Y : Type*} {s : Set (Y → ℂ)}
    (h : zariskiClosure s = s) :
    @IsClosed (Y → ℂ) (algebraicTopology Y) s :=
  (isClosed_algebraicTopology_iff s).mpr h

/-- Polynomial zero loci are closed for the explicit algebraic topology. -/
theorem polynomial_zeroLocus_isClosed {Y : Type*} (p : MvPolynomial Y ℂ) :
    @IsClosed (Y → ℂ) (algebraicTopology Y) {x | eval x p = 0} := by
  apply isClosed_of_zariskiClosure_eq
  apply Set.Subset.antisymm
  · intro x hx
    exact hx p (fun _ hy => hy)
  · exact subset_zariskiClosure _

/-- For finite coordinate spaces an algebraically closed set is also
Euclidean closed. The conclusion uses the unchanged standard topology. -/
theorem euclidean_isClosed_of_algebraic_isClosed {Y : Type*} [Fintype Y]
    {s : Set (Y → ℂ)} (h : @IsClosed (Y → ℂ) (algebraicTopology Y) s) :
    IsClosed s := by
  apply isClosed_of_closure_subset
  have hfixed := (isClosed_algebraicTopology_iff s).mp h
  exact (ZariskiBridge.euclidean_closure_subset_zariski s).trans hfixed.le

end Sheshadri.ConormalTopology
