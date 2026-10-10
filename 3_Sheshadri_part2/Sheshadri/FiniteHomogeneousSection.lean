/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SaturationHilbertTail

/-!
# A genuine affine chart for a finite homogeneous section

An eventually constant actual Hilbert function admits a homogeneous linear
chart whose boundary has no projective support. The chart is constructed by
generic filter-regular selection. The boundary support condition follows from
the exact Hilbert difference and literal coordinate-power membership.
-/

noncomputable section
namespace Sheshadri.FiniteHomogeneousSection
set_option synthInstance.maxHeartbeats 200000
open MvPolynomial FlatGradedHilbert HomogeneousQuotientExact
open GenericHomogeneousSections SaturationHilbertTail

variable {Z K : Type*} [Finite Z] [Field K]

/-- Eventual vanishing of actual homogeneous pieces forces every coordinate
to belong to the radical of the actual ideal. -/
theorem coordinate_mem_radical_of_eventually_zero
    (I : Ideal (MvPolynomial Z K))
    (hzero : ∃ N : ℕ, ∀ k, N ≤ k → Module.finrank K (coordinatePiece Z K I k) = 0) :
    ∀ i : Z, X i ∈ I.radical := by
  obtain ⟨N, hN⟩ := hzero
  intro i
  letI : Subsingleton (coordinatePiece Z K I N) := Module.finrank_zero_iff.mp (hN N le_rfl)
  let x : coordinatePiece Z K I N :=
    ⟨Ideal.Quotient.mk I (X i ^ N), X i ^ N,
      by simpa using (isHomogeneous_X K i).pow N, rfl⟩
  refine ⟨N, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  exact congrArg Subtype.val (Subsingleton.elim x 0)

theorem eventually_zero_after_filterRegular_hyperplane
    (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k f, f ∈ I → homogeneousComponent k f ∈ I)
    (M : ℕ) (hconst : ∃ N : ℕ, ∀ k > N, Module.finrank K (coordinatePiece Z K I k) = M)
    (l : MvPolynomial Z K) (hl : l.IsHomogeneous 1) (hreg : FilterRegular I l hl) :
    ∃ B : ℕ, ∀ k, B ≤ k →
      Module.finrank K (coordinatePiece Z K (enlargedIdeal I l) k) = 0 := by
  obtain ⟨N, hN⟩ := hconst
  obtain ⟨B, hB⟩ := hreg
  refine ⟨max N B + 2, fun k hk => ?_⟩
  have h := coordinate_finrank_difference_of_piece_injective I hI l hl (k-1)
    (hB (k-1) (by omega))
  have he : 1 + (k-1) = k := by omega
  rw [he, hN (k-1) (by omega), hN k (by omega)] at h
  omega

/-- The avoiding hyperplane and its actual ideal-theoretic support property
are conclusions. No generic flag, finite-support, or count certificate is
an input to this theorem. -/
theorem exists_hyperplane_avoiding_support_of_eventually_constant [Infinite K]
    (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k f, f ∈ I → homogeneousComponent k f ∈ I)
    (M : ℕ) (hconst : ∃ N : ℕ, ∀ k > N, Module.finrank K (coordinatePiece Z K I k) = M) :
    ∃ l : MvPolynomial Z K, ∃ hl : l.IsHomogeneous 1,
      FilterRegular I l hl ∧ ∀ i : Z, X i ∈ (enlargedIdeal I l).radical := by
  obtain ⟨l, hl, hreg⟩ := exists_filterRegular_hyperplane I hI
  exact ⟨l, hl, hreg, coordinate_mem_radical_of_eventually_zero _
    (eventually_zero_after_filterRegular_hyperplane I hI M hconst l hl hreg)⟩

end Sheshadri.FiniteHomogeneousSection
