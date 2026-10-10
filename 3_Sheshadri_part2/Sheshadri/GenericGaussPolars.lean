/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SmoothGaussPolars
import Sheshadri.GenericHomogeneousSections

/-!
# Actual generic Gauss polar sections

The flags are constructed by finite associated-prime avoidance. The smooth
hypersurface's actual gradient ideal supplies the required basepoint-free
linear system through Nullstellensatz. This produces coefficients of a polar,
not an unspecified regular polynomial or a numerical section certificate.
-/

noncomputable section
namespace Sheshadri.GenericGaussPolars
open MvPolynomial SmoothGaussPolars GenericHomogeneousSections

variable {σ k : Type*} [Fintype σ] [Field k] [CharZero k] [IsAlgClosed k]

/-- Every actual irrelevant-saturated quotient admits a regular polar of
a smooth homogeneous hypersurface. All coefficients are constructed. -/
theorem exists_regular_polar (I : Ideal (MvPolynomial σ k))
    (hI : IsIrrelevantSaturated I) {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hsmooth : ∀ x : σ → k, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) :
    ∃ ell : σ → k, IsRegular (Ideal.Quotient.mk I (polar f ell)) := by
  have hder : ∀ g ∈ derivativeList f, g.IsHomogeneous (d-1) := by
    intro g hg
    have hg' : g ∈ Set.range (fun i => pderiv i f) := by
      rw [← derivativeList_set]
      exact hg
    obtain ⟨i, rfl⟩ := hg'
    exact hf.pderiv
  have hrad : ∀ i : σ, X i ∈ (Ideal.ofList (derivativeList f)).radical := by
    rw [derivativeList_ideal]
    exact coordinate_mem_radical_gradient hf hd hsmooth
  obtain ⟨g, hspan, _, hreg⟩ :=
    exists_regular_homogeneous_of_radical I hI (derivativeList f) (d-1) hder hrad
  rw [derivativeList_set] at hspan
  obtain ⟨ell, rfl⟩ := (mem_polarSpan_iff f g).mp hspan
  exact ⟨ell, hreg⟩

end Sheshadri.GenericGaussPolars
