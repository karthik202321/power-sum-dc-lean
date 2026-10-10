/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.GenericGaussPolars
import Sheshadri.SaturationHilbertTail

/-! # Constructed sequences of actual Gauss polars

No global regularity of the original homogeneous quotient is required.
Each chosen polar is regular on its actual irrelevant saturation, hence
filter regular on the actual unsaturated equation ideal. This suffices for
the Hilbert-polynomial degree computation and retains scheme multiplicity.
-/

noncomputable section
namespace Sheshadri.GenericGaussPolarSequence
open MvPolynomial SmoothGaussPolars GenericGaussPolars GenericHomogeneousSections
open HomogeneousQuotientExact

variable {σ k : Type*} [Fintype σ] [Field k] [CharZero k] [IsAlgClosed k]

theorem exists_filterRegular_polar (I : Ideal (MvPolynomial σ k))
    (hI : ∀ d p, p ∈ I → homogeneousComponent d p ∈ I)
    {f : MvPolynomial σ k} {d : ℕ} (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hsmooth : ∀ x : σ → k, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) :
    ∃ ell : σ → k,
      FilterRegular I (polar f ell) (polar_homogeneous hf ell) := by
  obtain ⟨ell, hreg⟩ := exists_regular_polar (IrrelevantSaturation.saturation I)
    (IrrelevantSaturation.saturation_isSaturated I) hf hd hsmooth
  exact ⟨ell, SaturationHilbertTail.filterRegular_of_regular_saturation I hI
    (polar f ell) (polar_homogeneous hf ell) hreg⟩

/-- All the polar coefficients in an arbitrarily long sequence are
constructed simultaneously, using the actual preceding equation ideals. -/
theorem exists_filterRegular_polar_sequence (I : Ideal (MvPolynomial σ k))
    (hI : ∀ d p, p ∈ I → homogeneousComponent d p ∈ I)
    {f : MvPolynomial σ k} {d : ℕ} (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hsmooth : ∀ x : σ → k, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) :
    ∃ ell : ℕ → σ → k, ∀ j : ℕ,
      FilterRegular (idealSequence I (fun t => polar f (ell t)) j)
        (polar f (ell j)) (polar_homogeneous hf (ell j)) := by
  classical
  let H := {J : Ideal (MvPolynomial σ k) //
    ∀ d p, p ∈ J → homogeneousComponent d p ∈ J}
  have hex (J : H) := exists_filterRegular_polar J.val J.property hf hd hsmooth
  choose coeff hcoeff using hex
  let step (J : H) : H := ⟨enlargedIdeal J.val (polar f (coeff J)),
    enlargedIdeal_homogeneous J.val J.property _ (polar_homogeneous hf (coeff J))⟩
  let states : ℕ → H := fun j => Nat.rec ⟨I, hI⟩ (fun _ J => step J) j
  let ell : ℕ → σ → k := fun j => coeff (states j)
  refine ⟨ell, ?_⟩
  have hstates (j : ℕ) : (states j).val =
      idealSequence I (fun t => polar f (ell t)) j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change enlargedIdeal (states j).val (polar f (ell j)) = _
      rw [ih]
      rfl
  intro j
  rw [← hstates j]
  exact hcoeff (states j)

/-- The initial hypersurface equation is the literal principal ideal. -/
theorem exists_hypersurface_polar_sequence {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hsmooth : ∀ x : σ → k, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) :
    ∃ ell : ℕ → σ → k, ∀ j : ℕ,
      FilterRegular (idealSequence (Ideal.span {f}) (fun t => polar f (ell t)) j)
        (polar f (ell j)) (polar_homogeneous hf (ell j)) := by
  apply exists_filterRegular_polar_sequence (Ideal.span {f}) _ hf hd hsmooth
  have hh := enlargedIdeal_homogeneous (⊥ : Ideal (MvPolynomial σ k))
    (fun d p hp => by simpa only [Ideal.mem_bot.mp hp, map_zero] using
      (Ideal.zero_mem (⊥ : Ideal (MvPolynomial σ k)))) f hf
  simpa only [enlargedIdeal, bot_sup_eq] using hh

end Sheshadri.GenericGaussPolarSequence
