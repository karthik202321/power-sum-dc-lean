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
import Sheshadri.HomogeneousVanishing

/-!
# Bihomogeneity of the actual total Gauss family

The parameter variables have weight zero; the primal and dual homogeneous
coordinates have weights `(1,0)` and `(0,1)`. Independent rescaling of the
actual smooth Gauss graph proves that its actual vanishing ideal is closed
under taking every bihomogeneous component.
-/

noncomputable section

namespace Sheshadri.ActualGaussHomogeneous

open MvPolynomial ActualGaussFamily

variable {A Z : Type*} [Fintype A] [Fintype Z]

def totalWeight : TotalCoordinates A Z → ℕ × ℕ :=
  Sum.elim (fun _ => (0, 0)) (Sum.elim (fun _ => (1, 0)) (fun _ => (0, 1)))

theorem weighted_rescale_eq (s t : ℂ) (q : TotalAmbient A Z) :
    (fun i => s ^ (totalWeight i).1 * (t ^ (totalWeight i).2 * q i)) =
      rescaleTotal s t q := by
  funext i
  cases i with
  | inl i => simp [totalWeight, rescaleTotal]
  | inr i => cases i <;> simp [totalWeight, rescaleTotal]

/-- Bihomogeneity is proved for the literal ideal used to define the total
family. It is not a field in an assumed family certificate. -/
theorem totalIdeal_bihomogeneous
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ))
    (a b : ℕ) (p : MvPolynomial (TotalCoordinates A Z) ℂ)
    (hp : p ∈ totalIdeal F U) :
    weightedHomogeneousComponent totalWeight (a, b) p ∈ totalIdeal F U := by
  intro q hq
  apply HomogeneousVanishing.biweightedComponent_eval_zero (RingHom.id ℂ) q totalWeight p
  intro s t hs ht
  rw [weighted_rescale_eq]
  exact hp _ (rescaleTotal_mem_totalGraph F U s t hs ht hq)

end Sheshadri.ActualGaussHomogeneous
