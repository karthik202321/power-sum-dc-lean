/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.GenericGaussPolarSequence
import Sheshadri.FilterRegularCompleteIntersection

/-!
# The actual homogeneous Gauss-polar degree

For a smooth homogeneous hypersurface the flags are constructed as actual
linear combinations of its derivatives. The eventual Hilbert dimension of
the actual section ideal is the degree times the appropriate power of one
less than the degree. No degree function, section cardinality, genericity
certificate, or transversality premise occurs in the result.
-/

noncomputable section
namespace Sheshadri.SmoothGaussDegree
open MvPolynomial SmoothGaussPolars GenericGaussPolarSequence
open GenericHomogeneousSections HomogeneousQuotientExact FlatGradedHilbert

variable {σ K : Type*} [Fintype σ] [Field K] [CharZero K] [IsAlgClosed K]

/-- The literal ideal obtained by adjoining r derivative polars to f. -/
def polarIdeal (f : MvPolynomial σ K) (ell : ℕ → σ → K) (r : ℕ) :
    Ideal (MvPolynomial σ K) :=
  idealSequence (Ideal.span {f}) (fun j => polar f (ell j)) r

def augmentedPolars (f : MvPolynomial σ K) (ell : ℕ → σ → K) :
    ℕ → MvPolynomial σ K
  | 0 => f
  | j+1 => polar f (ell j)

def polarDegrees (d : ℕ) : ℕ → ℕ
  | 0 => d
  | _+1 => d-1

theorem augmentedPolars_idealSequence (f : MvPolynomial σ K)
    (ell : ℕ → σ → K) (r : ℕ) :
    idealSequence (⊥ : Ideal (MvPolynomial σ K)) (augmentedPolars f ell) (r+1) =
      polarIdeal f ell r := by
  induction r with
  | zero => simp [idealSequence, augmentedPolars, polarIdeal, enlargedIdeal]
  | succ r ih =>
    change enlargedIdeal
      (idealSequence (⊥ : Ideal (MvPolynomial σ K)) (augmentedPolars f ell) (r+1))
      (polar f (ell r)) = _
    rw [ih]
    rfl

theorem polarDegrees_product (d r : ℕ) :
    (∏ j ∈ Finset.range (r+1), polarDegrees d j) = d * (d-1)^r := by
  rw [Finset.prod_range_succ']
  simp [polarDegrees, mul_comm]

theorem polarIdeal_homogeneous {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsHomogeneous d) (ell : ℕ → σ → K) (r : ℕ) :
    ∀ j p, p ∈ polarIdeal f ell r → homogeneousComponent j p ∈ polarIdeal f ell r := by
  rw [← augmentedPolars_idealSequence]
  have hI : ∀ j p, p ∈ (⊥ : Ideal (MvPolynomial σ K)) →
      homogeneousComponent j p ∈ (⊥ : Ideal (MvPolynomial σ K)) := by
    intro j p hp
    simpa only [Ideal.mem_bot.mp hp, map_zero] using
      (Ideal.zero_mem (⊥ : Ideal (MvPolynomial σ K)))
  refine idealSequence_homogeneous _ hI _ (polarDegrees d) (r+1) ?_
  intro j hj
  cases j with
  | zero => exact hf
  | succ j => exact polar_homogeneous hf (ell j)

/-- Constructed Gauss flags give the expected full section Hilbert degree.
This statement counts scheme length once the finite-chart comparison is
applied; it makes no reducedness or distinct-point count assertion. -/
theorem exists_polar_hilbert_constant (r : ℕ) (hcard : Fintype.card σ = r+2)
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d)
    (hfn : f ≠ 0) (hd : 0 < d)
    (hsmooth : ∀ x : σ → K, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) :
    ∃ ell : ℕ → σ → K, ∃ N : ℕ, ∀ k : ℕ, N < k →
      Module.finrank K (coordinatePiece σ K (polarIdeal f ell r) k) =
        d * (d-1)^r := by
  obtain ⟨ell, hell⟩ := exists_hypersurface_polar_sequence hf hd hsmooth
  have hg (j : ℕ) : (augmentedPolars f ell j).IsHomogeneous (polarDegrees d j) := by
    cases j with
    | zero => exact hf
    | succ j => exact polar_homogeneous hf (ell j)
  have hreg (j : ℕ) : FilterRegular
      (idealSequence (⊥ : Ideal (MvPolynomial σ K)) (augmentedPolars f ell) j)
      (augmentedPolars f ell j) (hg j) := by
    cases j with
    | zero =>
      change FilterRegular (⊥ : Ideal (MvPolynomial σ K)) f hf
      apply regular_filterRegular
      let e := RingEquiv.quotientBot (MvPolynomial σ K)
      constructor
      · intro a b hab
        apply e.injective
        apply mul_left_cancel₀ hfn
        have he := congrArg e hab
        simpa only [map_mul, RingEquiv.quotientBot_mk] using he
      · intro a b hab
        apply e.injective
        apply mul_right_cancel₀ hfn
        have he := congrArg e hab
        simpa only [map_mul, RingEquiv.quotientBot_mk] using he
    | succ j =>
      rw [augmentedPolars_idealSequence]
      exact hell j
  obtain ⟨N, hN⟩ := FilterRegularCompleteIntersection.eventual_coordinate_finrank_eq_product_filterRegular
    (augmentedPolars f ell) (polarDegrees d) (r+1) (by omega)
    (fun j _ => hg j) (fun j _ => hreg j)
  refine ⟨ell, N, fun k hk => ?_⟩
  have hh := hN k hk
  rwa [augmentedPolars_idealSequence, polarDegrees_product] at hh

/-- The n-variable specialization used by the conormal cone slot. -/
theorem smooth_hypersurface_polar_degree {n d : ℕ} (hn : 2 ≤ n)
    {f : MvPolynomial (Fin n) K} (hf : f.IsHomogeneous d)
    (hfn : f ≠ 0) (hd : 0 < d)
    (hsmooth : ∀ x : Fin n → K, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) :
    ∃ ell : ℕ → Fin n → K, ∃ N : ℕ, ∀ k : ℕ, N < k →
      Module.finrank K (coordinatePiece (Fin n) K (polarIdeal f ell (n-2)) k) =
        d * (d-1)^(n-2) := by
  exact exists_polar_hilbert_constant (n-2) (by simpa using (Nat.sub_add_cancel hn).symm)
    hf hfn hd hsmooth

end Sheshadri.SmoothGaussDegree
