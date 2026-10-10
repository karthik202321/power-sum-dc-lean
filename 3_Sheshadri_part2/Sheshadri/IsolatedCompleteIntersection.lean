/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.LocalCompleteIntersection
import Sheshadri.CoordinatePowerRegular
import Mathlib.Data.Finset.Sort
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.Submodule

/-!
# An isolated square polynomial system is a local complete intersection

The equations are arbitrary polynomials over an infinite field. Isolation is
expressed by the actual quotient of the polynomial local ring being Artinian;
no Jacobian rank, reducedness, transversality or regular-sequence hypothesis is
imposed. Nilpotence puts positive coordinate powers in the equation ideal.
The proved regular-sequence exchange theorem then applies to these powers.
-/

noncomputable section
namespace Sheshadri.IsolatedCompleteIntersection
open MvPolynomial RingTheory.Sequence LocalCompleteIntersection CoordinatePowerRegular

variable {σ K : Type*} [Fintype σ] [Field K] [Infinite K]

def localEquations (p : σ → K) (fs : List (MvPolynomial σ K)) :
    List (PointLocalRing p) :=
  fs.map (algebraMap (MvPolynomial σ K) (PointLocalRing p))

def localEquationIdeal (p : σ → K) (fs : List (MvPolynomial σ K)) :
    Ideal (PointLocalRing p) := Ideal.ofList (localEquations p fs)

/-- Full local complete-intersection theorem for isolated square systems,
including singular and nonreduced isolated zeros. Other points and excess
components of the global system are unrestricted. -/
theorem isolated_square_regular (p : σ → K) (fs : List (MvPolynomial σ K))
    (hsquare : fs.length = Fintype.card σ)
    (hzero : ∀ f ∈ fs, eval p f = 0)
    [IsArtinianRing (PointLocalRing p ⧸ localEquationIdeal p fs)] :
    IsRegular (PointLocalRing p) (localEquations p fs) := by
  classical
  letI : IsNoetherianRing (PointLocalRing p) :=
    IsLocalization.isNoetherianRing (pointIdeal p).primeCompl _ inferInstance
  let l : List σ := Finset.univ.toList
  obtain ⟨n, hn, hpower⟩ :=
    exists_positive_power_mem_of_artinian_quotient (localEquationIdeal p fs)
  let gs : List (PointLocalRing p) := l.map (fun i =>
    (algebraMap (MvPolynomial σ K) (PointLocalRing p) (X i-C (p i)))^n)
  have hgs : IsRegular (PointLocalRing p) gs :=
    coordinate_powers_at_point p l (Finset.nodup_toList _) (fun _ => n)
      (fun _ _ => hn)
  refine ring_regular_of_contains_regular_sequence K (localEquations p fs) gs ?_ hgs ?_ ?_
  · intro f hf
    change f ∈ fs.map (algebraMap (MvPolynomial σ K) (PointLocalRing p)) at hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (PointLocalRing p) (pointIdeal p) g).mpr
    exact hzero g hg
  · simp [gs, l, localEquations, hsquare]
  · apply Ideal.span_le.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    apply hpower
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (PointLocalRing p) (pointIdeal p) _).mpr
    change eval p (X i-C (p i)) = 0
    simp

end Sheshadri.IsolatedCompleteIntersection
