/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldProjectiveLocalMultiplicity

noncomputable section
open Sheshadri.MultiProjective
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

namespace Sheshadri.FieldProjectiveMultiplicityInterpolation
variable {k₀ : Type*} [Field k₀] [CharZero k₀]
open MvPolynomial FieldMultiProjective FieldProjectiveLocalMultiplicity
open ProjectivePointInterpolation FatPointInterpolation FieldCommonProjectiveChart

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

variable {X U V E P : Type*}

def residueMap (f : E → MvPolynomial (Variables X U V) k₀)
    (p : Variables X U V → k₀) (c : Chart p) (hz : ∀ e, eval p (f e) = 0) :
    LocalRing f p c hz →ₐ[k₀] k₀ :=
  IsolatedLocalMultiplicity.localEvaluationAlg (chartIdeal f p c) p
    (chartIdeal_le_pointIdeal f p c hz)

@[simp] theorem residueMap_polynomialMap
    (f : E → MvPolynomial (Variables X U V) k₀)
    (p : Variables X U V → k₀) (c : Chart p) (hz : ∀ e, eval p (f e) = 0)
    (g : MvPolynomial (Variables X U V) k₀) :
    residueMap f p c hz (polynomialMap f p c hz g) = eval p g := by
  exact IsolatedLocalMultiplicity.localEvaluation_algebraMap _ _ _ _

theorem polynomialMap_isUnit
    (f : E → MvPolynomial (Variables X U V) k₀)
    (p : Variables X U V → k₀) (c : Chart p) (hz : ∀ e, eval p (f e) = 0)
    (g : MvPolynomial (Variables X U V) k₀) (hg : eval p g ≠ 0) :
    IsUnit (polynomialMap f p c hz g) := by
  apply IsLocalRing.not_mem_maximalIdeal.mp
  rw [← IsolatedLocalMultiplicity.localEvaluation_ker (chartIdeal f p c) p
    (chartIdeal_le_pointIdeal f p c hz)]
  change residueMap f p c hz (polynomialMap f p c hz g) ≠ 0
  simpa using hg

theorem chart_coordinate_block {p : Variables X U V → k₀} (c : Chart p) (i : Fin 3) :
    blockIndex (c.coordinate i) = i := by
  fin_cases i <;> rfl

/-- Every sufficiently high actual trihomogeneous piece has dimension at
least the sum of the full local intersection dimensions at the specified
isolated, projectively distinct points. Other components are unrestricted. -/
theorem eventual_sum_finrank_le_piece
    [Fintype X] [Fintype U] [Fintype V] [Fintype P]
    (f : E → MvPolynomial (Variables X U V) k₀)
    (points : P → Variables X U V → k₀) (charts : ∀ p, Chart (points p))
    (hz : ∀ p e, eval (points p) (f e) = 0)
    [∀ p, IsArtinianRing (LocalRing f (points p) (charts p) (hz p))]
    (I : Ideal (MvPolynomial (Variables X U V) k₀))
    (hI : FlatMultiGradedHilbert.IsHomogeneous (weight X U V) I)
    (hkill : ∀ p g, g ∈ I → polynomialMap f (points p) (charts p) (hz p) g = 0)
    (hdist : ∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      (∑ p, Module.finrank k₀ (LocalRing f (points p) (charts p) (hz p))) ≤
        Module.finrank k₀ (coordinatePiece (weight X U V) I (n, n, n)) := by
  classical
  let A := fun p => LocalRing f (points p) (charts p) (hz p)
  let φ : ∀ p, MvPolynomial (Variables X U V) k₀ →ₐ[k₀] A p :=
    fun p => polynomialMap f (points p) (charts p) (hz p)
  let ε : ∀ p, A p →ₐ[k₀] k₀ := fun p => residueMap f (points p) (charts p) (hz p)
  have hn : ∀ p, HasNonzeroBlocks (points p) := fun p =>
    ⟨⟨(charts p).ix, (charts p).hx⟩, ⟨(charts p).iu, (charts p).hu⟩,
      ⟨(charts p).iv, (charts p).hv⟩⟩
  obtain ⟨lx, lu, lv, hx, hu, hv⟩ := exists_three_common_forms points hn
  let L : Fin 3 → MvPolynomial (Variables X U V) k₀ :=
    ![firstForm lx, secondForm lu, thirdForm lv]
  have hL (p : P) (i : Fin 3) : eval (points p) (L i) ≠ 0 := by
    fin_cases i
    · exact hx p
    · exact hu p
    · exact hv p
  have hunit (p : P) (i : Fin 3) : IsUnit (φ p (L i)) :=
    polynomialMap_isUnit f (points p) (charts p) (hz p) (L i) (hL p i)
  let units (p : P) (i : Fin 3) : (A p)ˣ := (hunit p i).unit
  have hunits (p : P) (i : Fin 3) : (units p i : A p) = φ p (L i) :=
    (hunit p i).unit_spec
  let ψ : ∀ p, MvPolynomial (Variables X U V) k₀ →ₐ[k₀] A p :=
    fun p => normalizedMap (φ p) blockIndex (units p)
  have hφ (p : P) : Function.Surjective (φ p) :=
    IsolatedLocalMultiplicity.localPolynomialMap_surjective _ _ _
  have hψ (p : P) : Function.Surjective (ψ p) :=
    normalizedMap_surjective (φ p) (hφ p) blockIndex (units p)
      (charts p).coordinate (chart_coordinate_block (charts p))
      (fun i => points p ((charts p).coordinate i)) (charts p).coordinate_ne_zero
      (polynomialMap_chart_coordinate f (points p) (charts p) (hz p))
  have hε (p : P) (g : MvPolynomial (Variables X U V) k₀) :
      ε p (φ p g) = eval (points p) g := residueMap_polynomialMap f _ _ _ g
  have hres (p : P) : IsolatedLocalMultiplicity.residuePoint (ψ p) (ε p) =
      normalizedPoint (points p) (eval (points p) (firstForm lx))
        (eval (points p) (secondForm lu)) (eval (points p) (thirdForm lv)) := by
    funext i
    rcases i with i | (i | i) <;>
      simp [IsolatedLocalMultiplicity.residuePoint, ψ, normalizedMap_X,
        map_units_inv, hunits, hε, normalizedPoint, blockIndex, L]
  have hresinj : Function.Injective
      (fun p => IsolatedLocalMultiplicity.residuePoint (ψ p) (ε p)) := by
    simpa only [hres] using normalizedPoints_injective points
      (fun p => eval (points p) (firstForm lx))
      (fun p => eval (points p) (secondForm lu))
      (fun p => eval (points p) (thirdForm lv)) hx hu hv hdist
  let Φ := Pi.algHom k₀ _ ψ
  have hΦ : Function.Surjective Φ :=
    IsolatedLocalMultiplicity.piAlgHom_surjective_of_distinctResidues A ψ hψ ε hresinj
  have hkill' : ∀ g ∈ I, Φ g = 0 := by
    intro g hg
    funext p
    exact normalizedMap_kills_homogeneous_ideal (φ p) (units p) I hI (hkill p) g hg
  have hx' : Φ (firstForm lx) = 1 := by
    funext p
    exact normalizedMap_first_form (φ p) (units p) _ (firstForm_homogeneous lx)
      (hunits p 0).symm
  have hu' : Φ (secondForm lu) = 1 := by
    funext p
    exact normalizedMap_second_form (φ p) (units p) _ (secondForm_homogeneous lu)
      (hunits p 1).symm
  have hv' : Φ (thirdForm lv) = 1 := by
    funext p
    exact normalizedMap_third_form (φ p) (units p) _ (thirdForm_homogeneous lv)
      (hunits p 2).symm
  simpa only [Module.finrank_pi_fintype] using
    eventually_finrank_le_coordinatePiece_forms (weight X U V)
      (firstForm lx) (secondForm lu) (thirdForm lv)
      (firstForm_homogeneous lx) (secondForm_homogeneous lu) (thirdForm_homogeneous lv)
      I Φ hΦ hkill' hx' hu' hv'

end Sheshadri.FieldProjectiveMultiplicityInterpolation
