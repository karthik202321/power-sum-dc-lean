/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.DVRRootPersistence
import Sheshadri.HomogeneousSystemSaturation

/-! # Saturated generic equations preserve isolated special local algebras

Saturation by displayed open conditions does not lose any part of a special
local algebra where one condition is nonzero. The conclusion concerns the
literal local rings, retaining singular multiplicities and nilpotents.
-/

noncomputable section
namespace Sheshadri.DVRSaturatedPersistence
open MvPolynomial DVRRootPersistence BezoutHorizontalFamily GeneralGradedBaseChange
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

section LocalUnit
variable {σ k : Type*} [Field k]

theorem localPolynomialMap_isUnit_of_eval_ne_zero
    (I : Ideal (MvPolynomial σ k)) (p : σ → k)
    (hI : I ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (g : MvPolynomial σ k) (hg : eval p g ≠ 0) :
    IsUnit (IsolatedLocalMultiplicity.localPolynomialMap I p hI g) := by
  exact IsLocalization.map_units
    (M := (IsolatedLocalMultiplicity.quotientPointIdeal I p hI).primeCompl)
    (IsolatedLocalMultiplicity.LocalIntersectionRing I p hI)
    ⟨Ideal.Quotient.mk I g, hg⟩

end LocalUnit

section Persistence
variable {σ k D L E : Type*} [Fintype σ] [Field k] [Infinite k]
    [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Field L] [Algebra D L] [IsFractionRing D L]
    (ε : D →+* k) (hε : Function.Surjective ε) (π : D)
    (hπ : Irreducible π) (hker : RingHom.ker ε = Ideal.span {π})
    (fs : List (MvPolynomial σ D)) (p : σ → k)
    (hsquare : fs.length = Fintype.card σ)
    (hz : ∀ r ∈ fs, eval p (specialize ε r) = 0)
    [IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing
      (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz))]

include hε hπ hker hsquare hz in
/-- A single actual saturation denominator which is a unit at the selected
special local algebra suffices for full scheme-theoretic persistence. -/
theorem family_power_contraction_annihilates_local
    (g q : MvPolynomial σ D) (n : ℕ)
    (hg : IsUnit (IsolatedLocalMultiplicity.localPolynomialMap
      (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz) (specialize ε g)))
    (hq : MvPolynomial.map (algebraMap D L) g ^ n *
      MvPolynomial.map (algebraMap D L) q ∈ extendedIdeal (K := L) (Ideal.ofList fs)) :
    IsolatedLocalMultiplicity.localPolynomialMap
      (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz) (specialize ε q) = 0 := by
  have hmem : g^n*q ∈ contractedIdeal
      (extendedIdeal (K := L) (Ideal.ofList fs)) := by
    change MvPolynomial.map (algebraMap D L) (g^n*q) ∈
      extendedIdeal (K := L) (Ideal.ofList fs)
    simpa only [map_mul, map_pow] using hq
  have hzero := family_contraction_annihilates_local ε hε π hπ hker fs p hsquare hz _ hmem
  simp only [map_mul, map_pow] at hzero
  exact (hg.pow n).isRegular.left.mul_left_eq_zero_iff.mp hzero

include hε hπ hker hsquare hz in
/-- Any intermediate generic ideal contained in the actual saturation
annihilates the full selected special local algebra after contraction. -/
theorem family_saturated_contraction_annihilates_local_of_isUnit
    (gs : E → MvPolynomial σ D) (J : Ideal (MvPolynomial σ L))
    (hJ : J ≤ HomogeneousSystemSaturation.saturation
      (extendedIdeal (K := L) (Ideal.ofList fs))
      (fun i => MvPolynomial.map (algebraMap D L) (gs i)))
    (i : E) (hi : IsUnit (IsolatedLocalMultiplicity.localPolynomialMap
      (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz) (specialize ε (gs i))))
    (q : MvPolynomial σ D) (hq : q ∈ contractedIdeal (R := D) J) :
    IsolatedLocalMultiplicity.localPolynomialMap
      (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz) (specialize ε q) = 0 := by
  obtain ⟨n, hn⟩ := hJ hq i
  exact family_power_contraction_annihilates_local ε hε π hπ hker fs p hsquare hz
    (gs i) q n hi hn

include hε hπ hker hsquare hz in
/-- The unit condition follows from literal nonvanishing of one displayed
open condition at the selected special point. -/
theorem family_saturated_contraction_annihilates_local
    (gs : E → MvPolynomial σ D) (J : Ideal (MvPolynomial σ L))
    (hJ : J ≤ HomogeneousSystemSaturation.saturation
      (extendedIdeal (K := L) (Ideal.ofList fs))
      (fun i => MvPolynomial.map (algebraMap D L) (gs i)))
    (i : E) (hi : eval p (specialize ε (gs i)) ≠ 0)
    (q : MvPolynomial σ D) (hq : q ∈ contractedIdeal (R := D) J) :
    IsolatedLocalMultiplicity.localPolynomialMap
      (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz) (specialize ε q) = 0 :=
  family_saturated_contraction_annihilates_local_of_isUnit ε hε π hπ hker fs p hsquare hz
    gs J hJ i (localPolynomialMap_isUnit_of_eval_ne_zero _ p _ _ hi) q hq

include hε hπ hker hsquare hz in
/-- Ideal form for applying interpolation and finite-dimensional comparison
theorems to the actual specialized horizontal quotient. -/
theorem specialized_saturated_contraction_le_localKernel
    (gs : E → MvPolynomial σ D) (J : Ideal (MvPolynomial σ L))
    (hJ : J ≤ HomogeneousSystemSaturation.saturation
      (extendedIdeal (K := L) (Ideal.ofList fs))
      (fun i => MvPolynomial.map (algebraMap D L) (gs i)))
    (i : E) (hi : eval p (specialize ε (gs i)) ≠ 0) :
    (contractedIdeal (R := D) J).map (specialize ε) ≤
      RingHom.ker (IsolatedLocalMultiplicity.localPolynomialMap
        (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz)) := by
  rw [Ideal.map_le_iff_le_comap]
  intro q hq
  exact family_saturated_contraction_annihilates_local ε hε π hπ hker fs p hsquare hz
    gs J hJ i hi q hq

include hε hπ hker hsquare hz in
/-- If the generic ideal lies between the original equations and their
saturation, its contracted special ideal agrees exactly with the original
special equations in the actual polynomial local ring. -/
theorem specialized_saturated_contractedIdeal_localization_eq
    (gs : E → MvPolynomial σ D) (J : Ideal (MvPolynomial σ L))
    (hIJ : extendedIdeal (K := L) (Ideal.ofList fs) ≤ J)
    (hJI : J ≤ HomogeneousSystemSaturation.saturation
      (extendedIdeal (K := L) (Ideal.ofList fs))
      (fun i => MvPolynomial.map (algebraMap D L) (gs i)))
    (i : E) (hi : eval p (specialize ε (gs i)) ≠ 0) :
    ((contractedIdeal (R := D) J).map (specialize ε)).map
      (algebraMap _ (CoordinatePowerRegular.PointLocalRing p)) =
    (specialIdeal ε fs).map (algebraMap _ (CoordinatePowerRegular.PointLocalRing p)) := by
  apply le_antisymm
  · rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro q hq
    change algebraMap _ (CoordinatePowerRegular.PointLocalRing p) (specialize ε q) ∈
      (specialIdeal ε fs).map (algebraMap _ (CoordinatePowerRegular.PointLocalRing p))
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (SingularSpecialFiber.localEquationQuotientEquiv (specialIdeal ε fs) p
      (specialIdeal_le_pointIdeal ε fs p hz)).injective
    rw [map_zero, SingularSpecialFiber.localEquationQuotientEquiv_mk]
    exact family_saturated_contraction_annihilates_local ε hε π hπ hker fs p hsquare hz
      gs J hJI i hi q hq
  · apply Ideal.map_mono
    have h : Ideal.ofList fs ≤ contractedIdeal (R := D) J :=
      (originalIdeal_le_contraction (K := L) _).trans (Ideal.comap_mono hIJ)
    simpa only [specialIdeal, Ideal.map_ofList] using Ideal.map_mono (f := specialize ε) h

end Persistence
end Sheshadri.DVRSaturatedPersistence
