/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.DVRFibreDimension
import Sheshadri.DVRGaussSection
import Sheshadri.BezoutPieceComparison

/-!
# Full special section length is bounded by the actual finite generic algebra

The special lower bound is proved by simultaneous interpolation onto the
actual local rings. The generic comparison is the proved flat DVR fibre
inequality. A generic finite-dimensionality hypothesis remains explicit in
this intermediate algebraic theorem; it is not itself a border endpoint.
-/
noncomputable section
namespace Sheshadri.DVRSectionLength
open MvPolynomial IsolatedLocalMultiplicity
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

section LocalLengths
variable {σ P K : Type*} [Finite σ] [Fintype P] [Field K]

/-- A literal quotient retaining the full local algebras at distinct isolated
points has dimension at least the sum of their lengths. -/
theorem sum_local_finrank_le (I J : Ideal (MvPolynomial σ K))
    (p : P → σ → K) (hp : Function.Injective p)
    (hI : ∀ i, I ≤ pointIdeal (p i))
    [∀ i, IsArtinianRing (LocalIntersectionRing I (p i) (hI i))]
    [Module.Finite K (MvPolynomial σ K ⧸ J)]
    (hkill : ∀ i q, q ∈ J → localPolynomialMap I (p i) (hI i) q = 0) :
    (∑ i, Module.finrank K (LocalIntersectionRing I (p i) (hI i))) ≤
      Module.finrank K (MvPolynomial σ K ⧸ J) := by
  let Φ := localProductMap (fun _ : P => I) p hI
  have hΦ : Function.Surjective Φ := localProductMap_surjective _ p hI hp
  let ψ : (MvPolynomial σ K ⧸ J) →ₐ[K]
      (∀ i, LocalIntersectionRing I (p i) (hI i)) :=
    Ideal.Quotient.liftₐ J Φ (by
      intro q hq
      funext i
      exact hkill i q hq)
  have hψ : Function.Surjective ψ := by
    intro b
    obtain ⟨q, hq⟩ := hΦ b
    exact ⟨Ideal.Quotient.mk J q, hq⟩
  have h := ψ.toLinearMap.finrank_range_le
  rw [LinearMap.range_eq_top.mpr (show Function.Surjective ψ.toLinearMap from hψ),
    finrank_top] at h
  simpa only [Module.finrank_pi_fintype] using h

 theorem sum_local_length_le (I J : Ideal (MvPolynomial σ K))
    (p : P → σ → K) (hp : Function.Injective p)
    (hI : ∀ i, I ≤ pointIdeal (p i))
    [∀ i, IsArtinianRing (LocalIntersectionRing I (p i) (hI i))]
    [Module.Finite K (MvPolynomial σ K ⧸ J)]
    (hkill : ∀ i q, q ∈ J → localPolynomialMap I (p i) (hI i) q = 0) :
    (∑ i, multiplicity I (p i) (hI i)) ≤
      (Module.finrank K (MvPolynomial σ K ⧸ J) : ℕ∞) := by
  simp_rw [multiplicity_eq_finrank]
  rw [← Nat.cast_sum]
  exact_mod_cast sum_local_finrank_le I J p hp hI hkill

end LocalLengths

section DVR
variable {σ P D L k : Type*} [Finite σ] [Fintype P]
  [CommRing D] [IsDomain D] [IsLocalRing D] [IsPrincipalIdealRing D]
  [Field L] [Algebra D L] [IsFractionRing D L]
  [Field k] [Algebra D k]

/-- The actual generic algebra bounds every preserved special local length.
No finite generation over the DVR is assumed. The residue equations must
actually annihilate the displayed local algebras, and generic finiteness is
an explicit applicability condition to be proved in the geometric assembly. -/
theorem selected_lengths_le_generic
    (hε : Function.Surjective (algebraMap D k))
    (I : Ideal (MvPolynomial σ k)) [Module.Finite k (MvPolynomial σ k ⧸ I)]
    (J : Ideal (MvPolynomial σ L)) [Module.Finite L (MvPolynomial σ L ⧸ J)]
    (p : P → σ → k) (hp : Function.Injective p)
    (hI : ∀ i, I ≤ pointIdeal (p i))
    [∀ i, IsArtinianRing (LocalIntersectionRing I (p i) (hI i))]
    (hIJ : I ≤ GeneralGradedBaseChange.extendedIdeal (K := k)
      (BezoutHorizontalFamily.contractedIdeal (R := D) J))
    (hkill : ∀ i q, q ∈ BezoutHorizontalFamily.contractedIdeal (R := D) J →
      localPolynomialMap I (p i) (hI i) (map (algebraMap D k) q) = 0) :
    (∑ i, multiplicity I (p i) (hI i)) ≤
      (Module.finrank L (MvPolynomial σ L ⧸ J) : ℕ∞) := by
  let T := BezoutHorizontalFamily.contractedIdeal (R := D) J
  let J₀ := GeneralGradedBaseChange.extendedIdeal (K := k) T
  let ψ := BezoutPieceComparison.quotientMap hIJ
  have hψ : Function.Surjective ψ := by
    intro b
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨Ideal.Quotient.mk I q, rfl⟩
  letI : Module.Finite k (MvPolynomial σ k ⧸ J₀) :=
    Module.Finite.of_surjective ψ.toLinearMap hψ
  letI : Module.Finite L (MvPolynomial σ L ⧸
      GeneralGradedBaseChange.extendedIdeal (K := L) T) := by
    dsimp [T]
    rw [BezoutHorizontalFamily.extended_contractedIdeal]
    infer_instance
  have hJ₀ : ∀ i q, q ∈ J₀ → localPolynomialMap I (p i) (hI i) q = 0 := by
    intro i
    have hh : J₀ ≤ RingHom.ker (localPolynomialMap I (p i) (hI i)) := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro q hq
      exact hkill i q hq
    exact fun q hq => hh hq
  have hs := sum_local_length_le I J₀ p hp hI hJ₀
  have hg := DVRFibreDimension.polynomial_quotient_finrank_le_generic D L T k hε
  have hgeneric : GeneralGradedBaseChange.extendedIdeal (K := L) T = J :=
    BezoutHorizontalFamily.extended_contractedIdeal J
  rw [hgeneric] at hg
  exact hs.trans (by exact_mod_cast hg)

end DVR
end Sheshadri.DVRSectionLength
