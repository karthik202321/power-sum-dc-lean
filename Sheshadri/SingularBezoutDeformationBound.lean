/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SingularRootPersistence
import Sheshadri.ProjectiveMultiplicityInterpolation
import Sheshadri.BezoutDeformationBound

/-!
# Deformation comparison for actual singular intersection multiplicities

The special fibre retains the full isolated local intersection algebras.
Interpolation onto their product gives a sum-of-lengths lower bound. Flat
homogeneous pieces then compare this with any system of the same multidegrees.
Neither system is required to have a globally zero-dimensional zero locus.
-/

noncomputable section
namespace Sheshadri.SingularBezoutDeformationBound
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open MvPolynomial MultiProjective ProjectivePointInterpolation
open BezoutHorizontalFamily BezoutRootPersistence FlatMultiGradedHilbert
open ProjectiveLocalMultiplicity
open scoped BigOperators

variable {X U V E P : Type*} [Fintype X] [Fintype U] [Fintype V]
  [Fintype E] [Fintype P] [Nonempty X] [Nonempty U] [Nonempty V]

/-- Actual local dimensions, hence local lengths, survive in the comparison
bound. All local preservation and finite interpolation are proved inputs. -/
theorem isolated_multiplicities_le_comparison_piece
    {K : Type*} [Field K] [Algebra (Polynomial ℂ) K] [IsFractionRing (Polynomial ℂ) K]
    (f g : E → MvPolynomial (Variables X U V) ℂ) (degree : E → Degree)
    (points : P → Variables X U V → ℂ) (charts : ∀ p, Chart (points p))
    (hcard : Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
      (Fintype.card V - 1))
    (hf : ∀ e, (f e).IsWeightedHomogeneous (weight X U V) (degree e))
    (hg : ∀ e, (g e).IsWeightedHomogeneous (weight X U V) (degree e))
    (hzero : ∀ p e, eval (points p) (f e) = 0)
    [∀ p, IsArtinianRing (LocalRing f (points p) (charts p) (hzero p))]
    (hdist : ∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q) :
    ∃ N : ℕ, ∀ k, N ≤ k →
      (∑ p, Module.finrank ℂ (LocalRing f (points p) (charts p) (hzero p))) ≤
        Module.finrank ℂ
          (coordinatePiece (weight X U V) (Ideal.span (Set.range g)) (k,k,k)) := by
  classical
  let F (e : E) : MvPolynomial (Variables X U V) (Polynomial ℂ) :=
    coefficientEquiv (interpolation (f e) (g e))
  let I : Ideal (MvPolynomial (Variables X U V) (Polynomial ℂ)) := Ideal.span (Set.range F)
  let IK : Ideal (MvPolynomial (Variables X U V) K) :=
    I.map (MvPolynomial.map (algebraMap (Polynomial ℂ) K))
  let J : Ideal (MvPolynomial (Variables X U V) (Polynomial ℂ)) :=
    contractedIdeal (R := Polynomial ℂ) IK
  let J0 := J.map (MvPolynomial.map (Polynomial.evalRingHom (0 : ℂ)))
  let J1 := J.map (MvPolynomial.map (Polynomial.evalRingHom (1 : ℂ)))
  have hF (e : E) : (F e).IsWeightedHomogeneous (weight X U V) (degree e) :=
    coefficient_interpolation_homogeneous _ _ _ _ (hf e) (hg e)
  have hI : FlatMultiGradedHilbert.IsHomogeneous (weight X U V) I :=
    span_homogeneous _ F degree hF
  have hIK : FlatMultiGradedHilbert.IsHomogeneous (weight X U V) IK :=
    GeneralHomogeneousBaseChange.weightedIdeal_map _ _ I hI
  have hJ : FlatMultiGradedHilbert.IsHomogeneous (weight X U V) J :=
    contractedIdeal_homogeneous _ IK hIK
  have hJ0 : FlatMultiGradedHilbert.IsHomogeneous (weight X U V) J0 :=
    GeneralHomogeneousBaseChange.weightedIdeal_map _ _ J hJ
  have hIJ : I ≤ J := originalIdeal_le_contraction (R := Polynomial ℂ) (K := K) I
  have hkill : ∀ p q, q ∈ J0 → polynomialMap f (points p) (charts p) (hzero p) q = 0 := by
    intro p
    have hle : J0 ≤ RingHom.ker (polynomialMap f (points p) (charts p) (hzero p)) := by
      change J.map (MvPolynomial.map (Polynomial.evalRingHom (0 : ℂ))) ≤ _
      rw [Ideal.map_le_iff_le_comap]
      intro q hq
      exact SingularRootPersistence.original_isolated_root_annihilates_interpolation_contraction
        (K := K) f g (points p) hcard (hzero p) (charts p) q hq
    exact fun q hq => hle hq
  have hgJ1 : Ideal.span (Set.range g) ≤ J1 := by
    apply Ideal.span_le.mpr
    rintro _ ⟨e,rfl⟩
    have hmem := Ideal.mem_map_of_mem (MvPolynomial.map (Polynomial.evalRingHom (1 : ℂ)))
      (hIJ (Ideal.subset_span (Set.mem_range_self e)))
    have heq : MvPolynomial.map (Polynomial.evalRingHom (1 : ℂ)) (F e) = g e := by
      simp [F, BezoutDeformationBound.map_coefficient_interpolation]
    rwa [heq] at hmem
  obtain ⟨N,hN⟩ := ProjectiveMultiplicityInterpolation.eventual_sum_finrank_le_piece
    f points charts hzero J0 hJ0 hkill hdist
  refine ⟨N, fun k hk => ?_⟩
  calc
    (∑ p, Module.finrank ℂ (LocalRing f (points p) (charts p) (hzero p))) ≤
        Module.finrank ℂ (coordinatePiece (weight X U V) J0 (k,k,k)) := hN k hk
    _ = Module.finrank ℂ (coordinatePiece (weight X U V) J1 (k,k,k)) :=
      specialized_dimensions_equal (R := Polynomial ℂ) (K := K) (weight X U V) IK hIK
        (Polynomial.evalRingHom 0) (Polynomial.evalRingHom 1) (k,k,k)
    _ ≤ Module.finrank ℂ
        (coordinatePiece (weight X U V) (Ideal.span (Set.range g)) (k,k,k)) :=
      BezoutPieceComparison.piece_finrank_antitone _ hgJ1 _

end Sheshadri.SingularBezoutDeformationBound
