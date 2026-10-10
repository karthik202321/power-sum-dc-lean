/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.BezoutHorizontalFamily
import Sheshadri.BezoutPieceComparison
import Sheshadri.BezoutRootPersistence
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Actual excess-tolerant comparison by a polynomial deformation

For any two systems with the same multidegrees, selected simple zeros of the
first system are bounded by high diagonal coordinate pieces of the second.
The interpolation, generic contraction, fibre dimensions and special-root
containment are all constructed and proved. No absence of excess components,
generic transversality or intersection-degree hypothesis is used.
-/

noncomputable section
namespace Sheshadri.BezoutDeformationBound
set_option maxHeartbeats 800000
open MvPolynomial MultiProjective ProjectivePointInterpolation
open BezoutHorizontalFamily BezoutRootPersistence FlatMultiGradedHilbert

variable {X U V E P : Type*} [Fintype X] [Fintype U] [Fintype V]
  [Fintype E] [Fintype P] [Nonempty X] [Nonempty U] [Nonempty V]

theorem map_coefficient_interpolation (f g : MvPolynomial (Variables X U V) ℂ) (a : ℂ) :
    MvPolynomial.map (Polynomial.evalRingHom a) (coefficientEquiv (interpolation f g)) =
      C (1-a) * f + C a * g := by
  rw [coefficientEquiv_interpolation]
  have hc : (Polynomial.evalRingHom a).comp Polynomial.C = RingHom.id ℂ := by
    ext c
    simp
  simp only [map_add, map_mul, map_C,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
  simp only [MvPolynomial.map_map, hc, MvPolynomial.map_id]
  simp

/-- A numerical comparison with an actual second equation ideal, not a
replacement Bézout certificate. Extra components of either system are allowed. -/
theorem simple_roots_le_comparison_piece
    {K : Type*} [Field K] [Algebra (Polynomial ℂ) K] [IsFractionRing (Polynomial ℂ) K]
    (f g : E → MvPolynomial (Variables X U V) ℂ) (degree : E → Degree)
    (points : P → Variables X U V → ℂ)
    (hcard : Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
      (Fintype.card V - 1))
    (hf : ∀ e, (f e).IsWeightedHomogeneous (weight X U V) (degree e))
    (hg : ∀ e, (g e).IsWeightedHomogeneous (weight X U V) (degree e))
    (hzero : ∀ p e, eval (points p) (f e) = 0)
    (hsimple : ∀ p, SimpleInCharts f (points p))
    (hdist : ∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q)
    (k : ℕ) (hk : Fintype.card P - 1 ≤ k) :
    Fintype.card P ≤ Module.finrank ℂ
      (coordinatePiece (weight X U V) (Ideal.span (Set.range g)) (k,k,k)) := by
  classical
  let F (e : E) : MvPolynomial (Variables X U V) (Polynomial ℂ) :=
    coefficientEquiv (interpolation (f e) (g e))
  let I : Ideal (MvPolynomial (Variables X U V) (Polynomial ℂ)) := Ideal.span (Set.range F)
  let IK : Ideal (MvPolynomial (Variables X U V) K) :=
    I.map (MvPolynomial.map (algebraMap (Polynomial ℂ) K))
  let J : Ideal (MvPolynomial (Variables X U V) (Polynomial ℂ)) := contractedIdeal (R := Polynomial ℂ) IK
  let J0 := J.map (MvPolynomial.map (Polynomial.evalRingHom (0 : ℂ)))
  let J1 := J.map (MvPolynomial.map (Polynomial.evalRingHom (1 : ℂ)))
  have hF (e : E) : (F e).IsWeightedHomogeneous (weight X U V) (degree e) :=
    coefficient_interpolation_homogeneous _ _ _ _ (hf e) (hg e)
  have hI : FlatMultiGradedHilbert.IsHomogeneous (weight X U V) I :=
    span_homogeneous _ F degree hF
  have hIK : FlatMultiGradedHilbert.IsHomogeneous (weight X U V) IK :=
    GeneralHomogeneousBaseChange.weightedIdeal_map _ _ I hI
  have hIJ : I ≤ J := originalIdeal_le_contraction (R := Polynomial ℂ) (K := K) I
  have hJ0 : ∀ p q, q ∈ J0 → eval (points p) q = 0 := by
    intro p
    have hle : J0 ≤ RingHom.ker (eval (points p)) := by
      change J.map (MvPolynomial.map (Polynomial.evalRingHom (0 : ℂ))) ≤ _
      rw [Ideal.map_le_iff_le_comap]
      intro q hq
      have hv := original_simple_root_annihilates_interpolation_contraction (K := K)
        f g (points p) hcard (hzero p) (hsimple p) q hq
      change eval (points p) (MvPolynomial.map (Polynomial.evalRingHom 0) q) = 0
      simpa only [eval_map] using hv
    exact fun q hq => hle hq
  have hgJ1 : Ideal.span (Set.range g) ≤ J1 := by
    apply Ideal.span_le.mpr
    rintro _ ⟨e,rfl⟩
    have hmem := Ideal.mem_map_of_mem (MvPolynomial.map (Polynomial.evalRingHom (1 : ℂ)))
      (hIJ (Ideal.subset_span (Set.mem_range_self e)))
    have heq : MvPolynomial.map (Polynomial.evalRingHom (1 : ℂ)) (F e) = g e := by
      simp [F, map_coefficient_interpolation]
    rwa [heq] at hmem
  have hdim : Module.finrank ℂ (coordinatePiece (weight X U V) J0 (k,k,k)) =
      Module.finrank ℂ (coordinatePiece (weight X U V) J1 (k,k,k)) :=
    specialized_dimensions_equal (R := Polynomial ℂ) (K := K) (weight X U V) IK hIK
      (Polynomial.evalRingHom 0) (Polynomial.evalRingHom 1) (k,k,k)
  have hn (p : P) : HasNonzeroBlocks (points p) := by
    obtain ⟨ix,iu,iv,hx,hu,hv,_⟩ := hsimple p
    exact ⟨⟨ix,hx⟩,⟨iu,hu⟩,⟨iv,hv⟩⟩
  calc
    Fintype.card P ≤ Module.finrank ℂ (coordinatePiece (weight X U V) J0 (k,k,k)) :=
      card_le_three_factor_piece_finrank J0 points hn hdist hJ0 k hk
    _ = Module.finrank ℂ (coordinatePiece (weight X U V) J1 (k,k,k)) := hdim
    _ ≤ Module.finrank ℂ (coordinatePiece (weight X U V)
        (Ideal.span (Set.range g)) (k,k,k)) :=
      BezoutPieceComparison.piece_finrank_antitone _ hgJ1 _

end Sheshadri.BezoutDeformationBound
