/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ProjectivePointInterpolation
import Sheshadri.GeneralGradedBaseChange

/-!
# Actual multigraded coordinate fibres over a PID

For an actual homogeneous ideal, each coordinate piece splits off from the
quotient as a module. Tensor base change therefore embeds the piece, and the
explicit polynomial-quotient base-change equivalence carries its image onto
the literal piece of the extended ideal. Over a PID, torsion-freeness gives
equal dimensions at every field fibre, including special and generic fibres.

All results use actual quotient modules. No Hilbert-function or dimension
constancy hypothesis is introduced.
-/

noncomputable section
namespace Sheshadri.FlatMultiGradedHilbert

open MvPolynomial ProjectivePointInterpolation GeneralGradedBaseChange
open scoped TensorProduct

variable {σ R D : Type*} [CommRing R] [AddCommMonoid D]

/-- Stability of the ideal under all weighted homogeneous projections. -/
def IsHomogeneous (w : σ → D) (I : Ideal (MvPolynomial σ R)) : Prop :=
  ∀ d p, p ∈ I → weightedHomogeneousComponent w d p ∈ I

/-- The actual homogeneous projection descends to the quotient and lands
in its literal weighted coordinate piece. -/
def coordinateProjection (w : σ → D) (I : Ideal (MvPolynomial σ R))
    (hI : IsHomogeneous w I) (d : D) :
    (MvPolynomial σ R ⧸ I) →ₗ[R] coordinatePiece w I d := by
  let f : MvPolynomial σ R →ₗ[R] (MvPolynomial σ R ⧸ I) :=
    (Ideal.Quotient.mkₐ R I).toLinearMap.comp (weightedHomogeneousComponent w d)
  let g : MvPolynomial σ R →ₗ[R] coordinatePiece w I d :=
    f.codRestrict _ (fun p => ⟨_, weightedHomogeneousComponent_mem _ p _, rfl⟩)
  exact (I.restrictScalars R).liftQ g (by
    intro p hp
    apply Subtype.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI d p hp))

theorem coordinateProjection_retract (w : σ → D) (I : Ideal (MvPolynomial σ R))
    (hI : IsHomogeneous w I) (d : D) :
    (coordinateProjection w I hI d).comp (coordinatePiece w I d).subtype =
      LinearMap.id := by
  ext x
  obtain ⟨p, hp, hpx⟩ := x.property
  change (coordinateProjection w I hI d x : MvPolynomial σ R ⧸ I) = x
  rw [← hpx]
  change Ideal.Quotient.mk I (weightedHomogeneousComponent w d p) = Ideal.Quotient.mk I p
  rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hp]

theorem coordinate_piece_baseChange_injective
    (w : σ → D) (I : Ideal (MvPolynomial σ R)) (hI : IsHomogeneous w I)
    (K : Type*) [CommRing K] [Algebra R K] (d : D) :
    Function.Injective ((coordinatePiece w I d).subtype.baseChange K) := by
  have h := congrArg (LinearMap.baseChange K) (coordinateProjection_retract w I hI d)
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at h
  have hleft : Function.LeftInverse ((coordinateProjection w I hI d).baseChange K)
      ((coordinatePiece w I d).subtype.baseChange K) := by
    intro x
    exact LinearMap.congr_fun h x
  exact hleft.injective

/-- The concrete image of the tensor coordinate piece inside the fibre algebra. -/
def fibreCoordinatePiece (w : σ → D) (I : Ideal (MvPolynomial σ R))
    (K : Type*) [CommRing K] [Algebra R K] (d : D) :
    Submodule K (K ⊗[R] (MvPolynomial σ R ⧸ I)) :=
  LinearMap.range ((coordinatePiece w I d).subtype.baseChange K)

theorem fibreCoordinatePiece_finrank
    (w : σ → D) (I : Ideal (MvPolynomial σ R)) (hI : IsHomogeneous w I)
    (K : Type*) [Field K] [Algebra R K] (d : D) :
    Module.finrank K (fibreCoordinatePiece w I K d) =
      Module.finrank K (K ⊗[R] coordinatePiece w I d) :=
  LinearMap.finrank_range_of_inj (coordinate_piece_baseChange_injective w I hI K d)

theorem weightedHomogeneous_map {K : Type*} [CommRing K]
    (f : R →+* K) (w : σ → D) (d : D)
    {p : MvPolynomial σ R} (hp : IsWeightedHomogeneous w p d) :
    IsWeightedHomogeneous w (MvPolynomial.map f p) d := by
  intro e he
  apply hp
  intro hz
  apply he
  rw [coeff_map, hz, map_zero]

/-- The scalar-compatible actual quotient equivalence preserves the exact
weighted coordinate pieces, for arbitrary weights and arbitrary base change. -/
theorem map_fibreCoordinatePiece (w : σ → D) (I : Ideal (MvPolynomial σ R))
    (K : Type*) [CommRing K] [Algebra R K] (d : D) :
    (fibreCoordinatePiece w I K d).map (tensorQuotientEquiv I).toLinearMap =
      coordinatePiece w (extendedIdeal (K := K) I) d := by
  classical
  apply le_antisymm
  · rintro y ⟨x, ⟨t, rfl⟩, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simpa only [map_add] using
        (coordinatePiece w (extendedIdeal (K := K) I) d).add_mem hx hy
    | tmul k x =>
      obtain ⟨p, hp, hpx⟩ := x.property
      change tensorQuotientEquiv I (k ⊗ₜ[R] (x : MvPolynomial σ R ⧸ I)) ∈ _
      have hpx' : Ideal.Quotient.mk I p = (x : MvPolynomial σ R ⧸ I) := hpx
      rw [← hpx', tensorQuotientEquiv_tmul_mk]
      exact ⟨_, (weightedHomogeneousSubmodule K w d).smul_mem k
        (weightedHomogeneous_map _ _ _ hp), rfl⟩
  · rintro y ⟨p, hp, rfl⟩
    rw [← p.support_sum_monomial_coeff, map_sum]
    apply Submodule.sum_mem
    intro e he
    have hdegree : Finsupp.weight w e = d := hp (mem_support_iff.mp he)
    let q : MvPolynomial σ R := monomial e 1
    have hq : IsWeightedHomogeneous w q d := isWeightedHomogeneous_monomial _ _ _ hdegree
    let x : coordinatePiece w I d := ⟨Ideal.Quotient.mk I q, q, hq, rfl⟩
    refine ⟨coeff e p ⊗ₜ[R] (x : MvPolynomial σ R ⧸ I), ?_, ?_⟩
    · exact ⟨coeff e p ⊗ₜ[R] x, rfl⟩
    · change tensorQuotientEquiv I (coeff e p ⊗ₜ[R] Ideal.Quotient.mk I q) = _
      simp [tensorQuotientEquiv_tmul_mk, q, smul_monomial]

theorem coordinatePiece_finrank_eq_fibre
    (w : σ → D) (I : Ideal (MvPolynomial σ R))
    (K : Type*) [Field K] [Algebra R K] (d : D) :
    Module.finrank K (coordinatePiece w (extendedIdeal (K := K) I) d) =
      Module.finrank K (fibreCoordinatePiece w I K d) := by
  rw [← map_fibreCoordinatePiece]
  exact LinearEquiv.finrank_eq
    ((tensorQuotientEquiv I).toLinearEquiv.submoduleMap (fibreCoordinatePiece w I K d)).symm

/-- This is the bridge from literal specialized equations to tensor fibre
modules. Homogeneity supplies the required injection. -/
theorem coordinatePiece_finrank_eq_tensor
    (w : σ → D) (I : Ideal (MvPolynomial σ R)) (hI : IsHomogeneous w I)
    (K : Type*) [Field K] [Algebra R K] (d : D) :
    Module.finrank K (coordinatePiece w (extendedIdeal (K := K) I) d) =
      Module.finrank K (K ⊗[R] coordinatePiece w I d) := by
  rw [coordinatePiece_finrank_eq_fibre, fibreCoordinatePiece_finrank w I hI K d]

section PID
variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Over a PID, every finite torsion-free graded piece has the same dimension
in every actual field fibre. -/
theorem literal_fibre_dimensions_equal
    (w : σ → D) (I : Ideal (MvPolynomial σ R)) (hI : IsHomogeneous w I)
    [NoZeroSMulDivisors R (MvPolynomial σ R ⧸ I)]
    (K L : Type*) [Field K] [Field L] [Algebra R K] [Algebra R L]
    (d : D) [Module.Finite R (coordinatePiece w I d)] :
    Module.finrank K (coordinatePiece w (extendedIdeal (K := K) I) d) =
      Module.finrank L (coordinatePiece w (extendedIdeal (K := L) I) d) := by
  rw [coordinatePiece_finrank_eq_tensor w I hI K d,
    coordinatePiece_finrank_eq_tensor w I hI L d]
  exact FlatGradedHilbert.finrank_fibres_equal R (coordinatePiece w I d) K L

/-- Three projective factors: the finiteness needed for fibre conservation
is proved from their actual finite sets of monomials. -/
theorem three_factor_fibre_dimensions_equal
    {X U V : Type*} [Finite X] [Finite U] [Finite V]
    (I : Ideal (MvPolynomial (MultiProjective.Variables X U V) R))
    (hI : IsHomogeneous (MultiProjective.weight X U V) I)
    [NoZeroSMulDivisors R (MvPolynomial (MultiProjective.Variables X U V) R ⧸ I)]
    (K L : Type*) [Field K] [Field L] [Algebra R K] [Algebra R L]
    (a b c : ℕ) :
    Module.finrank K (coordinatePiece (MultiProjective.weight X U V)
      (extendedIdeal (K := K) I) (a, b, c)) =
    Module.finrank L (coordinatePiece (MultiProjective.weight X U V)
      (extendedIdeal (K := L) I) (a, b, c)) :=
  literal_fibre_dimensions_equal (MultiProjective.weight X U V) I hI K L (a, b, c)

end PID
end Sheshadri.FlatMultiGradedHilbert
