/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ActualGaussBaseChange
import Sheshadri.ActualGaussHilbert

/-! # Graded compatibility of the actual Gauss-family base change -/

noncomputable section
namespace Sheshadri.GradedGaussBaseChange

set_option maxHeartbeats 800000

open MvPolynomial ActualGaussFamily ActualGaussFlatness
open ActualGaussBaseChange ActualGaussCoefficientRing ActualGaussHilbert
open FlatGradedHilbert
open scoped TensorProduct

variable {Z : Type} [Fintype Z]

def residueSpecialEquiv (c : ℂ) : Residue c ≃ₐ[Polynomial ℂ] SpecialField c :=
  { residueEquivComplex c with
    commutes' := fun p => Polynomial.quotientSpanXSubCAlgEquiv_mk c p }

theorem fibreTensorEquiv_mk_tmul_mk
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ)
    (p : MvPolynomial (TotalCoordinates Unit Z) ℂ) (r : Polynomial ℂ) :
    fibreTensorEquiv F U c
      (Ideal.Quotient.mk (totalIdeal F U) p ⊗ₜ[Polynomial ℂ]
        Ideal.Quotient.mk (basePointIdeal c) r) =
      Ideal.Quotient.mk (fibreIdeal F U (fun _ => c))
        (specialize (fun _ : Unit => c) (baseMap r * p)) := by
  simp only [fibreTensorEquiv, RingEquiv.trans_apply,
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  rfl

def tensorFibreRingEquiv
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ) :
    (SpecialField c ⊗[Polynomial ℂ] CoefficientRing F U) ≃+*
      FibreCoordinateRing F U (fun _ => c) :=
  (Algebra.TensorProduct.congr (residueSpecialEquiv c).symm (quotientEquiv F U).symm).toRingEquiv
    |>.trans (Algebra.TensorProduct.comm (Polynomial ℂ) (Residue c) (CoordinateRing F U)).toRingEquiv
    |>.trans (fibreTensorEquiv F U c)

theorem specialize_baseMap (c : ℂ) (r : Polynomial ℂ) :
    specialize (Z := Z) (fun _ : Unit => c) (baseMap r) = C (r.eval c) := by
  induction r using Polynomial.induction_on' with
  | add r s hr hs => simp only [map_add, hr, hs, Polynomial.eval_add]
  | monomial k d =>
    simp [baseMap, specialize, Polynomial.eval₂_monomial, Polynomial.eval_monomial]

theorem specialize_coefficientEquiv_symm
    (c : ℂ) (p : MvPolynomial (SpatialVariables Z) (Polynomial ℂ)) :
    specialize (fun _ : Unit => c) (coefficientAlgEquiv.symm p) =
      MvPolynomial.map (Polynomial.evalRingHom c) p := by
  have he : (specialize (Z := Z) (fun _ : Unit => c)).comp coefficientAlgEquiv.symm.toRingHom =
      MvPolynomial.map (Polynomial.evalRingHom c) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change specialize (fun _ : Unit => c) (coefficientAlgEquiv.symm (C r)) = _
      have hh : coefficientAlgEquiv.symm (C r) = baseMap (Z := Z) r :=
        coefficientAlgEquiv.symm_apply_eq.mpr (coefficientEquiv_baseMap r).symm
      rw [hh, specialize_baseMap]
      simp
    · intro i
      have hh : coefficientAlgEquiv.symm (X i) = X (Sum.inr i) :=
        coefficientAlgEquiv.symm_apply_eq.mpr (coefficientEquiv_spatial i).symm
      change specialize (fun _ : Unit => c) (coefficientAlgEquiv.symm (X i)) = _
      rw [hh]
      simp [specialize]
  exact RingHom.congr_fun he p

theorem tensorFibreRingEquiv_tmul_mk
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ)
    (k : SpecialField c) (p : MvPolynomial (SpatialVariables Z) (Polynomial ℂ)) :
    tensorFibreRingEquiv F U c (k ⊗ₜ[Polynomial ℂ] Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk (fibreIdeal F U (fun _ => c))
        (C (k : ℂ) * MvPolynomial.map (Polynomial.evalRingHom c) p) := by
  have hk : (residueSpecialEquiv c).symm k =
      Ideal.Quotient.mk (basePointIdeal c) (Polynomial.C (k : ℂ)) :=
    Polynomial.quotientSpanXSubCAlgEquiv_symm_apply c k
  change fibreTensorEquiv F U c
    ((quotientEquiv F U).symm (Ideal.Quotient.mk _ p) ⊗ₜ[Polynomial ℂ]
      (residueSpecialEquiv c).symm k) = _
  rw [hk]
  change fibreTensorEquiv F U c
    (Ideal.Quotient.mk _ (coefficientAlgEquiv.symm p) ⊗ₜ[Polynomial ℂ]
      Ideal.Quotient.mk _ (Polynomial.C (k : ℂ))) = _
  rw [fibreTensorEquiv_mk_tmul_mk, map_mul, specialize_baseMap,
    specialize_coefficientEquiv_symm]
  simp only [Polynomial.eval_C]
  rfl

instance specialFieldComplexAlgebra (c : ℂ) : Algebra (SpecialField c) ℂ :=
  inferInstanceAs (Algebra ℂ ℂ)

def tensorFibreAlgEquiv
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ) :
    (SpecialField c ⊗[Polynomial ℂ] CoefficientRing F U) ≃ₐ[SpecialField c]
      FibreCoordinateRing F U (fun _ => c) :=
  { tensorFibreRingEquiv F U c with
    commutes' := by
      intro k
      change tensorFibreRingEquiv F U c (k ⊗ₜ[Polynomial ℂ] (1 : CoefficientRing F U)) = _
      rw [← map_one (Ideal.Quotient.mk (coefficientIdeal F U)), tensorFibreRingEquiv_tmul_mk]
      simp only [map_one, mul_one]
      rfl }

theorem weightedHomogeneous_map {σ R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (w : σ → ℕ × ℕ) (d : ℕ × ℕ)
    {p : MvPolynomial σ R} (hp : p.IsWeightedHomogeneous w d) :
    (MvPolynomial.map f p).IsWeightedHomogeneous w d := by
  intro e he
  apply hp
  intro hz
  apply he
  rw [coeff_map, hz, map_zero]

theorem map_eval_map_C (c : ℂ) (p : MvPolynomial (SpatialVariables Z) ℂ) :
    MvPolynomial.map (Polynomial.evalRingHom c) (MvPolynomial.map Polynomial.C p) = p := by
  rw [map_map]
  have he : (Polynomial.evalRingHom c).comp Polynomial.C = RingHom.id ℂ := by
    ext z
    simp
  rw [he, map_id]

/-- The literal bidegree module in the quotient by the specialized equations. -/
def specializedPiece
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ) (a b : ℕ) :
    Submodule (SpecialField c) (FibreCoordinateRing F U (fun _ => c)) :=
  bicoordinatePiece (SpatialVariables Z) ℂ ActualGaussHilbert.spatialBlock
    (fibreIdeal F U (fun _ => c)) a b

theorem tensorFibreAlgEquiv_tmul_mk
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ)
    (k : SpecialField c) (p : MvPolynomial (SpatialVariables Z) (Polynomial ℂ)) :
    tensorFibreAlgEquiv F U c (k ⊗ₜ[Polynomial ℂ] Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk (fibreIdeal F U (fun _ => c))
        ((k : ℂ) • MvPolynomial.map (Polynomial.evalRingHom c) p) := by
  rw [show (k : ℂ) • MvPolynomial.map (Polynomial.evalRingHom c) p =
      C (k : ℂ) * MvPolynomial.map (Polynomial.evalRingHom c) p from C_mul'.symm]
  exact tensorFibreRingEquiv_tmul_mk F U c k p

/-- The actual scalar-compatible base-change equivalence preserves exactly
the two graded coordinate pieces. No equality of dimensions is assumed. -/
theorem map_gaussFibrePiece
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ) (a b : ℕ) :
    (gaussFibrePiece F U (SpecialField c) a b).map
      (tensorFibreAlgEquiv F U c).toLinearMap = specializedPiece F U c a b := by
  apply le_antisymm
  · rintro y ⟨x, ⟨t, rfl⟩, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      simpa only [map_add] using (specializedPiece F U c a b).add_mem hx hy
    | tmul k x =>
      obtain ⟨p, hp, hpx⟩ := x.property
      change tensorFibreAlgEquiv F U c (k ⊗ₜ[Polynomial ℂ] (x : CoefficientRing F U)) ∈ _
      have hpx' : Ideal.Quotient.mk (coefficientIdeal F U) p = (x : CoefficientRing F U) := hpx
      rw [← hpx', tensorFibreAlgEquiv_tmul_mk]
      exact ⟨_, (weightedHomogeneousSubmodule ℂ
        (twoBlockWeight (SpatialVariables Z) ActualGaussHilbert.spatialBlock) (a, b)).smul_mem
          (k : ℂ) (weightedHomogeneous_map _ _ _ hp), rfl⟩
  · rintro y ⟨p, hp, rfl⟩
    let q : MvPolynomial (SpatialVariables Z) (Polynomial ℂ) := MvPolynomial.map Polynomial.C p
    have hq : q.IsWeightedHomogeneous
        (twoBlockWeight (SpatialVariables Z) ActualGaussHilbert.spatialBlock) (a, b) :=
      weightedHomogeneous_map _ _ _ hp
    let x : gaussCoordinatePiece F U a b := ⟨Ideal.Quotient.mk _ q, q, hq, rfl⟩
    refine ⟨1 ⊗ₜ[Polynomial ℂ] (x : CoefficientRing F U), ?_, ?_⟩
    · exact ⟨1 ⊗ₜ[Polynomial ℂ] x, rfl⟩
    · change tensorFibreAlgEquiv F U c (1 ⊗ₜ[Polynomial ℂ] Ideal.Quotient.mk _ q) = _
      rw [tensorFibreAlgEquiv_tmul_mk, one_smul, map_eval_map_C]
      rfl

theorem specializedPiece_finrank_eq_specialHilbertValue
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (c : ℂ) (a b : ℕ) :
    Module.finrank (SpecialField c) (specializedPiece F U c a b) =
      specialHilbertValue F U c a b := by
  rw [← map_gaussFibrePiece]
  exact LinearEquiv.finrank_eq
    ((tensorFibreAlgEquiv F U c).toLinearEquiv.submoduleMap
      (gaussFibrePiece F U (SpecialField c) a b)).symm

theorem specializedPiece_dimensions_constant
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U)
    (c c' : ℂ) (a b : ℕ) :
    Module.finrank (SpecialField c) (specializedPiece F U c a b) =
      Module.finrank (SpecialField c') (specializedPiece F U c' a b) := by
  rw [specializedPiece_finrank_eq_specialHilbertValue,
    specializedPiece_finrank_eq_specialHilbertValue]
  exact actual_gauss_specialHilbertValue_constant F U hU c c' a b

/-- Comparison with any field fibre, including the fraction field of the
base. The special side is the literal specialized polynomial quotient. -/
theorem specializedPiece_finrank_eq_fieldFibre
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U)
    (c : ℂ) (K : Type*) [Field K] [Algebra (Polynomial ℂ) K] (a b : ℕ) :
    Module.finrank (SpecialField c) (specializedPiece F U c a b) =
      Module.finrank K (gaussFibrePiece F U K a b) := by
  rw [specializedPiece_finrank_eq_specialHilbertValue]
  exact actual_gauss_fibre_dimensions_constant F U hU (SpecialField c) K a b

end Sheshadri.GradedGaussBaseChange
