/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.HomogeneousPolynomialLift
import Sheshadri.DVRGaussSection
import Sheshadri.PrescribedResidueGaussSequence

/-!
# Dehomogenizing the actual Gauss section and its open saturation

All identities concern literal equation ideals. The saturation comparison
only claims the direction proved by mapping its power-membership witnesses;
it does not postulate that arbitrary base change commutes with saturation.
-/

noncomputable section
namespace Sheshadri.DehomogeneousGaussSection
open MvPolynomial HomogeneousDeterminant HomogeneousPolynomialLift
open HomogeneousQuotientExact GenericHomogeneousSections
open HomogeneousSystemSaturation PrescribedResidueGaussSequence
open RegularFlagsWithResidue

section Maps
variable {A B E : Type*} [CommRing A] [CommRing B]

theorem map_saturation_le (I : Ideal A) (fs : E → A) (φ : A →+* B) :
    (saturation I fs).map φ ≤ saturation (I.map φ) (fun i => φ (fs i)) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro q hq i
  obtain ⟨d, hd⟩ := hq i
  refine ⟨d, ?_⟩
  simpa only [map_mul, map_pow] using Ideal.mem_map_of_mem φ hd

end Maps

section Polynomials
variable {R K : Type*} [CommRing R] [IsLocalRing R] [Field K] {n : ℕ}

omit [IsLocalRing R] in
theorem dehom_map_derivativeCombination (φ : R →+* K)
    (F : MvPolynomial (Fin (n+1)) R) (ell : Fin n → R) :
    dehom (map φ (linearCombination (fun i : Fin n => pderiv i.succ F) ell)) =
      DVRGaussSection.relativePolar (dehom (map φ F)) (fun i => φ (ell i)) := by
  simp only [linearCombination, DVRGaussSection.relativePolar, map_sum, map_mul,
    MvPolynomial.map_C, dehom_C, ← pderiv_map, dehom_pderiv_succ]

theorem dehom_map_primal (φ : R →+* K) (a : Fin n → R) :
    dehom (map φ (primalPolynomial a)) = DVRGaussSection.relativeLinear (fun i => φ (a i)) - 1 := by
  rw [primalPolynomial_eq]
  simp only [map_sub, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
    dehom_C, dehom_X_succ, dehom_X_zero, DVRGaussSection.relativeLinear]

theorem map_idealSequence_dehom (I : Ideal (MvPolynomial (Fin (n+1)) K))
    (g : ℕ → MvPolynomial (Fin (n+1)) K) (r : ℕ) :
    (idealSequence I g r).map dehom.toRingHom =
      idealSequence (I.map dehom.toRingHom) (fun j => dehom (g j)) r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simpa only [idealSequence, enlargedIdeal, Ideal.map_sup, Ideal.map_span,
      Set.image_singleton] using congrArg (fun J => J ⊔ Ideal.span {dehom (g r)}) ih

theorem list_idealSequence (f : MvPolynomial (Fin n) K)
    (g : ℕ → MvPolynomial (Fin n) K) (r : ℕ) :
    Ideal.ofList (f :: (List.range r).map g) = idealSequence (Ideal.span {f}) g r := by
  induction r with
  | zero => simp [idealSequence, Ideal.ofList_singleton]
  | succ r ih =>
    rw [List.range_succ, List.map_append]
    change Ideal.ofList ((f :: (List.range r).map g) ++ [g r]) = _
    rw [Ideal.ofList_append, ih, Ideal.ofList_singleton]
    rfl

def rawIdeal (φ : R →+* K) (F : MvPolynomial (Fin (n+1)) R)
    (ell : ℕ → Fin n → R) (r : ℕ) (a : Fin n → R) : Ideal (MvPolynomial (Fin (n+1)) K) :=
  idealSequence (Ideal.span {map φ F})
    (fun j => map φ (linearCombination (fun i : Fin n => pderiv i.succ F) (ell j))) r ⊔
      Ideal.span {map φ (primalPolynomial a)}

/-- The dehomogenized homogeneous cuts are exactly the original affine
equations, including the final normalized primal hyperplane. -/
theorem rawIdeal_map_dehom (φ : R →+* K) (F : MvPolynomial (Fin (n+1)) R)
    (ell : ℕ → Fin n → R) (r : ℕ) (a : Fin n → R) :
    (rawIdeal φ F ell r a).map dehom.toRingHom =
      Ideal.ofList (DVRGaussSection.equations (dehom (map φ F))
        (fun j i => φ (ell j i)) r (fun i => φ (a i))) := by
  simp only [rawIdeal, Ideal.map_sup, map_idealSequence_dehom, Ideal.map_span,
    Set.image_singleton]
  change idealSequence (Ideal.span {dehom (map φ F)})
      (fun j => dehom (map φ (linearCombination (fun i : Fin n => pderiv i.succ F) (ell j)))) r ⊔
      Ideal.span {dehom (map φ (primalPolynomial a))} = _
  simp_rw [dehom_map_derivativeCombination, dehom_map_primal]
  rw [DVRGaussSection.equations, Ideal.ofList_append, list_idealSequence,
    Ideal.ofList_singleton]

/-- Mapping the open-saturated homogeneous ideal only adds equations that
vanish on the actual affine smooth open. -/
theorem saturated_rawIdeal_map_le (φ : R →+* K) (F : MvPolynomial (Fin (n+1)) R)
    (ell : ℕ → Fin n → R) (r : ℕ) (a : Fin n → R) :
    (saturation (rawIdeal φ F ell r a)
      (fun i : Fin n => X 0 * map φ (pderiv i.succ F))).map dehom.toRingHom ≤
      saturation
        (Ideal.ofList (DVRGaussSection.equations (dehom (map φ F))
          (fun j i => φ (ell j i)) r (fun i => φ (a i))))
        (fun i : Fin n => pderiv i (dehom (map φ F))) := by
  have h := map_saturation_le (rawIdeal φ F ell r a)
    (fun i : Fin n => X 0 * map φ (pderiv i.succ F)) dehom.toRingHom
  rw [rawIdeal_map_dehom] at h
  convert h using 1
  congr 1
  funext i
  change pderiv i (dehom (map φ F)) = dehom (X 0 * map φ (pderiv i.succ F))
  rw [map_mul, dehom_X_zero, one_mul, ← pderiv_map, dehom_pderiv_succ]

end Polynomials
end Sheshadri.DehomogeneousGaussSection
