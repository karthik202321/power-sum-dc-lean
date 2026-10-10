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
import Sheshadri.SingularDeformation
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Generic contraction preserves a local quotient with a regular parameter

Every nonzero scalar polynomial is a power of the local parameter times a
unit. Thus regularity of the parameter in the ORIGINAL local equation
quotient forces all generic-contraction equations to vanish there. This
preserves nilpotents as well as support. Deriving parameter regularity from
mere isolatedness of a square polynomial system is a separate obligation.
-/

noncomputable section
namespace Sheshadri.SingularLocalContraction
set_option maxSynthPendingDepth 3

section LocalParameter
variable {k A : Type*} [Field k] [CommRing A] [IsLocalRing A]

theorem eval₂_isUnit_of_constant_ne_zero (μ : k →+* A) (t : A)
    (ht : t ∈ IsLocalRing.maximalIdeal A) (q : Polynomial k) (hq : q.coeff 0 ≠ 0) :
    IsUnit (q.eval₂ μ t) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  rw [Polynomial.hom_eval₂, (IsLocalRing.residue_eq_zero_iff t).mpr ht,
    Polynomial.eval₂_at_zero]
  exact fun h => hq (((IsLocalRing.residue A).comp μ).injective
    (h.trans (map_zero _).symm))

/-- Nonzero parameter denominators cannot kill elements of the local
quotient when its parameter itself is a nonzerodivisor. -/
theorem eval₂_isLeftRegular (μ : k →+* A) (t : A)
    (ht : t ∈ IsLocalRing.maximalIdeal A) (hreg : IsLeftRegular t)
    (q : Polynomial k) (hq : q ≠ 0) : IsLeftRegular (q.eval₂ μ t) := by
  obtain ⟨u, hu, hunit⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq 0
  have hu0 : u.coeff 0 ≠ 0 := by
    simpa only [Polynomial.C_0, sub_zero, Polynomial.X_dvd_iff] using hunit
  rw [hu, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_C, map_zero, sub_zero]
  exact (hreg.pow _).mul (eval₂_isUnit_of_constant_ne_zero μ t ht u hu0).isRegular.left

end LocalParameter

section Contraction
open MvPolynomial BezoutHorizontalFamily GeneralGradedBaseChange
variable {k K σ A : Type*} [Field k] [Field K] [Algebra (Polynomial k) K]
    [IsFractionRing (Polynomial k) K] [CommRing A] [IsLocalRing A]

omit [IsLocalRing A] in
theorem map_coefficient_polynomial (g : MvPolynomial σ (Polynomial k) →+* A)
    (q : Polynomial k) :
    g (C q) = q.eval₂ ((g.comp C).comp Polynomial.C) (g (C Polynomial.X)) := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => simp only [map_add, Polynomial.eval₂_add, hq, hr]
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow]
    simp

/-- Actual contracted equations vanish in the original local quotient.
The input is a concrete map annihilating the original ideal, together with
regularity of its actual parameter; no preservation-of-length premise. -/
theorem contractedIdeal_le_ker
    (I : Ideal (MvPolynomial σ (Polynomial k)))
    (g : MvPolynomial σ (Polynomial k) →+* A)
    (hI : I ≤ RingHom.ker g)
    (ht : g (C Polynomial.X) ∈ IsLocalRing.maximalIdeal A)
    (hreg : IsLeftRegular (g (C Polynomial.X))) :
    contractedIdeal (R := Polynomial k) (extendedIdeal (K := K) I) ≤ RingHom.ker g := by
  intro p hp
  obtain ⟨q, hq, hqp⟩ := (mem_contracted_extension_iff (K := K) I p).mp hp
  have he : g (C q) * g p = 0 := by
    simpa only [RingHom.mem_ker, map_mul] using hI hqp
  have hqr : IsLeftRegular (g (C q)) := by
    rw [map_coefficient_polynomial]
    exact eval₂_isLeftRegular _ _ ht hreg q hq
  exact hqr.mul_left_eq_zero_iff.mp he

/-- In any local target, extension of the generic contraction equals the
original equation ideal as soon as the parameter is regular in the original
quotient. In particular this retains its entire scheme structure. -/
theorem map_contractedIdeal_eq
    (I : Ideal (MvPolynomial σ (Polynomial k)))
    (φ : MvPolynomial σ (Polynomial k) →+* A)
    (hproper : I.map φ ≠ ⊤)
    (ht : φ (C Polynomial.X) ∈ IsLocalRing.maximalIdeal A)
    (hreg : IsSMulRegular (A ⧸ I.map φ) (φ (C Polynomial.X))) :
    (contractedIdeal (R := Polynomial k) (extendedIdeal (K := K) I)).map φ = I.map φ := by
  let Q := A ⧸ I.map φ
  letI : Nontrivial Q := Ideal.Quotient.nontrivial hproper
  letI : IsLocalRing Q := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (I.map φ)) Ideal.Quotient.mk_surjective
  letI : IsLocalHom (Ideal.Quotient.mk (I.map φ)) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let g : MvPolynomial σ (Polynomial k) →+* Q :=
    (Ideal.Quotient.mk (I.map φ)).comp φ
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    have hkernel : I ≤ RingHom.ker g := by
      intro p hp
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ hp)
    have htq : g (C Polynomial.X) ∈ IsLocalRing.maximalIdeal Q :=
      map_nonunit (Ideal.Quotient.mk (I.map φ)) _ ht
    have hrq : IsLeftRegular (g (C Polynomial.X)) := hreg
    intro p hp
    change φ p ∈ I.map φ
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact contractedIdeal_le_ker (K := K) I g hkernel htq hrq hp
  · exact Ideal.map_mono (originalIdeal_le_contraction I)

/-- At a prime of the special fibre, generic contraction has exactly the
same localized ideal whenever the deformation parameter is regular in the
localized original quotient. No reducedness of that quotient is required. -/
theorem localization_contractedIdeal_eq
    (I P : Ideal (MvPolynomial σ (Polynomial k))) [P.IsPrime]
    (hIP : I ≤ P) (ht : C Polynomial.X ∈ P)
    (hreg : IsSMulRegular
      ((Localization.AtPrime P) ⧸ (I.map
        (algebraMap (MvPolynomial σ (Polynomial k)) (Localization.AtPrime P))))
      ((algebraMap (MvPolynomial σ (Polynomial k)) (Localization.AtPrime P))
        (C Polynomial.X))) :
    (contractedIdeal (R := Polynomial k) (extendedIdeal (K := K) I)).map
      (algebraMap _ (Localization.AtPrime P)) =
        I.map (algebraMap _ (Localization.AtPrime P)) := by
  apply map_contractedIdeal_eq I (algebraMap _ (Localization.AtPrime P))
  · have hle := Ideal.map_mono (f := algebraMap _ (Localization.AtPrime P)) hIP
    rw [Localization.AtPrime.map_eq_maximalIdeal] at hle
    exact ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) hle
  · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P _).mpr ht
  · exact hreg

/-- The preceding ideal equality follows from regularity of the actual
special-fibre equations, using permutation of local regular sequences. -/
theorem map_contractedIdeal_eq_of_special_regular [IsNoetherianRing A]
    (fs : List (MvPolynomial σ (Polynomial k)))
    (φ : MvPolynomial σ (Polynomial k) →+* A)
    (hproper : (Ideal.ofList fs).map φ ≠ ⊤)
    (ht : φ (C Polynomial.X) ∈ IsLocalRing.maximalIdeal A)
    (htreg : IsSMulRegular A (φ (C Polynomial.X)))
    (hf : RingTheory.Sequence.IsRegular
      (A ⧸ Ideal.span {φ (C Polynomial.X)}) (fs.map φ)) :
    (contractedIdeal (R := Polynomial k)
      (extendedIdeal (K := K) (Ideal.ofList fs))).map φ = (Ideal.ofList fs).map φ := by
  apply map_contractedIdeal_eq (Ideal.ofList fs) φ hproper ht
  rw [Ideal.map_ofList]
  exact SingularDeformation.parameter_regular_on_equation_quotient _ _ htreg hf

/-- The actual polynomial deformation parameter is regular in its ambient
local ring, without an additional regularity hypothesis. -/
theorem localization_parameter_regular
    (P : Ideal (MvPolynomial σ (Polynomial k))) [P.IsPrime] :
    IsSMulRegular (Localization.AtPrime P)
      ((algebraMap (MvPolynomial σ (Polynomial k)) (Localization.AtPrime P))
        (C Polynomial.X)) := by
  apply IsLeftRegular.isSMulRegular
  apply (isRegular_of_ne_zero ?_).left
  apply fun h => (show (C Polynomial.X : MvPolynomial σ (Polynomial k)) ≠ 0 from
    by simp) ((IsLocalization.injective (Localization.AtPrime P)
      P.primeCompl_le_nonZeroDivisors) (h.trans (map_zero _).symm))

/-- Concrete localization wrapper: the only remaining regular-sequence
input concerns the original special equations. Ambient parameter regularity
and properness of the localized equation ideal are proved here. -/
theorem localization_contractedIdeal_eq_of_special_regular [Finite σ]
    (fs : List (MvPolynomial σ (Polynomial k)))
    (P : Ideal (MvPolynomial σ (Polynomial k))) [P.IsPrime]
    (hIP : Ideal.ofList fs ≤ P) (ht : C Polynomial.X ∈ P)
    (hf : RingTheory.Sequence.IsRegular
      ((Localization.AtPrime P) ⧸ Ideal.span {
        (algebraMap (MvPolynomial σ (Polynomial k)) (Localization.AtPrime P))
          (C Polynomial.X)})
      (fs.map (algebraMap (MvPolynomial σ (Polynomial k)) (Localization.AtPrime P)))) :
    (contractedIdeal (R := Polynomial k)
      (extendedIdeal (K := K) (Ideal.ofList fs))).map
        (algebraMap _ (Localization.AtPrime P)) =
      (Ideal.ofList fs).map (algebraMap _ (Localization.AtPrime P)) := by
  letI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  apply map_contractedIdeal_eq_of_special_regular fs
    (algebraMap _ (Localization.AtPrime P))
  · have hle := Ideal.map_mono (f := algebraMap _ (Localization.AtPrime P)) hIP
    rw [Localization.AtPrime.map_eq_maximalIdeal] at hle
    exact ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) hle
  · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P _).mpr ht
  · exact localization_parameter_regular P
  · exact hf

end Contraction
end Sheshadri.SingularLocalContraction
