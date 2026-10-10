/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FinitePrescribedGaussSection
import Sheshadri.DeterminantDvrHomogeneous
import Sheshadri.DeterminantDvrFamilyBasic
import Sheshadri.DehomogeneousGaussSection
import Sheshadri.HomogeneousDehomogenization
import Sheshadri.ConormalGaussSection

/-!
# A finite generic Gauss section of the actual determinant boundary family

Starting with the constructed special Fermat section, this theorem chooses
flags over the actual DVR with exactly those residues. It constructs the
generic affine section ideal, proves it finite, identifies it with the
derivative saturation of the literal polar equations, and produces a unit
gradient combination on its full scheme. No generic flags, finiteness,
smoothness, or local multiplicity preservation are assumed here.
-/

noncomputable section
namespace Sheshadri.ActualGenericGaussSection
open MvPolynomial PolynomialModel DeterminantDvrFamily DeterminantDvrHomogeneous
open HomogeneousSystemSaturation HomogeneousDeterminant HomogeneousQuotientExact
open RegularFlagsWithResidue SmoothGaussSectionLength

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

variable {n m : ℕ} {D L : Type*} [CommRing D] [IsDomain D]
  [Algebra ℂ D] [Field L] [Algebra ℂ L]

def polarEquationIdeal (family : Family n m D L)
    (ell : ℕ → Fin n → D) (a : Fin n → D) : Ideal (MvPolynomial (Fin n) L) :=
  polarChartIdeal (determinant family.pencil) (fun j i => family.generic (ell j i))
    (n-2) (fun i => family.generic (a i))

/-- This constructor applies all genericity and dimension theorems to the
literal DVR family. The only section input is the already constructed
special section, whose coefficients are retained exactly. -/
theorem exists_actual_section (family : Family n m D L) (hn : 2 ≤ n)
    (s : ConormalGaussSection.Section (fermat n) n) :
    ∃ (ell : ℕ → Fin n → D) (a : Fin n → D)
      (J : Ideal (MvPolynomial (Fin n) L)) (c : Fin n → L),
      (∀ j i, family.residue (ell j i) = s.ell j i) ∧
      (∀ i, family.residue (a i) = s.a i) ∧
      Module.Finite L (MvPolynomial (Fin n) L ⧸ J) ∧
      polarEquationIdeal family ell a ≤ J ∧
      J ≤ saturation (polarEquationIdeal family ell a)
        (fun i => pderiv i (determinant family.pencil)) ∧
      IsUnit (Ideal.Quotient.mk J
        (∑ i, MvPolynomial.C (c i) * pderiv i (determinant family.pencil))) ∧
      J = saturation (polarEquationIdeal family ell a)
        (fun i => pderiv i (determinant family.pencil)) := by
  classical
  letI := family.dvr
  letI := family.residue_isLocalHom
  let F := homogeneousPolynomial family
  let I : Ideal (MvPolynomial (Fin (n+1)) L) := Ideal.span {map family.generic.toRingHom F}
  let fs : Fin n → MvPolynomial (Fin (n+1)) D := fun i => pderiv i.succ F
  let d := homogeneousDegree family - 1
  have hfs (i : Fin n) : (fs i).IsHomogeneous d :=
    (homogeneousPolynomial_homogeneous family).pderiv
  have hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I := by
    have h := enlargedIdeal_homogeneous (⊥ : Ideal (MvPolynomial (Fin (n+1)) L))
      (fun k p hp => by simpa only [Ideal.mem_bot.mp hp, map_zero] using
        (Ideal.zero_mem (⊥ : Ideal (MvPolynomial (Fin (n+1)) L))))
      (map family.generic.toRingHom F) (generic_homogeneous family)
    simpa only [enlargedIdeal, bot_sup_eq] using h
  obtain ⟨P, hPdeg, N, hP⟩ := generic_hypersurface_hilbert family (by omega)
  obtain ⟨ell, a, hell, ha, hfinite, c, hunit⟩ :=
    FinitePrescribedGaussSection.exists_finite_section family.generic family.residue
      family.uniformizer family.uniformizer_generic_ne_zero family.uniformizer_residue
      I hI fs d hfs (fun j i => algebraMap ℂ D (s.ell j i))
      (fun i => algebraMap ℂ D (s.a i)) (n-2) P (N+1)
      (fun k hk => hP k (by omega)) (by omega)
  let S := FinitePrescribedGaussSection.sectionIdeal family.generic I fs ell a (n-2)
  let J : Ideal (MvPolynomial (Fin n) L) := S.map dehom.toRingHom
  have hraw : (DehomogeneousGaussSection.rawIdeal family.generic.toRingHom F ell (n-2) a).map
      dehom.toRingHom = polarEquationIdeal family ell a := by
    rw [DehomogeneousGaussSection.rawIdeal_map_dehom]
    rw [show dehom (map family.generic.toRingHom F) = determinant family.pencil from
      generic_dehom family, DVRGaussSection.equations_ideal]
    rfl
  have hbetween : polarEquationIdeal family ell a ≤ J := by
    rw [← hraw]
    exact Ideal.map_mono (le_saturation _ _)
  have hbound : J ≤ saturation (polarEquationIdeal family ell a)
      (fun i => pderiv i (determinant family.pencil)) := by
    have h := DehomogeneousGaussSection.saturated_rawIdeal_map_le
      family.generic.toRingHom F ell (n-2) a
    rw [show dehom (map family.generic.toRingHom F) = determinant family.pencil from
      generic_dehom family, DVRGaussSection.equations_ideal] at h
    exact h
  letI : Module.Finite L
      (MvPolynomial (Fin (n+1)) L ⧸ (S ⊔ Ideal.span {X 0 - 1})) := hfinite
  have hJfinite : Module.Finite L (MvPolynomial (Fin n) L ⧸ J) :=
    Module.Finite.of_surjective (HomogeneousDehomogenization.chartEquiv S).toLinearMap
      (HomogeneousDehomogenization.chartEquiv S).surjective
  have hu : IsUnit (Ideal.Quotient.mk J
      (∑ i, MvPolynomial.C (c i) * pderiv i (determinant family.pencil))) := by
    have h := hunit.map (HomogeneousDehomogenization.chartEquiv S)
    change IsUnit (Ideal.Quotient.mk J
      (dehom (∑ i, MvPolynomial.C (c i) * map family.generic.toRingHom (fs i)))) at h
    simpa only [map_sum, map_mul, dehom_C, fs, F, generic_pderiv_dehom] using h
  refine ⟨ell, a, J, c, ?_, ?_, hJfinite, hbetween, hbound, hu, ?_⟩
  · intro j i
    exact (hell j i).trans (family.residue.commutes _)
  · intro i
    exact (ha i).trans (family.residue.commutes _)
  · apply eq_saturation_of_unit_span (polarEquationIdeal family ell a) J
      (fun i => pderiv i (determinant family.pencil)) hbetween hbound _ hu
    rw [map_sum]
    apply Ideal.sum_mem
    intro i hi
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

end Sheshadri.ActualGenericGaussSection
