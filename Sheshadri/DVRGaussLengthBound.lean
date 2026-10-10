/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.DVRSectionLength
import Sheshadri.DVRSaturatedGaussPersistence
import Sheshadri.DeterminantDvrFamilyBasic

/-! # The special Gauss degree is bounded by the actual finite generic section

This applies the proved local persistence and flat fibre inequality to the
literal border family. The generic section is supplied by the subsequent
geometric constructor; this intermediate theorem is not a border endpoint.
-/

noncomputable section
namespace Sheshadri.DVRGaussLengthBound
open MvPolynomial PolynomialModel ConormalGaussSection SmoothGaussSectionLength
open DVRGaussSection
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

variable {n m : ℕ} {D L : Type*} [CommRing D] [IsDomain D]
  [Algebra ℂ D] [Field L] [Algebra ℂ L]

theorem generic_equations_ideal
    (family : DeterminantDvrFamily.Family n m D L)
    (ell : ℕ → Fin n → D) (a : Fin n → D) :
    (Ideal.ofList (equations family.polynomial ell (n-2) a)).map
      (map family.generic.toRingHom) =
    polarChartIdeal (determinant family.pencil) (fun j i => family.generic (ell j i))
      (n-2) (fun i => family.generic (a i)) := by
  rw [Ideal.map_ofList, map_equations, family.generic_eq, equations_ideal]
  rfl

theorem generic_derivative
    (family : DeterminantDvrFamily.Family n m D L) (i : Fin n) :
    map family.generic.toRingHom (pderiv i family.polynomial) =
      pderiv i (determinant family.pencil) := by
  rw [← pderiv_map, family.generic_eq]

theorem family_section_degree_le
    (family : DeterminantDvrFamily.Family n m D L) (s : Section (fermat n) n)
    (ell : ℕ → Fin n → D) (a : Fin n → D)
    (hell : ∀ j i, family.residue (ell j i) = s.ell j i)
    (ha : ∀ i, family.residue (a i) = s.a i) (hn : 2 ≤ n)
    (J : Ideal (MvPolynomial (Fin n) L))
    [Module.Finite L (MvPolynomial (Fin n) L ⧸ J)]
    (hIJ : (Ideal.ofList (equations family.polynomial ell (n-2) a)).map
      (map family.generic.toRingHom) ≤ J)
    (hJI : J ≤ HomogeneousSystemSaturation.saturation
      ((Ideal.ofList (equations family.polynomial ell (n-2) a)).map
        (map family.generic.toRingHom))
      (fun i : Fin n => map family.generic.toRingHom (pderiv i family.polynomial))) :
    fermatCount n ≤ Module.finrank L (MvPolynomial (Fin n) L ⧸ J) := by
  letI : IsDiscreteValuationRing D := family.dvr
  letI : Algebra D L := family.generic.toRingHom.toAlgebra
  letI : IsFractionRing D L := family.isFractionRing
  letI : Algebra D ℂ := family.residue.toRingHom.toAlgebra
  letI : Module.Finite ℂ (PolarChartAlgebra (fermat n) s.ell (n-2) s.a) := s.finite
  letI (p : Fin s.count) := s.artinian p
  obtain ⟨hinc, hkill⟩ := DVRSaturatedGaussPersistence.family_saturated_contraction_preserves
    family s ell a hell ha hn J hIJ hJI
  have hb := DVRSectionLength.selected_lengths_le_generic (D := D) (L := L)
    family.residue_surjective (polarChartIdeal (fermat n) s.ell (n-2) s.a)
    J s.point s.injective s.vanishes hinc hkill
  rw [s.length_sum] at hb
  exact_mod_cast hb

end Sheshadri.DVRGaussLengthBound
