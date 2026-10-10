/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.DVRGaussSection
import Sheshadri.DVRSaturatedPersistence

/-! # Actual border Gauss sections survive generic gradient saturation

Applied to the actual family polynomial and a constructed special Gauss
section, saturation by the generic derivative opens preserves every selected
special local algebra. Both flag families may vary while retaining their
specified residues. No degree, length, or persistence certificate is assumed.
-/

noncomputable section
namespace Sheshadri.DVRSaturatedGaussPersistence
open MvPolynomial PolynomialModel ConormalGaussSection SmoothGaussSectionLength
open DVRGaussSection DVRRootPersistence BezoutHorizontalFamily GeneralGradedBaseChange
open IsolatedLocalMultiplicity
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

section General
variable {n d : ℕ} {D L : Type*} [CommRing D] [IsDomain D]
  [Algebra ℂ D] [IsDiscreteValuationRing D]
  [Field L] [Algebra D L] [IsFractionRing D L]

/-- The actual special Gauss ideal is contained in the specialized
contraction, and every contracted equation annihilates each full local ring. -/
theorem section_saturated_contraction_preserves
    {f : MvPolynomial (Fin n) ℂ}
    (ε : D →ₐ[ℂ] ℂ) (π : D) (hπ : Irreducible π)
    (hker : RingHom.ker ε = Ideal.span {π})
    (F : MvPolynomial (Fin n) D) (hF : map ε.toRingHom F = f)
    (s : Section f d) (ell : ℕ → Fin n → D) (a : Fin n → D)
    (hell : ∀ j i, ε (ell j i) = s.ell j i) (ha : ∀ i, ε (a i) = s.a i)
    (hn : 2 ≤ n) (J : Ideal (MvPolynomial (Fin n) L))
    (hIJ : extendedIdeal (K := L) (Ideal.ofList (equations F ell (n-2) a)) ≤ J)
    (hJI : J ≤ HomogeneousSystemSaturation.saturation
      (extendedIdeal (K := L) (Ideal.ofList (equations F ell (n-2) a)))
      (fun i : Fin n => map (algebraMap D L) (pderiv i F))) :
    polarChartIdeal f s.ell (n-2) s.a ≤
      (contractedIdeal (R := D) J).map (map ε.toRingHom) ∧
    ∀ p q, q ∈ contractedIdeal (R := D) J →
      localPolynomialMap (polarChartIdeal f s.ell (n-2) s.a)
        (s.point p) (s.vanishes p) (map ε.toRingHom q) = 0 := by
  have hε : Function.Surjective ε.toRingHom := fun c =>
    ⟨algebraMap ℂ D c, ε.commutes c⟩
  have hsp := equations_specialIdeal ε F hF s ell a hell ha
  constructor
  · have h : Ideal.ofList (equations F ell (n-2) a) ≤ contractedIdeal (R := D) J :=
      (originalIdeal_le_contraction (K := L) _).trans (Ideal.comap_mono hIJ)
    have hm := Ideal.map_mono (f := map ε.toRingHom) h
    rw [Ideal.map_ofList] at hm
    exact hsp ▸ hm
  · intro p q hq
    have hz : ∀ r ∈ equations F ell (n-2) a,
        eval (s.point p) (specialize ε.toRingHom r) = 0 := by
      intro r hr
      apply s.vanishes p
      rw [← hsp]
      exact Ideal.subset_span (List.mem_map.mpr ⟨r, hr, rfl⟩)
    letI : IsArtinianRing (LocalIntersectionRing
        (specialIdeal ε.toRingHom (equations F ell (n-2) a)) (s.point p)
        (specialIdeal_le_pointIdeal ε.toRingHom _ _ hz)) := by
      letI := s.artinian p
      exact SingularRootPersistence.local_artinian_of_ideal_eq _ _ (s.point p) _
        (s.vanishes p) hsp
    obtain ⟨i, hi⟩ := s.smooth p
    have hgi : eval (s.point p) (specialize ε.toRingHom (pderiv i F)) ≠ 0 := by
      simpa only [specialize, ← pderiv_map, hF] using hi
    have hzq := DVRSaturatedPersistence.family_saturated_contraction_annihilates_local
      ε.toRingHom hε π hπ hker (equations F ell (n-2) a) (s.point p)
      (by simp only [equations_length, Fintype.card_fin]; omega) hz
      (fun i => pderiv i F) J hJI i hgi q hq
    exact SingularRootPersistence.local_map_zero_of_ideal_eq _ _ (s.point p) _
      (s.vanishes p) hsp _ hzq

/-- Applied ideal equality at every selected Gauss point, including all
nonreduced local structure. -/
theorem section_saturated_contraction_local_eq
    {f : MvPolynomial (Fin n) ℂ}
    (ε : D →ₐ[ℂ] ℂ) (π : D) (hπ : Irreducible π)
    (hker : RingHom.ker ε = Ideal.span {π})
    (F : MvPolynomial (Fin n) D) (hF : map ε.toRingHom F = f)
    (s : Section f d) (ell : ℕ → Fin n → D) (a : Fin n → D)
    (hell : ∀ j i, ε (ell j i) = s.ell j i) (ha : ∀ i, ε (a i) = s.a i)
    (hn : 2 ≤ n) (J : Ideal (MvPolynomial (Fin n) L))
    (hIJ : extendedIdeal (K := L) (Ideal.ofList (equations F ell (n-2) a)) ≤ J)
    (hJI : J ≤ HomogeneousSystemSaturation.saturation
      (extendedIdeal (K := L) (Ideal.ofList (equations F ell (n-2) a)))
      (fun i : Fin n => map (algebraMap D L) (pderiv i F))) (p : Fin s.count) :
    ((contractedIdeal (R := D) J).map (map ε.toRingHom)).map
      (algebraMap _ (CoordinatePowerRegular.PointLocalRing (s.point p))) =
    (polarChartIdeal f s.ell (n-2) s.a).map
      (algebraMap _ (CoordinatePowerRegular.PointLocalRing (s.point p))) := by
  obtain ⟨hinc, hkill⟩ := section_saturated_contraction_preserves
    ε π hπ hker F hF s ell a hell ha hn J hIJ hJI
  apply le_antisymm
  · rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro q hq
    change algebraMap _ (CoordinatePowerRegular.PointLocalRing (s.point p))
      (map ε.toRingHom q) ∈ (polarChartIdeal f s.ell (n-2) s.a).map
        (algebraMap _ (CoordinatePowerRegular.PointLocalRing (s.point p)))
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (SingularSpecialFiber.localEquationQuotientEquiv _ (s.point p) (s.vanishes p)).injective
    rw [map_zero, SingularSpecialFiber.localEquationQuotientEquiv_mk]
    exact hkill p q hq
  · exact Ideal.map_mono hinc

end General

section ActualFamily
variable {n m : ℕ} {D L : Type*} [CommRing D] [IsDomain D]
  [Algebra ℂ D] [Field L] [Algebra ℂ L]

/-- Actual-family version. The DVR, residue map, and fraction-field
structure are obtained from the constructed border family itself. -/
theorem family_saturated_contraction_preserves
    (family : DeterminantDvrFamily.Family n m D L) (s : Section (fermat n) n)
    (ell : ℕ → Fin n → D) (a : Fin n → D)
    (hell : ∀ j i, family.residue (ell j i) = s.ell j i)
    (ha : ∀ i, family.residue (a i) = s.a i) (hn : 2 ≤ n)
    (J : Ideal (MvPolynomial (Fin n) L))
    (hIJ : (Ideal.ofList (equations family.polynomial ell (n-2) a)).map
      (map family.generic.toRingHom) ≤ J)
    (hJI : J ≤ HomogeneousSystemSaturation.saturation
      ((Ideal.ofList (equations family.polynomial ell (n-2) a)).map
        (map family.generic.toRingHom))
      (fun i : Fin n => map family.generic.toRingHom (pderiv i family.polynomial))) :
    polarChartIdeal (fermat n) s.ell (n-2) s.a ≤
      (J.comap (map family.generic.toRingHom)).map (map family.residue.toRingHom) ∧
    ∀ p q, q ∈ J.comap (map family.generic.toRingHom) →
      localPolynomialMap (polarChartIdeal (fermat n) s.ell (n-2) s.a)
        (s.point p) (s.vanishes p) (map family.residue.toRingHom q) = 0 := by
  letI : IsDiscreteValuationRing D := family.dvr
  letI : Algebra D L := family.generic.toRingHom.toAlgebra
  letI : IsFractionRing D L := family.isFractionRing
  exact section_saturated_contraction_preserves family.residue family.uniformizer
    family.uniformizer_irreducible family.residue_kernel family.polynomial family.special_eq
    s ell a hell ha hn J hIJ hJI

end ActualFamily
end Sheshadri.DVRSaturatedGaussPersistence
