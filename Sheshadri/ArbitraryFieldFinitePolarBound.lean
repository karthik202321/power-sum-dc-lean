/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldFinitePolarBound
import Sheshadri.GeneralGradedBaseChange
import Sheshadri.HomogeneousSystemSaturation
import Sheshadri.GaussSectionSmoothLocalization
import Sheshadri.DVRGaussSection
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Finite saturated polar bounds over the actual generic coefficient field

Scalar extension to the algebraic closure preserves the full quotient
dimension. A unit derivative combination forces every geometric support
point to be smooth, and the actual saturation sandwich identifies the local
equation rings. Neither algebraic closure of the original field nor a
geometric counting hypothesis is required.
-/

noncomputable section
namespace Sheshadri.ArbitraryFieldFinitePolarBound
open MvPolynomial Incidence PolynomialModel SmoothGaussSectionLength
open IsolatedLocalMultiplicity GeneralGradedBaseChange HomogeneousSystemSaturation
open GaussSectionSmoothLocalization SmoothGaussPolars
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

section BaseChange
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [CharZero K] [CharZero L] {n : ℕ}

theorem map_polarChartIdeal (f : MvPolynomial (Fin n) K)
    (ell : ℕ → Fin n → K) (r : ℕ) (a : Fin n → K) :
    extendedIdeal (K := L) (polarChartIdeal f ell r a) =
      polarChartIdeal (map (algebraMap K L) f)
        (fun j i => algebraMap K L (ell j i)) r (fun i => algebraMap K L (a i)) := by
  rw [← DVRGaussSection.equations_ideal, extendedIdeal, Ideal.map_ofList,
    DVRGaussSection.map_equations, DVRGaussSection.equations_ideal]

theorem quotient_finite_baseChange (J : Ideal (MvPolynomial (Fin n) K))
    [Module.Finite K (EquationQuotient J)] :
    Module.Finite L (EquationQuotient (extendedIdeal (K := L) J)) := by
  exact Module.Finite.equiv (tensorQuotientEquiv (K := L) J).toLinearEquiv

theorem quotient_finrank_baseChange (J : Ideal (MvPolynomial (Fin n) K)) :
    Module.finrank L (EquationQuotient (extendedIdeal (K := L) J)) =
      Module.finrank K (EquationQuotient J) := by
  rw [← (tensorQuotientEquiv (K := L) J).toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange

theorem unit_combination_baseChange (J : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin n) K) (b : Fin n → K)
    (hb : IsUnit (Ideal.Quotient.mk J (derivativeCombination f b))) :
    IsUnit (Ideal.Quotient.mk (extendedIdeal (K := L) J)
      (derivativeCombination (map (algebraMap K L) f) (fun i => algebraMap K L (b i)))) := by
  have hh := hb.map (quotientCoefficientMap (K := L) J).toRingHom
  change IsUnit (quotientCoefficientMap (K := L) J
    (Ideal.Quotient.mk J (derivativeCombination f b))) at hh
  simpa only [quotientCoefficientMap_mk, map_derivativeCombination] using hh

end BaseChange

section Local
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

theorem smooth_of_quotient_unit (J : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin n) K) (b : Fin n → K)
    (hb : IsUnit (Ideal.Quotient.mk J (derivativeCombination f b)))
    (x : Fin n → K) (hx : J ≤ pointIdeal x) :
    ∃ i, eval x (pderiv i f) ≠ 0 := by
  apply smooth_of_combination_ne_zero f b x
  exact (hb.map (Ideal.Quotient.lift J (eval x) hx)).ne_zero

theorem local_eq_of_saturation_sandwich
    (I J : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin n) K)
    (hIJ : I ≤ J) (hJI : J ≤ saturation I (fun i => pderiv i f))
    (x : Fin n → K) (hsmooth : ∃ i, eval x (pderiv i f) ≠ 0) :
    J.map (algebraMap _ (CoordinatePowerRegular.PointLocalRing x)) =
      I.map (algebraMap _ (CoordinatePowerRegular.PointLocalRing x)) := by
  obtain ⟨i, hi⟩ := hsmooth
  apply le_antisymm _ (Ideal.map_mono hIJ)
  have hu : IsUnit (algebraMap _ (CoordinatePowerRegular.PointLocalRing x) (pderiv i f)) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff _ (CoordinatePowerRegular.pointIdeal x) _).mpr hi
  exact (Ideal.map_mono hJI).trans_eq
    (map_saturation_eq_of_unit I (fun j => pderiv j f) _ i hu)

end Local

section Bound
variable {K : Type*} [Field K] [CharZero K] {n m : ℕ}

/-- The literal finite saturated ordinary polar quotient over any
characteristic-zero field satisfies the proved incidence bound. -/
theorem ordinary_finite_saturated_polar_bound (hn : 2 ≤ n) (hm : 0 < m)
    (A : PencilCoefficients n m K) (ell : ℕ → Fin n → K) (a : Fin n → K)
    (J : Ideal (MvPolynomial (Fin n) K)) [Module.Finite K (EquationQuotient J)]
    (hIJ : polarChartIdeal (determinant A) ell (n-2) a ≤ J)
    (hJI : J ≤ saturation (polarChartIdeal (determinant A) ell (n-2) a)
      (fun i => pderiv i (determinant A)))
    (b : Fin n → K)
    (hb : IsUnit (Ideal.Quotient.mk J (derivativeCombination (determinant A) b))) :
    Module.finrank K (EquationQuotient J) ≤ ordinaryBezout m n := by
  let L := AlgebraicClosure K
  let A' : PencilCoefficients n m L := fun i j k => algebraMap K L (A i j k)
  let ell' : ℕ → Fin n → L := fun j i => algebraMap K L (ell j i)
  let a' : Fin n → L := fun i => algebraMap K L (a i)
  let J' := extendedIdeal (K := L) J
  let I' := polarChartIdeal (determinant A') ell' (n-2) a'
  have he : extendedIdeal (K := L) (polarChartIdeal (determinant A) ell (n-2) a) = I' := by
    rw [map_polarChartIdeal, ZariskiBridge.map_determinant]
  letI : Module.Finite L (EquationQuotient J') := quotient_finite_baseChange J
  have hI'J' : I' ≤ J' := he ▸ Ideal.map_mono hIJ
  have hJ'I' : J' ≤ saturation I' (fun i => pderiv i (determinant A')) := by
    have hh := (Ideal.map_mono (f := map (algebraMap K L)) hJI).trans
      (map_saturation_le _ _ (map (algebraMap K L)))
    simpa only [← pderiv_map, ZariskiBridge.map_determinant, ← he] using hh
  have hu : IsUnit (Ideal.Quotient.mk J'
      (derivativeCombination (determinant A') (fun i => algebraMap K L (b i)))) := by
    simpa only [ZariskiBridge.map_determinant] using
      unit_combination_baseChange (L := L) J (determinant A) b hb
  have hs (x) (hx : J' ≤ pointIdeal x) :=
    smooth_of_quotient_unit J' (determinant A') _ hu x hx
  have hh := FieldFinitePolarBound.ordinary_finite_local_polar_bound hn hm A' ell' a'
    J' hI'J' (fun x hx => local_eq_of_saturation_sandwich I' J' (determinant A')
      hI'J' hJ'I' x (hs x hx)) hs
  rwa [quotient_finrank_baseChange J] at hh

/-- The symmetric bound over the actual generic field, with every
geometric support point and its nonreduced local length constructed. -/
theorem symmetric_finite_saturated_polar_bound (hn : 2 ≤ n) (hm : 0 < m)
    (A : PencilCoefficients n m K) (hA : ∀ i, (A i).transpose = A i)
    (ell : ℕ → Fin n → K) (a : Fin n → K)
    (J : Ideal (MvPolynomial (Fin n) K)) [Module.Finite K (EquationQuotient J)]
    (hIJ : polarChartIdeal (determinant A) ell (n-2) a ≤ J)
    (hJI : J ≤ saturation (polarChartIdeal (determinant A) ell (n-2) a)
      (fun i => pderiv i (determinant A)))
    (b : Fin n → K)
    (hb : IsUnit (Ideal.Quotient.mk J (derivativeCombination (determinant A) b))) :
    Module.finrank K (EquationQuotient J) ≤ symmetricBezout m n := by
  let L := AlgebraicClosure K
  let A' : PencilCoefficients n m L := fun i j k => algebraMap K L (A i j k)
  let ell' : ℕ → Fin n → L := fun j i => algebraMap K L (ell j i)
  let a' : Fin n → L := fun i => algebraMap K L (a i)
  let J' := extendedIdeal (K := L) J
  let I' := polarChartIdeal (determinant A') ell' (n-2) a'
  have hA' (i) : (A' i).transpose = A' i := by
    ext j k
    exact congrArg (algebraMap K L) (congrFun (congrFun (hA i) j) k)
  have he : extendedIdeal (K := L) (polarChartIdeal (determinant A) ell (n-2) a) = I' := by
    rw [map_polarChartIdeal, ZariskiBridge.map_determinant]
  letI : Module.Finite L (EquationQuotient J') := quotient_finite_baseChange J
  have hI'J' : I' ≤ J' := he ▸ Ideal.map_mono hIJ
  have hJ'I' : J' ≤ saturation I' (fun i => pderiv i (determinant A')) := by
    have hh := (Ideal.map_mono (f := map (algebraMap K L)) hJI).trans
      (map_saturation_le _ _ (map (algebraMap K L)))
    simpa only [← pderiv_map, ZariskiBridge.map_determinant, ← he] using hh
  have hu : IsUnit (Ideal.Quotient.mk J'
      (derivativeCombination (determinant A') (fun i => algebraMap K L (b i)))) := by
    simpa only [ZariskiBridge.map_determinant] using
      unit_combination_baseChange (L := L) J (determinant A) b hb
  have hs (x) (hx : J' ≤ pointIdeal x) :=
    smooth_of_quotient_unit J' (determinant A') _ hu x hx
  have hh := FieldFinitePolarBound.symmetric_finite_local_polar_bound hn hm A' hA' ell' a'
    J' hI'J' (fun x hx => local_eq_of_saturation_sandwich I' J' (determinant A')
      hI'J' hJ'I' x (hs x hx)) hs
  rwa [quotient_finrank_baseChange J] at hh

end Bound

end Sheshadri.ArbitraryFieldFinitePolarBound
