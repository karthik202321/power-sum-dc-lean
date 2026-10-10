/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldPolarMultiplicityBound
import Sheshadri.FiniteQuotientPointFamily

/-! # Numerical incidence bounds for a literal finite generic polar algebra

All points and local multiplicities are recovered from the actual finite
polar quotient. Algebraic closure is needed only to realize its residue fields
as rational coordinates. The determinant polynomial may be nonhomogeneous.
-/

noncomputable section
namespace Sheshadri.FieldFinitePolarBound
open MvPolynomial Incidence PolynomialModel SmoothGaussSectionLength
open IsolatedLocalMultiplicity FieldPolarMultiplicityBound
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n m : ℕ}

/-- Universal finite-quotient conversion used below with the proved ordinary
and symmetric local multiplicity bounds. It constructs all residue points. -/
private theorem finrank_le_of_local_bound (I : Ideal (MvPolynomial (Fin n) K))
    [Module.Finite K (EquationQuotient I)] (B : ℕ)
    (hbound : ∀ (N : ℕ) (points : Fin N → Fin n → K),
      Function.Injective points → ∀ hp : ∀ p, I ≤ pointIdeal (points p),
      (∀ p, IsArtinianRing (LocalIntersectionRing I (points p) (hp p))) →
      (∑ p, multiplicity I (points p) (hp p)) ≤ (B : ℕ∞)) :
    Module.finrank K (EquationQuotient I) ≤ B := by
  classical
  let Q := EquationQuotient I
  letI : IsArtinianRing Q := IsArtinianRing.of_finite K Q
  letI := Fintype.ofFinite (MaximalSpectrum Q)
  let e := Fintype.equivFin (MaximalSpectrum Q)
  let points := fun p => FiniteQuotientPointFamily.point I (e.symm p)
  have hp (p) : I ≤ pointIdeal (points p) :=
    FiniteQuotientPointFamily.point_vanishes I (e.symm p)
  have hinj : Function.Injective points :=
    (FiniteQuotientPointFamily.point_injective I).comp e.symm.injective
  have hart (p) : IsArtinianRing (LocalIntersectionRing I (points p) (hp p)) :=
    FiniteQuotientPointFamily.point_local_artinian I (e.symm p)
  have hb := hbound (Fintype.card (MaximalSpectrum Q)) points hinj hp hart
  have hsum : (∑ p, multiplicity I (points p) (hp p)) =
      (Module.finrank K Q : ℕ∞) := by
    rw [FiniteQuotientPointFamily.finrank_eq_sum_point_multiplicity I]
    exact e.symm.sum_comp (fun P => multiplicity I
      (FiniteQuotientPointFamily.point I P) (FiniteQuotientPointFamily.point_vanishes I P))
  rw [hsum] at hb
  exact_mod_cast hb

/-- The full finite ordinary polar quotient has dimension bounded by the
ordinary incidence coefficient, with no supplied count or point family. -/
theorem ordinary_finite_polar_bound (hn : 2 ≤ n) (hm : 0 < m)
    (A : PencilCoefficients n m K) (ell : ℕ → Fin n → K) (a : Fin n → K)
    [Module.Finite K (PolarChartAlgebra (determinant A) ell (n-2) a)]
    (hsmooth : ∀ x, polarChartIdeal (determinant A) ell (n-2) a ≤ pointIdeal x →
      ∃ i, eval x (pderiv i (determinant A)) ≠ 0) :
    Module.finrank K (PolarChartAlgebra (determinant A) ell (n-2) a) ≤
      ordinaryBezout m n := by
  apply finrank_le_of_local_bound (polarChartIdeal (determinant A) ell (n-2) a)
  intro N points hinj hp hart
  letI := hart
  exact ordinary_polar_multiplicity_bound hn hm A ell a points hinj hp
    (fun p => hsmooth (points p) (hp p))

/-- Symmetric counterpart for the literal finite polar algebra. -/
theorem symmetric_finite_polar_bound (hn : 2 ≤ n) (hm : 0 < m)
    (A : PencilCoefficients n m K) (hA : ∀ i, (A i).transpose = A i)
    (ell : ℕ → Fin n → K) (a : Fin n → K)
    [Module.Finite K (PolarChartAlgebra (determinant A) ell (n-2) a)]
    (hsmooth : ∀ x, polarChartIdeal (determinant A) ell (n-2) a ≤ pointIdeal x →
      ∃ i, eval x (pderiv i (determinant A)) ≠ 0) :
    Module.finrank K (PolarChartAlgebra (determinant A) ell (n-2) a) ≤
      symmetricBezout m n := by
  apply finrank_le_of_local_bound (polarChartIdeal (determinant A) ell (n-2) a)
  intro N points hinj hp hart
  letI := hart
  exact symmetric_polar_multiplicity_bound hn hm A hA ell a points hinj hp
    (fun p => hsmooth (points p) (hp p))


/-- Equality of the actual localized equation ideals identifies their full
local rings. The equality may come from saturation on a smooth open. -/
def localEquivOfLocalizedIdealEq
    (I J : Ideal (MvPolynomial (Fin n) K)) (x : Fin n → K)
    (hI : I ≤ pointIdeal x) (hJ : J ≤ pointIdeal x)
    (he : J.map (algebraMap _ (CoordinatePowerRegular.PointLocalRing x)) =
      I.map (algebraMap _ (CoordinatePowerRegular.PointLocalRing x))) :
    LocalIntersectionRing J x hJ ≃+* LocalIntersectionRing I x hI :=
  (SingularSpecialFiber.localEquationQuotientEquiv J x hJ).symm.trans
    ((Ideal.quotEquivOfEq he).trans (SingularSpecialFiber.localEquationQuotientEquiv I x hI))

/-- A finite equation quotient that agrees locally with the literal polar
section at its smooth support obeys the ordinary incidence bound. The full
unsaturated polar section may have arbitrary excess components elsewhere. -/
theorem ordinary_finite_local_polar_bound (hn : 2 ≤ n) (hm : 0 < m)
    (A : PencilCoefficients n m K) (ell : ℕ → Fin n → K) (a : Fin n → K)
    (J : Ideal (MvPolynomial (Fin n) K)) [Module.Finite K (EquationQuotient J)]
    (hIJ : polarChartIdeal (determinant A) ell (n-2) a ≤ J)
    (hlocal : ∀ x, J ≤ pointIdeal x →
      J.map (algebraMap _ (CoordinatePowerRegular.PointLocalRing x)) =
        (polarChartIdeal (determinant A) ell (n-2) a).map
          (algebraMap _ (CoordinatePowerRegular.PointLocalRing x)))
    (hsmooth : ∀ x, J ≤ pointIdeal x → ∃ i, eval x (pderiv i (determinant A)) ≠ 0) :
    Module.finrank K (EquationQuotient J) ≤ ordinaryBezout m n := by
  apply finrank_le_of_local_bound J
  intro N points hinj hp hart
  letI := hart
  let I := polarChartIdeal (determinant A) ell (n-2) a
  have hI (p) : I ≤ pointIdeal (points p) := le_trans hIJ (hp p)
  let e (p) := localEquivOfLocalizedIdealEq I J (points p) (hI p) (hp p)
    (hlocal (points p) (hp p))
  letI (p : Fin N) : IsArtinianRing (LocalIntersectionRing I (points p) (hI p)) :=
    (e p).isArtinianRing
  have hb := ordinary_polar_multiplicity_bound hn hm A ell a points hinj hI
    (fun p => hsmooth (points p) (hp p))
  calc
    (∑ p, multiplicity J (points p) (hp p)) =
        ∑ p, multiplicity I (points p) (hI p) := by
      apply Finset.sum_congr rfl
      intro p _
      exact ProjectiveCycleLengths.ringEquiv_length (e p)
    _ ≤ _ := hb

/-- The corresponding symmetric finite smooth-support quotient bound. -/
theorem symmetric_finite_local_polar_bound (hn : 2 ≤ n) (hm : 0 < m)
    (A : PencilCoefficients n m K) (hA : ∀ i, (A i).transpose = A i)
    (ell : ℕ → Fin n → K) (a : Fin n → K)
    (J : Ideal (MvPolynomial (Fin n) K)) [Module.Finite K (EquationQuotient J)]
    (hIJ : polarChartIdeal (determinant A) ell (n-2) a ≤ J)
    (hlocal : ∀ x, J ≤ pointIdeal x →
      J.map (algebraMap _ (CoordinatePowerRegular.PointLocalRing x)) =
        (polarChartIdeal (determinant A) ell (n-2) a).map
          (algebraMap _ (CoordinatePowerRegular.PointLocalRing x)))
    (hsmooth : ∀ x, J ≤ pointIdeal x → ∃ i, eval x (pderiv i (determinant A)) ≠ 0) :
    Module.finrank K (EquationQuotient J) ≤ symmetricBezout m n := by
  apply finrank_le_of_local_bound J
  intro N points hinj hp hart
  letI := hart
  let I := polarChartIdeal (determinant A) ell (n-2) a
  have hI (p) : I ≤ pointIdeal (points p) := le_trans hIJ (hp p)
  let e (p) := localEquivOfLocalizedIdealEq I J (points p) (hI p) (hp p)
    (hlocal (points p) (hp p))
  letI (p : Fin N) : IsArtinianRing (LocalIntersectionRing I (points p) (hI p)) :=
    (e p).isArtinianRing
  have hb := symmetric_polar_multiplicity_bound hn hm A hA ell a points hinj hI
    (fun p => hsmooth (points p) (hp p))
  calc
    (∑ p, multiplicity J (points p) (hp p)) =
        ∑ p, multiplicity I (points p) (hI p) := by
      apply Finset.sum_congr rfl
      intro p _
      exact ProjectiveCycleLengths.ringEquiv_length (e p)
    _ ≤ _ := hb

end Sheshadri.FieldFinitePolarBound
