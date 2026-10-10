/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldSymmetricIncidenceLocalMultiplicity
import Sheshadri.FieldConormalPolarIdeal

/-!
# Actual isolated Gauss-polar multiplicities for arbitrary represented polynomials

The coefficient field has characteristic zero and may be a generic fraction
field. The represented polynomial need not be homogeneous. Only the selected
polar-section roots must be smooth on the hypersurface and isolated in the
literal polar section. Kernel lifts, one common reduction, incidence chart
isomorphisms, and the numerical Bézout bounds are proved constructions.
-/

noncomputable section
namespace Sheshadri.FieldPolarMultiplicityBound
open MvPolynomial Matrix Incidence PolynomialModel
open SmoothGaussPolars SmoothGaussDegree SmoothGaussSection SmoothGaussSectionLength
open IsolatedLocalMultiplicity FieldExactKernelLifts FieldConormalPolarIdeal
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

variable {K : Type*} [Field K] [CharZero K] {n m : ℕ}

private theorem chart_root (f : MvPolynomial (Fin n) K) (ell : ℕ → Fin n → K)
    (a x : Fin n → K) (hx : polarChartIdeal f ell (n-2) a ≤ pointIdeal x) :
    eval x f = 0 :=
  hx ((show polarIdeal f ell (n-2) ≤ polarChartIdeal f ell (n-2) a from le_sup_left)
    ((polarIdeal_le_iff f ell (n-2) _).mp le_rfl).1)

private theorem chart_polar (f : MvPolynomial (Fin n) K) (ell : ℕ → Fin n → K)
    (a x : Fin n → K) (hx : polarChartIdeal f ell (n-2) a ≤ pointIdeal x)
    (t : Fin (n-2)) : eval x (polar f (ell t)) = 0 :=
  hx ((show polarIdeal f ell (n-2) ≤ polarChartIdeal f ell (n-2) a from le_sup_left)
    (((polarIdeal_le_iff f ell (n-2) _).mp le_rfl).2 t t.isLt))

private theorem chart_primal (f : MvPolynomial (Fin n) K) (ell : ℕ → Fin n → K)
    (a x : Fin n → K) (hx : polarChartIdeal f ell (n-2) a ≤ pointIdeal x) :
    ∑ i, a i * x i = 1 := by
  have h : linearPolynomial a - 1 ∈ polarChartIdeal f ell (n-2) a :=
    (show Ideal.span {linearPolynomial a - 1} ≤ polarChartIdeal f ell (n-2) a
      from le_sup_right) (Ideal.subset_span (Set.mem_singleton _))
  have he : eval x (linearPolynomial a - 1) = 0 := hx h
  simpa only [map_sub, map_one, eval_linearPolynomial, sub_eq_zero] using he

private def localEquivOfIdealEq {Z : Type*}
    (I J : Ideal (MvPolynomial Z K)) (he : I = J) (p : Z → K)
    (hI : I ≤ pointIdeal p) (hJ : J ≤ pointIdeal p) :
    LocalIntersectionRing I p hI ≃+* LocalIntersectionRing J p hJ := by
  subst J
  exact RingEquiv.refl _

private theorem primal_equation (a x : Fin n → K) (hx : ∑ i, a i*x i = 1) :
    ∑ i, primalFlag a i * (Fin.cons 1 x : Fin (n+1) → K) i = 0 := by
  rw [Fin.sum_univ_succ]
  change (-1 : K)*1 + (∑ i, a i*x i) = 0
  rw [hx]
  ring

/-- All selected smooth isolated polar roots, with their full local lengths,
obey the ordinary determinant incidence coefficient bound. -/
theorem ordinary_polar_multiplicity_bound (hn : 2 ≤ n) (hm : 0 < m)
    (A : PencilCoefficients n m K) (ell : ℕ → Fin n → K) (a : Fin n → K)
    {P : Type} [Fintype P] (points : P → Fin n → K) (hinj : Function.Injective points)
    (hpoint : ∀ p, polarChartIdeal (determinant A) ell (n-2) a ≤ pointIdeal (points p))
    [∀ p, IsArtinianRing (LocalIntersectionRing
      (polarChartIdeal (determinant A) ell (n-2) a) (points p) (hpoint p))]
    (hsmooth : ∀ p, ∃ i, eval (points p) (pderiv i (determinant A)) ≠ 0) :
    (∑ p, multiplicity (polarChartIdeal (determinant A) ell (n-2) a)
      (points p) (hpoint p)) ≤ (ordinaryBezout m n : ℕ∞) := by
  classical
  cases m with
  | zero => omega
  | succ k =>
    let x : P → Fin (n+1) → K := fun p => Fin.cons 1 (points p)
    have hx : Function.Injective x := by
      intro p q hpq
      apply hinj
      funext i
      exact congrFun hpq i.succ
    obtain ⟨family⟩ := FieldExactKernelLifts.exists_ordinary_lift_family A hm
      (polarFlags ell) (primalFlag a) x hx (fun _ => rfl)
      (fun p => chart_root _ ell a _ (hpoint p)) hsmooth (fun _ => rfl)
      (fun p t => by
        simpa [polarFlags, polar] using chart_polar _ ell a _ (hpoint p) t)
      (fun p => primal_equation a _ (chart_primal _ ell a _ (hpoint p)))
    let charts (p : P) := FieldIncidenceAffineChartIdeals.ordinaryChart (points p)
      (family.lift p).u (family.lift p).v (family.lift p).rightIndex
      (family.lift p).leftIndex (family.lift p).left_normalized (family.lift p).right_normalized
    have heq := polarIntersectionIdeal_eq_polarChartIdeal A ell a
    let e (p : P) : FieldProjectiveLocalMultiplicity.LocalRing
        (ordinarySystem A family.reduction (polarFlags ell) (primalFlag a))
        (ordinaryAssignment (x p) (family.lift p).u (family.lift p).v)
        (charts p) (family.zeros p) ≃+*
        LocalIntersectionRing (polarChartIdeal (determinant A) ell (n-2) a)
          (points p) (hpoint p) := by
      have ha : eval (points p) ((affinePencil A).adjugate
          (family.lift p).rightIndex (family.lift p).leftIndex) ≠ 0 := by
        have h := (eval (points p)).map_adjugate (affinePencil A)
        change (affinePencil A).adjugate.map (eval (points p)) =
          ((affinePencil A).map (eval (fun q => x p q.succ))).adjugate at h
        rw [eval_affinePencil A (x p) (by rfl)] at h
        change ((affinePencil A).adjugate.map (eval (points p)))
          (family.lift p).rightIndex (family.lift p).leftIndex ≠ 0
        rw [h]
        exact (family.lift p).cofactor_nonzero
      have hb : KernelIncidenceLocalMultiplicity.polarIntersectionIdeal (affinePencil A)
          (fun t => IncidenceAffineEquations.flagMatrix A (polarFlags ell t))
          (Ideal.span {IncidenceAffineEquations.primalPolynomial (primalFlag a)}) ≤
            pointIdeal (points p) := by rw [heq]; exact hpoint p
      exact (FieldOrdinaryIncidenceLocalMultiplicity.ordinaryChartLocalEquiv A family.reduction
        (polarFlags ell) (primalFlag a) (points p) (family.lift p).u (family.lift p).v
        (family.lift p).rightIndex (family.lift p).leftIndex
        (family.lift p).left_normalized (family.lift p).right_normalized ha
        (family.reduction_injective p) (family.zeros p) hb).trans
          (localEquivOfIdealEq _ _ heq (points p) hb (hpoint p))
    letI (p : P) : IsArtinianRing (FieldProjectiveLocalMultiplicity.LocalRing
        (ordinarySystem A family.reduction (polarFlags ell) (primalFlag a))
        (ordinaryAssignment (x p) (family.lift p).u (family.lift p).v)
        (charts p) (family.zeros p)) := (e p).symm.isArtinianRing
    have hb := FieldIncidence.ordinary_incidence_multiplicity_bound hn (by omega) A
      family.reduction (polarFlags ell) (primalFlag a)
      (fun p => ordinaryAssignment (x p) (family.lift p).u (family.lift p).v)
      charts family.zeros family.projectively_distinct
    have hlen : (∑ p, FieldProjectiveLocalMultiplicity.multiplicity
        (ordinarySystem A family.reduction (polarFlags ell) (primalFlag a))
        (ordinaryAssignment (x p) (family.lift p).u (family.lift p).v)
        (charts p) (family.zeros p)) =
        ∑ p, multiplicity (polarChartIdeal (determinant A) ell (n-2) a)
          (points p) (hpoint p) := by
      apply Finset.sum_congr rfl
      intro p _
      exact ProjectiveCycleLengths.ringEquiv_length (e p)
    rwa [hlen] at hb

/-- The native symmetric one-kernel incidence gives the symmetric coefficient
bound for the same literal polar-section multiplicities. -/
theorem symmetric_polar_multiplicity_bound (hn : 2 ≤ n) (hm : 0 < m)
    (A : PencilCoefficients n m K) (hA : ∀ i, (A i).transpose = A i)
    (ell : ℕ → Fin n → K) (a : Fin n → K)
    {P : Type} [Fintype P] (points : P → Fin n → K) (hinj : Function.Injective points)
    (hpoint : ∀ p, polarChartIdeal (determinant A) ell (n-2) a ≤ pointIdeal (points p))
    [∀ p, IsArtinianRing (LocalIntersectionRing
      (polarChartIdeal (determinant A) ell (n-2) a) (points p) (hpoint p))]
    (hsmooth : ∀ p, ∃ i, eval (points p) (pderiv i (determinant A)) ≠ 0) :
    (∑ p, multiplicity (polarChartIdeal (determinant A) ell (n-2) a)
      (points p) (hpoint p)) ≤ (symmetricBezout m n : ℕ∞) := by
  classical
  cases m with
  | zero => omega
  | succ k =>
    let x : P → Fin (n+1) → K := fun p => Fin.cons 1 (points p)
    have hx : Function.Injective x := by
      intro p q hpq
      apply hinj
      funext i
      exact congrFun hpq i.succ
    obtain ⟨family⟩ := FieldExactKernelLifts.exists_symmetric_lift_family A hm hA
      (polarFlags ell) (primalFlag a) x hx (fun _ => rfl)
      (fun p => chart_root _ ell a _ (hpoint p)) hsmooth (fun _ => rfl)
      (fun p t => by
        simpa [polarFlags, polar] using chart_polar _ ell a _ (hpoint p) t)
      (fun p => primal_equation a _ (chart_primal _ ell a _ (hpoint p)))
    let charts (p : P) := FieldSymmetricIncidenceAffineEquations.normalizedChart
      (x p) (family.lift p).v (family.lift p).index (by rfl) (family.lift p).normalized
    have heq := polarIntersectionIdeal_eq_polarChartIdeal A ell a
    let e (p : P) : FieldBiProjectiveLocalMultiplicity.LocalRing
        (symmetricSystem A (polarFlags ell) (primalFlag a))
        (symmetricAssignment (x p) (family.lift p).v) (charts p) (family.zeros p) ≃+*
        LocalIntersectionRing (polarChartIdeal (determinant A) ell (n-2) a)
          (points p) (hpoint p) := by
      have hb : FieldSymmetricIncidenceLocalMultiplicity.basePolarIdeal A
          (polarFlags ell) (primalFlag a) ≤ pointIdeal (points p) := by
        change KernelIncidenceLocalMultiplicity.polarIntersectionIdeal (affinePencil A)
          (fun t => IncidenceAffineEquations.flagMatrix A (polarFlags ell t))
          (Ideal.span {IncidenceAffineEquations.primalPolynomial (primalFlag a)}) ≤ _
        rw [heq]
        exact hpoint p
      exact (FieldSymmetricIncidenceLocalMultiplicity.localEquiv A hA
        (polarFlags ell) (primalFlag a) (x p) (by rfl) (family.lift p) (family.zeros p) hb).trans
          (localEquivOfIdealEq _ _ heq (points p) hb (hpoint p))
    letI (p : P) : IsArtinianRing (FieldBiProjectiveLocalMultiplicity.LocalRing
        (symmetricSystem A (polarFlags ell) (primalFlag a))
        (symmetricAssignment (x p) (family.lift p).v) (charts p) (family.zeros p)) :=
      (e p).symm.isArtinianRing
    have hb := FieldIncidence.symmetric_incidence_multiplicity_bound hn (by omega) A
      (polarFlags ell) (primalFlag a) (fun p => symmetricAssignment (x p) (family.lift p).v)
      charts family.zeros family.projectively_distinct
    have hlen : (∑ p, FieldBiProjectiveLocalMultiplicity.multiplicity
        (symmetricSystem A (polarFlags ell) (primalFlag a))
        (symmetricAssignment (x p) (family.lift p).v) (charts p) (family.zeros p)) =
        ∑ p, multiplicity (polarChartIdeal (determinant A) ell (n-2) a)
          (points p) (hpoint p) := by
      apply Finset.sum_congr rfl
      intro p _
      exact ProjectiveCycleLengths.ringEquiv_length (e p)
    rwa [hlen] at hb

end Sheshadri.FieldPolarMultiplicityBound
