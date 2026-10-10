/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalGaussSection
import Sheshadri.ConormalPolarIdeal
import Sheshadri.IncidenceMultiplicity
import Sheshadri.ProjectiveCycleLengths
import Sheshadri.ConormalExact
import Sheshadri.OrdinaryIncidenceLocalMultiplicity
import Sheshadri.SymmetricIncidenceLocalMultiplicity

/-! # Exact conormal bounds using full local section multiplicities

The finite Gauss section is constructed from the original smooth homogeneous
form. The comparison below uses actual local-ring isomorphisms with the
literal determinant incidence, then the proved singular Bezout theorem.
-/

noncomputable section
namespace Sheshadri.ConormalExactMultiplicity
open MvPolynomial Incidence PolynomialModel ExactKernelLifts ConormalGaussSection
open SmoothGaussSectionLength
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 3

variable {n m d : ℕ} {f : MvPolynomial (Fin n) ℂ}

/-- Positive homogeneous degree forces an actual zero at the origin, so a
literal representation cannot have matrix size zero. -/
theorem homogeneous_representation_size_pos (A : PencilCoefficients n m ℂ)
    (hrep : determinant A = f) (hf : f.IsHomogeneous d) (hd : 0 < d) : 0 < m := by
  apply ConormalIncidence.matrix_size_pos_of_root A (fun _ => 0)
  rw [hrep]
  have he := SmoothGaussPolars.euler_evaluation hf (fun _ => (0 : ℂ))
  simp only [zero_mul, Finset.sum_const_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (Nat.cast_ne_zero.mpr hd.ne')

/-- Composition with actual local-ring comparison; the final smooth-form
bounds instantiate these isomorphisms with the proved Schur chart maps. -/
theorem ordinary_section_bound (hn : 2 ≤ n) (hm : 0 < m)
    (s : Section f d) (A : PencilCoefficients n m ℂ)
    (family : OrdinaryLiftFamily A (polarFlags s.ell) (primalFlag s.a) s.projectivePoint)
    (charts : ∀ p, ProjectiveLocalMultiplicity.Chart
      (ordinaryAssignment (s.projectivePoint p) (family.lift p).u (family.lift p).v))
    (localEquiv : ∀ p,
      ProjectiveLocalMultiplicity.LocalRing
        (ordinarySystem A family.reduction (polarFlags s.ell) (primalFlag s.a))
        (ordinaryAssignment (s.projectivePoint p) (family.lift p).u (family.lift p).v)
        (charts p) (family.zeros p) ≃+*
      IsolatedLocalMultiplicity.LocalIntersectionRing
        (polarChartIdeal f s.ell (n-2) s.a) (s.point p) (s.vanishes p)) :
    d*(d-1)^(n-2) ≤ ordinaryBezout m n := by
  letI (p : Fin s.count) := s.artinian p
  letI (p : Fin s.count) : IsArtinianRing
      (ProjectiveLocalMultiplicity.LocalRing
        (ordinarySystem A family.reduction (polarFlags s.ell) (primalFlag s.a))
        (ordinaryAssignment (s.projectivePoint p) (family.lift p).u (family.lift p).v)
        (charts p) (family.zeros p)) := (localEquiv p).symm.isArtinianRing
  have hb := ordinary_incidence_multiplicity_bound hn (by omega) A family.reduction
    (polarFlags s.ell) (primalFlag s.a)
    (fun p => ordinaryAssignment (s.projectivePoint p) (family.lift p).u (family.lift p).v)
    charts family.zeros family.projectively_distinct
  have he : (∑ p, ProjectiveLocalMultiplicity.multiplicity
        (ordinarySystem A family.reduction (polarFlags s.ell) (primalFlag s.a))
        (ordinaryAssignment (s.projectivePoint p) (family.lift p).u (family.lift p).v)
        (charts p) (family.zeros p)) = (d*(d-1)^(n-2) : ℕ) := by
    calc
      _ = ∑ p, IsolatedLocalMultiplicity.multiplicity
          (polarChartIdeal f s.ell (n-2) s.a) (s.point p) (s.vanishes p) := by
        apply Finset.sum_congr rfl
        intro p _
        exact ProjectiveCycleLengths.ringEquiv_length (localEquiv p)
      _ = _ := s.length_sum
  rw [he] at hb
  exact_mod_cast hb

theorem symmetric_section_bound (hn : 2 ≤ n) (hm : 0 < m)
    (s : Section f d) (A : PencilCoefficients n m ℂ)
    (family : SymmetricLiftFamily A (polarFlags s.ell) (primalFlag s.a) s.projectivePoint)
    (charts : ∀ p, BiProjectiveLocalMultiplicity.Chart
      (symmetricAssignment (s.projectivePoint p) (family.lift p).v))
    (localEquiv : ∀ p,
      BiProjectiveLocalMultiplicity.LocalRing
        (symmetricSystem A (polarFlags s.ell) (primalFlag s.a))
        (symmetricAssignment (s.projectivePoint p) (family.lift p).v)
        (charts p) (family.zeros p) ≃+*
      IsolatedLocalMultiplicity.LocalIntersectionRing
        (polarChartIdeal f s.ell (n-2) s.a) (s.point p) (s.vanishes p)) :
    d*(d-1)^(n-2) ≤ symmetricBezout m n := by
  letI (p : Fin s.count) := s.artinian p
  letI (p : Fin s.count) : IsArtinianRing
      (BiProjectiveLocalMultiplicity.LocalRing
        (symmetricSystem A (polarFlags s.ell) (primalFlag s.a))
        (symmetricAssignment (s.projectivePoint p) (family.lift p).v)
        (charts p) (family.zeros p)) := (localEquiv p).symm.isArtinianRing
  have hb := symmetric_incidence_multiplicity_bound hn (by omega) A
    (polarFlags s.ell) (primalFlag s.a)
    (fun p => symmetricAssignment (s.projectivePoint p) (family.lift p).v)
    charts family.zeros family.projectively_distinct
  have he : (∑ p, BiProjectiveLocalMultiplicity.multiplicity
        (symmetricSystem A (polarFlags s.ell) (primalFlag s.a))
        (symmetricAssignment (s.projectivePoint p) (family.lift p).v)
        (charts p) (family.zeros p)) = (d*(d-1)^(n-2) : ℕ) := by
    calc
      _ = ∑ p, IsolatedLocalMultiplicity.multiplicity
          (polarChartIdeal f s.ell (n-2) s.a) (s.point p) (s.vanishes p) := by
        apply Finset.sum_congr rfl
        intro p _
        exact ProjectiveCycleLengths.ringEquiv_length (localEquiv p)
      _ = _ := s.length_sum
  rw [he] at hb
  exact_mod_cast hb

private def localEquivOfIdealEq {Z : Type*}
    (I J : Ideal (MvPolynomial Z ℂ)) (he : I = J) (p : Z → ℂ)
    (hI : I ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (hJ : J ≤ IsolatedLocalMultiplicity.pointIdeal p) :
    IsolatedLocalMultiplicity.LocalIntersectionRing I p hI ≃+*
      IsolatedLocalMultiplicity.LocalIntersectionRing J p hJ := by
  subst J
  exact RingEquiv.refl _

/-- The full ordinary smooth-homogeneous degree bound, with the polar
section, common reduction, isolatedness, and local multiplicities constructed
from the literal determinant representation. -/
theorem ordinary_smooth_degree_bound (hn : 2 ≤ n)
    (A : PencilCoefficients n m ℂ) (f : MvPolynomial (Fin n) ℂ)
    (hrep : determinant A = f) (hf : f.IsHomogeneous d) (hfn : f ≠ 0) (hd : 0 < d)
    (hsmooth : ∀ x : Fin n → ℂ, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) :
    d*(d-1)^(n-2) ≤ ordinaryBezout m n := by
  have hm := homogeneous_representation_size_pos A hrep hf hd
  subst f
  cases m with
  | zero => omega
  | succ k =>
    obtain ⟨s⟩ := exists_section hn hf hfn hd hsmooth
    obtain ⟨family⟩ := s.ordinaryLiftFamily A hm rfl
    let charts (p : Fin s.count) := IncidenceAffineEquations.ordinaryChart (s.point p)
      (family.lift p).u (family.lift p).v
      (family.lift p).rightIndex (family.lift p).leftIndex
      (family.lift p).left_normalized (family.lift p).right_normalized
    apply ordinary_section_bound hn hm s A family charts
    intro p
    have ha : eval (s.point p) ((affinePencil A).adjugate
        (family.lift p).rightIndex (family.lift p).leftIndex) ≠ 0 := by
      have h := (eval (s.point p)).map_adjugate (affinePencil A)
      change (affinePencil A).adjugate.map (eval (s.point p)) =
        ((affinePencil A).map (eval (fun q => s.projectivePoint p q.succ))).adjugate at h
      rw [eval_affinePencil A (s.projectivePoint p) (by rfl)] at h
      change ((affinePencil A).adjugate.map (eval (s.point p)))
        (family.lift p).rightIndex (family.lift p).leftIndex ≠ 0
      rw [h]
      exact (family.lift p).cofactor_nonzero
    exact OrdinaryIncidenceLocalMultiplicity.ordinaryGaussChartLocalEquiv A family.reduction
      s.ell s.a (s.point p) (family.lift p).u (family.lift p).v
      (family.lift p).rightIndex (family.lift p).leftIndex
      (family.lift p).left_normalized (family.lift p).right_normalized ha
      (family.reduction_injective p) (family.zeros p) (s.vanishes p)

/-- The symmetric bound uses the native one-kernel-vector chart and its
proved local-ring equivalence with the actual Gauss-polar section. -/
theorem symmetric_smooth_degree_bound (hn : 2 ≤ n)
    (A : PencilCoefficients n m ℂ) (hA : ∀ i, (A i).transpose = A i)
    (f : MvPolynomial (Fin n) ℂ) (hrep : determinant A = f)
    (hf : f.IsHomogeneous d) (hfn : f ≠ 0) (hd : 0 < d)
    (hsmooth : ∀ x : Fin n → ℂ, x ≠ 0 → eval x f = 0 →
      ∃ i, eval x (pderiv i f) ≠ 0) :
    d*(d-1)^(n-2) ≤ symmetricBezout m n := by
  have hm := homogeneous_representation_size_pos A hrep hf hd
  subst f
  cases m with
  | zero => omega
  | succ k =>
    obtain ⟨s⟩ := exists_section hn hf hfn hd hsmooth
    obtain ⟨family⟩ := s.symmetricLiftFamily A hm hA rfl
    let charts (p : Fin s.count) := SymmetricIncidenceAffineEquations.normalizedChart
      (s.projectivePoint p) (family.lift p).v (family.lift p).index
      (by rfl) (family.lift p).normalized
    apply symmetric_section_bound hn hm s A family charts
    intro p
    have hb : SymmetricIncidenceLocalMultiplicity.basePolarIdeal A
        (polarFlags s.ell) (primalFlag s.a) ≤
          IsolatedLocalMultiplicity.pointIdeal (fun q => s.projectivePoint p q.succ) := by
      change KernelIncidenceLocalMultiplicity.polarIntersectionIdeal (affinePencil A)
        (fun t => IncidenceAffineEquations.flagMatrix A (polarFlags s.ell t))
        (Ideal.span {IncidenceAffineEquations.primalPolynomial (primalFlag s.a)}) ≤
          IsolatedLocalMultiplicity.pointIdeal (s.point p)
      rw [ConormalPolarIdeal.polarIntersectionIdeal_eq_polarChartIdeal]
      exact s.vanishes p
    have e := SymmetricIncidenceLocalMultiplicity.localEquiv A hA
      (polarFlags s.ell) (primalFlag s.a) (s.projectivePoint p) (by rfl)
      (family.lift p) (family.zeros p) hb
    exact e.trans (localEquivOfIdealEq _ _
      (ConormalPolarIdeal.polarIntersectionIdeal_eq_polarChartIdeal A s.ell s.a)
      (s.point p) hb (s.vanishes p))

/-- Exact ordinary coefficient bound from a literal Fermat determinant
representation, without GaussDegreeTheory or any geometric certificate. -/
theorem ordinary_exact_count (hn : 3 ≤ n) (hrep : ExactRepresentation n m ℂ) :
    fermatCount n ≤ ordinaryBezout m n := by
  obtain ⟨A, hA⟩ := hrep
  exact ordinary_smooth_degree_bound (by omega) A (fermat n) hA
    (ConormalExact.fermat_isHomogeneous n) (ConormalExact.fermat_ne_zero n (by omega))
    (by omega) (fun x hx _ => ConormalExact.fermat_smooth_away_from_vertex n (by omega) x hx)

theorem ordinary_exact_quadratic (hn : 3 ≤ n) (hrep : ExactRepresentation n m ℂ) :
    ((n : ℝ)-1)^2 / (4*Real.exp 1) ≤ (m : ℝ) :=
  ordinary_quadratic_bound n m hn (ordinary_exact_count hn hrep)

/-- Symmetric exact Fermat coefficient bound from a literal representation. -/
theorem symmetric_exact_count (hn : 3 ≤ n) (hrep : SymmetricExactRepresentation n m ℂ) :
    fermatCount n ≤ symmetricBezout m n := by
  obtain ⟨A, hsym, hA⟩ := hrep
  exact symmetric_smooth_degree_bound (by omega) A hsym (fermat n) hA
    (ConormalExact.fermat_isHomogeneous n) (ConormalExact.fermat_ne_zero n (by omega))
    (by omega) (fun x hx _ => ConormalExact.fermat_smooth_away_from_vertex n (by omega) x hx)

theorem symmetric_exact_quadratic (hn : 3 ≤ n) (hrep : SymmetricExactRepresentation n m ℂ) :
    ((n : ℝ)-1)^2 / (2*Real.exp 1) ≤ (m : ℝ) :=
  symmetric_quadratic_bound n m hn (symmetric_exact_count hn hrep)

end Sheshadri.ConormalExactMultiplicity
