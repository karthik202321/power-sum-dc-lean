/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldIncidenceAffineChartIdeals
import Sheshadri.OrdinaryIncidenceLocalMultiplicity

noncomputable section
open Sheshadri.MultiProjective
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

namespace Sheshadri.FieldOrdinaryIncidenceLocalMultiplicity
variable {k₀ : Type*} [Field k₀] [CharZero k₀]
open Matrix MvPolynomial Incidence PolynomialModel
open IncidenceAffineEquations FieldIncidenceAffineChartIdeals AffineIncidenceCharts KernelIncidenceLocalMultiplicity
open FieldProjectiveLocalMultiplicity
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

variable {n m : ℕ}

theorem affineOrdinaryIdeal_eq (A : PencilCoefficients n (m+1) k₀)
    (Λ : Matrix (Fin m) (Fin (m+1)) k₀)
    (flags : Fin (n-2) → Fin (n+1) → k₀) (M : Fin (n+1) → k₀)
    (i j : Fin (m+1)) :
    FieldIncidenceAffineChartIdeals.affineOrdinaryIdeal A Λ flags M i j =
      reducedIncidenceIntersectionIdeal (affinePencil A) (Λ.map C) i j
        (fun t => flagMatrix A (flags t)) (Ideal.span {primalPolynomial M}) := by
  unfold FieldIncidenceAffineChartIdeals.affineOrdinaryIdeal reducedIncidenceIntersectionIdeal incidenceFlagIdeal
  rw [ConormalPolarIdeal.iSup_span_singleton_eq_span_range, Ideal.map_span]
  simp only [Set.image_singleton]
  ac_rfl

private def localEquivOfIdealEq {Z V : Type*} {K : Type*} [Field K]
    (I J : Ideal (MvPolynomial V (MvPolynomial Z K))) (he : I = J)
    (p : Z → K) (q : V → K)
    (hI : I ≤ RingHom.ker (NestedPolynomialLocalPoint.evaluation p q))
    (hJ : J ≤ RingHom.ker (NestedPolynomialLocalPoint.evaluation p q)) :
    NestedPolynomialLocalPoint.LocalRing I p q hI ≃+*
      NestedPolynomialLocalPoint.LocalRing J p q hJ := by
  subst J
  exact RingEquiv.refl _

private def localEquivOfPointEq {Z : Type*}
    (I : Ideal (MvPolynomial Z k₀)) (p q : Z → k₀)
    (hp : I ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (hq : I ≤ IsolatedLocalMultiplicity.pointIdeal q) (h : p = q) :
    IsolatedLocalMultiplicity.LocalIntersectionRing I p hp ≃+*
      IsolatedLocalMultiplicity.LocalIntersectionRing I q hq := by
  subst q
  exact RingEquiv.refl _

/-- No transversality hypothesis: the actual incidence chart local ring
equals the actual determinant-polar local ring at the selected smooth point. -/
def ordinaryChartLocalEquiv (A : PencilCoefficients n (m+1) k₀)
    (Λ : Matrix (Fin m) (Fin (m+1)) k₀)
    (flags : Fin (n-2) → Fin (n+1) → k₀) (M : Fin (n+1) → k₀)
    (x : Fin n → k₀) (u v : Fin (m+1) → k₀)
    (i j : Fin (m+1)) (hu : u j = 1) (hv : v i = 1)
    (ha : eval x ((affinePencil A).adjugate i j) ≠ 0)
    (hΛ : ∀ z, u ⬝ᵥ z = 0 → Λ *ᵥ z = 0 → z = 0)
    (hz : ∀ e, eval (ordinaryAssignment (Fin.cons 1 x) u v) (ordinarySystem A Λ flags M e) = 0)
    (hbase : polarIntersectionIdeal (affinePencil A)
      (fun t => flagMatrix A (flags t)) (Ideal.span {primalPolynomial M}) ≤
        IsolatedLocalMultiplicity.pointIdeal x) :
    LocalRing (ordinarySystem A Λ flags M) (ordinaryAssignment (Fin.cons 1 x) u v)
      (FieldIncidenceAffineChartIdeals.ordinaryChart x u v i j hu hv) hz ≃+*
    IsolatedLocalMultiplicity.LocalIntersectionRing
      (polarIntersectionIdeal (affinePencil A) (fun t => flagMatrix A (flags t))
        (Ideal.span {primalPolynomial M})) x hbase := by
  let I := chartIdeal (ordinarySystem A Λ flags M) (ordinaryAssignment (Fin.cons 1 x) u v)
    (FieldIncidenceAffineChartIdeals.ordinaryChart x u v i j hu hv)
  have hepoint : ordinaryAssignment (Fin.cons 1 x) u v =
      AffineIncidenceLocalCharts.sourcePoint x (Sum.elim u v) := by
    funext z
    rcases z with z | z
    · rfl
    · cases z <;> rfl
  have hIold := chartIdeal_le_pointIdeal (ordinarySystem A Λ flags M)
    (ordinaryAssignment (Fin.cons 1 x) u v) (FieldIncidenceAffineChartIdeals.ordinaryChart x u v i j hu hv) hz
  have hI : I ≤ IsolatedLocalMultiplicity.pointIdeal
      (AffineIncidenceLocalCharts.sourcePoint x (Sum.elim u v)) := by
    rw [← hepoint]
    exact hIold
  have hchart : MvPolynomial.X (.inl 0) - 1 ∈ I :=
    FieldIncidenceAffineChartIdeals.ordinaryChart_zeroCoordinate_mem A Λ flags M x u v i j hu hv
  let e := (AffineIncidenceLocalCharts.localEquiv I hchart x (Sum.elim u v) hI).toRingEquiv
  have he : I.map dehom.toRingHom =
      reducedIncidenceIntersectionIdeal (affinePencil A) (Λ.map C) i j
        (fun t => flagMatrix A (flags t)) (Ideal.span {primalPolynomial M}) :=
    (FieldIncidenceAffineChartIdeals.ordinaryChart_ideal_map A Λ flags M x u v i j hu hv).trans
      (affineOrdinaryIdeal_eq A Λ flags M i j)
  have hp := AffineIncidenceLocalCharts.mappedIdeal_le_point I x (Sum.elim u v) hI
  have hred : reducedIncidenceIntersectionIdeal (affinePencil A) (Λ.map C) i j
      (fun t => flagMatrix A (flags t)) (Ideal.span {primalPolynomial M}) ≤
        RingHom.ker (NestedPolynomialLocalPoint.evaluation x (Sum.elim u v)) := by
    rwa [← he]
  exact ((localEquivOfPointEq I _ _ hIold hI hepoint).trans
    (e.trans (localEquivOfIdealEq _ _ he x (Sum.elim u v) hp hred))).trans
    (pointReducedIncidenceLocalEquiv (affinePencil A) (Λ.map C) i j x ha
      (fun t => flagMatrix A (flags t)) (Ideal.span {primalPolynomial M}) hbase
      (Sum.elim u v) hred
      (IncidenceReductionPoint.evaluation_augmentedPolynomialMatrix_ne_zero x u v Λ hΛ))


end Sheshadri.FieldOrdinaryIncidenceLocalMultiplicity
