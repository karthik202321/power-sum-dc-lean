/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SymmetricIncidenceAffineEquations
import Sheshadri.AffineIncidenceLocalCharts

/-!
# The actual symmetric conormal incidence local ring

At an actual normalized kernel lift, the native two-projective-factor
incidence chart is isomorphic to the determinant/polar local intersection
ring. This identifies the full local algebras, including all nilpotents.
The nonzero cofactor is obtained from the constructed kernel lift.
-/

noncomputable section
namespace Sheshadri.SymmetricIncidenceLocalMultiplicity
open MvPolynomial Matrix Incidence PolynomialModel ExactKernelLifts
open IncidenceAffineEquations SymmetricIncidenceAffineEquations
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

variable {n m : ℕ}

/-- Transport along equality of the displayed point retains the literal ideal. -/
def localEquivOfPointEq {Z : Type*} (I : Ideal (MvPolynomial Z ℂ))
    (p q : Z → ℂ) (hp : I ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (hq : I ≤ IsolatedLocalMultiplicity.pointIdeal q) (h : p = q) :
    IsolatedLocalMultiplicity.LocalIntersectionRing I p hp ≃+*
      IsolatedLocalMultiplicity.LocalIntersectionRing I q hq := by
  subst q
  exact RingEquiv.refl _

theorem assignment_eq (x : Fin (n+1) → ℂ) (v : Fin (m+1) → ℂ) :
    symmetricAssignment x v = Sum.elim x v := by
  funext z
  cases z <;> rfl

def basePolarIdeal (A : PencilCoefficients n (m+1) ℂ)
    (flags : Fin (n-2) → Fin (n+1) → ℂ) (M : Fin (n+1) → ℂ) :=
  KernelIncidenceLocalMultiplicity.polarIntersectionIdeal (affinePencil A)
    (fun e => flagMatrix A (flags e)) (Ideal.span {primalPolynomial M})

theorem affinePencil_symmetric (A : PencilCoefficients n (m+1) ℂ)
    (hA : ∀ s, (A s).transpose = A s) :
    (affinePencil A).transpose = affinePencil A := by
  ext a b
  simp only [Matrix.transpose_apply, affinePencil]
  have hs (s) : A s b a = A s a b := congrFun (congrFun (hA s) a) b
  simp only [hs]

theorem lift_cofactor_nonzero (A : PencilCoefficients n (m+1) ℂ)
    (x : Fin (n+1) → ℂ) (hx : x 0 = 1) (L : SymmetricKernelLift A x) :
    eval (fun q => x q.succ) ((affinePencil A).adjugate L.index L.index) ≠ 0 := by
  have h := (eval (fun q => x q.succ)).map_adjugate (affinePencil A)
  change (affinePencil A).adjugate.map (eval (fun q => x q.succ)) =
    ((affinePencil A).map (eval (fun q => x q.succ))).adjugate at h
  rw [eval_affinePencil A x hx] at h
  change ((affinePencil A).adjugate.map (eval (fun q => x q.succ)))
    L.index L.index ≠ 0
  rw [h]
  exact L.cofactor_nonzero

/-- Literal affine symmetric incidence equations vanish at the actual
constructed kernel point whenever the projective equations do. -/
theorem affineIdeal_le_point (A : PencilCoefficients n (m+1) ℂ)
    (flags : Fin (n-2) → Fin (n+1) → ℂ) (M : Fin (n+1) → ℂ)
    (x : Fin (n+1) → ℂ) (hx : x 0 = 1) (L : SymmetricKernelLift A x)
    (hz : ∀ e, eval (symmetricAssignment x L.v) (symmetricSystem A flags M e) = 0) :
    affineIncidenceIdeal A L.index flags M ≤ RingHom.ker
      (NestedPolynomialLocalPoint.evaluation (fun q => x q.succ) L.v) := by
  rw [← chartIdeal_map A flags M x L.v L.index hx L.normalized]
  apply AffineIncidenceLocalCharts.mappedIdeal_le_point
  rw [AffineIncidenceLocalCharts.sourcePoint_eq x L.v hx, ← assignment_eq x L.v]
  exact BiProjectiveLocalMultiplicity.chartIdeal_le_pointIdeal
    (symmetricSystem A flags M) (symmetricAssignment x L.v)
    (normalizedChart x L.v L.index hx L.normalized) hz

/-- The actual two-factor projective incidence chart and the actual base
polar intersection have isomorphic local rings, with no transversality or
reducedness premise. -/
def localEquiv (A : PencilCoefficients n (m+1) ℂ)
    (hA : ∀ s, (A s).transpose = A s)
    (flags : Fin (n-2) → Fin (n+1) → ℂ) (M : Fin (n+1) → ℂ)
    (x : Fin (n+1) → ℂ) (hx : x 0 = 1) (L : SymmetricKernelLift A x)
    (hz : ∀ e, eval (symmetricAssignment x L.v) (symmetricSystem A flags M e) = 0)
    (hbase : basePolarIdeal A flags M ≤
      IsolatedLocalMultiplicity.pointIdeal (fun q => x q.succ)) :
    BiProjectiveLocalMultiplicity.LocalRing (symmetricSystem A flags M)
      (symmetricAssignment x L.v) (normalizedChart x L.v L.index hx L.normalized) hz ≃+*
      IsolatedLocalMultiplicity.LocalIntersectionRing (basePolarIdeal A flags M)
        (fun q => x q.succ) hbase := by
  let I := BiProjectiveLocalMultiplicity.chartIdeal (symmetricSystem A flags M)
    (symmetricAssignment x L.v) (normalizedChart x L.v L.index hx L.normalized)
  have hI : X (.inl 0) - 1 ∈ I := by
    have h : BiProjectiveLocalMultiplicity.chartEquations (symmetricSystem A flags M)
        (symmetricAssignment x L.v) (normalizedChart x L.v L.index hx L.normalized)
        (.inr 0) ∈ I := Ideal.subset_span ⟨.inr 0, rfl⟩
    simpa [BiProjectiveLocalMultiplicity.chartEquations, normalizedChart,
      symmetricAssignment, hx] using h
  have hp : I ≤ IsolatedLocalMultiplicity.pointIdeal (symmetricAssignment x L.v) :=
    BiProjectiveLocalMultiplicity.chartIdeal_le_pointIdeal _ _ _ hz
  have hp' : I ≤ IsolatedLocalMultiplicity.pointIdeal (Sum.elim x L.v) := by
    rw [← assignment_eq x L.v]
    exact hp
  let e0 := localEquivOfPointEq I _ _ hp hp' (assignment_eq x L.v)
  let e := AffineIncidenceLocalCharts.normalizedLocalEquiv I hI x L.v hx hp' 
    (affineIncidenceIdeal A L.index flags M)
    (chartIdeal_map A flags M x L.v L.index hx L.normalized)
    (affineIdeal_le_point A flags M x hx L hz)
  exact e0.trans (e.toRingEquiv.trans
    (SymmetricKernelIncidenceLocalMultiplicity.pointIncidenceLocalEquiv
      (affinePencil A) (affinePencil_symmetric A hA) L.index (fun q => x q.succ)
      (lift_cofactor_nonzero A x hx L) (fun e => flagMatrix A (flags e))
      (Ideal.span {primalPolynomial M}) hbase L.v
      (affineIdeal_le_point A flags M x hx L hz)))

/-- Singular isolated-root multiplicity is exactly preserved. -/
theorem multiplicity_eq (A : PencilCoefficients n (m+1) ℂ)
    (hA : ∀ s, (A s).transpose = A s)
    (flags : Fin (n-2) → Fin (n+1) → ℂ) (M : Fin (n+1) → ℂ)
    (x : Fin (n+1) → ℂ) (hx : x 0 = 1) (L : SymmetricKernelLift A x)
    (hz : ∀ e, eval (symmetricAssignment x L.v) (symmetricSystem A flags M e) = 0)
    (hbase : basePolarIdeal A flags M ≤
      IsolatedLocalMultiplicity.pointIdeal (fun q => x q.succ)) :
    BiProjectiveLocalMultiplicity.multiplicity (symmetricSystem A flags M)
      (symmetricAssignment x L.v) (normalizedChart x L.v L.index hx L.normalized) hz =
      IsolatedLocalMultiplicity.multiplicity (basePolarIdeal A flags M)
        (fun q => x q.succ) hbase :=
  ProjectiveCycleLengths.ringEquiv_length (localEquiv A hA flags M x hx L hz hbase)

theorem local_artinian (A : PencilCoefficients n (m+1) ℂ)
    (hA : ∀ s, (A s).transpose = A s)
    (flags : Fin (n-2) → Fin (n+1) → ℂ) (M : Fin (n+1) → ℂ)
    (x : Fin (n+1) → ℂ) (hx : x 0 = 1) (L : SymmetricKernelLift A x)
    (hz : ∀ e, eval (symmetricAssignment x L.v) (symmetricSystem A flags M e) = 0)
    (hbase : basePolarIdeal A flags M ≤
      IsolatedLocalMultiplicity.pointIdeal (fun q => x q.succ))
    [IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing
      (basePolarIdeal A flags M) (fun q => x q.succ) hbase)] :
    IsArtinianRing (BiProjectiveLocalMultiplicity.LocalRing (symmetricSystem A flags M)
      (symmetricAssignment x L.v) (normalizedChart x L.v L.index hx L.normalized) hz) :=
  (localEquiv A hA flags M x hx L hz hbase).symm.isArtinianRing

end Sheshadri.SymmetricIncidenceLocalMultiplicity
