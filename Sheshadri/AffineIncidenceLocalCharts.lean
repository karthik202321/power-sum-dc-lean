/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.AffineIncidenceCharts
import Sheshadri.NestedPolynomialLocalPoint
import Sheshadri.IsolatedLocalMultiplicity
import Sheshadri.ProjectiveCycleLengths

/-!
# The actual point local rings of affine incidence charts

The literal dehomogenization isomorphism respects evaluation at the displayed
point. It therefore identifies its actual local equation rings, retaining all
nilpotents and every local-length multiplicity.
-/

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3
namespace Sheshadri.AffineIncidenceLocalCharts
open MvPolynomial AffineIncidenceCharts

variable {K T : Type*} [Field K] {n : ℕ}

/-- The homogeneous primal chart point with first coordinate one. -/
def sourcePoint (p : Fin n → K) (q : T → K) : Fin (n+1) ⊕ T → K :=
  Sum.elim (Fin.cons 1 p) q

theorem sourcePoint_eq (x : Fin (n+1) → K) (q : T → K) (hx : x 0 = 1) :
    sourcePoint (fun i => x i.succ) q = Sum.elim x q := by
  have h : Fin.cons 1 (fun i => x i.succ) = x := by
    simpa only [Fin.tail, hx] using (Fin.cons_self_tail x)
  exact congrArg (fun a => Sum.elim a q) h

@[simp] theorem evaluation_dehom (p : Fin n → K) (q : T → K)
    (f : HomogeneousRing n T K) :
    NestedPolynomialLocalPoint.evaluation p q (dehom f) = eval (sourcePoint p q) f := by
  induction f using MvPolynomial.induction_on with
  | C r => simp [NestedPolynomialLocalPoint.evaluation]
  | add f g hf hg => simp [hf,hg]
  | mul_X f i hf =>
    change eval₂ (eval p) q (dehom f) = eval (Sum.elim (Fin.cons 1 p) q) f at hf
    rcases i with i | t
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp [hf, sourcePoint, NestedPolynomialLocalPoint.evaluation]
      · simp [hf, sourcePoint, NestedPolynomialLocalPoint.evaluation]
    · simp [hf, sourcePoint, NestedPolynomialLocalPoint.evaluation]

/-- The transported literal ideal vanishes at the nested polynomial point. -/
theorem mappedIdeal_le_point (I : Ideal (HomogeneousRing n T K))
    (p : Fin n → K) (q : T → K)
    (hp : I ≤ IsolatedLocalMultiplicity.pointIdeal (sourcePoint p q)) :
    I.map dehom.toRingHom ≤ RingHom.ker (NestedPolynomialLocalPoint.evaluation p q) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro f hf
  change NestedPolynomialLocalPoint.evaluation p q (dehom f) = 0
  rw [evaluation_dehom]
  exact hp hf

@[simp] theorem quotientEvaluation_equiv (I : Ideal (HomogeneousRing n T K))
    (hI : X (.inl 0) - 1 ∈ I) (p : Fin n → K) (q : T → K)
    (hp : I ≤ IsolatedLocalMultiplicity.pointIdeal (sourcePoint p q))
    (f : HomogeneousRing n T K ⧸ I) :
    NestedPolynomialLocalPoint.quotientEvaluation (I.map dehom.toRingHom) p q
      (mappedIdeal_le_point I p q hp) (quotientEquiv I hI f) =
      IsolatedLocalMultiplicity.quotientEvaluation I (sourcePoint p q) hp f := by
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective f
  change NestedPolynomialLocalPoint.evaluation p q (dehom f) = eval (sourcePoint p q) f
  exact evaluation_dehom p q f

/-- The isomorphism sends precisely the actual point's permissible
localization denominators to the affine point's permissible denominators. -/
theorem map_primeCompl (I : Ideal (HomogeneousRing n T K))
    (hI : X (.inl 0) - 1 ∈ I) (p : Fin n → K) (q : T → K)
    (hp : I ≤ IsolatedLocalMultiplicity.pointIdeal (sourcePoint p q)) :
    Submonoid.map (quotientEquiv I hI)
      (IsolatedLocalMultiplicity.quotientPointIdeal I (sourcePoint p q) hp).primeCompl =
      (NestedPolynomialLocalPoint.quotientPointIdeal (I.map dehom.toRingHom) p q
        (mappedIdeal_le_point I p q hp)).primeCompl := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change NestedPolynomialLocalPoint.quotientEvaluation _ p q _ (quotientEquiv I hI x) ≠ 0
    rw [quotientEvaluation_equiv]
    exact hx
  · intro hy
    refine ⟨(quotientEquiv I hI).symm y, ?_, (quotientEquiv I hI).apply_symm_apply y⟩
    change IsolatedLocalMultiplicity.quotientEvaluation I (sourcePoint p q) hp _ ≠ 0
    rw [← quotientEvaluation_equiv I hI p q hp,
      (quotientEquiv I hI).apply_symm_apply]
    exact hy

/-- The actual local ring of the homogeneous incidence equations at the
normalized point equals the actual nested affine incidence local ring. -/
def localEquiv (I : Ideal (HomogeneousRing n T K))
    (hI : X (.inl 0) - 1 ∈ I) (p : Fin n → K) (q : T → K)
    (hp : I ≤ IsolatedLocalMultiplicity.pointIdeal (sourcePoint p q)) :
    IsolatedLocalMultiplicity.LocalIntersectionRing I (sourcePoint p q) hp ≃ₐ[K]
      NestedPolynomialLocalPoint.LocalRing (I.map dehom.toRingHom) p q
        (mappedIdeal_le_point I p q hp) :=
  IsLocalization.algEquivOfAlgEquiv _ _ (quotientEquiv I hI)
    (map_primeCompl I hI p q hp)

/-- Affine chart transport preserves singular isolated-zero multiplicity,
with no smoothness, reducedness, or finite-length premise. -/
theorem multiplicity_eq (I : Ideal (HomogeneousRing n T K))
    (hI : X (.inl 0) - 1 ∈ I) (p : Fin n → K) (q : T → K)
    (hp : I ≤ IsolatedLocalMultiplicity.pointIdeal (sourcePoint p q)) :
    IsolatedLocalMultiplicity.multiplicity I (sourcePoint p q) hp =
      Module.length
        (NestedPolynomialLocalPoint.LocalRing (I.map dehom.toRingHom) p q
          (mappedIdeal_le_point I p q hp))
        (NestedPolynomialLocalPoint.LocalRing (I.map dehom.toRingHom) p q
          (mappedIdeal_le_point I p q hp)) :=
  ProjectiveCycleLengths.ringEquiv_length (localEquiv I hI p q hp).toRingEquiv

/-- A literal ideal equality can replace the affine image ideal by its
native incidence presentation, without changing the actual local point. -/
def localEquivOfMappedIdealEq (I : Ideal (HomogeneousRing n T K))
    (hI : X (.inl 0) - 1 ∈ I) (p : Fin n → K) (q : T → K)
    (hp : I ≤ IsolatedLocalMultiplicity.pointIdeal (sourcePoint p q))
    (J : Ideal (AffineRing n T K)) (hJ : I.map dehom.toRingHom = J)
    (hpoint : J ≤ RingHom.ker (NestedPolynomialLocalPoint.evaluation p q)) :
    IsolatedLocalMultiplicity.LocalIntersectionRing I (sourcePoint p q) hp ≃ₐ[K]
      NestedPolynomialLocalPoint.LocalRing J p q hpoint := by
  subst J
  exact localEquiv I hI p q hp

/-- Version for an already normalized source point and an independently
named literal affine equation ideal. -/
def normalizedLocalEquiv (I : Ideal (HomogeneousRing n T K))
    (hI : X (.inl 0) - 1 ∈ I) (x : Fin (n+1) → K) (q : T → K) (hx : x 0 = 1)
    (hp : I ≤ IsolatedLocalMultiplicity.pointIdeal (Sum.elim x q))
    (J : Ideal (AffineRing n T K)) (hJ : I.map dehom.toRingHom = J)
    (hpoint : J ≤ RingHom.ker
      (NestedPolynomialLocalPoint.evaluation (fun i => x i.succ) q)) :
    IsolatedLocalMultiplicity.LocalIntersectionRing I (Sum.elim x q) hp ≃ₐ[K]
      NestedPolynomialLocalPoint.LocalRing J (fun i => x i.succ) q hpoint := by
  subst J
  have heval (f : HomogeneousRing n T K ⧸ I) :
      NestedPolynomialLocalPoint.quotientEvaluation (I.map dehom.toRingHom)
        (fun i => x i.succ) q hpoint (quotientEquiv I hI f) =
        IsolatedLocalMultiplicity.quotientEvaluation I (Sum.elim x q) hp f := by
    obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective f
    change NestedPolynomialLocalPoint.evaluation (fun i => x i.succ) q (dehom f) =
      eval (Sum.elim x q) f
    rw [evaluation_dehom, sourcePoint_eq x q hx]
  refine IsLocalization.algEquivOfAlgEquiv
    (M := (IsolatedLocalMultiplicity.quotientPointIdeal I (Sum.elim x q) hp).primeCompl)
    (T := (NestedPolynomialLocalPoint.quotientPointIdeal (I.map dehom.toRingHom)
      (fun i => x i.succ) q hpoint).primeCompl) _ _ (quotientEquiv I hI) ?_
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    change NestedPolynomialLocalPoint.quotientEvaluation _ _ q _ (quotientEquiv I hI z) ≠ 0
    rw [heval]
    exact hz
  · intro hy
    refine ⟨(quotientEquiv I hI).symm y, ?_, (quotientEquiv I hI).apply_symm_apply y⟩
    change IsolatedLocalMultiplicity.quotientEvaluation I (Sum.elim x q) hp _ ≠ 0
    rw [← heval, (quotientEquiv I hI).apply_symm_apply]
    exact hy

end Sheshadri.AffineIncidenceLocalCharts
