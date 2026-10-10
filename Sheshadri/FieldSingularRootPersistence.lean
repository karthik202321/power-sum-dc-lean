/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldBezoutVariableTransport

noncomputable section
open Sheshadri.MultiProjective
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

namespace Sheshadri.FieldSingularRootPersistence
variable {k₀ : Type*} [Field k₀] [CharZero k₀]
open MvPolynomial BezoutHorizontalFamily GeneralGradedBaseChange
open SingularSpecialFiber CoordinatePowerRegular IsolatedCompleteIntersection
open RingTheory.Sequence
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

section General
variable {σ k K : Type*} [Fintype σ] [Field k] [Infinite k]
    [Field K] [Algebra (Polynomial k) K] [IsFractionRing (Polynomial k) K]

def specialIdeal (fs : List (MvPolynomial σ (Polynomial k))) :
    Ideal (MvPolynomial σ k) := Ideal.ofList (fs.map evalZero)

omit [Fintype σ] [Infinite k] in
theorem specialIdeal_le_pointIdeal (fs : List (MvPolynomial σ (Polynomial k)))
    (p : σ → k) (hz : ∀ r ∈ fs, eval p (evalZero r) = 0) :
    specialIdeal fs ≤ IsolatedLocalMultiplicity.pointIdeal p := by
  apply Ideal.span_le.mpr
  rintro r hr
  change r ∈ fs.map evalZero at hr
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
  exact hz a ha

/-- Every generic-contracted equation annihilates the original complete
local intersection algebra, rather than only its residue field. -/
theorem family_contraction_annihilates_local
    (fs : List (MvPolynomial σ (Polynomial k))) (p : σ → k)
    (hsquare : fs.length = Fintype.card σ)
    (hz : ∀ r ∈ fs, eval p (evalZero r) = 0)
    [IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing
      (specialIdeal fs) p (specialIdeal_le_pointIdeal fs p hz))]
    (q : MvPolynomial σ (Polynomial k))
    (hq : q ∈ contractedIdeal (extendedIdeal (K := K) (Ideal.ofList fs))) :
    IsolatedLocalMultiplicity.localPolynomialMap
      (specialIdeal fs) p (specialIdeal_le_pointIdeal fs p hz) (evalZero q) = 0 := by
  let S := MvPolynomial σ (Polynomial k)
  let L := TotalLocalRing p
  let B := IsolatedLocalMultiplicity.LocalIntersectionRing
    (specialIdeal fs) p (specialIdeal_le_pointIdeal fs p hz)
  letI : IsArtinianRing (PointLocalRing p ⧸ localEquationIdeal p (fs.map evalZero)) := by
    change IsArtinianRing (PointLocalRing p ⧸
      Ideal.ofList ((fs.map evalZero).map (algebraMap _ (PointLocalRing p))))
    rw [← Ideal.map_ofList]
    exact local_equation_quotient_artinian (specialIdeal fs) p
      (specialIdeal_le_pointIdeal fs p hz)
  have hreg := isolated_square_regular p (fs.map evalZero)
    (by simpa using hsquare) (by
      intro r hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact hz a ha)
  let e := specialFiberEquiv p
  have hrelation : List.Forall₂
      (fun (r : L) (s : PointLocalRing p) => ∀ x, e (r • x) = s • e x)
      (fs.map (algebraMap S L))
      (fs.map (fun r => algebraMap (MvPolynomial σ k) (PointLocalRing p) (evalZero r))) := by
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r hr x
    change e (Ideal.Quotient.mk _ (algebraMap S L r) * x) = _ * e x
    rw [map_mul, specialFiberEquiv_mk]
  have hf : IsRegular (L ⧸ Ideal.span {localParameter p}) (fs.map (algebraMap S L)) :=
    e.toAddEquiv.isRegular_congr hrelation |>.mpr (by
      simpa only [localEquations, List.map_map, Function.comp_def] using hreg)
  have hIP : Ideal.ofList fs ≤ totalPointIdeal p := by
    apply Ideal.span_le.mpr
    intro r hr
    exact hz r hr
  have ht : (C Polynomial.X : S) ∈ totalPointIdeal p := by
    change eval p (evalZero (C Polynomial.X)) = 0
    simp [evalZero]
  have heq := SingularLocalContraction.localization_contractedIdeal_eq_of_special_regular
    (K := K) fs (totalPointIdeal p) hIP ht hf
  let P := IsolatedLocalMultiplicity.quotientPointIdeal
    (specialIdeal fs) p (specialIdeal_le_pointIdeal fs p hz)
  let g : S →+* (MvPolynomial σ k ⧸ specialIdeal fs) :=
    (Ideal.Quotient.mk (specialIdeal fs)).comp evalZero
  have hP : totalPointIdeal p = P.comap g := by ext r; rfl
  let ψ : L →+* B := Localization.localRingHom (totalPointIdeal p) P g hP
  have hψ (r : S) : ψ (algebraMap S L r) =
      IsolatedLocalMultiplicity.localPolynomialMap
        (specialIdeal fs) p (specialIdeal_le_pointIdeal fs p hz) (evalZero r) :=
    Localization.localRingHom_to_map _ _ _ _ r
  have hkill : (Ideal.ofList fs).map (algebraMap S L) ≤ RingHom.ker ψ := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    intro r hr
    change ψ (algebraMap S L r) = 0
    rw [hψ]
    change algebraMap _ _ (Ideal.Quotient.mk (specialIdeal fs) (evalZero r)) = 0
    have hm : evalZero r ∈ specialIdeal fs :=
      Ideal.subset_span (show evalZero r ∈ {x | x ∈ fs.map evalZero} from
        List.mem_map.mpr ⟨r,hr,rfl⟩)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]
  have hloc : algebraMap S L q ∈ (Ideal.ofList fs).map (algebraMap S L) := by
    rw [← heq]
    exact Ideal.mem_map_of_mem _ hq
  have hv : ψ (algebraMap S L q) = 0 := hkill hloc
  rwa [hψ] at hv

end General

section IdealTransport
variable {σ k : Type*} [Field k]

theorem local_artinian_of_ideal_eq (I J : Ideal (MvPolynomial σ k)) (p : σ → k)
    (hI : I ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (hJ : J ≤ IsolatedLocalMultiplicity.pointIdeal p) (h : I = J)
    [IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing J p hJ)] :
    IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing I p hI) := by
  subst J
  infer_instance

theorem local_map_zero_of_ideal_eq (I J : Ideal (MvPolynomial σ k)) (p : σ → k)
    (hI : I ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (hJ : J ≤ IsolatedLocalMultiplicity.pointIdeal p) (h : I = J)
    (q : MvPolynomial σ k)
    (hq : IsolatedLocalMultiplicity.localPolynomialMap I p hI q = 0) :
    IsolatedLocalMultiplicity.localPolynomialMap J p hJ q = 0 := by
  subst J
  exact hq

end IdealTransport

section Projective
open FieldMultiProjective FieldProjectiveLocalMultiplicity FieldBezoutRootPersistence
variable {X U V E K : Type*} [Fintype X] [Fintype U] [Fintype V] [Fintype E]
    [Nonempty X] [Nonempty U] [Nonempty V]
    [Field K] [Algebra (Polynomial k₀) K] [IsFractionRing (Polynomial k₀) K]

/-- The actual horizontal interpolation ideal annihilates every selected
isolated chart-local algebra, including its nonreduced structure. -/
theorem original_isolated_root_annihilates_interpolation_contraction
    (f g : E → MvPolynomial (Variables X U V) k₀)
    (p : Variables X U V → k₀)
    (hcard : Fintype.card E = (Fintype.card X-1)+(Fintype.card U-1)+(Fintype.card V-1))
    (hz : ∀ e, eval p (f e) = 0) (c : Chart p)
    [IsArtinianRing (FieldProjectiveLocalMultiplicity.LocalRing f p c hz)]
    (q : MvPolynomial (Variables X U V) (Polynomial k₀))
    (hq : q ∈ contractedIdeal (extendedIdeal (K := K)
      (Ideal.span (Set.range (fun e => coefficientEquiv (interpolation (f e) (g e))))))) :
    polynomialMap f p c hz (MvPolynomial.map (Polynomial.evalRingHom 0) q) = 0 := by
  classical
  let Z := Variables X U V
  let H : E ⊕ Fin 3 → MvPolynomial Z (Polynomial k₀)
    | .inl e => coefficientEquiv (interpolation (f e) (g e))
    | .inr i => MvPolynomial.X (c.coordinate i) - C (Polynomial.C (p (c.coordinate i)))
  let l : List (E ⊕ Fin 3) := Finset.univ.toList
  let fs := l.map H
  have hspecial (e : E ⊕ Fin 3) : evalZero (H e) = chartEquations f p c e := by
    cases e with
    | inl e =>
      simpa [H, chartEquations, evalZero] using
        FieldBezoutDeformationBound.map_coefficient_interpolation (f e) (g e) 0
    | inr i =>
      simp only [H, evalZero, chartEquations, map_sub, map_X, map_C]
      rw [MvPolynomial.map_C]
      simp
      rfl
  have hideal : specialIdeal fs = chartIdeal f p c := by
    unfold specialIdeal chartIdeal Ideal.ofList
    congr 1
    ext r
    simp only [fs, List.map_map, Function.comp_def, hspecial, Set.mem_setOf_eq,
      List.mem_map, Set.mem_range]
    simp [l]
  have hzero : ∀ r ∈ fs, eval p (evalZero r) = 0 := by
    intro r hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    rw [hspecial]
    exact chartEquations_zero f p c hz e
  have hsquare : fs.length = Fintype.card Z := by
    simpa [fs, l, Z] using chart_system_square hcard
  letI : IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing
      (specialIdeal fs) p (specialIdeal_le_pointIdeal fs p hzero)) := by
    exact local_artinian_of_ideal_eq _ _ p _ (chartIdeal_le_pointIdeal f p c hz) hideal
  have hinc : Ideal.span (Set.range
      (fun e => coefficientEquiv (interpolation (f e) (g e)))) ≤ Ideal.ofList fs := by
    apply Ideal.span_le.mpr
    rintro r ⟨e,rfl⟩
    apply Ideal.subset_span
    exact List.mem_map.mpr ⟨.inl e, by simp [l], rfl⟩
  have hq' : q ∈ contractedIdeal (extendedIdeal (K := K) (Ideal.ofList fs)) :=
    Ideal.comap_mono (Ideal.map_mono hinc) hq
  have hv := family_contraction_annihilates_local (K := K) fs p hsquare hzero q hq'
  change IsolatedLocalMultiplicity.localPolynomialMap (chartIdeal f p c) p
    (chartIdeal_le_pointIdeal f p c hz) (evalZero q) = 0
  exact local_map_zero_of_ideal_eq _ _ p _ _ hideal _ hv

end Projective

end Sheshadri.FieldSingularRootPersistence
