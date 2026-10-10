/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.IncidenceAffineEquations

/-! Exact transport of the literal ordinary incidence chart ideal. -/
noncomputable section
namespace Sheshadri.IncidenceAffineEquations
open MvPolynomial Matrix Incidence PolynomialModel AffineIncidenceCharts
open ProjectiveLocalMultiplicity
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

theorem span_range_sum {R E F : Type*} [CommRing R] (f : E ⊕ F → R) :
    Ideal.span (Set.range f) =
      Ideal.span (Set.range (fun e => f (.inl e))) ⊔
        Ideal.span (Set.range (fun e => f (.inr e))) := by
  have he : Set.range f = Set.range (fun e => f (.inl e)) ∪
      Set.range (fun e => f (.inr e)) := by
    ext z
    constructor
    · rintro ⟨e,rfl⟩
      cases e with
      | inl e => exact Or.inl ⟨e,rfl⟩
      | inr e => exact Or.inr ⟨e,rfl⟩
    · rintro (⟨e,rfl⟩ | ⟨e,rfl⟩)
      · exact ⟨.inl e,rfl⟩
      · exact ⟨.inr e,rfl⟩
  rw [he, Ideal.span_union]

variable {n m : ℕ}

def ordinaryChart (x : Fin n → ℂ) (u v : Fin (m+1) → ℂ)
    (i j : Fin (m+1)) (hu : u j = 1) (hv : v i = 1) :
    Chart (ordinaryAssignment (Fin.cons 1 x) u v) :=
  ⟨0,j,i,by simp [ordinaryAssignment],by simp [ordinaryAssignment,hu],
    by simp [ordinaryAssignment,hv]⟩

def affineOrdinaryIdeal (A : PencilCoefficients n (m+1) ℂ)
    (Λ : Matrix (Fin m) (Fin (m+1)) ℂ)
    (flags : Fin (n-2) → Fin (n+1) → ℂ) (M : Fin (n+1) → ℂ)
    (i j : Fin (m+1)) :=
  KernelReducedIncidenceAlgebra.reducedIncidenceIdeal (affinePencil A) (Λ.map C) i j ⊔
    Ideal.span (Set.range (fun t => KernelIncidenceAlgebra.polarEquation (flagMatrix A (flags t)))) ⊔
      Ideal.span {C (primalPolynomial M)}

theorem ordinaryChart_ideal_map (A : PencilCoefficients n (m+1) ℂ)
    (Λ : Matrix (Fin m) (Fin (m+1)) ℂ)
    (flags : Fin (n-2) → Fin (n+1) → ℂ) (M : Fin (n+1) → ℂ)
    (x : Fin n → ℂ) (u v : Fin (m+1) → ℂ)
    (i j : Fin (m+1)) (hu : u j = 1) (hv : v i = 1) :
    (chartIdeal (ordinarySystem A Λ flags M) (ordinaryAssignment (Fin.cons 1 x) u v)
      (ordinaryChart x u v i j hu hv)).map dehom.toRingHom =
        affineOrdinaryIdeal A Λ flags M i j := by
  rw [chartIdeal, Ideal.map_span, ← Set.range_comp, span_range_sum]
  have hs : Ideal.span (Set.range (fun e => dehom (ordinarySystem A Λ flags M e))) =
      (Ideal.span (Set.range (KernelIncidenceAlgebra.leftEquation (affinePencil A))) ⊔
        Ideal.span (Set.range (KernelReducedIncidenceAlgebra.reducedRightEquation
          (affinePencil A) (Λ.map C)))) ⊔
      Ideal.span (Set.range (fun t => KernelIncidenceAlgebra.polarEquation (flagMatrix A (flags t)))) ⊔
        Ideal.span {C (primalPolynomial M)} := by
    rw [span_range_sum, span_range_sum, span_range_sum]
    simp only [ordinarySystem, dehom_leftEquation, dehom_rightEquation,
      dehom_dualEquation, dehom_primalEquation, Set.range_const]
    change (Ideal.span (Set.range (KernelIncidenceAlgebra.leftEquation (affinePencil A))) ⊔
      (Ideal.span (Set.range (KernelReducedIncidenceAlgebra.reducedRightEquation
        (affinePencil A) (Λ.map C))) ⊔
      (Ideal.span (Set.range (fun t => KernelIncidenceAlgebra.polarEquation (flagMatrix A (flags t)))) ⊔
        Ideal.span {C (primalPolynomial M)}))) = _
    ac_rfl
  have hc : Ideal.span (Set.range (fun k : Fin 3 =>
      dehom (chartEquations (ordinarySystem A Λ flags M)
        (ordinaryAssignment (Fin.cons 1 x) u v) (ordinaryChart x u v i j hu hv) (.inr k)))) =
      Ideal.span {KernelIncidenceAlgebra.leftVariable j - 1} ⊔
        Ideal.span {KernelIncidenceAlgebra.rightVariable i - 1} := by
    have he : Set.range (fun k : Fin 3 =>
        dehom (chartEquations (ordinarySystem A Λ flags M)
          (ordinaryAssignment (Fin.cons 1 x) u v) (ordinaryChart x u v i j hu hv) (.inr k))) =
        {0, KernelIncidenceAlgebra.leftVariable j - 1,
          KernelIncidenceAlgebra.rightVariable i - 1} := by
      ext q
      simp only [Set.mem_range, Fin.exists_fin_succ, chartEquations, Chart.coordinate,
        ordinaryChart, ordinaryAssignment, hu,hv, KernelIncidenceAlgebra.leftVariable,
        KernelIncidenceAlgebra.rightVariable]
      simp
      aesop
    rw [he]
    simp only [Ideal.span_insert, Ideal.span_singleton_eq_bot.mpr rfl, bot_sup_eq]
  change Ideal.span (Set.range (fun e => dehom (ordinarySystem A Λ flags M e))) ⊔
    Ideal.span (Set.range (fun k : Fin 3 =>
      dehom (chartEquations (ordinarySystem A Λ flags M)
        (ordinaryAssignment (Fin.cons 1 x) u v) (ordinaryChart x u v i j hu hv) (.inr k)))) = _
  rw [hs,hc]
  unfold affineOrdinaryIdeal KernelReducedIncidenceAlgebra.reducedIncidenceIdeal
  ac_rfl

theorem ordinaryChart_zeroCoordinate_mem (A : PencilCoefficients n (m+1) ℂ)
    (Λ : Matrix (Fin m) (Fin (m+1)) ℂ)
    (flags : Fin (n-2) → Fin (n+1) → ℂ) (M : Fin (n+1) → ℂ)
    (x : Fin n → ℂ) (u v : Fin (m+1) → ℂ)
    (i j : Fin (m+1)) (hu : u j = 1) (hv : v i = 1) :
    MvPolynomial.X (.inl 0) - 1 ∈
      chartIdeal (ordinarySystem A Λ flags M) (ordinaryAssignment (Fin.cons 1 x) u v)
        (ordinaryChart x u v i j hu hv) := by
  apply Ideal.subset_span
  exact ⟨.inr 0, by simp [chartEquations, Chart.coordinate, ordinaryChart, ordinaryAssignment]⟩

end Sheshadri.IncidenceAffineEquations
