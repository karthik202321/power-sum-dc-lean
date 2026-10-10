/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldOrdinaryIncidenceLocalMultiplicity
import Sheshadri.SymmetricIncidenceAffineEquations

noncomputable section
open Sheshadri.MultiProjective
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

namespace Sheshadri.FieldSymmetricIncidenceAffineEquations
variable {k₀ : Type*} [Field k₀] [CharZero k₀]
open MvPolynomial Matrix Incidence PolynomialModel AffineIncidenceCharts
open IncidenceAffineEquations
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

variable {K : Type*} [CommRing K] {n m : ℕ}

@[simp] theorem dehom_pencilEntry (A : PencilCoefficients n m K) (a b : Fin m) :
    dehom (symmetricPencilEntry A a b) = C (affinePencil A a b) := by
  simp [symmetricPencilEntry, affinePencil, Fin.sum_univ_succ]

@[simp] theorem dehom_kernelEquation (A : PencilCoefficients n (m+1) K) (a : Fin (m+1)) :
    dehom (symmetricKernelEquation A a) =
      SymmetricKernelIncidenceAlgebra.kernelEquation (affinePencil A) a := by
  simp [symmetricKernelEquation, SymmetricKernelIncidenceAlgebra.kernelEquation]

@[simp] theorem dehom_pairing (A : PencilCoefficients n (m+1) K) (i : Fin (n+1)) :
    dehom (symmetricPairing A i) =
      SymmetricKernelIncidenceAlgebra.polarEquation ((A i).map C) := by
  simp [symmetricPairing, SymmetricKernelIncidenceAlgebra.polarEquation]

@[simp] theorem dehom_dualEquation (A : PencilCoefficients n (m+1) K)
    (ell : Fin (n+1) → K) :
    dehom (symmetricDualEquation A ell) =
      SymmetricKernelIncidenceAlgebra.polarEquation (flagMatrix A ell) := by
  simp only [symmetricDualEquation, map_sum, map_mul, dehom_C, dehom_pairing]
  simp only [SymmetricKernelIncidenceAlgebra.polarEquation, flagMatrix, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul, Matrix.map_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem dehom_primalEquation (M : Fin (n+1) → K) :
    dehom (T := Fin (m+1)) (symmetricPrimalEquation (m := m+1) M) =
      C (primalPolynomial M) := by
  simp [symmetricPrimalEquation, primalPolynomial, Fin.sum_univ_succ]

def normalizedChart (x : Fin (n+1) → k₀) (v : Fin (m+1) → k₀)
    (i : Fin (m+1)) (hx : x 0 = 1) (hv : v i = 1) :
    FieldBiProjectiveLocalMultiplicity.Chart (symmetricAssignment x v) :=
  ⟨0, i, by simpa [symmetricAssignment, hx], by simpa [symmetricAssignment, hv]⟩

def affineIncidenceIdeal (A : PencilCoefficients n (m+1) K) (i : Fin (m+1))
    (flags : Fin (n-2) → Fin (n+1) → K) (M : Fin (n+1) → K) :=
  SymmetricKernelIncidenceLocalMultiplicity.incidenceIntersectionIdeal
    (affinePencil A) i (fun e => flagMatrix A (flags e)) (Ideal.span {primalPolynomial M})

/-- The literal normalized projective chart ideal maps to exactly the
native one-vector kernel and quadratic-polar incidence ideal. -/
theorem chartIdeal_map (A : PencilCoefficients n (m+1) k₀)
    (flags : Fin (n-2) → Fin (n+1) → k₀) (M : Fin (n+1) → k₀)
    (x : Fin (n+1) → k₀) (v : Fin (m+1) → k₀) (i : Fin (m+1))
    (hx : x 0 = 1) (hv : v i = 1) :
    (FieldBiProjectiveLocalMultiplicity.chartIdeal (symmetricSystem A flags M)
      (symmetricAssignment x v) (normalizedChart x v i hx hv)).map dehom.toRingHom =
        affineIncidenceIdeal A i flags M := by
  let B := affinePencil A
  let H := fun e => flagMatrix A (flags e)
  let J : Ideal (MvPolynomial (Fin n) k₀) := Ideal.span {primalPolynomial M}
  let L := SymmetricKernelIncidenceLocalMultiplicity.incidenceIntersectionIdeal B i H J
  have hk (a : Fin (m+1)) : SymmetricKernelIncidenceAlgebra.kernelEquation B a ∈ L :=
    (show Ideal.span (Set.range (SymmetricKernelIncidenceAlgebra.kernelEquation B)) ≤ L from
      le_trans le_sup_left le_sup_left) (Ideal.subset_span (Set.mem_range_self a))
  have hn : MvPolynomial.X i - 1 ∈ L :=
    (show Ideal.span {MvPolynomial.X i - 1} ≤ L from le_trans le_sup_right le_sup_left)
      (Ideal.subset_span (Set.mem_singleton _))
  have hd (e : Fin (n-2)) : SymmetricKernelIncidenceAlgebra.polarEquation (H e) ∈ L :=
    (show Ideal.span {SymmetricKernelIncidenceAlgebra.polarEquation (H e)} ≤ L from
      le_trans (le_iSup (fun e : Fin (n-2) =>
        Ideal.span {SymmetricKernelIncidenceAlgebra.polarEquation (H e)}) e)
        (le_trans le_sup_right le_sup_right))
        (Ideal.subset_span (Set.mem_singleton _))
  have hp : C (primalPolynomial M) ∈ L :=
    (show J.map C ≤ L from le_trans le_sup_left le_sup_right)
      (Ideal.mem_map_of_mem C (Ideal.subset_span (Set.mem_singleton _)))
  let Cideal := FieldBiProjectiveLocalMultiplicity.chartIdeal (symmetricSystem A flags M)
    (symmetricAssignment x v) (normalizedChart x v i hx hv)
  have heq (e : SymmetricEquationIndex n (m+1) ⊕ Fin 2) :
      dehom (FieldBiProjectiveLocalMultiplicity.chartEquations (symmetricSystem A flags M)
        (symmetricAssignment x v) (normalizedChart x v i hx hv) e) ∈ L := by
    rcases e with a | j
    · rcases a with a | (e | u)
      · simpa only [FieldBiProjectiveLocalMultiplicity.chartEquations, symmetricSystem,
          dehom_kernelEquation] using hk a
      · simpa only [FieldBiProjectiveLocalMultiplicity.chartEquations, symmetricSystem,
          dehom_dualEquation] using hd e
      · simpa only [FieldBiProjectiveLocalMultiplicity.chartEquations, symmetricSystem,
          dehom_primalEquation] using hp
    · fin_cases j
      · simp [FieldBiProjectiveLocalMultiplicity.chartEquations, normalizedChart,
          symmetricAssignment, hx]
      · simpa [FieldBiProjectiveLocalMultiplicity.chartEquations, normalizedChart,
          symmetricAssignment, hv] using hn
  have hmem (e : SymmetricEquationIndex n (m+1) ⊕ Fin 2) :
      dehom (FieldBiProjectiveLocalMultiplicity.chartEquations (symmetricSystem A flags M)
        (symmetricAssignment x v) (normalizedChart x v i hx hv) e) ∈ Cideal.map dehom.toRingHom :=
    Ideal.mem_map_of_mem dehom.toRingHom (Ideal.subset_span ⟨e, rfl⟩)
  apply le_antisymm
  · rw [FieldBiProjectiveLocalMultiplicity.chartIdeal, Ideal.map_span, ← Set.range_comp]
    exact Ideal.span_le.mpr (by rintro _ ⟨e,rfl⟩; exact heq e)
  · change L ≤ Cideal.map dehom.toRingHom
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · apply Ideal.span_le.mpr
      rintro _ ⟨a,rfl⟩
      simpa only [FieldBiProjectiveLocalMultiplicity.chartEquations, symmetricSystem,
        dehom_kernelEquation] using hmem (.inl (.inl a))
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟩
      simpa [FieldBiProjectiveLocalMultiplicity.chartEquations, normalizedChart,
        symmetricAssignment, hv] using hmem (.inr 1)
    · change (Ideal.span {primalPolynomial M}).map C ≤ _
      rw [Ideal.map_span, Set.image_singleton]
      apply Ideal.span_le.mpr
      rintro _ ⟨⟩
      simpa only [FieldBiProjectiveLocalMultiplicity.chartEquations, symmetricSystem,
        dehom_primalEquation] using hmem (.inl (.inr (.inr ())))
    · apply iSup_le
      intro e
      apply Ideal.span_le.mpr
      rintro _ ⟨⟩
      simpa only [FieldBiProjectiveLocalMultiplicity.chartEquations, symmetricSystem,
        dehom_dualEquation] using hmem (.inl (.inr (.inl e)))

end Sheshadri.FieldSymmetricIncidenceAffineEquations
