/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.KernelLines
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual normalized kernel incidence algebra

At a unit cofactor, the equation scheme with both normalized kernel vectors is
isomorphic to the determinant hypersurface, over arbitrary commutative rings.
The construction retains nilpotents and therefore identifies local intersection
multiplicities, not merely the underlying sets of points.
-/

noncomputable section
namespace Sheshadri.KernelIncidenceAlgebra

open Matrix MvPolynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] {m : ℕ}

abbrev Variables (m : ℕ) := Fin (m+1) ⊕ Fin (m+1)
abbrev Polynomials (R : Type*) [CommRing R] (m : ℕ) := MvPolynomial (Variables m) R

def leftVariable (k : Fin (m+1)) : Polynomials R m := X (Sum.inl k)
def rightVariable (k : Fin (m+1)) : Polynomials R m := X (Sum.inr k)

def leftEquation (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (l : Fin (m+1)) :
    Polynomials R m := ∑ k, leftVariable k * C (A k l)

def rightEquation (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (l : Fin (m+1)) :
    Polynomials R m := ∑ k, C (A l k) * rightVariable k

/-- All left and right kernel equations, together with both normalizations. -/
def incidenceIdeal (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1)) :
    Ideal (Polynomials R m) :=
  Ideal.span (Set.range (leftEquation A)) ⊔
    Ideal.span (Set.range (rightEquation A)) ⊔
    Ideal.span {leftVariable j - 1} ⊔ Ideal.span {rightVariable i - 1}

abbrev IncidenceRing (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1)) :=
  Polynomials R m ⧸ incidenceIdeal A i j

abbrev DeterminantRing (A : Matrix (Fin (m+1)) (Fin (m+1)) R) := R ⧸ Ideal.span {A.det}

/-- Universal property of the literal equation ideal. -/
theorem incidenceIdeal_le_ker_iff {S : Type*} [CommRing S] [Algebra R S]
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (φ : Polynomials R m →ₐ[R] S) :
    incidenceIdeal A i j ≤ RingHom.ker φ ↔
      (fun k => φ (leftVariable k)) ᵥ* A.map (algebraMap R S) = 0 ∧
      A.map (algebraMap R S) *ᵥ (fun k => φ (rightVariable k)) = 0 ∧
      φ (leftVariable j) = 1 ∧ φ (rightVariable i) = 1 := by
  simp only [incidenceIdeal, sup_le_iff, Ideal.span_le, Set.range_subset_iff,
    Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, leftEquation, rightEquation,
    map_sum, map_mul, map_sub, map_one, sub_eq_zero,
    ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  simp only [funext_iff, Matrix.vecMul, Matrix.mulVec, dotProduct,
    Matrix.map_apply, Pi.zero_apply]
  tauto

/-- The actual quotient carries the displayed normalized kernel vectors. -/
theorem quotient_kernels (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (i j : Fin (m+1)) :
    let φ := Ideal.Quotient.mkₐ R (incidenceIdeal A i j)
    (fun k => φ (leftVariable k)) ᵥ* A.map (algebraMap R (IncidenceRing A i j)) = 0 ∧
      A.map (algebraMap R (IncidenceRing A i j)) *ᵥ (fun k => φ (rightVariable k)) = 0 ∧
      φ (leftVariable j) = 1 ∧ φ (rightVariable i) = 1 := by
  apply (incidenceIdeal_le_ker_iff A i j _).mp
  intro f hf
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hf

/-- Normalization itself forces the determinant to vanish in the incidence
quotient; no determinant equation has been inserted into its ideal. -/
theorem determinant_zero (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (i j : Fin (m+1)) : algebraMap R (IncidenceRing A i j) A.det = 0 := by
  obtain ⟨hu, hv, huj, hvi⟩ := quotient_kernels A i j
  have h := det_eq_zero_of_normalized_right_kernel
    (A.map (algebraMap R (IncidenceRing A i j)))
    (fun k => Ideal.Quotient.mk (incidenceIdeal A i j) (rightVariable k)) i hvi hv
  change ((algebraMap R (IncidenceRing A i j)).mapMatrix A).det = 0 at h
  rw [← RingHom.map_det] at h
  exact h

/-- The determinant quotient has a canonical map into the actual incidence
quotient. -/
def determinantToIncidence (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (i j : Fin (m+1)) : DeterminantRing A →ₐ[R] IncidenceRing A i j :=
  Ideal.Quotient.liftₐ (Ideal.span {A.det}) (Algebra.ofId R (IncidenceRing A i j))
    (by
      have hk : Ideal.span {A.det} ≤ RingHom.ker
          (Algebra.ofId R (IncidenceRing A i j)) := by
        apply Ideal.span_le.mpr
        intro r hr
        rcases Set.mem_singleton_iff.mp hr with rfl
        exact determinant_zero A i j
      exact fun r hr => hk hr)

/-- A unit cofactor remains a unit after any scalar extension. -/
theorem map_cofactor_unit {S : Type*} [CommRing S] [Algebra R S]
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (ha : IsUnit (A.adjugate i j)) :
    IsUnit ((A.map (algebraMap R S)).adjugate i j) := by
  have hh := (algebraMap R S).map_adjugate A
  change IsUnit (((algebraMap R S).mapMatrix A).adjugate i j)
  rw [← hh]
  exact ha.map (algebraMap R S)

/-- Two algebra maps from the incidence quotient necessarily agree at a unit
cofactor: their normalized kernel vectors are forced to be identical. -/
theorem incidence_hom_ext {S : Type*} [CommRing S] [Algebra R S]
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (ha : IsUnit (A.adjugate i j))
    (f g : IncidenceRing A i j →ₐ[R] S) : f = g := by
  let φ := Ideal.Quotient.mkₐ R (incidenceIdeal A i j)
  have hf := (incidenceIdeal_le_ker_iff A i j (f.comp φ)).mp (by
    intro a ha
    change f (φ a) = 0
    rw [show φ a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero])
  have hg := (incidenceIdeal_le_ker_iff A i j (g.comp φ)).mp (by
    intro a ha
    change g (φ a) = 0
    rw [show φ a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero])
  have hdet : (A.map (algebraMap R S)).det = 0 :=
    det_eq_zero_of_normalized_right_kernel _ _ i hf.2.2.2 hf.2.1
  obtain ⟨u, v, hu, hv, huA, hAv, hright, hleft, hadj⟩ :=
    kernel_lines_and_adjugate_factorization_of_unit (A.map (algebraMap R S)) i j
      hdet (map_cofactor_unit A i j ha)
  have hu' : (fun k => (f.comp φ) (leftVariable k)) =
      (fun k => (g.comp φ) (leftVariable k)) := by
    rw [hleft _ hf.1, hleft _ hg.1, hf.2.2.1, hg.2.2.1]
  have hv' : (fun k => (f.comp φ) (rightVariable k)) =
      (fun k => (g.comp φ) (rightVariable k)) := by
    rw [hright _ hf.2.1, hright _ hg.2.1, hf.2.2.2, hg.2.2.2]
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro k
  cases k with
  | inl k => exact congrFun hu' k
  | inr k => exact congrFun hv' k


/-- Existence of an actual map to the determinant quotient follows from the
normalized adjugate kernel vectors in that quotient. -/
theorem exists_incidenceToDeterminant
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (ha : IsUnit (A.adjugate i j)) :
    Nonempty (IncidenceRing A i j →ₐ[R] DeterminantRing A) := by
  have hdet : (A.map (algebraMap R (DeterminantRing A))).det = 0 := by
    change ((algebraMap R (DeterminantRing A)).mapMatrix A).det = 0
    rw [← RingHom.map_det]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self A.det)
  obtain ⟨u, v, hu, hv, huA, hAv, _, _, _⟩ :=
    kernel_lines_and_adjugate_factorization_of_unit (A.map (algebraMap R (DeterminantRing A)))
      i j hdet (map_cofactor_unit A i j ha)
  let ψ : Polynomials R m →ₐ[R] DeterminantRing A := aeval (Sum.elim u v)
  have hk : incidenceIdeal A i j ≤ RingHom.ker ψ := by
    apply (incidenceIdeal_le_ker_iff A i j ψ).mpr
    simpa only [ψ, leftVariable, rightVariable, aeval_X, Sum.elim_inl, Sum.elim_inr]
      using And.intro huA (And.intro hAv (And.intro hu hv))
  exact ⟨Ideal.Quotient.liftₐ (incidenceIdeal A i j) ψ (fun r hr => hk hr)⟩

/-- Canonical inverse to the base-ring map at a unit cofactor. Its defining
existence proof supplies actual normalized kernels in `R/(det A)`. -/
def incidenceToDeterminant
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (ha : IsUnit (A.adjugate i j)) : IncidenceRing A i j →ₐ[R] DeterminantRing A :=
  Classical.choice (exists_incidenceToDeterminant A i j ha)

/-- Algebra maps from a quotient of the base ring are uniquely determined. -/
theorem determinant_hom_ext {S : Type*} [CommRing S] [Algebra R S]
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (f g : DeterminantRing A →ₐ[R] S) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.ext
  intro r
  change f (algebraMap R (DeterminantRing A) r) =
    g (algebraMap R (DeterminantRing A) r)
  rw [f.commutes, g.commutes]

/-- Scheme-theoretic equality: adjoining both normalized kernel vectors at a
unit cofactor gives exactly the determinant quotient, including nilpotents. -/
def incidenceEquivDeterminant
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (ha : IsUnit (A.adjugate i j)) : IncidenceRing A i j ≃ₐ[R] DeterminantRing A :=
  AlgEquiv.ofAlgHom (incidenceToDeterminant A i j ha) (determinantToIncidence A i j)
    (determinant_hom_ext A _ _) (incidence_hom_ext A i j ha _ _)


/-- The literal bilinear polar equation in the two kernel-variable blocks. -/
def polarEquation (H : Matrix (Fin (m+1)) (Fin (m+1)) R) : Polynomials R m :=
  ∑ k, ∑ l, leftVariable k * C (H k l) * rightVariable l

/-- In the actual incidence ring, the determinant polar is a unit multiple
of the literal bilinear kernel polar. -/
theorem quotient_polar_identity
    (A H : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (ha : IsUnit (A.adjugate i j)) :
    algebraMap R (IncidenceRing A i j) (Matrix.trace (A.adjugate * H)) =
      algebraMap R (IncidenceRing A i j) (A.adjugate i j) *
        Ideal.Quotient.mk (incidenceIdeal A i j) (polarEquation H) := by
  let φ := Ideal.Quotient.mkₐ R (incidenceIdeal A i j)
  let ψ := algebraMap R (IncidenceRing A i j)
  obtain ⟨hu, hv, huj, hvi⟩ := quotient_kernels A i j
  have hadj := adjugate_factorization_of_unit_cofactor (A.map ψ) i j
    (fun k => φ (leftVariable k)) (fun k => φ (rightVariable k)) huj hvi hu hv
    (map_cofactor_unit A i j ha)
  have h := adjugate_trace_pairing (A.map ψ) (H.map ψ)
    (fun k => φ (leftVariable k)) (fun k => φ (rightVariable k)) _ hadj
  have htrace : Matrix.trace ((A.map ψ).adjugate * H.map ψ) =
      ψ (Matrix.trace (A.adjugate * H)) := by
    have hm := ψ.map_adjugate A
    change ψ.mapMatrix A.adjugate = (A.map ψ).adjugate at hm
    rw [← hm]
    simp only [RingHom.mapMatrix_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.map_apply, map_sum, map_mul]
  rw [htrace] at h
  have hα : (A.map ψ).adjugate i j = ψ (A.adjugate i j) := by
    exact (congrArg (fun N : Matrix (Fin (m+1)) (Fin (m+1)) (IncidenceRing A i j) => N i j)
      (ψ.map_adjugate A)).symm
  rw [hα] at h
  convert h using 1
  simp only [polarEquation, map_sum, map_mul, ← MvPolynomial.algebraMap_eq,
    Ideal.Quotient.mk_algebraMap, dotProduct, Matrix.mulVec, Matrix.map_apply,
    Finset.mul_sum, mul_assoc, φ, ψ]
  rfl

/-- The two principal polar ideals agree exactly after the graph
identification. This is an ideal equality, not only vanishing-set equality. -/
theorem polar_span_map
    (A H : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (ha : IsUnit (A.adjugate i j)) :
    (Ideal.span {Ideal.Quotient.mk (incidenceIdeal A i j) (polarEquation H)}).map
        (incidenceEquivDeterminant A i j ha).toRingHom =
      Ideal.span {algebraMap R (DeterminantRing A) (Matrix.trace (A.adjugate * H))} := by
  rw [Ideal.map_span, Set.image_singleton]
  have h := congrArg (incidenceEquivDeterminant A i j ha) (quotient_polar_identity A H i j ha)
  simp only [map_mul, AlgEquiv.commutes] at h
  rw [h, Ideal.span_singleton_mul_left_unit (ha.map (algebraMap R (DeterminantRing A)))]
  rfl

/-- Arbitrary additional base equations are carried to precisely their
extension in the determinant quotient. -/
theorem baseIdeal_map
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (ha : IsUnit (A.adjugate i j)) (J : Ideal R) :
    (J.map (algebraMap R (IncidenceRing A i j))).map
      (incidenceEquivDeterminant A i j ha).toRingHom =
        J.map (algebraMap R (DeterminantRing A)) := by
  rw [Ideal.map_map]
  congr 1
  ext r
  exact (incidenceEquivDeterminant A i j ha).commutes r

/-- Adding any collection of polar equations and any base ideal preserves the
actual quotient-algebra identification, including all intersection lengths. -/
def cutIncidenceEquivDeterminant {E : Type*}
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i j : Fin (m+1))
    (ha : IsUnit (A.adjugate i j)) (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R)
    (J : Ideal R) :
    (IncidenceRing A i j ⧸
      (J.map (algebraMap R (IncidenceRing A i j)) ⊔
        ⨆ e, Ideal.span {Ideal.Quotient.mk (incidenceIdeal A i j) (polarEquation (H e))}))
      ≃ₐ[R]
    (DeterminantRing A ⧸
      (J.map (algebraMap R (DeterminantRing A)) ⊔
        ⨆ e, Ideal.span {algebraMap R (DeterminantRing A) (Matrix.trace (A.adjugate * H e))})) :=
  Ideal.quotientEquivAlg _ _ (incidenceEquivDeterminant A i j ha) (by
    rw [Ideal.map_sup, Ideal.map_iSup]
    apply congrArg₂ (· ⊔ ·)
    · exact (baseIdeal_map A i j ha J).symm
    · exact iSup_congr fun e => (polar_span_map A (H e) i j ha).symm)

end Sheshadri.KernelIncidenceAlgebra
