/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.KernelIncidenceAlgebra

/-!
# The actual symmetric normalized-kernel incidence algebra

At a unit diagonal cofactor, adjoining one normalized kernel vector gives
exactly the determinant quotient over any commutative ring. For symmetric
matrices this one vector serves as both kernels; the literal quadratic polar
equations therefore correspond to determinant polars up to a unit. All maps
and arbitrary further cut ideals are scheme-theoretic, retaining nilpotents.
-/

noncomputable section
namespace Sheshadri.SymmetricKernelIncidenceAlgebra
open Matrix MvPolynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] {m : ℕ}

abbrev Polynomials (R : Type*) [CommRing R] (m : ℕ) := MvPolynomial (Fin (m+1)) R

def kernelEquation (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (l : Fin (m+1)) :
    Polynomials R m := ∑ k, C (A l k) * X k

def incidenceIdeal (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1)) :
    Ideal (Polynomials R m) :=
  Ideal.span (Set.range (kernelEquation A)) ⊔ Ideal.span {X i - 1}

abbrev IncidenceRing (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1)) :=
  Polynomials R m ⧸ incidenceIdeal A i

abbrev DeterminantRing (A : Matrix (Fin (m+1)) (Fin (m+1)) R) :=
  KernelIncidenceAlgebra.DeterminantRing A

theorem incidenceIdeal_le_ker_iff {S : Type*} [CommRing S] [Algebra R S]
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1))
    (φ : Polynomials R m →ₐ[R] S) :
    incidenceIdeal A i ≤ RingHom.ker φ ↔
      A.map (algebraMap R S) *ᵥ (fun k => φ (X k)) = 0 ∧ φ (X i) = 1 := by
  simp only [incidenceIdeal, sup_le_iff, Ideal.span_le, Set.range_subset_iff,
    Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, kernelEquation,
    map_sum, map_mul, map_sub, map_one, sub_eq_zero,
    ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  simp only [funext_iff, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply]

theorem quotient_kernel (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1)) :
    let φ := Ideal.Quotient.mkₐ R (incidenceIdeal A i)
    A.map (algebraMap R (IncidenceRing A i)) *ᵥ (fun k => φ (X k)) = 0 ∧ φ (X i) = 1 := by
  apply (incidenceIdeal_le_ker_iff A i _).mp
  intro f hf
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hf

/-- Normalization forces the determinant equation; it is not inserted
as an extra generator of the incidence ideal. -/
theorem determinant_zero (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1)) :
    algebraMap R (IncidenceRing A i) A.det = 0 := by
  obtain ⟨hu, hui⟩ := quotient_kernel A i
  have h := det_eq_zero_of_normalized_right_kernel
    (A.map (algebraMap R (IncidenceRing A i)))
    (fun k => Ideal.Quotient.mk (incidenceIdeal A i) (X k)) i hui hu
  change ((algebraMap R (IncidenceRing A i)).mapMatrix A).det = 0 at h
  rwa [← RingHom.map_det] at h

def determinantToIncidence (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1)) :
    DeterminantRing A →ₐ[R] IncidenceRing A i :=
  Ideal.Quotient.liftₐ (Ideal.span {A.det}) (Algebra.ofId R (IncidenceRing A i))
    (by
      have hk : Ideal.span {A.det} ≤ RingHom.ker (Algebra.ofId R (IncidenceRing A i)) := by
        apply Ideal.span_le.mpr
        intro r hr
        rcases Set.mem_singleton_iff.mp hr with rfl
        exact determinant_zero A i
      exact fun r hr => hk hr)

theorem incidence_hom_ext {S : Type*} [CommRing S] [Algebra R S]
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1))
    (ha : IsUnit (A.adjugate i i)) (f g : IncidenceRing A i →ₐ[R] S) : f = g := by
  let φ := Ideal.Quotient.mkₐ R (incidenceIdeal A i)
  have hf := (incidenceIdeal_le_ker_iff A i (f.comp φ)).mp (by
    intro a ha
    change f (φ a) = 0
    rw [show φ a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero])
  have hg := (incidenceIdeal_le_ker_iff A i (g.comp φ)).mp (by
    intro a ha
    change g (φ a) = 0
    rw [show φ a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero])
  have hdet : (A.map (algebraMap R S)).det = 0 :=
    det_eq_zero_of_normalized_right_kernel _ _ i hf.2 hf.1
  obtain ⟨u, v, hu, hv, huA, hAv, hright, hleft, hadj⟩ :=
    kernel_lines_and_adjugate_factorization_of_unit (A.map (algebraMap R S)) i i
      hdet (KernelIncidenceAlgebra.map_cofactor_unit A i i ha)
  have hv' : (fun k => (f.comp φ) (X k)) = (fun k => (g.comp φ) (X k)) := by
    rw [hright _ hf.1, hright _ hg.1, hf.2, hg.2]
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro k
  exact congrFun hv' k

theorem exists_incidenceToDeterminant
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1))
    (ha : IsUnit (A.adjugate i i)) :
    Nonempty (IncidenceRing A i →ₐ[R] DeterminantRing A) := by
  have hdet : (A.map (algebraMap R (DeterminantRing A))).det = 0 := by
    change ((algebraMap R (DeterminantRing A)).mapMatrix A).det = 0
    rw [← RingHom.map_det]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self A.det)
  obtain ⟨u, v, hu, hv, huA, hAv, _, _, _⟩ :=
    kernel_lines_and_adjugate_factorization_of_unit (A.map (algebraMap R (DeterminantRing A)))
      i i hdet (KernelIncidenceAlgebra.map_cofactor_unit A i i ha)
  let ψ : Polynomials R m →ₐ[R] DeterminantRing A := aeval v
  have hk : incidenceIdeal A i ≤ RingHom.ker ψ := by
    apply (incidenceIdeal_le_ker_iff A i ψ).mpr
    simpa only [ψ, aeval_X] using And.intro hAv hv
  exact ⟨Ideal.Quotient.liftₐ (incidenceIdeal A i) ψ (fun r hr => hk hr)⟩

def incidenceToDeterminant
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1))
    (ha : IsUnit (A.adjugate i i)) : IncidenceRing A i →ₐ[R] DeterminantRing A :=
  Classical.choice (exists_incidenceToDeterminant A i ha)

/-- The literal one-vector normalized-kernel equation algebra is the
determinant quotient, with every nilpotent preserved. -/
def incidenceEquivDeterminant
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1))
    (ha : IsUnit (A.adjugate i i)) : IncidenceRing A i ≃ₐ[R] DeterminantRing A :=
  AlgEquiv.ofAlgHom (incidenceToDeterminant A i ha) (determinantToIncidence A i)
    (KernelIncidenceAlgebra.determinant_hom_ext A _ _) (incidence_hom_ext A i ha _ _)

/-- The native symmetric quadratic polar, with one kernel-variable block. -/
def polarEquation (H : Matrix (Fin (m+1)) (Fin (m+1)) R) : Polynomials R m :=
  ∑ k, ∑ l, X k * C (H k l) * X l

theorem quotient_polar_identity
    (A H : Matrix (Fin (m+1)) (Fin (m+1)) R) (hA : A.transpose = A)
    (i : Fin (m+1)) (ha : IsUnit (A.adjugate i i)) :
    algebraMap R (IncidenceRing A i) (Matrix.trace (A.adjugate * H)) =
      algebraMap R (IncidenceRing A i) (A.adjugate i i) *
        Ideal.Quotient.mk (incidenceIdeal A i) (polarEquation H) := by
  let φ := Ideal.Quotient.mkₐ R (incidenceIdeal A i)
  let ψ := algebraMap R (IncidenceRing A i)
  obtain ⟨hu, hui⟩ := quotient_kernel A i
  have hsym : (A.map ψ).transpose = A.map ψ := by
    rw [← Matrix.transpose_map, hA]
  have hu' : (fun k => φ (X k)) ᵥ* A.map ψ = 0 := by
    rw [← hsym, Matrix.vecMul_transpose]
    exact hu
  have hadj := adjugate_factorization_of_unit_cofactor (A.map ψ) i i
    (fun k => φ (X k)) (fun k => φ (X k)) hui hui hu' hu
    (KernelIncidenceAlgebra.map_cofactor_unit A i i ha)
  have h := adjugate_trace_pairing (A.map ψ) (H.map ψ)
    (fun k => φ (X k)) (fun k => φ (X k)) _ hadj
  have htrace : Matrix.trace ((A.map ψ).adjugate * H.map ψ) =
      ψ (Matrix.trace (A.adjugate * H)) := by
    have hm := ψ.map_adjugate A
    change ψ.mapMatrix A.adjugate = (A.map ψ).adjugate at hm
    rw [← hm]
    simp only [RingHom.mapMatrix_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.map_apply, map_sum, map_mul]
  rw [htrace] at h
  have hα : (A.map ψ).adjugate i i = ψ (A.adjugate i i) := by
    exact (congrArg (fun N : Matrix (Fin (m+1)) (Fin (m+1)) (IncidenceRing A i) => N i i)
      (ψ.map_adjugate A)).symm
  rw [hα] at h
  convert h using 1
  simp only [polarEquation, map_sum, map_mul, ← MvPolynomial.algebraMap_eq,
    Ideal.Quotient.mk_algebraMap, dotProduct, Matrix.mulVec, Matrix.map_apply,
    Finset.mul_sum, mul_assoc, φ, ψ]
  rfl

theorem polar_span_map
    (A H : Matrix (Fin (m+1)) (Fin (m+1)) R) (hA : A.transpose = A)
    (i : Fin (m+1)) (ha : IsUnit (A.adjugate i i)) :
    (Ideal.span {Ideal.Quotient.mk (incidenceIdeal A i) (polarEquation H)}).map
        (incidenceEquivDeterminant A i ha).toRingHom =
      Ideal.span {algebraMap R (DeterminantRing A) (Matrix.trace (A.adjugate * H))} := by
  rw [Ideal.map_span, Set.image_singleton]
  have h := congrArg (incidenceEquivDeterminant A i ha) (quotient_polar_identity A H hA i ha)
  simp only [map_mul, AlgEquiv.commutes] at h
  rw [h, Ideal.span_singleton_mul_left_unit (ha.map (algebraMap R (DeterminantRing A)))]
  rfl

theorem baseIdeal_map
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (i : Fin (m+1))
    (ha : IsUnit (A.adjugate i i)) (J : Ideal R) :
    (J.map (algebraMap R (IncidenceRing A i))).map
      (incidenceEquivDeterminant A i ha).toRingHom =
        J.map (algebraMap R (DeterminantRing A)) := by
  rw [Ideal.map_map]
  congr 1
  ext r
  exact (incidenceEquivDeterminant A i ha).commutes r

/-- Arbitrary native quadratic polar cuts and arbitrary base equations
preserve the actual determinant-quotient algebra identification. -/
def cutIncidenceEquivDeterminant {E : Type*}
    (A : Matrix (Fin (m+1)) (Fin (m+1)) R) (hA : A.transpose = A)
    (i : Fin (m+1)) (ha : IsUnit (A.adjugate i i))
    (H : E → Matrix (Fin (m+1)) (Fin (m+1)) R) (J : Ideal R) :
    (IncidenceRing A i ⧸
      (J.map (algebraMap R (IncidenceRing A i)) ⊔
        ⨆ e, Ideal.span {Ideal.Quotient.mk (incidenceIdeal A i) (polarEquation (H e))}))
      ≃ₐ[R]
    (DeterminantRing A ⧸
      (J.map (algebraMap R (DeterminantRing A)) ⊔
        ⨆ e, Ideal.span {algebraMap R (DeterminantRing A) (Matrix.trace (A.adjugate * H e))})) :=
  Ideal.quotientEquivAlg _ _ (incidenceEquivDeterminant A i ha) (by
    rw [Ideal.map_sup, Ideal.map_iSup]
    apply congrArg₂ (· ⊔ ·)
    · exact (baseIdeal_map A i ha J).symm
    · exact iSup_congr fun e => (polar_span_map A (H e) hA i ha).symm)

end Sheshadri.SymmetricKernelIncidenceAlgebra
