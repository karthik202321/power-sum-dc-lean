/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.Ring

/-!
# Algebraic Jacobi identity

The determinant differential is proved for an arbitrary algebraic derivation.
Thus polynomial partial derivatives are included without an analytic or
geometric axiom. The adjugate pairing lemma describes the conormal identity
once the kernel-line factorization of the adjugate is supplied.
-/

namespace Sheshadri

open Matrix
open scoped BigOperators

section Derivation

variable {K R ι : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable [DecidableEq ι]

/-- The finite product rule for a derivation with values in its source ring. -/
theorem derivation_prod (D : Derivation K R R) (s : Finset ι) (f : ι → R) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, D (f i) * ∏ j ∈ s.erase i, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih, Finset.sum_insert ha]
    simp only [smul_eq_mul, Finset.erase_insert ha]
    have hterm : ∀ i ∈ s,
        D (f i) * ∏ j ∈ (insert a s).erase i, f j =
          f a * (D (f i) * ∏ j ∈ s.erase i, f j) := by
      intro i hi
      have hai : a ≠ i := by intro h; subst i; exact ha hi
      rw [Finset.erase_insert_of_ne hai, Finset.prod_insert]
      · ring
      · exact fun h => ha (Finset.mem_of_mem_erase h)
    have hs : (∑ i ∈ s, D (f i) * ∏ j ∈ (insert a s).erase i, f j) =
        f a * ∑ i ∈ s, D (f i) * ∏ j ∈ s.erase i, f j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i hi
    rw [hs]
    ring

variable [Fintype ι]

/-- Differentiating the determinant replaces each column once. -/
theorem derivation_det_columns (D : Derivation K R R) (A : Matrix ι ι R) :
    D A.det = ∑ j, (A.updateCol j (fun i => D (A i j))).det := by
  classical
  simp only [Matrix.det_apply', map_sum, D.leibniz, D.map_intCast, smul_eq_mul,
    mul_zero, add_zero, derivation_prod]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro σ hσ
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ
    (fun i => (A.updateCol j (fun k => D (A k j))) (σ i) i) (Finset.mem_univ j)]
  simp only [Matrix.updateCol_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hi)]

/-- Jacobi's formula for an arbitrary algebraic derivation. -/
theorem derivation_det (D : Derivation K R R) (A : Matrix ι ι R) :
    D A.det = Matrix.trace (A.adjugate * A.map D) := by
  rw [derivation_det_columns D A]
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

/-- A nonzero determinant differential forces a nonzero adjugate. -/
theorem adjugate_ne_zero_of_derivation_det_ne_zero
    (D : Derivation K R R) (A : Matrix ι ι R) (h : D A.det ≠ 0) :
    A.adjugate ≠ 0 := by
  intro hzero
  apply h
  rw [derivation_det D A, hzero, Matrix.zero_mul, Matrix.trace_zero]

/-- Some cofactor is nonzero at any point with a nonzero determinant
differential. Turning this into a rank statement is a separate linear-algebra
step; the adjugate here is the actual matrix adjugate. -/
theorem exists_adjugate_entry_ne_zero
    (D : Derivation K R R) (A : Matrix ι ι R) (h : D A.det ≠ 0) :
    ∃ i j, A.adjugate i j ≠ 0 := by
  by_contra! hall
  apply adjugate_ne_zero_of_derivation_det_ne_zero D A h
  ext i j
  exact hall i j

/-- Jacobi's formula after evaluation, e.g. at a point of affine space. -/
theorem derivation_det_eval {S : Type*} [CommRing S]
    (D : Derivation K R R) (A : Matrix ι ι R) (φ : R →+* S) :
    φ (D A.det) =
      Matrix.trace ((A.map φ).adjugate * A.map (fun x => φ (D x))) := by
  rw [derivation_det D A, AddMonoidHom.map_trace]
  change Matrix.trace ((A.adjugate * A.map D).map φ) = _
  have hadj : A.adjugate.map φ = (A.map φ).adjugate := φ.map_adjugate A
  rw [Matrix.map_mul, hadj]
  rfl

/-- At a point where a determinant derivative is nonzero, an actual
cofactor of the evaluated matrix is nonzero. -/
theorem exists_adjugate_entry_ne_zero_eval {S : Type*} [CommRing S]
    (D : Derivation K R R) (A : Matrix ι ι R) (φ : R →+* S)
    (h : φ (D A.det) ≠ 0) :
    ∃ i j, (A.map φ).adjugate i j ≠ 0 := by
  by_contra! hall
  have hzero : (A.map φ).adjugate = 0 := by ext i j; exact hall i j
  apply h
  rw [derivation_det_eval D A φ, hzero, Matrix.zero_mul, Matrix.trace_zero]

/-- The nonvanishing differential supplies a nonzero minor of size m-1,
which is the concrete input needed to choose the Schur chart. -/
theorem exists_minor_ne_zero_eval {S : Type*} [CommRing S] {m : ℕ}
    (D : Derivation K R R) (A : Matrix (Fin (m+1)) (Fin (m+1)) R)
    (φ : R →+* S) (h : φ (D A.det) ≠ 0) :
    ∃ i j : Fin (m+1), ((A.map φ).submatrix j.succAbove i.succAbove).det ≠ 0 := by
  obtain ⟨i, j, hij⟩ := exists_adjugate_entry_ne_zero_eval D A φ h
  refine ⟨i, j, ?_⟩
  intro hz
  apply hij
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, hz, mul_zero]

/-- The actual formal partial derivative of a polynomial determinant. -/
theorem pderiv_det {σ : Type*} (x : σ) (A : Matrix ι ι (MvPolynomial σ R)) :
    MvPolynomial.pderiv x A.det =
      Matrix.trace (A.adjugate * A.map (MvPolynomial.pderiv x)) :=
  derivation_det (MvPolynomial.pderiv x) A

end Derivation

section Pairing

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- The trace of a rank-one matrix times a matrix is the kernel pairing. -/
theorem trace_outer_mul (v u : ι → R) (H : Matrix ι ι R) :
    Matrix.trace (vecMulVec v u * H) = u ⬝ᵥ (H *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.vecMulVec, Matrix.of_apply, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

variable [DecidableEq ι]

/-- The conormal pairing follows from actual adjugate factorization. -/
theorem adjugate_trace_pairing (A H : Matrix ι ι R) (u v : ι → R) (a : R)
    (hadj : A.adjugate = a • vecMulVec v u) :
    Matrix.trace (A.adjugate * H) = a * (u ⬝ᵥ (H *ᵥ v)) := by
  rw [hadj, Matrix.smul_mul, Matrix.trace_smul, trace_outer_mul]
  rfl

/-- Kernel lines force the actual adjugate to be a rank-one outer product.
The scalar is its pivot entry. Normalized kernel generators and the
one-dimensional kernel descriptions are explicit linear-algebra hypotheses.
-/
theorem adjugate_factorization_of_kernel_lines
    (A : Matrix ι ι R) (u v : ι → R) (i₀ j₀ : ι)
    (hdet : A.det = 0) (hv : v i₀ = 1) (hu : u j₀ = 1)
    (hker : ∀ w : ι → R, A *ᵥ w = 0 → ∃ a : R, w = a • v)
    (hleft : ∀ w : ι → R, w ᵥ* A = 0 → ∃ a : R, w = a • u) :
    A.adjugate = A.adjugate i₀ j₀ • vecMulVec v u := by
  have hcol (j : ι) : A *ᵥ (fun i => A.adjugate i j) = 0 := by
    ext i
    have h := congrArg (fun M : Matrix ι ι R => M i j) (Matrix.mul_adjugate A)
    simpa only [hdet, zero_smul, Matrix.zero_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Pi.zero_apply] using h
  have hrow : (fun j => A.adjugate i₀ j) ᵥ* A = 0 := by
    ext j
    have h := congrArg (fun M : Matrix ι ι R => M i₀ j) (Matrix.adjugate_mul A)
    simpa only [hdet, zero_smul, Matrix.zero_apply, Matrix.mul_apply,
      Matrix.vecMul, dotProduct, Pi.zero_apply] using h
  obtain ⟨a, ha⟩ := hleft _ hrow
  have hpivot : A.adjugate i₀ j₀ = a := by
    have h := congrFun ha j₀
    simpa only [Pi.smul_apply, smul_eq_mul, hu, mul_one] using h
  ext i j
  obtain ⟨b, hb⟩ := hker _ (hcol j)
  have hbi : A.adjugate i j = b * v i := by
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hb i
  have hb₀ : A.adjugate i₀ j = b := by
    simpa only [Pi.smul_apply, smul_eq_mul, hv, mul_one] using congrFun hb i₀
  have haj : A.adjugate i₀ j = a * u j := by
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun ha j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec, Matrix.of_apply]
  rw [hbi, ← hb₀, haj, hpivot]
  ring

end Pairing

section Conormal

variable {K R S ι : Type*} [CommRing K] [CommRing R] [Algebra K R]
  [CommRing S] [Fintype ι] [DecidableEq ι]

/-- The evaluated conormal identity, with Jacobi's formula discharged. -/
theorem derivation_det_eval_pairing
    (D : Derivation K R R) (A : Matrix ι ι R) (φ : R →+* S)
    (u v : ι → S) (a : S)
    (hadj : (A.map φ).adjugate = a • vecMulVec v u) :
    φ (D A.det) = a * (u ⬝ᵥ (A.map (fun x => φ (D x)) *ᵥ v)) := by
  rw [derivation_det_eval D A φ]
  exact adjugate_trace_pairing (A.map φ) _ u v a hadj

/-- At a smooth determinant point, neither the adjugate scalar nor the
corresponding kernel pairing can vanish. -/
theorem scalar_and_pairing_ne_zero
    (D : Derivation K R R) (A : Matrix ι ι R) (φ : R →+* S)
    (u v : ι → S) (a : S)
    (hadj : (A.map φ).adjugate = a • vecMulVec v u)
    (h : φ (D A.det) ≠ 0) :
    a ≠ 0 ∧ u ⬝ᵥ (A.map (fun x => φ (D x)) *ᵥ v) ≠ 0 := by
  have heq := derivation_det_eval_pairing D A φ u v a hadj
  constructor
  · intro hz
    apply h
    rw [heq, hz, zero_mul]
  · intro hz
    apply h
    rw [heq, hz, mul_zero]

end Conormal

end Sheshadri
