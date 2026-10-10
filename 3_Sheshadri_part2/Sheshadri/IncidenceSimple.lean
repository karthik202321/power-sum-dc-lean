/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.TangentEvaluation
import Sheshadri.KernelLines
import Sheshadri.PolynomialModel

/-! Actual first-order incidence elimination and simple projective zeros.
The conormal comparison is proved over dual numbers. No transversality of
the incidence itself is assumed. -/

noncomputable section
namespace Sheshadri.IncidenceSimple

open Matrix MvPolynomial Incidence IncidenceDifferential MultiProjective
open PolynomialModel TangentEvaluation
open scoped BigOperators Matrix

variable {n m : ℕ}

def dualVector {ι : Type*} (v dv : ι → ℂ) : ι → DualNumber ℂ :=
  fun i => ⟨v i, dv i⟩

def dualMatrix {ι κ : Type*} (A D : Matrix ι κ ℂ) : Matrix ι κ (DualNumber ℂ) :=
  fun i j => ⟨A i j, D i j⟩

theorem left_tangent_pairing_zero {ι : Type*} [Fintype ι]
    (A D : Matrix ι ι ℂ) (u v du : ι → ℂ)
    (hAv : A *ᵥ v = 0) (hl : du ᵥ* A + u ᵥ* D = 0) :
    u ⬝ᵥ (D *ᵥ v) = 0 := by
  have h := congrArg (fun w => w ⬝ᵥ v) hl
  simpa only [add_dotProduct, ← dotProduct_mulVec, hAv,
    dotProduct_zero, zero_dotProduct, zero_add] using h

theorem full_right_tangent {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A D : Matrix ι ι ℂ) (L : Matrix κ ι ℂ) (u v du dv : ι → ℂ)
    (huA : u ᵥ* A = 0) (hAv : A *ᵥ v = 0)
    (hL : ∀ z, u ⬝ᵥ z = 0 → L *ᵥ z = 0 → z = 0)
    (hl : du ᵥ* A + u ᵥ* D = 0)
    (hr : L *ᵥ (D *ᵥ v + A *ᵥ dv) = 0) : D *ᵥ v + A *ᵥ dv = 0 := by
  apply hL _ _ hr
  rw [dotProduct_add, left_tangent_pairing_zero A D u v du hAv hl,
    dotProduct_mulVec, huA, zero_dotProduct, add_zero]

theorem dual_left_kernel {ι : Type*} [Fintype ι]
    (A D : Matrix ι ι ℂ) (u du : ι → ℂ)
    (huA : u ᵥ* A = 0) (hl : du ᵥ* A + u ᵥ* D = 0) :
    dualVector u du ᵥ* dualMatrix A D = 0 := by
  funext j
  apply TrivSqZeroExt.ext
  · simpa only [vecMul, dotProduct, dualVector, dualMatrix,
      TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul] using congrFun huA j
  · simpa only [vecMul, dotProduct, dualVector, dualMatrix,
      TrivSqZeroExt.snd_sum, DualNumber.snd_mul, Finset.sum_add_distrib,
      Pi.add_apply, Pi.zero_apply, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk,
      TrivSqZeroExt.snd_zero,
      add_comm] using congrFun hl j

theorem dual_right_kernel {ι : Type*} [Fintype ι]
    (A D : Matrix ι ι ℂ) (v dv : ι → ℂ)
    (hAv : A *ᵥ v = 0) (hr : D *ᵥ v + A *ᵥ dv = 0) :
    dualMatrix A D *ᵥ dualVector v dv = 0 := by
  funext j
  apply TrivSqZeroExt.ext
  · simpa only [mulVec, dotProduct, dualVector, dualMatrix,
      TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul] using congrFun hAv j
  · simpa only [mulVec, dotProduct, dualVector, dualMatrix,
      TrivSqZeroExt.snd_sum, DualNumber.snd_mul, Finset.sum_add_distrib,
      Pi.add_apply, Pi.zero_apply, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk,
      TrivSqZeroExt.snd_zero,
      add_comm] using congrFun hr j

theorem dual_cofactor_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A D : Matrix ι ι ℂ) (i j : ι) (ha : A.adjugate i j ≠ 0) :
    IsUnit ((dualMatrix A D).adjugate i j) := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  have h := congrArg (fun M : Matrix ι ι ℂ => M i j)
    ((TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.map_adjugate (dualMatrix A D))
  change ((dualMatrix A D).adjugate i j).fst = A.adjugate i j at h
  rw [h]
  exact isUnit_iff_ne_zero.mpr ha

theorem tangentEval_affinePencil (A : PencilCoefficients n m ℂ)
    (x dx : Fin (n + 1) → ℂ) (hx : x 0 = 1) (hdx : dx 0 = 0) :
    (affinePencil A).map (tangentEval (fun i => x i.succ) (fun i => dx i.succ)) =
      dualMatrix (pencil A x) (pencil A dx) := by
  apply Matrix.ext
  intro a b
  apply TrivSqZeroExt.ext
  · exact congrArg (fun M : Matrix (Fin m) (Fin m) ℂ => M a b)
      (eval_affinePencil A x hx)
  · simp only [Matrix.map_apply, tangentEval_snd, directional,
      pderiv_affinePencil, eval_C, dualMatrix, TrivSqZeroExt.snd_mk]
    simp only [pencil, Fin.sum_univ_succ, hdx, mul_zero, zero_add]

/-- An affine gradient flag, with its coefficients still indexed by the
homogeneous pencil. The zero-th coefficient will be required to vanish. -/
def affineGradientFlag (f : MvPolynomial (Fin n) ℂ) (ell : Fin (n + 1) → ℂ) :
    MvPolynomial (Fin n) ℂ := ∑ i : Fin n, C (ell i.succ) * pderiv i f

theorem dual_polar_zero (A : PencilCoefficients n m ℂ)
    (ell : Fin (n + 1) → ℂ) (u v du dv : Fin m → ℂ)
    (hell : ell 0 = 0)
    (hval : (∑ k, ell k * (u ⬝ᵥ (A k *ᵥ v))) = 0)
    (hder : (∑ k, ell k *
      (du ⬝ᵥ (A k *ᵥ v) + u ⬝ᵥ (A k *ᵥ dv))) = 0) :
    (∑ k : Fin n, (TrivSqZeroExt.inl (ell k.succ) : DualNumber ℂ) *
      (dualVector u du ⬝ᵥ ((A k.succ).map TrivSqZeroExt.inl *ᵥ
        dualVector v dv))) = 0 := by
  apply TrivSqZeroExt.ext
  · simpa only [TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.fst_inl, dual_pairing_fst, dualVector,
      Fin.sum_univ_succ, hell, zero_mul, zero_add] using hval
  · simpa only [TrivSqZeroExt.snd_sum, DualNumber.snd_mul,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, zero_mul, add_zero,
      dual_pairing_snd, dualVector, Fin.sum_univ_succ, hell, zero_add] using hder

/-- Differentiating the *actual* incidence implies the actual determinant
and affine gradient-flag tangent equations. The proof evaluates all
polynomials in the dual-number ring and uses the proved adjugate identity. -/
theorem incidence_tangent_implies_base_tangent
    (A : PencilCoefficients n (m + 1) ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ)
    (x dx : Fin (n + 1) → ℂ) (u v du dv : Fin (m + 1) → ℂ)
    (i j : Fin (m + 1))
    (hx : x 0 = 1) (hdx : dx 0 = 0)
    (hu : u j = 1) (hv : v i = 1) (hdu : du j = 0) (hdv : dv i = 0)
    (huA : u ᵥ* pencil A x = 0) (hAv : pencil A x *ᵥ v = 0)
    (hl : du ᵥ* pencil A x + u ᵥ* pencil A dx = 0)
    (hr : pencil A dx *ᵥ v + pencil A x *ᵥ dv = 0)
    (ha : (pencil A x).adjugate i j ≠ 0)
    (hflags0 : ∀ t, flags t 0 = 0)
    (hflags : ∀ t, (∑ k, flags t k * (u ⬝ᵥ (A k *ᵥ v))) = 0)
    (hdflags : ∀ t, (∑ k, flags t k *
      (du ⬝ᵥ (A k *ᵥ v) + u ⬝ᵥ (A k *ᵥ dv))) = 0) :
    directional (determinant A) (fun k => x k.succ) (fun k => dx k.succ) = 0 ∧
    ∀ t, directional (affineGradientFlag (determinant A) (flags t))
      (fun k => x k.succ) (fun k => dx k.succ) = 0 := by
  let φ := tangentEval (fun k : Fin n => x k.succ) (fun k : Fin n => dx k.succ)
  let E := (affinePencil A).map φ
  let U := dualVector u du
  let V := dualVector v dv
  have hE : E = dualMatrix (pencil A x) (pencil A dx) :=
    tangentEval_affinePencil A x dx hx hdx
  have hU : U j = 1 := by
    apply TrivSqZeroExt.ext
    · exact hu
    · exact hdu
  have hV : V i = 1 := by
    apply TrivSqZeroExt.ext
    · exact hv
    · exact hdv
  have hUE : U ᵥ* E = 0 := by
    rw [hE]
    exact dual_left_kernel (pencil A x) (pencil A dx) u du huA hl
  have hEV : E *ᵥ V = 0 := by
    rw [hE]
    exact dual_right_kernel (pencil A x) (pencil A dx) v dv hAv hr
  have haE : IsUnit (E.adjugate i j) := by
    rw [hE]
    exact dual_cofactor_isUnit _ _ i j ha
  have hadj := adjugate_factorization_of_unit_cofactor E i j U V hU hV hUE hEV haE
  have hdet : φ (determinant A) = 0 := by
    rw [determinant, RingHom.map_det]
    exact det_eq_zero_of_normalized_right_kernel E V i hV hEV
  refine ⟨congrArg TrivSqZeroExt.snd hdet, ?_⟩
  have hgrad (k : Fin n) : φ (pderiv k (determinant A)) =
      E.adjugate i j * (U ⬝ᵥ ((A k.succ).map TrivSqZeroExt.inl *ᵥ V)) := by
    have h := derivation_det_eval_pairing (pderiv k) (affinePencil A) φ U V
      (E.adjugate i j) hadj
    have hmat : (affinePencil A).map (fun f => φ (pderiv k f)) =
        (A k.succ).map TrivSqZeroExt.inl := by
      apply Matrix.ext
      intro a b
      simp only [Matrix.map_apply, pderiv_affinePencil, φ, tangentEval_C]
    rw [hmat] at h
    exact h
  intro t
  have hzero : (∑ k : Fin n, (TrivSqZeroExt.inl (flags t k.succ) : DualNumber ℂ) *
      (U ⬝ᵥ ((A k.succ).map TrivSqZeroExt.inl *ᵥ V))) = 0 :=
    dual_polar_zero A (flags t) u v du dv (hflags0 t) (hflags t) (hdflags t)
  have hflag : φ (affineGradientFlag (determinant A) (flags t)) = 0 := by
    simp only [affineGradientFlag, map_sum, map_mul, hgrad, φ, tangentEval_C]
    rw [show (∑ k : Fin n,
      TrivSqZeroExt.inl (flags t k.succ) *
        (E.adjugate i j * (U ⬝ᵥ ((A k.succ).map TrivSqZeroExt.inl *ᵥ V)))) =
        E.adjugate i j * ∑ k : Fin n,
          TrivSqZeroExt.inl (flags t k.succ) *
            (U ⬝ᵥ ((A k.succ).map TrivSqZeroExt.inl *ᵥ V)) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring]
    rw [hzero, mul_zero]
  exact congrArg TrivSqZeroExt.snd hflag

/-- The actual three-factor incidence has a trivial tangent kernel in its
chosen charts. The only transversality hypothesis is on the explicitly
specified base determinant/gradient-flag equations. -/
theorem ordinary_simple_in_charts
    (A : PencilCoefficients n (m + 1) ℂ)
    (L : Matrix (Fin ((m + 1) - 1)) (Fin (m + 1)) ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (x : Fin (n + 1) → ℂ) (u v : Fin (m + 1) → ℂ) (i j : Fin (m + 1))
    (hx : x 0 = 1) (hu : u j = 1) (hv : v i = 1)
    (huA : u ᵥ* pencil A x = 0) (hAv : pencil A x *ᵥ v = 0)
    (ha : (pencil A x).adjugate i j ≠ 0)
    (hL : ∀ z, u ⬝ᵥ z = 0 → L *ᵥ z = 0 → z = 0)
    (hflags0 : ∀ t, flags t 0 = 0)
    (hflags : ∀ t, (∑ k, flags t k * (u ⬝ᵥ (A k *ᵥ v))) = 0)
    (hbase : ∀ dx : Fin (n + 1) → ℂ, dx 0 = 0 →
      directional (determinant A) (fun k => x k.succ) (fun k => dx k.succ) = 0 →
      (∀ t, directional (affineGradientFlag (determinant A) (flags t))
        (fun k => x k.succ) (fun k => dx k.succ) = 0) →
      (∑ k, M k * dx k) = 0 → dx = 0) :
    SimpleInCharts (ordinarySystem A L flags M) (ordinaryAssignment x u v) := by
  refine ⟨0, j, i, ?_, ?_, ?_, ?_⟩
  · simpa only [ordinaryAssignment, hx] using (one_ne_zero : (1 : ℂ) ≠ 0)
  · simpa only [ordinaryAssignment, hu] using (one_ne_zero : (1 : ℂ) ≠ 0)
  · simpa only [ordinaryAssignment, hv] using (one_ne_zero : (1 : ℂ) ≠ 0)
  intro w hwx hwu hwv hsys
  let dx : Fin (n + 1) → ℂ := fun k => w (Sum.inl k)
  let du : Fin (m + 1) → ℂ := fun k => w (Sum.inr (Sum.inl k))
  let dv : Fin (m + 1) → ℂ := fun k => w (Sum.inr (Sum.inr k))
  have hw : ordinaryAssignment dx du dv = w := by
    funext k
    rcases k with k | (k | k) <;> rfl
  obtain ⟨hl, hr, hdflags, hM⟩ :=
    (ordinarySystem_directional_zero_iff A L flags M x dx u v du dv).mp
      (by rw [hw]; exact hsys)
  have hfull := full_right_tangent (pencil A x) (pencil A dx) L u v du dv
    huA hAv hL hl hr
  obtain ⟨hdet, hgrad⟩ := incidence_tangent_implies_base_tangent A flags x dx u v du dv
    i j hx hwx hu hv hwu hwv huA hAv hl hfull ha hflags0 hflags hdflags
  have hdx : dx = 0 := hbase dx hwx hdet hgrad hM
  have hD : pencil A dx = 0 := by
    rw [hdx]
    ext a b
    simp [pencil]
  have hduA : du ᵥ* pencil A x = 0 := by simpa only [hD, vecMul_zero, add_zero] using hl
  have hAdv : pencil A x *ᵥ dv = 0 := by simpa only [hD, zero_mulVec, zero_add] using hfull
  have hdv : dv = 0 := kernel_zero_of_minor_and_coordinate (pencil A x) i j
    (minor_ne_zero_of_adjugate_entry _ i j ha) dv hAdv hwv
  have hat : (pencil A x).transpose.adjugate j i ≠ 0 := by
    rw [← Matrix.adjugate_transpose]
    exact ha
  have hdu : du = 0 := kernel_zero_of_minor_and_coordinate (pencil A x).transpose j i
    (minor_ne_zero_of_adjugate_entry _ j i hat) du
    (by simpa only [Matrix.mulVec_transpose] using hduA) hwu
  rw [← hw, hdx, hdu, hdv]
  funext k
  rcases k with k | (k | k) <;> rfl

theorem pencil_transpose (A : PencilCoefficients n m ℂ)
    (hsym : ∀ k, (A k).transpose = A k) (x : Fin (n + 1) → ℂ) :
    (pencil A x).transpose = pencil A x := by
  ext a b
  change (∑ k, A k b a * x k) = ∑ k, A k a b * x k
  apply Finset.sum_congr rfl
  intro k _
  have h := congrArg (fun H : Matrix (Fin m) (Fin m) ℂ => H a b) (hsym k)
  exact congrArg (fun z => z * x k) h

/-- The symmetric two-factor incidence is simple in charts by the same
proved dual-number argument, without a reduction matrix. -/
theorem symmetric_simple_in_charts
    (A : PencilCoefficients n (m + 1) ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (x : Fin (n + 1) → ℂ) (v : Fin (m + 1) → ℂ) (i : Fin (m + 1))
    (hsym : ∀ k, (A k).transpose = A k)
    (hx : x 0 = 1) (hv : v i = 1) (hAv : pencil A x *ᵥ v = 0)
    (ha : (pencil A x).adjugate i i ≠ 0)
    (hflags0 : ∀ t, flags t 0 = 0)
    (hflags : ∀ t, (∑ k, flags t k * (v ⬝ᵥ (A k *ᵥ v))) = 0)
    (hbase : ∀ dx : Fin (n + 1) → ℂ, dx 0 = 0 →
      directional (determinant A) (fun k => x k.succ) (fun k => dx k.succ) = 0 →
      (∀ t, directional (affineGradientFlag (determinant A) (flags t))
        (fun k => x k.succ) (fun k => dx k.succ) = 0) →
      (∑ k, M k * dx k) = 0 → dx = 0) :
    BiSimpleInCharts (symmetricSystem A flags M) (symmetricAssignment x v) := by
  refine ⟨0, i, ?_, ?_, ?_⟩
  · simpa only [symmetricAssignment, hx] using (one_ne_zero : (1 : ℂ) ≠ 0)
  · simpa only [symmetricAssignment, hv] using (one_ne_zero : (1 : ℂ) ≠ 0)
  intro w hwx hwv hsys
  let dx : Fin (n + 1) → ℂ := fun k => w (Sum.inl k)
  let dv : Fin (m + 1) → ℂ := fun k => w (Sum.inr k)
  have hw : symmetricAssignment dx dv = w := by
    funext k
    cases k <;> rfl
  obtain ⟨hr, hdflags, hM⟩ :=
    (symmetricSystem_directional_zero_iff A flags M x dx v dv).mp
      (by rw [hw]; exact hsys)
  have hxSym := pencil_transpose A hsym x
  have hdSym := pencil_transpose A hsym dx
  have hvA : v ᵥ* pencil A x = 0 := by
    rw [← Matrix.mulVec_transpose, hxSym]
    exact hAv
  have hl : dv ᵥ* pencil A x + v ᵥ* pencil A dx = 0 := by
    rw [← Matrix.mulVec_transpose, ← Matrix.mulVec_transpose, hxSym, hdSym]
    simpa only [add_comm] using hr
  obtain ⟨hdet, hgrad⟩ := incidence_tangent_implies_base_tangent A flags x dx v v dv dv
    i i hx hwx hv hv hwv hwv hvA hAv hl hr ha hflags0 hflags hdflags
  have hdx : dx = 0 := hbase dx hwx hdet hgrad hM
  have hD : pencil A dx = 0 := by
    rw [hdx]
    ext a b
    simp [pencil]
  have hAdv : pencil A x *ᵥ dv = 0 := by simpa only [hD, zero_mulVec, zero_add] using hr
  have hdv : dv = 0 := kernel_zero_of_minor_and_coordinate (pencil A x) i i
    (minor_ne_zero_of_adjugate_entry _ i i ha) dv hAdv hwv
  rw [← hw, hdx, hdv]
  funext k
  cases k <;> rfl

end Sheshadri.IncidenceSimple
