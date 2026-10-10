/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.GenericKernelLifts
import Sheshadri.IncidenceSimple

/-!
# Determinantal incidence for arbitrary projective Gauss flags

In the chart x₀=1, the homogeneous Gauss covector on f=0 is
(-∑ xᵢ ∂ᵢf, ∂₁f, ..., ∂ₙf). Thus a general projective dual
hyperplane has equation ∑(ℓᵢ-ℓ₀xᵢ)∂ᵢf=0. No coefficient ℓ₀ is
required to vanish. The finite roots and their base transversality are
inputs; the determinantal kernel incidence and its simplicity are proved.
-/

noncomputable section
namespace Sheshadri.ConormalIncidence

open Matrix MvPolynomial Incidence PolynomialModel MultiProjective
open ExactKernelLifts IncidenceSimple IncidenceDifferential TangentEvaluation
open scoped BigOperators Matrix

variable {n m : ℕ}

def projectiveGradientFlag (f : MvPolynomial (Fin n) ℂ)
    (ell : Fin (n + 1) → ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ i : Fin n, (C (ell i.succ) - C (ell 0) * X i) * pderiv i f

def gaussCovector (f : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    Fin (n + 1) → ℂ :=
  Fin.cases (-∑ i, x i * eval x (pderiv i f)) (fun i => eval x (pderiv i f))

theorem eval_projectiveGradientFlag (f : MvPolynomial (Fin n) ℂ)
    (ell : Fin (n + 1) → ℂ) (x : Fin n → ℂ) :
    eval x (projectiveGradientFlag f ell) = ∑ k, ell k * gaussCovector f x k := by
  simp only [projectiveGradientFlag, map_sum, map_mul, map_sub, eval_C, eval_X,
    gaussCovector, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
    sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  ring

theorem shifted_sum_eq_full {R : Type*} [CommRing R]
    (x ell p : Fin (n + 1) → R) (hx : x 0 = 1)
    (hp : ∑ k, x k * p k = 0) :
    (∑ i : Fin n, (ell i.succ - ell 0 * x i.succ) * p i.succ) =
      ∑ k, ell k * p k := by
  rw [Fin.sum_univ_succ, hx, one_mul] at hp
  rw [Fin.sum_univ_succ]
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  linear_combination -(ell 0) * hp

theorem pairing_pencil {R : Type*} [CommRing R]
    (A : PencilCoefficients n m R) (x : Fin (n + 1) → R) (u v : Fin m → R) :
    u ⬝ᵥ (pencil A x *ᵥ v) = ∑ k, x k * (u ⬝ᵥ (A k *ᵥ v)) := by
  simp only [pencil, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ a, ∑ k, ∑ b, u a * (A k a b * x k * v b) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, u a * (A k a b * x k * v b) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

theorem map_affinePencil_eq_pencil {R : Type*} [CommRing R]
    (A : PencilCoefficients n m ℂ) (φ : MvPolynomial (Fin n) ℂ →+* R) :
    (affinePencil A).map φ =
      pencil (fun k => (A k).map (fun c => φ (C c)))
        (Fin.cases 1 (fun i => φ (X i))) := by
  ext a b
  simp [affinePencil, pencil, Fin.sum_univ_succ]

theorem projective_flag_eval_pairing {R : Type*} [CommRing R]
    (A : PencilCoefficients n m ℂ) (φ : MvPolynomial (Fin n) ℂ →+* R)
    (u v : Fin m → R) (alpha : R) (ell : Fin (n + 1) → ℂ)
    (hkernel : (affinePencil A).map φ *ᵥ v = 0)
    (hgrad : ∀ i : Fin n, φ (pderiv i (determinant A)) =
      alpha * (u ⬝ᵥ ((A i.succ).map (fun c => φ (C c)) *ᵥ v))) :
    φ (projectiveGradientFlag (determinant A) ell) =
      alpha * ∑ k, φ (C (ell k)) *
        (u ⬝ᵥ ((A k).map (fun c => φ (C c)) *ᵥ v)) := by
  let B : PencilCoefficients n m R := fun k => (A k).map (fun c => φ (C c))
  let z : Fin (n + 1) → R := Fin.cases 1 (fun i => φ (X i))
  have hpair : ∑ k, z k * (u ⬝ᵥ (B k *ᵥ v)) = 0 := by
    rw [← pairing_pencil]
    have he : pencil B z = (affinePencil A).map φ :=
      (map_affinePencil_eq_pencil A φ).symm
    rw [he, hkernel, dotProduct_zero]
  have hs := shifted_sum_eq_full z (fun k => φ (C (ell k)))
    (fun k => u ⬝ᵥ (B k *ᵥ v)) rfl hpair
  simp only [projectiveGradientFlag, map_sum, map_mul, map_sub, hgrad]
  calc
    _ = alpha * ∑ i : Fin n,
        (φ (C (ell i.succ)) - φ (C (ell 0)) * φ (X i)) *
          (u ⬝ᵥ (B i.succ *ᵥ v)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [B]
      ring
    _ = _ := congrArg (alpha * ·) hs

theorem dual_full_polar_zero (A : PencilCoefficients n m ℂ)
    (ell : Fin (n + 1) → ℂ) (u v du dv : Fin m → ℂ)
    (hval : (∑ k, ell k * (u ⬝ᵥ (A k *ᵥ v))) = 0)
    (hder : (∑ k, ell k *
      (du ⬝ᵥ (A k *ᵥ v) + u ⬝ᵥ (A k *ᵥ dv))) = 0) :
    (∑ k : Fin (n + 1), (TrivSqZeroExt.inl (ell k) : DualNumber ℂ) *
      (dualVector u du ⬝ᵥ ((A k).map TrivSqZeroExt.inl *ᵥ
        dualVector v dv))) = 0 := by
  apply TrivSqZeroExt.ext
  · simpa only [TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.fst_inl, dual_pairing_fst, dualVector] using hval
  · simpa only [TrivSqZeroExt.snd_sum, DualNumber.snd_mul,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, zero_mul, add_zero,
      dual_pairing_snd, dualVector] using hder

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
    (hflags : ∀ t, (∑ k, flags t k * (u ⬝ᵥ (A k *ᵥ v))) = 0)
    (hdflags : ∀ t, (∑ k, flags t k *
      (du ⬝ᵥ (A k *ᵥ v) + u ⬝ᵥ (A k *ᵥ dv))) = 0) :
    directional (determinant A) (fun k => x k.succ) (fun k => dx k.succ) = 0 ∧
    ∀ t, directional (projectiveGradientFlag (determinant A) (flags t))
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
  have hzero : (∑ k : Fin (n + 1), (TrivSqZeroExt.inl (flags t k) : DualNumber ℂ) *
      (U ⬝ᵥ ((A k).map TrivSqZeroExt.inl *ᵥ V))) = 0 :=
    dual_full_polar_zero A (flags t) u v du dv (hflags t) (hdflags t)
  have hflag : φ (projectiveGradientFlag (determinant A) (flags t)) = 0 := by
    have hp := projective_flag_eval_pairing A φ U V (E.adjugate i j)
      (flags t) hEV (by simpa only [φ, tangentEval_C] using hgrad)
    simpa only [φ, tangentEval_C, hzero, mul_zero] using hp
  exact congrArg TrivSqZeroExt.snd hflag

theorem ordinary_simple_in_charts
    (A : PencilCoefficients n (m + 1) ℂ)
    (L : Matrix (Fin ((m + 1) - 1)) (Fin (m + 1)) ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (x : Fin (n + 1) → ℂ) (u v : Fin (m + 1) → ℂ) (i j : Fin (m + 1))
    (hx : x 0 = 1) (hu : u j = 1) (hv : v i = 1)
    (huA : u ᵥ* pencil A x = 0) (hAv : pencil A x *ᵥ v = 0)
    (ha : (pencil A x).adjugate i j ≠ 0)
    (hL : ∀ z, u ⬝ᵥ z = 0 → L *ᵥ z = 0 → z = 0)
    (hflags : ∀ t, (∑ k, flags t k * (u ⬝ᵥ (A k *ᵥ v))) = 0)
    (hbase : ∀ dx : Fin (n + 1) → ℂ, dx 0 = 0 →
      directional (determinant A) (fun k => x k.succ) (fun k => dx k.succ) = 0 →
      (∀ t, directional (projectiveGradientFlag (determinant A) (flags t))
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
    i j hx hwx hu hv hwu hwv huA hAv hl hfull ha hflags hdflags
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

theorem symmetric_simple_in_charts
    (A : PencilCoefficients n (m + 1) ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (x : Fin (n + 1) → ℂ) (v : Fin (m + 1) → ℂ) (i : Fin (m + 1))
    (hsym : ∀ k, (A k).transpose = A k)
    (hx : x 0 = 1) (hv : v i = 1) (hAv : pencil A x *ᵥ v = 0)
    (ha : (pencil A x).adjugate i i ≠ 0)
    (hflags : ∀ t, (∑ k, flags t k * (v ⬝ᵥ (A k *ᵥ v))) = 0)
    (hbase : ∀ dx : Fin (n + 1) → ℂ, dx 0 = 0 →
      directional (determinant A) (fun k => x k.succ) (fun k => dx k.succ) = 0 →
      (∀ t, directional (projectiveGradientFlag (determinant A) (flags t))
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
    i i hx hwx hv hv hwv hwv hvA hAv hl hr ha hflags hdflags
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



/-- Arbitrary homogeneous dual flags vanish on the constructed kernel lift. -/
theorem kernel_lift_dual_flag_zero {A : PencilCoefficients n m ℂ}
    {x : Fin (n + 1) → ℂ} (L : OrdinaryKernelLift A x)
    (hx : x 0 = 1) (ell : Fin (n + 1) → ℂ)
    (hflag : eval (fun q => x q.succ) (projectiveGradientFlag (determinant A) ell) = 0) :
    ∑ i, ell i * (L.u ⬝ᵥ (A i *ᵥ L.v)) = 0 := by
  have h := projective_flag_eval_pairing A (eval (fun q => x q.succ))
    L.u L.v ((pencil A x).adjugate L.rightIndex L.leftIndex) ell
    (by rw [eval_affinePencil A x hx]; exact L.right_kernel)
    (by simpa only [eval_C] using L.gradient_pairing)
  simp only [eval_C] at h
  rw [hflag] at h
  exact (mul_eq_zero.mp h.symm).resolve_left L.cofactor_nonzero

/-- Symmetric kernel lifts obey the same unrestricted dual flags. -/
theorem symmetric_kernel_lift_dual_flag_zero {A : PencilCoefficients n m ℂ}
    {x : Fin (n + 1) → ℂ} (L : SymmetricKernelLift A x)
    (hx : x 0 = 1) (ell : Fin (n + 1) → ℂ)
    (hflag : eval (fun q => x q.succ) (projectiveGradientFlag (determinant A) ell) = 0) :
    ∑ i, ell i * (L.v ⬝ᵥ (A i *ᵥ L.v)) = 0 := by
  have h := projective_flag_eval_pairing A (eval (fun q => x q.succ))
    L.v L.v ((pencil A x).adjugate L.index L.index) ell
    (by rw [eval_affinePencil A x hx]; exact L.kernel)
    (by simpa only [eval_C] using L.gradient_pairing)
  simp only [eval_C] at h
  rw [hflag] at h
  exact (mul_eq_zero.mp h.symm).resolve_left L.cofactor_nonzero

/-- Kernel lifts and a common right reduction for arbitrary projective flags. -/
theorem exists_ordinary_lift_family {P : Type} [Fintype P]
    (A : PencilCoefficients n m ℂ) (hm : 0 < m)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (x : P → Fin (n + 1) → ℂ) (hx : Function.Injective x) (hnorm : ∀ p, x p 0 = 1)
    (hdet : ∀ p, eval (fun q => x p q.succ) (determinant A) = 0)
    (hsmooth : ∀ p, ∃ i : Fin n,
      eval (fun q => x p q.succ) (pderiv i (determinant A)) ≠ 0)
    (hflags : ∀ p t, eval (fun q => x p q.succ)
      (projectiveGradientFlag (determinant A) (flags t)) = 0)
    (hprimal : ∀ p, ∑ i, M i * x p i = 0) :
    Nonempty (OrdinaryLiftFamily A flags M x) := by
  classical
  let L : ∀ p, OrdinaryKernelLift A (x p) := fun p =>
    Classical.choice (exists_ordinary_kernel_lift A hm (x p) (hnorm p) (hdet p) (hsmooth p))
  obtain ⟨Λ, hsurj, hinj⟩ := GenericReduction.exists_reduction_on_hyperplanes_of_pos
    m hm (fun p => (L p).u) (fun p => (L p).u_ne_zero)
  refine ⟨⟨L, Λ, hsurj, hinj, ?_, ?_⟩⟩
  · intro p
    apply (ordinarySystem_zero_iff A Λ flags M (x p) (L p).u (L p).v).2
    refine ⟨(L p).left_kernel, ?_, ?_, hprimal p⟩
    · rw [(L p).right_kernel, Matrix.mulVec_zero]
    · intro t
      exact kernel_lift_dual_flag_zero (L p) (hnorm p) (flags t) (hflags p t)
  · exact ordinary_projective_distinct_of_primal x (fun p => (L p).u)
      (fun p => (L p).v) hx hnorm

/-- Symmetric lift family for arbitrary projective flags. -/
theorem exists_symmetric_lift_family {P : Type} [Fintype P]
    (A : PencilCoefficients n m ℂ) (hm : 0 < m) (hA : ∀ i, (A i).transpose = A i)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (x : P → Fin (n + 1) → ℂ) (hx : Function.Injective x) (hnorm : ∀ p, x p 0 = 1)
    (hdet : ∀ p, eval (fun q => x p q.succ) (determinant A) = 0)
    (hsmooth : ∀ p, ∃ i : Fin n,
      eval (fun q => x p q.succ) (pderiv i (determinant A)) ≠ 0)
    (hflags : ∀ p t, eval (fun q => x p q.succ)
      (projectiveGradientFlag (determinant A) (flags t)) = 0)
    (hprimal : ∀ p, ∑ i, M i * x p i = 0) :
    Nonempty (SymmetricLiftFamily A flags M x) := by
  classical
  let L : ∀ p, SymmetricKernelLift A (x p) := fun p =>
    Classical.choice ((Classical.choice
      (exists_ordinary_kernel_lift A hm (x p) (hnorm p) (hdet p) (hsmooth p))).symmetric hA)
  refine ⟨⟨L, ?_, ?_⟩⟩
  · intro p
    apply (symmetricSystem_zero_iff A flags M (x p) (L p).v).2
    refine ⟨(L p).kernel, ?_, hprimal p⟩
    intro t
    exact symmetric_kernel_lift_dual_flag_zero (L p) (hnorm p) (flags t) (hflags p t)
  · exact symmetric_projective_distinct_of_primal x (fun p => (L p).v) hx hnorm

/-- A finite transverse intersection with arbitrary primal and dual projective
flags, expressed in the chart x₀=1 using actual polynomial equations.
There is no incidence simplicity or numerical count premise. -/
structure TransverseGaussRootFamily
    (f : MvPolynomial (Fin n) ℂ)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ)
    (primal : Fin (n + 1) → ℂ) (P : Type) where
  point : P → Fin (n + 1) → ℂ
  injective : Function.Injective point
  normalized : ∀ p, point p 0 = 1
  root : ∀ p, eval (fun i => point p i.succ) f = 0
  smooth : ∀ p, ∃ i : Fin n,
    eval (fun q => point p q.succ) (pderiv i f) ≠ 0
  gradient_flags : ∀ p t, eval (fun q => point p q.succ)
    (projectiveGradientFlag f (flags t)) = 0
  primal_zero : ∀ p, ∑ i, primal i * point p i = 0
  base_simple : ∀ p, ∀ dx : Fin (n + 1) → ℂ, dx 0 = 0 →
    directional f (fun i => point p i.succ) (fun i => dx i.succ) = 0 →
    (∀ t, directional (projectiveGradientFlag f (flags t))
      (fun i => point p i.succ) (fun i => dx i.succ) = 0) →
    (∑ i, primal i * dx i) = 0 → dx = 0

/-- The original determinant-side incidence bound, for any finite transverse
Gauss-flag intersection in x₀=1 and completely unrestricted dual flags. -/
theorem ordinary_bound (bezout : UniversalSimpleBezout)
    {P : Type} [Fintype P] (hn : 2 ≤ n) (hm : 0 < m)
    (A : PencilCoefficients n m ℂ) (f : MvPolynomial (Fin n) ℂ)
    (hrep : determinant A = f)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (roots : TransverseGaussRootFamily f flags M P) :
    Fintype.card P ≤ ordinaryBezout m n := by
  subst f
  cases m with
  | zero => exact (Nat.not_lt_zero _ hm).elim
  | succ k =>
    obtain ⟨family⟩ := exists_ordinary_lift_family A hm flags M roots.point
      roots.injective roots.normalized roots.root roots.smooth
      roots.gradient_flags roots.primal_zero
    apply ordinary_incidence_count_bound bezout hn (by omega) A family.reduction flags M
      (fun p => ordinaryAssignment (roots.point p) (family.lift p).u (family.lift p).v)
      family.zeros ?_ family.projectively_distinct
    intro p
    let L := family.lift p
    apply ordinary_simple_in_charts A family.reduction flags M (roots.point p)
      L.u L.v L.rightIndex L.leftIndex (roots.normalized p)
      L.left_normalized L.right_normalized L.left_kernel L.right_kernel
      L.cofactor_nonzero (family.reduction_injective p)
    · intro t
      exact kernel_lift_dual_flag_zero L (roots.normalized p) (flags t)
        (roots.gradient_flags p t)
    · exact roots.base_simple p

/-- The original symmetric incidence coefficient for arbitrary projective flags. -/
theorem symmetric_bound (bezout : UniversalBiSimpleBezout)
    {P : Type} [Fintype P] (hn : 2 ≤ n) (hm : 0 < m)
    (A : PencilCoefficients n m ℂ) (hA : ∀ i, (A i).transpose = A i)
    (f : MvPolynomial (Fin n) ℂ) (hrep : determinant A = f)
    (flags : Fin (n - 2) → Fin (n + 1) → ℂ) (M : Fin (n + 1) → ℂ)
    (roots : TransverseGaussRootFamily f flags M P) :
    Fintype.card P ≤ symmetricBezout m n := by
  subst f
  cases m with
  | zero => exact (Nat.not_lt_zero _ hm).elim
  | succ k =>
    obtain ⟨family⟩ := exists_symmetric_lift_family A hm hA flags M roots.point
      roots.injective roots.normalized roots.root roots.smooth
      roots.gradient_flags roots.primal_zero
    apply symmetric_incidence_count_bound bezout hn (by omega) A flags M
      (fun p => symmetricAssignment (roots.point p) (family.lift p).v)
      family.zeros ?_ family.projectively_distinct
    intro p
    let L := family.lift p
    apply symmetric_simple_in_charts A flags M (roots.point p) L.v L.index hA
      (roots.normalized p) L.normalized L.kernel L.cofactor_nonzero
    · exact ((symmetricSystem_zero_iff A flags M (roots.point p) L.v).mp
        (family.zeros p)).2.1
    · exact roots.base_simple p


/-- The literal homogeneous matrix pencil, in projective primal variables. -/
def homogeneousPencil (A : PencilCoefficients n m ℂ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin (n + 1)) ℂ) :=
  fun a b => ∑ k, C (A k a b) * X k

/-- The determinant of the homogeneous pencil, not an abstract Gauss model. -/
def homogeneousDeterminant (A : PencilCoefficients n m ℂ) :
    MvPolynomial (Fin (n + 1)) ℂ := (homogeneousPencil A).det

theorem eval_homogeneousPencil (A : PencilCoefficients n m ℂ)
    (x : Fin (n + 1) → ℂ) :
    (homogeneousPencil A).map (eval x) = pencil A x := by
  ext a b
  simp [homogeneousPencil, pencil]

theorem pderiv_homogeneousPencil (A : PencilCoefficients n m ℂ)
    (k : Fin (n + 1)) (a b : Fin m) :
    pderiv k (homogeneousPencil A a b) = C (A k a b) := by
  classical
  simp [homogeneousPencil, pderiv_X, pderiv_mul, Pi.single_apply, mul_ite]

theorem kernel_lift_homogeneous_gradient {A : PencilCoefficients n m ℂ}
    {x : Fin (n + 1) → ℂ} (L : OrdinaryKernelLift A x) (k : Fin (n + 1)) :
    eval x (pderiv k (homogeneousDeterminant A)) =
      (pencil A x).adjugate L.rightIndex L.leftIndex * (L.u ⬝ᵥ (A k *ᵥ L.v)) := by
  have hadj : ((homogeneousPencil A).map (eval x)).adjugate =
      (pencil A x).adjugate L.rightIndex L.leftIndex • vecMulVec L.v L.u := by
    rw [eval_homogeneousPencil]
    exact L.adjugate_factorization
  have h := derivation_det_eval_pairing (pderiv k) (homogeneousPencil A) (eval x)
    L.u L.v ((pencil A x).adjugate L.rightIndex L.leftIndex) hadj
  have hmat : (homogeneousPencil A).map (fun f => eval x (pderiv k f)) = A k := by
    ext a b
    simp only [Matrix.map_apply, pderiv_homogeneousPencil, eval_C]
  rw [hmat] at h
  exact h

/-- Euler's missing zero-th coordinate is recovered from the actual kernel
identity. This establishes the entire Gauss vector, including coordinate 0. -/
theorem kernel_lift_gaussCovector {A : PencilCoefficients n m ℂ}
    {x : Fin (n + 1) → ℂ} (L : OrdinaryKernelLift A x) (hx : x 0 = 1)
    (k : Fin (n + 1)) :
    gaussCovector (determinant A) (fun q => x q.succ) k =
      (pencil A x).adjugate L.rightIndex L.leftIndex * (L.u ⬝ᵥ (A k *ᵥ L.v)) := by
  refine Fin.cases ?_ (fun i => ?_) k
  · have hp : ∑ k, x k * (L.u ⬝ᵥ (A k *ᵥ L.v)) = 0 := by
      rw [← pairing_pencil, L.right_kernel, dotProduct_zero]
    rw [Fin.sum_univ_succ, hx, one_mul] at hp
    simp only [gaussCovector, Fin.cases_zero, L.gradient_pairing]
    have hs : (∑ i : Fin n, x i.succ *
        ((pencil A x).adjugate L.rightIndex L.leftIndex *
          (L.u ⬝ᵥ (A i.succ *ᵥ L.v)))) =
        (pencil A x).adjugate L.rightIndex L.leftIndex *
          ∑ i : Fin n, x i.succ * (L.u ⬝ᵥ (A i.succ *ᵥ L.v)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    linear_combination -((pencil A x).adjugate L.rightIndex L.leftIndex) * hp
  · exact L.gradient_pairing i

/-- The affine formula is proved equal to the full gradient of the literal
homogeneous determinant on every normalized smooth determinant root. -/
theorem gaussCovector_eq_homogeneous_gradient {A : PencilCoefficients n m ℂ}
    {x : Fin (n + 1) → ℂ} (L : OrdinaryKernelLift A x) (hx : x 0 = 1) :
    gaussCovector (determinant A) (fun q => x q.succ) =
      fun k => eval x (pderiv k (homogeneousDeterminant A)) := by
  funext k
  rw [kernel_lift_gaussCovector L hx, kernel_lift_homogeneous_gradient L]

/-- Evaluation of an unrestricted projective Gauss flag agrees with its
linear form on all n+1 actual homogeneous gradient coordinates. -/
theorem projectiveGaussFlag_evaluation {A : PencilCoefficients n m ℂ}
    {x : Fin (n + 1) → ℂ} (L : OrdinaryKernelLift A x) (hx : x 0 = 1)
    (ell : Fin (n + 1) → ℂ) :
    eval (fun q => x q.succ) (projectiveGradientFlag (determinant A) ell) =
      ∑ k, ell k * eval x (pderiv k (homogeneousDeterminant A)) := by
  rw [eval_projectiveGradientFlag, gaussCovector_eq_homogeneous_gradient L hx]

/-- A zero of an affine determinant rules out matrix size zero. In particular,
the size hypothesis is automatic whenever the displayed root family is nonempty. -/
theorem matrix_size_pos_of_root (A : PencilCoefficients n m ℂ)
    (x : Fin n → ℂ) (hroot : eval x (determinant A) = 0) : 0 < m := by
  cases m with
  | zero => simp [determinant, Matrix.det_isEmpty] at hroot
  | succ k => omega

end Sheshadri.ConormalIncidence
