/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldIncidenceMultiplicity
import Sheshadri.GenericKernelLifts

noncomputable section
open Sheshadri.MultiProjective
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

namespace Sheshadri.FieldIncidence
variable {k₀ : Type*} [Field k₀] [CharZero k₀]
open MvPolynomial Matrix Incidence FieldMultiProjective
/-- Normalizing one primal coordinate to 1 makes distinct primal points
projectively distinct, regardless of the chosen kernel-vector representatives. -/
theorem ordinary_projective_distinct_of_primal
    {n m : ℕ} {P : Type} (x : P → Fin (n + 1) → k₀)
    (u v : P → Fin m → k₀) (hx : Function.Injective x)
    (hnorm : ∀ p, x p 0 = 1) :
    ∀ p q, ProjectivelyEquivalent (ordinaryAssignment (x p) (u p) (v p))
      (ordinaryAssignment (x q) (u q) (v q)) → p = q := by
  intro p q h
  obtain ⟨a, b, c, _, _, _, heq, _, _⟩ := h
  have ha : a = 1 := by
    have hz := heq 0
    simpa [ordinaryAssignment, hnorm] using hz.symm
  apply hx
  funext i
  simpa [ordinaryAssignment, ha] using heq i

theorem symmetric_projective_distinct_of_primal
    {n m : ℕ} {P : Type} (x : P → Fin (n + 1) → k₀)
    (u : P → Fin m → k₀) (hx : Function.Injective x)
    (hnorm : ∀ p, x p 0 = 1) :
    ∀ p q, BiProjectivelyEquivalent (symmetricAssignment (x p) (u p))
      (symmetricAssignment (x q) (u q)) → p = q := by
  intro p q h
  obtain ⟨a, b, _, _, heq, _⟩ := h
  have ha : a = 1 := by
    have hz := heq 0
    simpa [symmetricAssignment, hnorm] using hz.symm
  apply hx
  funext i
  simpa [symmetricAssignment, ha] using heq i


end Sheshadri.FieldIncidence

namespace Sheshadri.FieldExactKernelLifts
variable {k₀ : Type*} [Field k₀] [CharZero k₀]

open Matrix MvPolynomial Incidence FieldIncidence PolynomialModel FieldMultiProjective
open scoped Matrix

variable {n m : ℕ}

/-- A concrete normalized conormal lift, including the nonzero cofactor and
the kernel-line uniqueness properties needed in the tangent argument. -/
structure OrdinaryKernelLift (A : PencilCoefficients n m k₀)
    (x : Fin (n + 1) → k₀) where
  leftIndex : Fin m
  rightIndex : Fin m
  u : Fin m → k₀
  v : Fin m → k₀
  left_normalized : u leftIndex = 1
  right_normalized : v rightIndex = 1
  cofactor_nonzero : (pencil A x).adjugate rightIndex leftIndex ≠ 0
  left_kernel : u ᵥ* pencil A x = 0
  right_kernel : pencil A x *ᵥ v = 0
  right_line : ∀ w, pencil A x *ᵥ w = 0 → w = w rightIndex • v
  left_line : ∀ w, w ᵥ* pencil A x = 0 → w = w leftIndex • u
  adjugate_factorization : (pencil A x).adjugate =
    (pencil A x).adjugate rightIndex leftIndex • vecMulVec v u
  gradient_pairing : ∀ i : Fin n,
    eval (fun q => x q.succ) (pderiv i (determinant A)) =
      (pencil A x).adjugate rightIndex leftIndex * (u ⬝ᵥ (A i.succ *ᵥ v))

theorem OrdinaryKernelLift.u_ne_zero {A : PencilCoefficients n m k₀}
    {x : Fin (n + 1) → k₀} (L : OrdinaryKernelLift A x) : L.u ≠ 0 := by
  intro h
  have hc := congrFun h L.leftIndex
  exact one_ne_zero (L.left_normalized.symm.trans hc)

theorem OrdinaryKernelLift.v_ne_zero {A : PencilCoefficients n m k₀}
    {x : Fin (n + 1) → k₀} (L : OrdinaryKernelLift A x) : L.v ≠ 0 := by
  intro h
  have hc := congrFun h L.rightIndex
  exact one_ne_zero (L.right_normalized.symm.trans hc)

/-- Smoothness is used only as an actual nonzero evaluated formal derivative. -/
theorem exists_ordinary_kernel_lift (A : PencilCoefficients n m k₀) (hm : 0 < m)
    (x : Fin (n + 1) → k₀) (hx : x 0 = 1)
    (hdet : eval (fun q => x q.succ) (determinant A) = 0)
    (hsmooth : ∃ i : Fin n, eval (fun q => x q.succ) (pderiv i (determinant A)) ≠ 0) :
    Nonempty (OrdinaryKernelLift A x) := by
  cases m with
  | zero => exact (Nat.not_lt_zero _ hm).elim
  | succ k =>
    obtain ⟨q, hq⟩ := hsmooth
    obtain ⟨i, j, hij⟩ := exists_adjugate_entry_ne_zero_eval
      (pderiv q) (affinePencil A) (eval (fun t => x t.succ)) hq
    rw [eval_affinePencil A x hx] at hij
    have hd : (pencil A x).det = 0 := (eval_determinant A x hx).symm.trans hdet
    obtain ⟨u, v, hu, hv, huA, hAv, hright, hleft, hadj⟩ :=
      kernel_lines_and_adjugate_factorization (pencil A x) i j hd hij
    refine ⟨⟨j, i, u, v, hu, hv, hij, huA, hAv, hright, hleft, hadj, ?_⟩⟩
    intro r
    have hadj' : ((affinePencil A).map (eval (fun t => x t.succ))).adjugate =
        (pencil A x).adjugate i j • vecMulVec v u := by
      rw [eval_affinePencil A x hx]
      exact hadj
    have hg := derivation_det_eval_pairing (pderiv r) (affinePencil A)
      (eval (fun t => x t.succ)) u v ((pencil A x).adjugate i j) hadj'
    simpa only [determinant, eval_pderiv_affinePencil] using hg

/-- Gradient flags become the actual bilinear dual flag equations. -/
theorem OrdinaryKernelLift.dual_flag_zero {A : PencilCoefficients n m k₀}
    {x : Fin (n + 1) → k₀} (L : OrdinaryKernelLift A x)
    (ℓ : Fin (n + 1) → k₀) (hzero : ℓ 0 = 0)
    (hflag : ∑ i : Fin n, ℓ i.succ *
      eval (fun q => x q.succ) (pderiv i (determinant A)) = 0) :
    ∑ i, ℓ i * (L.u ⬝ᵥ (A i *ᵥ L.v)) = 0 := by
  have hscalar : (pencil A x).adjugate L.rightIndex L.leftIndex *
      (∑ i : Fin n, ℓ i.succ * (L.u ⬝ᵥ (A i.succ *ᵥ L.v))) = 0 := by
    rw [Finset.mul_sum]
    simpa only [L.gradient_pairing, mul_assoc, mul_left_comm, mul_comm] using hflag
  have hs := (mul_eq_zero.mp hscalar).resolve_left L.cofactor_nonzero
  rw [Fin.sum_univ_succ, hzero, zero_mul, zero_add]
  exact hs

theorem OrdinaryKernelLift.incidence_zero {A : PencilCoefficients n m k₀}
    {x : Fin (n + 1) → k₀} (L : OrdinaryKernelLift A x)
    (Λ : Matrix (Fin (m - 1)) (Fin m) k₀)
    (flags : Fin (n - 2) → Fin (n + 1) → k₀) (M : Fin (n + 1) → k₀)
    (hflags0 : ∀ t, flags t 0 = 0)
    (hflags : ∀ t, ∑ i : Fin n, flags t i.succ *
      eval (fun q => x q.succ) (pderiv i (determinant A)) = 0)
    (hprimal : ∑ i, M i * x i = 0) :
    ∀ e, eval (ordinaryAssignment x L.u L.v) (ordinarySystem A Λ flags M e) = 0 := by
  apply (ordinarySystem_zero_iff A Λ flags M x L.u L.v).2
  refine ⟨L.left_kernel, ?_, ?_, hprimal⟩
  · rw [L.right_kernel, Matrix.mulVec_zero]
  · intro t
    exact L.dual_flag_zero (flags t) (hflags0 t) (hflags t)

/-- An actually constructed family of projectively distinct incidence zeros.
Simple-root information is deliberately absent and is proved separately. -/
structure OrdinaryLiftFamily {P : Type} (A : PencilCoefficients n m k₀)
    (flags : Fin (n - 2) → Fin (n + 1) → k₀) (M : Fin (n + 1) → k₀)
    (x : P → Fin (n + 1) → k₀) where
  lift : ∀ p, OrdinaryKernelLift A (x p)
  reduction : Matrix (Fin (m - 1)) (Fin m) k₀
  reduction_surjective : Function.Surjective reduction.mulVecLin
  reduction_injective : ∀ p z, (lift p).u ⬝ᵥ z = 0 → reduction *ᵥ z = 0 → z = 0
  zeros : ∀ p e, eval (ordinaryAssignment (x p) (lift p).u (lift p).v)
    (ordinarySystem A reduction flags M e) = 0
  projectively_distinct : ∀ p q,
    ProjectivelyEquivalent (ordinaryAssignment (x p) (lift p).u (lift p).v)
      (ordinaryAssignment (x q) (lift q).u (lift q).v) → p = q

theorem exists_ordinary_lift_family {P : Type} [Fintype P]
    (A : PencilCoefficients n m k₀) (hm : 0 < m)
    (flags : Fin (n - 2) → Fin (n + 1) → k₀) (M : Fin (n + 1) → k₀)
    (x : P → Fin (n + 1) → k₀) (hx : Function.Injective x) (hnorm : ∀ p, x p 0 = 1)
    (hdet : ∀ p, eval (fun q => x p q.succ) (determinant A) = 0)
    (hsmooth : ∀ p, ∃ i : Fin n,
      eval (fun q => x p q.succ) (pderiv i (determinant A)) ≠ 0)
    (hflags0 : ∀ t, flags t 0 = 0)
    (hflags : ∀ p t, ∑ i : Fin n, flags t i.succ *
      eval (fun q => x p q.succ) (pderiv i (determinant A)) = 0)
    (hprimal : ∀ p, ∑ i, M i * x p i = 0) :
    Nonempty (OrdinaryLiftFamily A flags M x) := by
  classical
  let L : ∀ p, OrdinaryKernelLift A (x p) := fun p =>
    Classical.choice (exists_ordinary_kernel_lift A hm (x p) (hnorm p) (hdet p) (hsmooth p))
  obtain ⟨Λ, hsurj, hinj⟩ := GenericReduction.exists_reduction_on_hyperplanes_of_pos
    m hm (fun p => (L p).u) (fun p => (L p).u_ne_zero)
  refine ⟨⟨L, Λ, hsurj, hinj, ?_, ?_⟩⟩
  · intro p
    exact (L p).incidence_zero Λ flags M hflags0 (hflags p) (hprimal p)
  · exact ordinary_projective_distinct_of_primal x (fun p => (L p).u)
      (fun p => (L p).v) hx hnorm

theorem pencil_transpose_eq (A : PencilCoefficients n m k₀)
    (hA : ∀ i, (A i).transpose = A i) (x : Fin (n + 1) → k₀) :
    (pencil A x).transpose = pencil A x := by
  ext a b
  change (∑ i, A i b a * x i) = ∑ i, A i a b * x i
  apply Finset.sum_congr rfl
  intro i hi
  rw [show A i b a = A i a b from congrFun (congrFun (hA i) a) b]

/-- The symmetric lift uses one normalized vector and an actual nonzero
diagonal cofactor. -/
structure SymmetricKernelLift (A : PencilCoefficients n m k₀)
    (x : Fin (n + 1) → k₀) where
  index : Fin m
  v : Fin m → k₀
  normalized : v index = 1
  cofactor_nonzero : (pencil A x).adjugate index index ≠ 0
  kernel : pencil A x *ᵥ v = 0
  line : ∀ w, pencil A x *ᵥ w = 0 → w = w index • v
  adjugate_factorization : (pencil A x).adjugate =
    (pencil A x).adjugate index index • vecMulVec v v
  gradient_pairing : ∀ i : Fin n,
    eval (fun q => x q.succ) (pderiv i (determinant A)) =
      (pencil A x).adjugate index index * (v ⬝ᵥ (A i.succ *ᵥ v))

theorem OrdinaryKernelLift.symmetric {A : PencilCoefficients n m k₀}
    {x : Fin (n + 1) → k₀} (L : OrdinaryKernelLift A x)
    (hA : ∀ i, (A i).transpose = A i) :
    Nonempty (SymmetricKernelLift A x) := by
  have hsym := pencil_transpose_eq A hA x
  have huR : pencil A x *ᵥ L.u = 0 := by
    rw [← hsym, Matrix.mulVec_transpose]
    exact L.left_kernel
  have hu := L.right_line L.u huR
  have hc : L.u L.rightIndex ≠ 0 := by
    intro h
    apply L.u_ne_zero
    rw [hu, h, zero_smul]
  have hdiag : (pencil A x).adjugate L.rightIndex L.rightIndex =
      (pencil A x).adjugate L.rightIndex L.leftIndex * L.u L.rightIndex := by
    have h := congrFun (congrFun L.adjugate_factorization L.rightIndex) L.rightIndex
    simpa [Matrix.smul_apply, Matrix.vecMulVec_apply, L.right_normalized] using h
  refine ⟨⟨L.rightIndex, L.v, L.right_normalized, ?_, L.right_kernel, L.right_line, ?_, ?_⟩⟩
  · rw [hdiag]
    exact mul_ne_zero L.cofactor_nonzero hc
  · calc
      (pencil A x).adjugate =
          (pencil A x).adjugate L.rightIndex L.leftIndex • vecMulVec L.v L.u :=
        L.adjugate_factorization
      _ = (pencil A x).adjugate L.rightIndex L.rightIndex • vecMulVec L.v L.v := by
        rw [hdiag]
        ext a b
        simp only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
        have hub := congrFun hu b
        simp only [Pi.smul_apply, smul_eq_mul] at hub
        rw [hub]
        ring
  · intro i
    have hpair := congrArg (fun z => z ⬝ᵥ (A i.succ *ᵥ L.v)) hu
    simp only [smul_dotProduct, smul_eq_mul] at hpair
    rw [L.gradient_pairing, hdiag, hpair]
    ring

structure SymmetricLiftFamily {P : Type} (A : PencilCoefficients n m k₀)
    (flags : Fin (n - 2) → Fin (n + 1) → k₀) (M : Fin (n + 1) → k₀)
    (x : P → Fin (n + 1) → k₀) where
  lift : ∀ p, SymmetricKernelLift A (x p)
  zeros : ∀ p e, eval (symmetricAssignment (x p) (lift p).v)
    (symmetricSystem A flags M e) = 0
  projectively_distinct : ∀ p q,
    BiProjectivelyEquivalent (symmetricAssignment (x p) (lift p).v)
      (symmetricAssignment (x q) (lift q).v) → p = q

theorem exists_symmetric_lift_family {P : Type} [Fintype P]
    (A : PencilCoefficients n m k₀) (hm : 0 < m) (hA : ∀ i, (A i).transpose = A i)
    (flags : Fin (n - 2) → Fin (n + 1) → k₀) (M : Fin (n + 1) → k₀)
    (x : P → Fin (n + 1) → k₀) (hx : Function.Injective x) (hnorm : ∀ p, x p 0 = 1)
    (hdet : ∀ p, eval (fun q => x p q.succ) (determinant A) = 0)
    (hsmooth : ∀ p, ∃ i : Fin n,
      eval (fun q => x p q.succ) (pderiv i (determinant A)) ≠ 0)
    (hflags0 : ∀ t, flags t 0 = 0)
    (hflags : ∀ p t, ∑ i : Fin n, flags t i.succ *
      eval (fun q => x p q.succ) (pderiv i (determinant A)) = 0)
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
    have hs := hflags p t
    have hscalar : (pencil A (x p)).adjugate (L p).index (L p).index *
        (∑ i : Fin n, flags t i.succ * ((L p).v ⬝ᵥ (A i.succ *ᵥ (L p).v))) = 0 := by
      rw [Finset.mul_sum]
      simpa only [(L p).gradient_pairing, mul_assoc, mul_left_comm, mul_comm] using hs
    rw [Fin.sum_univ_succ, hflags0 t, zero_mul, zero_add]
    exact (mul_eq_zero.mp hscalar).resolve_left (L p).cofactor_nonzero
  · exact symmetric_projective_distinct_of_primal x (fun p => (L p).v) hx hnorm

end Sheshadri.FieldExactKernelLifts
