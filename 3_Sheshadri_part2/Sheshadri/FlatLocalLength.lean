/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Length under flat local extension with field closed fibre

A flat extension of local rings preserves the length of every finite-length
module when the extended maximal ideal is the target maximal ideal. The proof
uses an actual composition series, exactness of flat tensoring, and the actual
quotient description of the tensor product of the residue field.
-/

noncomputable section
namespace Sheshadri.FlatLocalLength

open TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B]

/-- The residue field base changes to the actual target residue field when
extension carries the source maximal ideal onto the target maximal ideal. -/
def residueTensorEquiv
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B) :
    (B ⊗[A] (A ⧸ IsLocalRing.maximalIdeal A)) ≃ₐ[B]
      (B ⧸ IsLocalRing.maximalIdeal B) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
    (IsLocalRing.maximalIdeal A)).symm.trans (Ideal.quotientEquivAlgOfEq B hmax)

/-- Every simple source module base changes to a module of length one. -/
theorem simple_tensor_length
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (M : Type*) [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Module.length B (B ⊗[A] M) = 1 := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
    (inferInstance : IsSimpleModule A M)
  have hIeq : I = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hI
  let e' : M ≃ₗ[A] (A ⧸ IsLocalRing.maximalIdeal A) :=
    e.trans (Ideal.quotientEquivAlgOfEq A hIeq).toLinearEquiv
  let et : (B ⊗[A] M) ≃ₗ[B] B ⊗[A] (A ⧸ IsLocalRing.maximalIdeal A) :=
    AlgebraTensorModule.congr (LinearEquiv.refl B B) e'
  rw [et.length_eq, (residueTensorEquiv hmax).toLinearEquiv.length_eq]
  letI : IsSimpleModule B (B ⧸ IsLocalRing.maximalIdeal B) :=
    isSimpleModule_iff_quot_maximal.mpr ⟨IsLocalRing.maximalIdeal B, inferInstance,
      ⟨LinearEquiv.refl B _⟩⟩
  exact Module.length_eq_one B _

/-- Flat local base change preserves finite module length when the closed
fibre is a field, expressed by equality of the actual maximal ideals. -/
theorem tensor_length_eq [Module.Flat A B]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (M : Type*) [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    Module.length B (B ⊗[A] M) = Module.length A M := by
  induction hM with
  | of_subsingleton => simp
  | @of_simple_quotient M _ _ N _ hN ih =>
    let f : (B ⊗[A] N) →ₗ[B] B ⊗[A] M :=
      AlgebraTensorModule.lTensor B B N.subtype
    let g : (B ⊗[A] M) →ₗ[B] B ⊗[A] (M ⧸ N) :=
      AlgebraTensorModule.lTensor B B N.mkQ
    have hf : Function.Injective f :=
      Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype
    have hg : Function.Surjective g :=
      LinearMap.lTensor_surjective B N.mkQ_surjective
    have hfg : Function.Exact f g :=
      Module.Flat.lTensor_exact B (LinearMap.exact_subtype_mkQ N)
    rw [Module.length_eq_add_of_exact f g hf hg hfg, ih,
      simple_tensor_length hmax (M ⧸ N)]
    rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype
      N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
      Module.length_eq_one (R := A) (M := M ⧸ N)]

/-- In particular the generic local-ring lengths agree. No degree or length
identity is assumed; it follows by tensoring the finite composition series. -/
theorem ring_length_eq [Module.Flat A B]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (hA : IsFiniteLength A A) : Module.length B B = Module.length A A := by
  rw [← (AlgebraTensorModule.rid A B B).length_eq]
  exact tensor_length_eq hmax A hA

/-- A convenient Artinian/Noetherian formulation for generic local rings. -/
theorem ring_length_eq_of_artinian [Module.Flat A B] [IsArtinianRing A] [IsNoetherianRing A]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B) : Module.length B B = Module.length A A :=
  ring_length_eq hmax (isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨inferInstance, inferInstance⟩)

end Sheshadri.FlatLocalLength
