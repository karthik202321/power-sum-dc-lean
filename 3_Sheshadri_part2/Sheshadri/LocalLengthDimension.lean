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
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-!
# Local multiplicities as actual vector-space dimensions

For a local algebra with residue field equal to its coefficient field, every
simple module has coefficient-field dimension one. Consequently actual module
length agrees with coefficient-field dimension for finite-dimensional modules.
Nilpotents are retained throughout.
-/

noncomputable section
namespace Sheshadri.LocalLengthDimension

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] [IsLocalRing A]

theorem residue_surjective (ε : A →ₐ[K] K) : Function.Surjective ε :=
  fun c => ⟨algebraMap K A c, ε.commutes c⟩

theorem simple_finrank_eq_one (ε : A →ₐ[K] K)
    (M : Type*) [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [IsSimpleModule A M] : Module.finrank K M = 1 := by
  obtain ⟨I,hI,⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp (inferInstance : IsSimpleModule A M)
  have hker : I = RingHom.ker ε.toRingHom :=
    (IsLocalRing.eq_maximalIdeal hI).trans
      (IsLocalRing.ker_eq_maximalIdeal ε.toRingHom (residue_surjective ε)).symm
  let eI : (A ⧸ I) ≃ₐ[K] (A ⧸ RingHom.ker ε.toRingHom) :=
    Ideal.quotientEquivAlgOfEq K hker
  let eK : (A ⧸ RingHom.ker ε.toRingHom) ≃ₐ[K] K :=
    Ideal.quotientKerAlgEquivOfSurjective (residue_surjective ε)
  rw [(e.restrictScalars K).finrank_eq, eI.toLinearEquiv.finrank_eq,
    eK.toLinearEquiv.finrank_eq, Module.finrank_self]

theorem simple_length_restrict (ε : A →ₐ[K] K)
    (M : Type*) [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [IsSimpleModule A M] : Module.length K M = 1 := by
  have hd := simple_finrank_eq_one ε M
  letI : Module.Finite K M := Module.finite_of_finrank_pos (by omega : 0 < Module.finrank K M)
  rw [Module.length_eq_finrank, hd]
  rfl

theorem length_eq_restrict (ε : A →ₐ[K] K)
    (M : Type*) [AddCommGroup M] [Module A M]
    (h : IsFiniteLength A M) [iK : Module K M] [iT : IsScalarTower K A M] :
    Module.length A M = Module.length K M := by
  revert iK iT
  induction h with
  | of_subsingleton => intro _ _; simp
  | @of_simple_quotient M _ _ N _ hN ih =>
    intro _ _
    rw [Module.length_eq_add_of_exact N.subtype N.mkQ
      (Submodule.subtype_injective N) (Submodule.mkQ_surjective N)
      (LinearMap.exact_subtype_mkQ N)]
    rw [Module.length_eq_add_of_exact (N.subtype.restrictScalars K) (N.mkQ.restrictScalars K)
      (Submodule.subtype_injective N) (Submodule.mkQ_surjective N)
      (LinearMap.exact_subtype_mkQ N)]
    rw [ih, Module.length_eq_one (R := A) (M := M ⧸ N),
      simple_length_restrict ε (M ⧸ N)]

theorem length_eq_finrank (ε : A →ₐ[K] K)
    (M : Type*) [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [Module.Finite K M] :
    Module.length A M = (Module.finrank K M : ℕ∞) := by
  letI : IsNoetherian A M := isNoetherian_of_tower K (inferInstance : IsNoetherian K M)
  letI : IsArtinian A M := isArtinian_of_tower K (inferInstance : IsArtinian K M)
  rw [length_eq_restrict ε M
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance,inferInstance⟩),
    Module.length_eq_finrank]

end Sheshadri.LocalLengthDimension
