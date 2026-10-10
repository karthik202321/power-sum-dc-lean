/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalFlatness
import Sheshadri.GeneralGradedBaseChange
import Sheshadri.ArtinianLocalDecomposition
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Flat.Localization
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Special dimension versus generic dimension without a finite total space

A flat module over a local domain need not be finite over the base, even when
both its fibres are finite. Nevertheless, the dimension of its residue fibre
is at most the dimension of its finite generic fibre. The proof lifts a basis
of the residue fibre, proves these lifts independent by flatness, and extends
the independent family to the fraction field. No finite-module assertion is
made about the total module, and no reducedness assumption is used.
-/

noncomputable section
namespace Sheshadri.DVRFibreDimension

open IsLocalRing TensorProduct
open scoped TensorProduct

variable (R M K : Type*) [CommRing R] [IsDomain R] [IsLocalRing R]
  [AddCommGroup M] [Module R M] [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] in
/-- Every residue-independent family of lifts remains independent in the
actual generic tensor fibre. Finiteness of the total module is unnecessary. -/
theorem generic_independent_of_residue_independent [Module.Flat R M]
    {ι : Type*} (v : ι → M)
    (hv : LinearIndependent (ResidueField R)
      (fun i => (1 : ResidueField R) ⊗ₜ[R] v i)) :
    LinearIndependent K (fun i => (1 : K) ⊗ₜ[R] v i) := by
  letI : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  exact Module.Flat.linearIndependent_one_tmul
    (Module.IsLocalRing.linearIndependent_of_flat v hv)

omit [IsDomain R] in
/-- A finite generic fibre bounds the dimension of the actual residue fibre.
The total module is allowed to be infinite over the local base. -/
theorem residue_finrank_le_generic [Module.Flat R M]
    [Module.Finite K (K ⊗[R] M)] :
    Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) ≤
      Module.finrank K (K ⊗[R] M) := by
  let b := Module.Free.chooseBasis (ResidueField R) (ResidueField R ⊗[R] M)
  obtain ⟨v, hv⟩ :=
    (TensorProduct.mk_surjective R M (ResidueField R)
      Ideal.Quotient.mk_surjective).comp_left b
  dsimp only at hv
  have hi : LinearIndependent K (fun i => (1 : K) ⊗ₜ[R] v i) :=
    generic_independent_of_residue_independent R M K v (by
      change LinearIndependent (ResidueField R)
        (TensorProduct.mk R (ResidueField R) M 1 ∘ v)
      rw [hv]
      exact b.linearIndependent)
  letI : Finite (Module.Free.ChooseBasisIndex (ResidueField R)
      (ResidueField R ⊗[R] M)) := hi.finite
  letI := Fintype.ofFinite (Module.Free.ChooseBasisIndex (ResidueField R)
    (ResidueField R ⊗[R] M))
  rw [Module.finrank_eq_card_basis b]
  exact hi.fintype_card_le_finrank

omit [IsDomain R] in
/-- The residue fibre is actually finite-dimensional if the generic fibre
is finite-dimensional. This avoids relying on the zero value of `finrank`
for infinite-dimensional vector spaces. -/
theorem residue_finite_of_generic [Module.Flat R M]
    [Module.Finite K (K ⊗[R] M)] :
    Module.Finite (ResidueField R) (ResidueField R ⊗[R] M) := by
  let b := Module.Free.chooseBasis (ResidueField R) (ResidueField R ⊗[R] M)
  obtain ⟨v, hv⟩ :=
    (TensorProduct.mk_surjective R M (ResidueField R)
      Ideal.Quotient.mk_surjective).comp_left b
  dsimp only at hv
  have hi : LinearIndependent K (fun i => (1 : K) ⊗ₜ[R] v i) :=
    generic_independent_of_residue_independent R M K v (by
      change LinearIndependent (ResidueField R)
        (TensorProduct.mk R (ResidueField R) M 1 ∘ v)
      rw [hv]
      exact b.linearIndependent)
  letI : Finite (Module.Free.ChooseBasisIndex (ResidueField R)
      (ResidueField R ⊗[R] M)) := hi.finite
  exact Module.Finite.of_basis b

/-- DVR/PID version: torsion-freeness, with no finite generation over the
base, supplies the flatness used by the preceding theorem. -/
theorem residue_finrank_le_generic_of_torsionfree [IsPrincipalIdealRing R]
    [NoZeroSMulDivisors R M] [Module.Finite K (K ⊗[R] M)] :
    Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) ≤
      Module.finrank K (K ⊗[R] M) := by
  letI : Module.Flat R M := ConormalFlatness.flat_of_torsionfree_pid R M
  exact residue_finrank_le_generic R M K

omit [IsDomain R] in
/-- The same inequality for a specified residue field and residue map. Its
surjectivity is used only to identify it with the actual local residue field. -/
theorem special_finrank_le_generic [Module.Flat R M]
    [Module.Finite K (K ⊗[R] M)]
    (k : Type*) [Field k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k)) :
    Module.finrank k (k ⊗[R] M) ≤ Module.finrank K (K ⊗[R] M) := by
  letI : IsLocalHom (algebraMap R k) := IsLocalHom.of_surjective _ hk
  letI : Algebra (ResidueField R) k :=
    (ResidueField.lift (algebraMap R k)).toAlgebra
  letI : IsScalarTower R (ResidueField R) k :=
    IsScalarTower.of_algebraMap_eq fun r => rfl
  rw [← (AlgebraTensorModule.cancelBaseChange R (ResidueField R) k k M).finrank_eq,
    Module.finrank_baseChange]
  exact residue_finrank_le_generic R M K

/-- Torsion-free DVR/PID specialization with the chosen residue-field map. -/
theorem special_finrank_le_generic_of_torsionfree [IsPrincipalIdealRing R]
    [NoZeroSMulDivisors R M] [Module.Finite K (K ⊗[R] M)]
    (k : Type*) [Field k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k)) :
    Module.finrank k (k ⊗[R] M) ≤ Module.finrank K (K ⊗[R] M) := by
  letI : Module.Flat R M := ConormalFlatness.flat_of_torsionfree_pid R M
  exact special_finrank_le_generic R M K k hk

/-- The inequality for literal polynomial quotients by extended ideals.
In particular, nilpotent multiplicities are retained in both fibres. -/
theorem polynomial_quotient_finrank_le_generic {σ : Type*}
    (I : Ideal (MvPolynomial σ R)) [IsPrincipalIdealRing R]
    [NoZeroSMulDivisors R (MvPolynomial σ R ⧸ I)]
    (k : Type*) [Field k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k))
    [Module.Finite K (MvPolynomial σ K ⧸
      GeneralGradedBaseChange.extendedIdeal (K := K) I)] :
    Module.finrank k (MvPolynomial σ k ⧸
      GeneralGradedBaseChange.extendedIdeal (K := k) I) ≤
      Module.finrank K (MvPolynomial σ K ⧸
        GeneralGradedBaseChange.extendedIdeal (K := K) I) := by
  let eK := (GeneralGradedBaseChange.tensorQuotientEquiv (K := K) I).toLinearEquiv
  let ek := (GeneralGradedBaseChange.tensorQuotientEquiv (K := k) I).toLinearEquiv
  letI : Module.Finite K (K ⊗[R] (MvPolynomial σ R ⧸ I)) :=
    Module.Finite.of_injective eK.toLinearMap eK.injective
  rw [← eK.finrank_eq, ← ek.finrank_eq]
  exact special_finrank_le_generic_of_torsionfree R (MvPolynomial σ R ⧸ I) K k hk

/-- The same numerical comparison as a sum of all actual special local-ring
lengths. The generic field need not be algebraically closed. -/
theorem polynomial_quotient_sum_local_length_le_generic {σ : Type*}
    (I : Ideal (MvPolynomial σ R)) [IsPrincipalIdealRing R]
    [NoZeroSMulDivisors R (MvPolynomial σ R ⧸ I)]
    (k : Type*) [Field k] [IsAlgClosed k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k))
    [Module.Finite k (MvPolynomial σ k ⧸
      GeneralGradedBaseChange.extendedIdeal (K := k) I)]
    [Module.Finite K (MvPolynomial σ K ⧸
      GeneralGradedBaseChange.extendedIdeal (K := K) I)]
    [Fintype (MaximalSpectrum (MvPolynomial σ k ⧸
      GeneralGradedBaseChange.extendedIdeal (K := k) I))] :
    (∑ p : MaximalSpectrum (MvPolynomial σ k ⧸
      GeneralGradedBaseChange.extendedIdeal (K := k) I),
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) ≤
      (Module.finrank K (MvPolynomial σ K ⧸
        GeneralGradedBaseChange.extendedIdeal (K := K) I) : ℕ∞) := by
  rw [← ArtinianLocalDecomposition.finrank_eq_sum_local_length k]
  exact_mod_cast polynomial_quotient_finrank_le_generic R K I k hk

end Sheshadri.DVRFibreDimension
