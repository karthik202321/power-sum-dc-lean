/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Localization.Ideal

/-!
# A parameter is regular after a local complete-intersection deformation

These statements concern the actual quotient by the deformed equations. If
the parameter is regular on the ambient local ring and the special equations
form a regular sequence modulo the parameter, permutation of local regular
sequences proves that the parameter stays regular on the equation quotient.
Consequently saturation by its powers does not alter that quotient.

The hypothesis of regularity of the special equations is explicit. This file
does not identify an arbitrary isolated square polynomial system as a local
complete intersection.
-/

noncomputable section
namespace Sheshadri.SingularDeformation
open RingTheory.Sequence
open scoped Pointwise

section Module
variable {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [IsNoetherian R M]

/-- The local permutation theorem moves the deformation parameter to the
end of the regular sequence, proving its injective action after the actual
deformed equations have been imposed. -/
theorem parameter_regular_on_equation_module (t : R) (fs : List R)
    (ht : IsSMulRegular M t) (hf : IsRegular (QuotSMulTop t M) fs) :
    IsSMulRegular (M ⧸ (Ideal.ofList fs • (⊤ : Submodule R M))) t := by
  have htf : IsRegular M (t :: fs) := hf.cons ht
  have hft : IsRegular M (fs ++ [t]) :=
    IsLocalRing.isRegular_of_perm htf (List.perm_append_comm (l₁ := [t]) (l₂ := fs))
  exact (isWeaklyRegular_singleton_iff _ t).mp
    ((isWeaklyRegular_append_iff M fs [t]).mp hft.toIsWeaklyRegular).2

end Module

section Ring
variable {R : Type*} [CommRing R]

/-- Relates the module quotient by `t • ⊤` to the literal special-fibre ring. -/
def parameterQuotientEquiv (t : R) : QuotSMulTop t R ≃ₗ[R] R ⧸ Ideal.span {t} :=
  Submodule.quotEquivOfEq _ _ (by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top])

/-- An explicit equivalence with the actual ring quotient by the equations. -/
def equationQuotientEquiv (fs : List R) :
    (R ⧸ (Ideal.ofList fs • (⊤ : Submodule R R))) ≃ₗ[R] R ⧸ Ideal.ofList fs :=
  Submodule.quotEquivOfEq _ _ (by rw [Ideal.smul_eq_mul, Ideal.mul_top])

variable [IsLocalRing R] [IsNoetherianRing R]

theorem parameter_regular_on_equation_quotient (t : R) (fs : List R)
    (ht : IsSMulRegular R t) (hf : IsRegular (R ⧸ Ideal.span {t}) fs) :
    IsSMulRegular (R ⧸ Ideal.ofList fs) t := by
  have hf' := ((parameterQuotientEquiv t).isRegular_congr fs).mpr hf
  have h := parameter_regular_on_equation_module t fs ht hf'
  exact ((equationQuotientEquiv fs).isSMulRegular_congr t).mp h

/-- The special-fibre regularity can equivalently be supplied as a regular
sequence of the images of the equations in the special-fibre ring itself. -/
theorem parameter_regular_of_special_regular (t : R) (fs : List R)
    (ht : IsSMulRegular R t)
    (hf : IsRegular (R ⧸ Ideal.span {t})
      (fs.map (Ideal.Quotient.mk (Ideal.span {t})))) :
    IsSMulRegular (R ⧸ Ideal.ofList fs) t := by
  apply parameter_regular_on_equation_quotient t fs ht
  have h : IsRegular (R ⧸ Ideal.span {t}) fs ↔
      IsRegular (R ⧸ Ideal.span {t}) (fs.map (Ideal.Quotient.mk (Ideal.span {t}))) :=
    (AddEquiv.refl (R ⧸ Ideal.span {t})).isRegular_congr
      (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr (fun r _ x => by
        exact (algebraMap_smul (R ⧸ Ideal.span {t}) r x).symm)))
  exact h.mpr hf

end Ring

section Saturation
variable {R : Type*} [CommRing R]

/-- Regularity on an actual quotient is exactly cancellation modulo its
defining ideal. This preserves nilpotents as well as set-theoretic support. -/
theorem parameter_saturated_of_regular (I : Ideal R) (t : R)
    (ht : IsSMulRegular (R ⧸ I) t) (n : ℕ) (x : R)
    (hx : t^n * x ∈ I) : x ∈ I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (ht.pow n).eq_zero_of_smul_eq_zero
  change Ideal.Quotient.mk I (t^n*x) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

/-- Extension to the parameter-inverted ring and contraction return the
same equation ideal, as an ideal equality rather than equality of zero sets. -/
theorem contraction_localizationAway_eq (I : Ideal R) (t : R)
    (ht : IsSMulRegular (R ⧸ I) t) :
    (I.map (algebraMap R (Localization.Away t))).comap
      (algebraMap R (Localization.Away t)) = I := by
  ext x
  change algebraMap R (Localization.Away t) x ∈ I.map (algebraMap R (Localization.Away t)) ↔ x ∈ I
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers t)]
  constructor
  · rintro ⟨s,⟨n,rfl⟩,hx⟩
    exact parameter_saturated_of_regular I t ht n x hx
  · intro hx
    exact ⟨1, Submonoid.one_mem _, by simpa using hx⟩

end Saturation
end Sheshadri.SingularDeformation
