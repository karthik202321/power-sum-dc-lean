/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# A local localization with a prescribed residue field

If a localization is already local and the displayed evaluation to a field is
surjective, it is the localization at the kernel of that evaluation. This is
used to identify local graph algebras at the actual incidence point.
-/

noncomputable section
namespace Sheshadri.LocalResidueLocalization

variable {T S K : Type*} [CommRing T] [CommRing S] [Field K]
    [Algebra T S] (M : Submonoid T) [IsLocalization M S] [IsLocalRing S]

attribute [local instance] RingHom.ker_isPrime

/-- A local localization carrying the given residue evaluation is exactly the
local ring at the actual evaluation prime. -/
def atKernelEquiv (ε : T →+* K) (hε : Function.Surjective ε)
    (hM : ∀ s : M, ε s ≠ 0) : Localization.AtPrime (RingHom.ker ε) ≃+* S := by
  let εS : S →+* K := IsLocalization.lift (S := S) (fun s : M => isUnit_iff_ne_zero.mpr (hM s))
  have hεS : Function.Surjective εS := by
    intro k
    obtain ⟨t, ht⟩ := hε k
    refine ⟨algebraMap T S t, ?_⟩
    exact (IsLocalization.lift_eq _ _).trans ht
  have hker : (IsLocalRing.maximalIdeal S).comap (algebraMap T S) = RingHom.ker ε := by
    rw [← IsLocalRing.ker_eq_maximalIdeal εS hεS]
    ext t
    change εS (algebraMap T S t) = 0 ↔ ε t = 0
    rw [show εS (algebraMap T S t) = ε t from IsLocalization.lift_eq _ _]
  letI : IsLocalization (IsLocalRing.maximalIdeal S).primeCompl S :=
    IsLocalization.at_units _ (fun _ ht => IsLocalRing.not_mem_maximalIdeal.mp ht)
  letI : IsLocalization.AtPrime S ((IsLocalRing.maximalIdeal S).comap (algebraMap T S)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M S
      (IsLocalRing.maximalIdeal S)
  letI : IsLocalization.AtPrime S (RingHom.ker ε) := by
    simpa only [hker] using (inferInstance : IsLocalization.AtPrime S
      ((IsLocalRing.maximalIdeal S).comap (algebraMap T S)))
  exact (IsLocalization.algEquiv (RingHom.ker ε).primeCompl _ _).toRingEquiv

end Sheshadri.LocalResidueLocalization
