/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Radical kernels are detected by actual fraction fields of prime quotients.
No algebraic-closure or reducedness assumption is imposed on the target ring. -/

noncomputable section
namespace Sheshadri.RadicalKernelFieldPoints

variable {S T : Type*} [CommRing S] [CommRing T]

/-- The canonical field-valued point attached to a prime of an arbitrary ring. -/
def fieldPoint (P : PrimeSpectrum T) : T →+* FractionRing (T ⧸ P.asIdeal) :=
  (algebraMap (T ⧸ P.asIdeal) (FractionRing (T ⧸ P.asIdeal))).comp
    (Ideal.Quotient.mk P.asIdeal)

@[simp] theorem fieldPoint_eq_zero_iff (P : PrimeSpectrum T) (x : T) :
    fieldPoint P x = 0 ↔ x ∈ P.asIdeal := by
  change algebraMap (T ⧸ P.asIdeal) (FractionRing (T ⧸ P.asIdeal))
    (Ideal.Quotient.mk P.asIdeal x) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

/-- Testing the radical of the kernel uses all residue fraction fields, so it
also detects nilpotents and works for a nonreduced generic chart algebra. -/
theorem mem_radical_ker_iff_fieldPoints (φ : S →+* T) (q : S) :
    q ∈ (RingHom.ker φ).radical ↔
      ∀ P : PrimeSpectrum T, fieldPoint P (φ q) = 0 := by
  have hn : q ∈ (RingHom.ker φ).radical ↔ IsNilpotent (φ q) := by
    simp only [Ideal.mem_radical_iff, RingHom.mem_ker, map_pow, IsNilpotent]
  rw [hn, nilpotent_iff_mem_prime]
  simp only [fieldPoint_eq_zero_iff]
  exact ⟨fun h P => h P.asIdeal P.isPrime,
    fun h J hJ => h ⟨J, hJ⟩⟩

end Sheshadri.RadicalKernelFieldPoints
