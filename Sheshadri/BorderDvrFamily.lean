/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.DeterminantDvrFamily

/-!
# From literal Euclidean border membership to algebraic determinant families

Coefficient reindexing is continuous and sends every actual determinant to
its canonical coefficient vector. Thus a Euclidean limit in any finite
coefficient space is in the canonical Zariski closure. Only the elementary
Euclidean-to-Zariski inclusion is used; no equality of the two closures is
assumed.
-/
noncomputable section
namespace Sheshadri.BorderDvrFamily
open MvPolynomial PolynomialModel BorderRepresentation ZariskiBridge
open scoped Topology
set_option maxHeartbeats 600000

/-- Literal coefficient reindexing between arbitrary finite supports. -/
def coefficientReindex {n : ℕ} (S T : Finset (Exponent n)) : Coefficients S → Coefficients T :=
  fun c => canonicalCoefficients T (polynomialOfCoefficients S c)

theorem continuous_coefficientReindex {n : ℕ} (S T : Finset (Exponent n)) :
    Continuous (coefficientReindex S T) := by
  classical
  apply continuous_pi
  intro d
  simp only [coefficientReindex, canonicalCoefficients, coeff_polynomialOfCoefficients]
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

/-- The canonical symbolic support contains every actual size-m determinant;
this is proved by specialization of the universal matrix pencil. -/
theorem actual_determinant_support_subset {n m : ℕ}
    (A : Incidence.PencilCoefficients n m ℂ) :
    (determinant A).support ⊆ canonicalSupport n m := by
  let x : Entry n m → ℂ := fun j => A j.1 j.2.1 j.2.2
  have heq : MvPolynomial.map (eval x) (determinant (universalPencil n m)) = determinant A := by
    rw [map_determinant]
    change determinant (specializePencil (universalPencil n m) x) = determinant A
    rw [specialize_universalPencil]
  rw [← heq]
  exact (support_map_subset (eval x) _).trans (ordinary_support_subset n m)

theorem coefficientReindex_mem_ordinary {n m : ℕ} (S : Finset (Exponent n))
    {c : Coefficients S} (hc : c ∈ ordinaryLocus n m S) :
    coefficientReindex S (canonicalSupport n m) c ∈
      ordinaryLocus n m (canonicalSupport n m) := by
  obtain ⟨A, hA⟩ := hc
  refine ⟨A, ?_⟩
  change determinant A = polynomialOfCoefficients _ (canonicalCoefficients _ (polynomialOfCoefficients S c))
  rw [← hA, polynomialOfCoefficients_canonical _ _ (actual_determinant_support_subset A)]

theorem coefficientReindex_mem_symmetric {n m : ℕ} (S : Finset (Exponent n))
    {c : Coefficients S} (hc : c ∈ symmetricLocus n m S) :
    coefficientReindex S (canonicalSupport n m) c ∈
      symmetricLocus n m (canonicalSupport n m) := by
  obtain ⟨A, hsym, hA⟩ := hc
  refine ⟨A, hsym, ?_⟩
  change determinant A = polynomialOfCoefficients _ (canonicalCoefficients _ (polynomialOfCoefficients S c))
  rw [← hA, polynomialOfCoefficients_canonical _ _ (actual_determinant_support_subset A)]

/-- Border membership in any finite coefficient space gives border membership
in the actual universal determinant coefficient space. -/
theorem ordinary_border_canonical {n m : ℕ} (S : Finset (Exponent n))
    (h : OrdinaryBorder n m S) :
    canonicalCoefficients (canonicalSupport n m) (fermat n) ∈
      closure (ordinaryLocus n m (canonicalSupport n m)) := by
  obtain ⟨c, hc, hcl⟩ := h
  have hmap : coefficientReindex S (canonicalSupport n m) c ∈
      closure (coefficientReindex S (canonicalSupport n m) '' ordinaryLocus n m S) :=
    image_closure_subset_closure_image (continuous_coefficientReindex _ _) ⟨c, hcl, rfl⟩
  have hinc : coefficientReindex S (canonicalSupport n m) '' ordinaryLocus n m S ⊆
      ordinaryLocus n m (canonicalSupport n m) := by
    rintro _ ⟨c', hc', rfl⟩
    exact coefficientReindex_mem_ordinary S hc'
  have hh := closure_mono hinc hmap
  simpa only [coefficientReindex, hc] using hh

theorem symmetric_border_canonical {n m : ℕ} (S : Finset (Exponent n))
    (h : SymmetricBorder n m S) :
    canonicalCoefficients (canonicalSupport n m) (fermat n) ∈
      closure (symmetricLocus n m (canonicalSupport n m)) := by
  obtain ⟨c, hc, hcl⟩ := h
  have hmap : coefficientReindex S (canonicalSupport n m) c ∈
      closure (coefficientReindex S (canonicalSupport n m) '' symmetricLocus n m S) :=
    image_closure_subset_closure_image (continuous_coefficientReindex _ _) ⟨c, hcl, rfl⟩
  have hinc : coefficientReindex S (canonicalSupport n m) '' symmetricLocus n m S ⊆
      symmetricLocus n m (canonicalSupport n m) := by
    rintro _ ⟨c', hc', rfl⟩
    exact coefficientReindex_mem_symmetric S hc'
  have hh := closure_mono hinc hmap
  simpa only [coefficientReindex, hc] using hh

theorem ordinary_finiteSupportBorder_zariski {n m : ℕ}
    (h : OrdinaryFiniteSupportBorder n m) : OrdinaryZariskiBorder n m := by
  obtain ⟨S, hS⟩ := h
  exact euclidean_closure_subset_zariski _ (ordinary_border_canonical S hS)

theorem symmetric_finiteSupportBorder_zariski {n m : ℕ}
    (h : SymmetricFiniteSupportBorder n m) : SymmetricZariskiBorder n m := by
  obtain ⟨S, hS⟩ := h
  exact euclidean_closure_subset_zariski _ (symmetric_border_canonical S hS)

/-- The paper-facing Euclidean border predicate yields an actual constructed
DVR family, unless a complex exact representation already exists. -/
theorem ordinary_finiteSupportBorder_exact_or_family {n m : ℕ}
    (h : OrdinaryFiniteSupportBorder n m) :
    ExactRepresentation n m ℂ ∨ DeterminantDvrFamily.HasOrdinaryFamily n m :=
  DeterminantDvrFamily.ordinary_border_exact_or_family n m
    (ordinary_finiteSupportBorder_zariski h)

theorem symmetric_finiteSupportBorder_exact_or_family {n m : ℕ}
    (h : SymmetricFiniteSupportBorder n m) :
    SymmetricExactRepresentation n m ℂ ∨ DeterminantDvrFamily.HasSymmetricFamily n m :=
  DeterminantDvrFamily.symmetric_border_exact_or_family n m
    (symmetric_finiteSupportBorder_zariski h)

theorem ordinary_borderAtSize_exact_or_family {n m : ℕ}
    (h : OrdinaryBorderAtSize n m) :
    ExactRepresentation n m ℂ ∨ DeterminantDvrFamily.HasOrdinaryFamily n m :=
  ordinary_finiteSupportBorder_exact_or_family ⟨coefficientSupport n m, h⟩

theorem symmetric_borderAtSize_exact_or_family {n m : ℕ}
    (h : SymmetricBorderAtSize n m) :
    SymmetricExactRepresentation n m ℂ ∨ DeterminantDvrFamily.HasSymmetricFamily n m :=
  symmetric_finiteSupportBorder_exact_or_family ⟨coefficientSupport n m, h⟩

end Sheshadri.BorderDvrFamily
