/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ActualGenericGaussSection
import Sheshadri.ArbitraryFieldFinitePolarBound
import Sheshadri.DVRGaussLengthBound
import Sheshadri.ConormalExactMultiplicity
import Sheshadri.BorderDvrFamily

/-!
# End-to-end border bounds by specialization of actual Gauss sections

The endpoints assume only the dimension and literal determinant border
membership. All special and generic sections, DVR families, finite algebras,
local multiplicities and incidence bounds are constructed within the proof.
This is the local-section implementation of the conormal/Gauss specialization
argument. It does not assume a global cycle or intersection certificate.
-/

noncomputable section
namespace Sheshadri.ConormalBorderMultiplicity
open MvPolynomial PolynomialModel BorderRepresentation ConormalGaussSection
open ActualGenericGaussSection DVRGaussLengthBound
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 250000
set_option maxSynthPendingDepth 3

variable {n m : ℕ}

section Family
variable {D L : Type*} [CommRing D] [IsDomain D]
  [Algebra ℂ D] [Field L] [Algebra ℂ L]

/-- The ordinary degree count for an actual boundary family. No generic
finite-section, preservation, or numerical-bound hypothesis is input. -/
theorem ordinary_family_count (hn : 3 ≤ n)
    (family : DeterminantDvrFamily.Family n m D L) :
    fermatCount n ≤ ordinaryBezout m n := by
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℂ L).injective
  obtain ⟨s⟩ := exists_section (n := n) (by omega)
    (ConormalExact.fermat_isHomogeneous n) (ConormalExact.fermat_ne_zero n (by omega))
    (by omega) (fun x hx _ => ConormalExact.fermat_smooth_away_from_vertex n (by omega) x hx)
  obtain ⟨ell,a,J,c,hell,ha,hfinite,hIJ,hJI,hu,_⟩ :=
    exists_actual_section family (by omega) s
  letI := hfinite
  have hlo := family_section_degree_le family s ell a hell ha (by omega) J
    (by simpa only [generic_equations_ideal, polarEquationIdeal] using hIJ)
    (by simpa only [generic_equations_ideal, generic_derivative, polarEquationIdeal] using hJI)
  have hhi := ArbitraryFieldFinitePolarBound.ordinary_finite_saturated_polar_bound
    (by omega) (family.matrix_size_pos (by omega)) family.pencil
    (fun j i => family.generic (ell j i)) (fun i => family.generic (a i))
    J hIJ hJI c hu
  exact hlo.trans hhi

/-- The symmetric family count uses the native symmetric incidence system. -/
theorem symmetric_family_count (hn : 3 ≤ n)
    (family : DeterminantDvrFamily.Family n m D L)
    (hsym : ∀ i, (family.pencil i).transpose = family.pencil i) :
    fermatCount n ≤ symmetricBezout m n := by
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℂ L).injective
  obtain ⟨s⟩ := exists_section (n := n) (by omega)
    (ConormalExact.fermat_isHomogeneous n) (ConormalExact.fermat_ne_zero n (by omega))
    (by omega) (fun x hx _ => ConormalExact.fermat_smooth_away_from_vertex n (by omega) x hx)
  obtain ⟨ell,a,J,c,hell,ha,hfinite,hIJ,hJI,hu,_⟩ :=
    exists_actual_section family (by omega) s
  letI := hfinite
  have hlo := family_section_degree_le family s ell a hell ha (by omega) J
    (by simpa only [generic_equations_ideal, polarEquationIdeal] using hIJ)
    (by simpa only [generic_equations_ideal, generic_derivative, polarEquationIdeal] using hJI)
  have hhi := ArbitraryFieldFinitePolarBound.symmetric_finite_saturated_polar_bound
    (by omega) (family.matrix_size_pos (by omega)) family.pencil hsym
    (fun j i => family.generic (ell j i)) (fun i => family.generic (a i))
    J hIJ hJI c hu
  exact hlo.trans hhi

end Family

/-- Bare Zariski-border membership suffices for the ordinary count. -/
theorem ordinary_zariski_count (hn : 3 ≤ n)
    (h : ZariskiBridge.OrdinaryZariskiBorder n m) :
    fermatCount n ≤ ordinaryBezout m n := by
  rcases DeterminantDvrFamily.ordinary_border_exact_or_family n m h with h | h
  · exact ConormalExactMultiplicity.ordinary_exact_count hn h
  · obtain ⟨Q,M,P,⟨family⟩⟩ := h
    exact ordinary_family_count hn family

/-- Bare Zariski-border membership suffices for the symmetric count. -/
theorem symmetric_zariski_count (hn : 3 ≤ n)
    (h : ZariskiBridge.SymmetricZariskiBorder n m) :
    fermatCount n ≤ symmetricBezout m n := by
  rcases DeterminantDvrFamily.symmetric_border_exact_or_family n m h with h | h
  · exact ConormalExactMultiplicity.symmetric_exact_count hn h
  · obtain ⟨Q,M,P,family,hsym⟩ := h
    exact symmetric_family_count hn family hsym

/-- Ordinary Fermat border count in any actual finite coefficient space. -/
theorem ordinary_border_count (hn : 3 ≤ n) (h : OrdinaryFiniteSupportBorder n m) :
    fermatCount n ≤ ordinaryBezout m n :=
  ordinary_zariski_count hn (BorderDvrFamily.ordinary_finiteSupportBorder_zariski h)

/-- Symmetric Fermat border count in any actual finite coefficient space. -/
theorem symmetric_border_count (hn : 3 ≤ n) (h : SymmetricFiniteSupportBorder n m) :
    fermatCount n ≤ symmetricBezout m n :=
  symmetric_zariski_count hn (BorderDvrFamily.symmetric_finiteSupportBorder_zariski h)

/-- The ordinary border lower bound, with no geometric certificate. -/
theorem ordinary_border_quadratic (hn : 3 ≤ n) (h : OrdinaryFiniteSupportBorder n m) :
    ((n : ℝ)-1)^2 / (4*Real.exp 1) ≤ (m : ℝ) :=
  ordinary_quadratic_bound n m hn (ordinary_border_count hn h)

/-- The symmetric border lower bound, with no geometric certificate. -/
theorem symmetric_border_quadratic (hn : 3 ≤ n) (h : SymmetricFiniteSupportBorder n m) :
    ((n : ℝ)-1)^2 / (2*Real.exp 1) ≤ (m : ℝ) :=
  symmetric_quadratic_bound n m hn (symmetric_border_count hn h)

theorem ordinary_borderAtSize_count (hn : 3 ≤ n) (h : OrdinaryBorderAtSize n m) :
    fermatCount n ≤ ordinaryBezout m n :=
  ordinary_border_count hn ⟨coefficientSupport n m, h⟩

theorem symmetric_borderAtSize_count (hn : 3 ≤ n) (h : SymmetricBorderAtSize n m) :
    fermatCount n ≤ symmetricBezout m n :=
  symmetric_border_count hn ⟨coefficientSupport n m, h⟩

theorem ordinary_borderAtSize_quadratic (hn : 3 ≤ n) (h : OrdinaryBorderAtSize n m) :
    ((n : ℝ)-1)^2 / (4*Real.exp 1) ≤ (m : ℝ) :=
  ordinary_border_quadratic hn ⟨coefficientSupport n m, h⟩

theorem symmetric_borderAtSize_quadratic (hn : 3 ≤ n) (h : SymmetricBorderAtSize n m) :
    ((n : ℝ)-1)^2 / (2*Real.exp 1) ≤ (m : ℝ) :=
  symmetric_border_quadratic hn ⟨coefficientSupport n m, h⟩

-- BEGIN release Zariski quadratic endpoints
/-- The ordinary quadratic bound directly from literal Zariski border membership. -/
theorem ordinary_zariski_quadratic (hn : 3 ≤ n)
    (h : ZariskiBridge.OrdinaryZariskiBorder n m) :
    ((n : ℝ)-1)^2 / (4*Real.exp 1) ≤ (m : ℝ) :=
  ordinary_quadratic_bound n m hn (ordinary_zariski_count hn h)

/-- The symmetric quadratic bound directly from literal Zariski border membership. -/
theorem symmetric_zariski_quadratic (hn : 3 ≤ n)
    (h : ZariskiBridge.SymmetricZariskiBorder n m) :
    ((n : ℝ)-1)^2 / (2*Real.exp 1) ≤ (m : ℝ) :=
  symmetric_quadratic_bound n m hn (symmetric_zariski_count hn h)
-- END release Zariski quadratic endpoints

end Sheshadri.ConormalBorderMultiplicity
