/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SingularLocalContraction

/-!
# Why isolated support alone does not preserve multiplicity

The family `(t*x, x^2)` has special equation ideal `(x^2)`, but its
generic contraction contains `x`, which does not belong to the original
ideal. Thus a parameter-regularity argument is necessary. There are two
equations in one spatial variable: this is not a counterexample to the
square complete-intersection theorem that the singular Bezout route needs.
-/

noncomputable section
namespace Sheshadri.SingularContractionRegressions
open MvPolynomial BezoutHorizontalFamily GeneralGradedBaseChange

variable (k : Type*) [Field k]
abbrev Ring := MvPolynomial Unit (Polynomial k)
def parameter : Ring k := C Polynomial.X
def spatial : Ring k := X ()
def equations : Ideal (Ring k) := Ideal.span {parameter k * spatial k, spatial k ^ 2}

def specialize : Ring k →+* Polynomial k :=
  eval₂Hom (Polynomial.C.comp (Polynomial.evalRingHom 0)) (fun _ => Polynomial.X)

@[simp] theorem specialize_parameter : specialize k (parameter k) = 0 := by
  simp [specialize, parameter]

@[simp] theorem specialize_spatial : specialize k (spatial k) = Polynomial.X := by
  simp [specialize, spatial]

theorem specialIdeal : (equations k).map (specialize k) =
    Ideal.span {(Polynomial.X : Polynomial k) ^ 2} := by
  rw [equations, Ideal.map_span]
  rw [Set.image_pair]
  simp only [map_mul, map_pow, specialize_parameter, specialize_spatial, zero_mul]
  exact Submodule.span_insert_zero

theorem spatial_not_mem : spatial k ∉ equations k := by
  intro h
  have hx : Polynomial.X ∈ Ideal.span {(Polynomial.X : Polynomial k) ^ 2} := by
    rw [← specialIdeal k]
    simpa using Ideal.mem_map_of_mem (specialize k) h
  have hcoeff := Polynomial.X_pow_dvd_iff.mp (Ideal.mem_span_singleton.mp hx) 1 (by decide)
  simp at hcoeff

theorem parameter_mul_spatial_mem : parameter k * spatial k ∈ equations k :=
  Ideal.subset_span (by simp)

/-- The original equation quotient has an actual nonzero parameter torsion
element, despite its special equation ideal being the double-point ideal. -/
theorem parameter_not_regular : ¬ IsSMulRegular (Ring k ⧸ equations k) (parameter k) := by
  intro h
  have he : parameter k • Ideal.Quotient.mk (equations k) (spatial k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (parameter_mul_spatial_mem k)
  exact spatial_not_mem k (Ideal.Quotient.eq_zero_iff_mem.mp
    (h.eq_zero_of_smul_eq_zero he))

variable {K : Type*} [Field K] [Algebra (Polynomial k) K] [IsFractionRing (Polynomial k) K]

theorem spatial_mem_contracted : spatial k ∈ contractedIdeal
    (extendedIdeal (K := K) (equations k)) := by
  apply (mem_contracted_extension_iff (K := K) (equations k) (spatial k)).mpr
  exact ⟨Polynomial.X, Polynomial.X_ne_zero, parameter_mul_spatial_mem k⟩

theorem contracted_ne_original : contractedIdeal
    (extendedIdeal (K := K) (equations k)) ≠ equations k := by
  intro h
  exact spatial_not_mem k (h ▸ spatial_mem_contracted (K := K) k)

end Sheshadri.SingularContractionRegressions
