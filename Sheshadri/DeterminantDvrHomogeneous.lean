/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.HomogeneousPolynomialLift
import Sheshadri.DeterminantDvrFamily
import Sheshadri.ConormalExact

/-!
# Homogeneous equations for the actual determinant boundary family

The construction is over the actual DVR already obtained from border
membership. Its homogeneous degree is a finite support bound constructed
from the coefficient polynomial. Extra factors at the hyperplane at infinity
are permitted: dehomogenization recovers the exact generic and special
equations, and the planned chart saturation removes that boundary.
-/

noncomputable section
namespace Sheshadri.DeterminantDvrHomogeneous

open MvPolynomial PolynomialModel DeterminantDvrFamily HomogeneousPolynomialLift
open HomogeneousDeterminant FlatGradedHilbert

variable {n m : ℕ} {D L : Type*} [CommRing D] [IsDomain D]
  [Algebra ℂ D] [Field L] [Algebra ℂ L]

def homogeneousPolynomial (family : Family n m D L) : MvPolynomial (Fin (n+1)) D :=
  lift family.polynomial

def homogeneousDegree (family : Family n m D L) : ℕ := supportDegree family.polynomial

theorem homogeneousPolynomial_homogeneous (family : Family n m D L) :
    (homogeneousPolynomial family).IsHomogeneous (homogeneousDegree family) :=
  lift_homogeneous family.polynomial

theorem generic_homogeneous (family : Family n m D L) :
    (map family.generic.toRingHom (homogeneousPolynomial family)).IsHomogeneous
      (homogeneousDegree family) :=
  (homogeneousPolynomial_homogeneous family).map _

theorem special_homogeneous (family : Family n m D L) :
    (map family.residue.toRingHom (homogeneousPolynomial family)).IsHomogeneous
      (homogeneousDegree family) :=
  (homogeneousPolynomial_homogeneous family).map _

theorem generic_dehom (family : Family n m D L) :
    dehom (map family.generic.toRingHom (homogeneousPolynomial family)) =
      determinant family.pencil := by
  rw [homogeneousPolynomial, dehom_map_lift, family.generic_eq]

theorem special_dehom (family : Family n m D L) :
    dehom (map family.residue.toRingHom (homogeneousPolynomial family)) = fermat n := by
  rw [homogeneousPolynomial, dehom_map_lift, family.special_eq]

theorem generic_pderiv_dehom (family : Family n m D L) (i : Fin n) :
    dehom (map family.generic.toRingHom (pderiv i.succ (homogeneousPolynomial family))) =
      pderiv i (determinant family.pencil) := by
  rw [homogeneousPolynomial, dehom_map_pderiv_lift, family.generic_eq]

theorem special_pderiv_dehom (family : Family n m D L) (i : Fin n) :
    dehom (map family.residue.toRingHom (pderiv i.succ (homogeneousPolynomial family))) =
      pderiv i (fermat n) := by
  rw [homogeneousPolynomial, dehom_map_pderiv_lift, family.special_eq]

theorem generic_polynomial_ne_zero (family : Family n m D L) (hn : 0 < n) :
    map family.generic.toRingHom family.polynomial ≠ 0 := by
  intro h
  have hp : family.polynomial = 0 :=
    (MvPolynomial.map_injective family.generic.toRingHom family.generic_injective)
      (h.trans (map_zero _).symm)
  have hz := family.special_eq
  rw [hp, map_zero] at hz
  exact ConormalExact.fermat_ne_zero n hn hz.symm

theorem generic_homogeneous_ne_zero (family : Family n m D L) (hn : 0 < n) :
    map family.generic.toRingHom (homogeneousPolynomial family) ≠ 0 :=
  map_lift_ne_zero _ _ (generic_polynomial_ne_zero family hn)

/-- The actual generic homogeneous hypersurface has the required Hilbert
dimension bound, independently of singularities or factors at infinity. -/
theorem generic_hypersurface_hilbert (family : Family n m D L) (hn : 0 < n) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ n-1 ∧ ∃ N : ℕ, ∀ k > N,
      P.eval (k : ℚ) =
        (Module.finrank L (coordinatePiece (Fin (n+1)) L
          (Ideal.span {map family.generic.toRingHom (homogeneousPolynomial family)}) k) : ℚ) := by
  refine ⟨hypersurfacePolynomial n (homogeneousDegree family),
    hypersurfacePolynomial_natDegree_le _ _ hn, ?_⟩
  exact eventual_homogeneous_hypersurface_hilbert _ (generic_homogeneous family)
    (generic_homogeneous_ne_zero family hn)

end Sheshadri.DeterminantDvrHomogeneous
