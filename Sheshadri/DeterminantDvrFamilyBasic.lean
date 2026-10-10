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
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Elementary applicability facts for the actual determinant DVR family -/

noncomputable section
namespace Sheshadri.DeterminantDvrFamily
open MvPolynomial PolynomialModel
variable {n m : ℕ} {D L : Type*} [CommRing D] [IsDomain D]
  [Algebra ℂ D] [Field L] [Algebra ℂ L]

theorem Family.residue_surjective (family : Family n m D L) :
    Function.Surjective family.residue.toRingHom :=
  fun c => ⟨algebraMap ℂ D c, family.residue.commutes c⟩

theorem Family.residue_isLocalHom (family : Family n m D L) :
    IsLocalHom family.residue.toRingHom := by
  letI := family.dvr
  exact IsLocalHom.of_surjective family.residue.toRingHom family.residue_surjective

theorem Family.uniformizer_residue (family : Family n m D L) :
    family.residue family.uniformizer = 0 := by
  change family.uniformizer ∈ RingHom.ker family.residue
  rw [family.residue_kernel]
  exact Ideal.subset_span (by simp)

theorem Family.uniformizer_generic_ne_zero (family : Family n m D L) :
    family.generic family.uniformizer ≠ 0 := by
  intro h
  exact family.uniformizer_irreducible.ne_zero
    (family.generic_injective (h.trans (map_zero family.generic).symm))

/-- Matrix size zero would make the generic polynomial identically one.
Injectivity would force the same special polynomial, contradicting the
literal Fermat specialization at the origin. -/
theorem Family.matrix_size_pos (family : Family n m D L) (hn : 0 < n) : 0 < m := by
  cases m with
  | zero =>
    have hg : map family.generic.toRingHom family.polynomial = 1 := by
      simpa only [determinant, Matrix.det_isEmpty] using family.generic_eq
    have hp : family.polynomial = 1 :=
      (MvPolynomial.map_injective family.generic.toRingHom family.generic_injective)
        (hg.trans (map_one _).symm)
    have hs : (1 : MvPolynomial (Fin n) ℂ) = fermat n := by
      simpa only [hp, map_one] using family.special_eq
    have he := congrArg (eval (fun _ : Fin n => (0 : ℂ))) hs
    simp [fermat, hn.ne'] at he
  | succ k => omega

end Sheshadri.DeterminantDvrFamily
