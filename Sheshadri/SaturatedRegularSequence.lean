/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SaturatedSectionHilbert
import Sheshadri.HomogeneousSystemSaturation

/-!
# Literal cut-and-saturate sequences

This module connects regular section construction to the actual homogeneous
quotients used by the Hilbert induction. Every intermediate ideal is defined
by cut-and-saturate, not by a count or finiteness certificate. The final
localization agrees with the unsaturated original equations on every
specified open, and a common linear open coordinate is proved regular.
-/
noncomputable section
namespace Sheshadri.SaturatedRegularSequence
open MvPolynomial HomogeneousQuotientExact HomogeneousSystemSaturation
open FlatGradedHilbert GenericHomogeneousSections

section Ring
variable {A E : Type*} [CommRing A]

/-- Repeatedly impose the next equation and discard only components
supported on the common zero locus of the displayed open system. -/
def sequence (I : Ideal A) (fs : E → A) (g : ℕ → A) : ℕ → Ideal A
  | 0 => saturation I fs
  | j+1 => saturation (sequence I fs g j ⊔ Ideal.span {g j}) fs

@[simp] theorem sequence_zero (I : Ideal A) (fs : E → A) (g : ℕ → A) :
    sequence I fs g 0 = saturation I fs := rfl

@[simp] theorem sequence_succ (I : Ideal A) (fs : E → A) (g : ℕ → A) (j : ℕ) :
    sequence I fs g (j+1) = saturation (sequence I fs g j ⊔ Ideal.span {g j}) fs := rfl

theorem initial_le (I : Ideal A) (fs : E → A) (g : ℕ → A) : I ≤ sequence I fs g 0 :=
  le_saturation I fs

theorem cut_le_succ (I : Ideal A) (fs : E → A) (g : ℕ → A) (j : ℕ) :
    sequence I fs g j ⊔ Ideal.span {g j} ≤ sequence I fs g (j+1) :=
  le_saturation _ _

theorem monotone_sequence (I : Ideal A) (fs : E → A) (g : ℕ → A) :
    Monotone (sequence I fs g) := by
  apply monotone_nat_of_le_succ
  intro j
  exact le_sup_left.trans (cut_le_succ I fs g j)

theorem initial_le_each (I : Ideal A) (fs : E → A) (g : ℕ → A) (j : ℕ) :
    I ≤ sequence I fs g j :=
  (initial_le I fs g).trans (monotone_sequence I fs g (Nat.zero_le j))

theorem cut_mem (I : Ideal A) (fs : E → A) (g : ℕ → A) {j r : ℕ} (hj : j < r) :
    g j ∈ sequence I fs g r :=
  (monotone_sequence I fs g (Nat.succ_le_of_lt hj))
    ((cut_le_succ I fs g j) ((show Ideal.span {g j} ≤
      sequence I fs g j ⊔ Ideal.span {g j} from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton _))))

end Ring

section Polynomial
variable {Z E K : Type*} [Fintype Z] [Field K]

/-- Repeated saturation is exactly saturation of the complete original
list of equations. It introduces no additional equations on the open set. -/
theorem sequence_eq_saturation_idealSequence
    (I : Ideal (MvPolynomial Z K)) (fs : E → MvPolynomial Z K)
    (g : ℕ → MvPolynomial Z K) (r : ℕ) :
    sequence I fs g r = saturation (idealSequence I g r) fs := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [sequence_succ,ih,saturation_sup_left]
    rfl

/-- Equality of the literal original and saturated equation ideals after
inverting any member of the actual open system. Nilpotents are preserved. -/
theorem map_sequence_eq_of_unit {B : Type*} [CommRing B]
    (I : Ideal (MvPolynomial Z K)) (fs : E → MvPolynomial Z K)
    (g : ℕ → MvPolynomial Z K) (r : ℕ) (φ : MvPolynomial Z K →+* B)
    (i : E) (hi : IsUnit (φ (fs i))) :
    (sequence I fs g r).map φ = (idealSequence I g r).map φ := by
  rw [sequence_eq_saturation_idealSequence]
  exact map_saturation_eq_of_unit _ fs φ i hi

/-- Homogeneity is inherited by each literal cut-and-saturate ideal. -/
theorem sequence_homogeneous
    (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I)
    (fs : E → MvPolynomial Z K) (ds : E → ℕ)
    (hfs : ∀ i, (fs i).IsHomogeneous (ds i))
    (g : ℕ → MvPolynomial Z K) (d : ℕ → ℕ)
    (r : ℕ) (hg : ∀ j < r, (g j).IsHomogeneous (d j)) :
    ∀ k p, p ∈ sequence I fs g r → homogeneousComponent k p ∈ sequence I fs g r := by
  rw [sequence_eq_saturation_idealSequence]
  exact saturation_homogeneous _ fs ds hfs (idealSequence_homogeneous I hI g d r hg)

/-- If the open system includes a common factor, that factor is regular
on every constructed quotient. No genericity is needed for this fact. -/
theorem common_factor_regular_sequence
    (I : Ideal (MvPolynomial Z K)) (u : MvPolynomial Z K)
    (fs : E → MvPolynomial Z K) (g : ℕ → MvPolynomial Z K) (r : ℕ) :
    IsRegular (Ideal.Quotient.mk (sequence I (fun i => u * fs i) g r) u) := by
  rw [sequence_eq_saturation_idealSequence]
  exact common_factor_regular _ u fs

/-- Enough genuinely regular homogeneous cuts of the saturated derivative
open yield an actual finite affine chart at the prescribed linear coordinate.
All Hilbert polynomials and eventual dimensions are constructed in the proof.
-/
theorem chart_finite_of_regular_sequence
    (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I)
    (fs : E → MvPolynomial Z K) (ds : E → ℕ)
    (hfs : ∀ i, (fs i).IsHomogeneous (ds i))
    (l : MvPolynomial Z K) (hl : l.IsHomogeneous 1)
    (g : ℕ → MvPolynomial Z K) (d : ℕ → ℕ)
    (hg : ∀ j, (g j).IsHomogeneous (d j)) (r : ℕ)
    (hreg : ∀ j < r, IsRegular
      (Ideal.Quotient.mk (sequence I (fun i => l * fs i) g j) (g j)))
    (P : Polynomial ℚ) (N : ℕ)
    (hP : ∀ k : ℕ, N ≤ k → P.eval (k : ℚ) =
      (Module.finrank K (coordinatePiece Z K I k) : ℚ))
    (hdeg : P.natDegree ≤ r) :
    Module.Finite K (OrdinaryProjectiveHilbert.ChartAlgebra
      (sequence I (fun i => l * fs i) g r) l) := by
  apply SaturatedSectionHilbert.cut_sequence_chart_finite_of_initial_enlargement
    I hI (sequence I (fun i => l * fs i) g) (initial_le _ _ _)
    (fun j => sequence_homogeneous I hI _ (fun i => 1 + ds i)
      (fun i => hl.mul (hfs i)) g d j (fun j _ => hg j)) g d r
    (fun j _ => hg j) hreg (fun j _ => cut_le_succ _ _ _ j) P N hP hdeg l hl
  exact common_factor_regular_sequence I l fs g r

end Polynomial
end Sheshadri.SaturatedRegularSequence
