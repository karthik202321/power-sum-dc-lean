/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldBezoutDeformationBound

noncomputable section
open Sheshadri.MultiProjective
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

namespace Sheshadri.FieldBezoutSplitSystem
variable {k₀ : Type*} [Field k₀] [CharZero k₀]
open MvPolynomial FieldMultiProjective BezoutSplitBudget SplitHyperplanes
open scoped BigOperators Classical

variable {E : Type*} [Fintype E]

abbrev ProjectiveVariables (dim : Fin 3 → ℕ) := Σ b : Fin 3, Fin (dim b + 1)
abbrev AffineVariables (dim : Fin 3 → ℕ) := Σ b : Fin 3, Fin (dim b)
abbrev FactorIndex (degree : E → Degree) := Σ e, Factor (degree e)

/-- Explicit globally distinct parameters; no genericity oracle is required. -/
def fieldParameters (degree : E → Degree) (i : FactorIndex degree) : k₀ :=
  ((Fintype.equivFin (FactorIndex degree) i).val : k₀)

theorem fieldParameters_injective (degree : E → Degree) :
    Function.Injective (fieldParameters (k₀ := k₀) degree) := by
  intro i j h
  apply (Fintype.equivFin (FactorIndex degree)).injective
  apply Fin.ext
  exact Nat.cast_injective h

def blockDegree : Fin 3 → Degree := ![(1,0,0), (0,1,0), (0,0,1)]
def blockWeight (dim : Fin 3 → ℕ) (v : ProjectiveVariables dim) : Degree :=
  blockDegree v.1

def homogeneousFactor (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (e : E) (f : Factor (degree e)) :
    MvPolynomial (ProjectiveVariables dim) k₀ :=
  rename (Sigma.mk (factorBlock f))
    (projectiveForm (dim (factorBlock f)) (α ⟨e,f⟩))

def affineFactor (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (e : E) (f : Factor (degree e)) :
    MvPolynomial (AffineVariables dim) k₀ :=
  rename (Sigma.mk (factorBlock f))
    (affineForm (dim (factorBlock f)) (α ⟨e,f⟩))

def splitEquation (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (e : E) :
    MvPolynomial (ProjectiveVariables dim) k₀ :=
  ∏ f : Factor (degree e), homogeneousFactor dim degree α e f

theorem homogeneousFactor_homogeneous (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (e : E) (f : Factor (degree e)) :
    IsWeightedHomogeneous (blockWeight dim) (homogeneousFactor dim degree α e f)
      (blockDegree (factorBlock f)) := by
  simp only [homogeneousFactor, projectiveForm, map_sum, map_mul, rename_C, rename_X]
  apply IsWeightedHomogeneous.sum
  intro j _
  simpa only [zero_add, blockWeight] using
    (isWeightedHomogeneous_C (blockWeight dim) (α ⟨e,f⟩ ^ (j : ℕ))).mul
      (isWeightedHomogeneous_X k₀ (blockWeight dim) ⟨factorBlock f, j⟩)

theorem sum_blockDegree (d : Degree) :
    (∑ f : Factor d, blockDegree (factorBlock f)) = d := by
  simp [Factor, factorBlock, blockDegree, Fintype.sum_sum_type]

theorem splitEquation_homogeneous (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (e : E) :
    IsWeightedHomogeneous (blockWeight dim) (splitEquation dim degree α e) (degree e) := by
  unfold splitEquation
  simpa only [sum_blockDegree] using IsWeightedHomogeneous.prod Finset.univ
    (homogeneousFactor dim degree α e) (fun f => blockDegree (factorBlock f))
    (fun f _ => homogeneousFactor_homogeneous dim degree α e f)

abbrev homogeneousBranchIdeal (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (s : ∀ e, Factor (degree e)) :=
  BezoutExcessProducts.branchIdeal (homogeneousFactor dim degree α) s

def selectedIndex (degree : E → Degree) (s : ∀ e, Factor (degree e))
    (b : Fin 3) (e : Selected degree s b) : FactorIndex degree := ⟨e.1, s e.1⟩

theorem selectedIndex_injective (degree : E → Degree) (s : ∀ e, Factor (degree e))
    (b : Fin 3) : Function.Injective (selectedIndex degree s b) := by
  intro e e' h
  apply Subtype.ext
  exact congrArg Sigma.fst h

theorem sum_selected_card (degree : E → Degree) (s : ∀ e, Factor (degree e)) :
    (∑ b : Fin 3, Fintype.card (Selected degree s b)) = Fintype.card E := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv (fun e => factorBlock (s e)))

theorem exists_excess_of_not_quota (dim : Fin 3 → ℕ) (degree : E → Degree)
    (s : ∀ e, Factor (degree e)) (hN : Fintype.card E = ∑ b, dim b)
    (hquota : ¬ ∀ b, Fintype.card (Selected degree s b) = dim b) :
    ∃ b, dim b < Fintype.card (Selected degree s b) := by
  by_contra! hle
  apply hquota
  have hs := (sum_selected_card degree s).trans hN
  exact fun b => (Finset.sum_eq_sum_iff_of_le (fun b _ => hle b)).mp hs b (Finset.mem_univ b)

/-- Every selected form, regrouped by its actual block, belongs to the branch. -/
theorem selected_form_mem (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (s : ∀ e, Factor (degree e))
    (b : Fin 3) (e : Selected degree s b) :
    rename (Sigma.mk b) (projectiveForm (dim b) (α (selectedIndex degree s b e))) ∈
      homogeneousBranchIdeal dim degree α s := by
  rcases e with ⟨e,he⟩
  change factorBlock (s e) = b at he
  subst b
  exact BezoutExcessProducts.factor_mem (homogeneousFactor dim degree α) s e

/-- An overfull branch kills every variable in the overfull projective block. -/
theorem excess_variables_mem (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (hα : Function.Injective α)
    (s : ∀ e, Factor (degree e)) (b : Fin 3)
    (hb : dim b < Fintype.card (Selected degree s b))
    (j : Fin (dim b + 1)) : X (⟨b,j⟩ : ProjectiveVariables dim) ∈
      homogeneousBranchIdeal dim degree α s := by
  obtain ⟨f⟩ : Nonempty (Fin (dim b + 1) ↪ Selected degree s b) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hb)
  apply projectiveCoordinate_mem (r := dim b)
    (fun j => (⟨b,j⟩ : ProjectiveVariables dim))
    (α ∘ selectedIndex degree s b ∘ f)
    (hα.comp ((selectedIndex_injective degree s b).comp f.injective))
    (homogeneousBranchIdeal dim degree α s) _ j
  intro i
  exact selected_form_mem dim degree α s b (f i)

/-- An actual enumeration of the selected factors in a quota-sized block. -/
def quotaEnumeration (degree : E → Degree) (s : ∀ e, Factor (degree e))
    (b : Fin 3) (r : ℕ) (h : Fintype.card (Selected degree s b) = r) :
    Fin r ≃ Selected degree s b := (Fintype.equivFinOfCardEq h).symm

def quotaPoint (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (s : ∀ e, Factor (degree e))
    (hquota : ∀ b, Fintype.card (Selected degree s b) = dim b)
    (b : Fin 3) : Fin (dim b) → k₀ :=
  intersectionPoint (α ∘ selectedIndex degree s b ∘
    quotaEnumeration degree s b (dim b) (hquota b))

/-- Every quota branch has the actual homogeneous ideal relations of one
multiprojective point. -/
theorem quota_coordinateDifference_mem (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (hα : Function.Injective α)
    (s : ∀ e, Factor (degree e))
    (hquota : ∀ b, Fintype.card (Selected degree s b) = dim b)
    (b : Fin 3) (j : Fin (dim b)) :
    X (⟨b,j.castSucc⟩ : ProjectiveVariables dim) - C (quotaPoint dim degree α s hquota b j) *
      X ⟨b,Fin.last (dim b)⟩ ∈ homogeneousBranchIdeal dim degree α s := by
  apply homogeneousCoordinateDifference_mem (r := dim b)
    (fun j => (⟨b,j⟩ : ProjectiveVariables dim))
    (α ∘ selectedIndex degree s b ∘ quotaEnumeration degree s b (dim b) (hquota b))
    (hα.comp ((selectedIndex_injective degree s b).comp
      (quotaEnumeration degree s b (dim b) (hquota b)).injective))
    (homogeneousBranchIdeal dim degree α s) _ j
  intro i
  exact selected_form_mem dim degree α s b
    (quotaEnumeration degree s b (dim b) (hquota b) i)

theorem branchIdeal_le_eval_kernel (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (s : ∀ e, Factor (degree e))
    (p : ProjectiveVariables dim → k₀)
    (hp : ∀ e, eval p (homogeneousFactor dim degree α e (s e)) = 0) :
    homogeneousBranchIdeal dim degree α s ≤ RingHom.ker (eval p) :=
  (BezoutExcessProducts.branchIdeal_le_iff _ _ _).mpr hp

/-- An actual nonzero-block zero of the split equations selects a quota
branch. In particular an excess component cannot survive projectivization. -/
theorem split_zero_has_quota_choice (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (hα : Function.Injective α)
    (hN : Fintype.card E = ∑ b, dim b) (p : ProjectiveVariables dim → k₀)
    (hblocks : ∀ b, ∃ j, p ⟨b,j⟩ ≠ 0)
    (hp : ∀ e, eval p (splitEquation dim degree α e) = 0) :
    ∃ s : ∀ e, Factor (degree e),
      (∀ b, Fintype.card (Selected degree s b) = dim b) ∧
      ∀ e, eval p (homogeneousFactor dim degree α e (s e)) = 0 := by
  have hex : ∀ e, ∃ f : Factor (degree e),
      eval p (homogeneousFactor dim degree α e f) = 0 := by
    intro e
    simpa only [splitEquation, map_prod, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and] using hp e
  choose s hs using hex
  refine ⟨s, ?_, hs⟩
  by_contra hquota
  obtain ⟨b,hb⟩ := exists_excess_of_not_quota dim degree s hN hquota
  obtain ⟨j,hj⟩ := hblocks b
  have hz := branchIdeal_le_eval_kernel dim degree α s p hs
    (excess_variables_mem dim degree α hα s b hb j)
  exact hj (by simpa only [RingHom.mem_ker, eval_X] using hz)

/-- At every quota-branch point with nonzero blocks, the chosen last
coordinates really are nonzero. The affine chart is therefore proved to
cover the entire split projective zero set. -/
theorem quota_last_ne_zero (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (hα : Function.Injective α)
    (s : ∀ e, Factor (degree e))
    (hquota : ∀ b, Fintype.card (Selected degree s b) = dim b)
    (p : ProjectiveVariables dim → k₀)
    (hblocks : ∀ b, ∃ j, p ⟨b,j⟩ ≠ 0)
    (hp : ∀ e, eval p (homogeneousFactor dim degree α e (s e)) = 0)
    (b : Fin 3) : p ⟨b,Fin.last (dim b)⟩ ≠ 0 := by
  intro hz
  obtain ⟨j,hj⟩ := hblocks b
  apply hj
  refine Fin.lastCases hz (fun k => ?_) j
  have h := branchIdeal_le_eval_kernel dim degree α s p hp
    (quota_coordinateDifference_mem dim degree α hα s hquota b k)
  simpa only [RingHom.mem_ker, map_sub, map_mul, eval_X, eval_C, hz,
    mul_zero, sub_zero] using h

/-- The explicit normalized projective point of a quota branch. -/
def quotaProjectivePoint (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (s : ∀ e, Factor (degree e))
    (hquota : ∀ b, Fintype.card (Selected degree s b) = dim b) :
    ProjectiveVariables dim → k₀ :=
  fun v => Fin.lastCases 1 (quotaPoint dim degree α s hquota v.1) v.2

/-- Coordinate relations determine the entire point up to the three block
scalars. This is a classification of actual zeros, not a finiteness label. -/
theorem quota_point_coordinates (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (hα : Function.Injective α)
    (s : ∀ e, Factor (degree e))
    (hquota : ∀ b, Fintype.card (Selected degree s b) = dim b)
    (p : ProjectiveVariables dim → k₀)
    (hp : ∀ e, eval p (homogeneousFactor dim degree α e (s e)) = 0)
    (b : Fin 3) (j : Fin (dim b + 1)) :
    p ⟨b,j⟩ = quotaProjectivePoint dim degree α s hquota ⟨b,j⟩ *
      p ⟨b,Fin.last (dim b)⟩ := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [quotaProjectivePoint]
  · have h := branchIdeal_le_eval_kernel dim degree α s p hp
      (quota_coordinateDifference_mem dim degree α hα s hquota b k)
    have he : p ⟨b,k.castSucc⟩ - quotaPoint dim degree α s hquota b k *
        p ⟨b,Fin.last (dim b)⟩ = 0 := by
      simpa only [RingHom.mem_ker, map_sub, map_mul, eval_X, eval_C] using h
    simpa only [quotaProjectivePoint, Fin.lastCases_castSucc] using sub_eq_zero.mp he

/-- The normalized point really is a zero of each selected hyperplane. -/
theorem quotaProjectivePoint_zero_selected (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (hα : Function.Injective α)
    (s : ∀ e, Factor (degree e))
    (hquota : ∀ b, Fintype.card (Selected degree s b) = dim b)
    (b : Fin 3) (e : Selected degree s b) :
    eval (quotaProjectivePoint dim degree α s hquota)
      (rename (Sigma.mk b) (projectiveForm (dim b) (α (selectedIndex degree s b e)))) = 0 := by
  let g := quotaEnumeration degree s b (dim b) (hquota b)
  let a : Fin (dim b) → k₀ := α ∘ selectedIndex degree s b ∘ g
  have ha : Function.Injective a :=
    hα.comp ((selectedIndex_injective degree s b).comp g.injective)
  have he : a (g.symm e) = α (selectedIndex degree s b e) := by
    simp [a]
  have h := intersectionPoint_zero a ha (g.symm e)
  simp only [eval_affineForm, he] at h
  simpa only [eval_rename, eval_projectiveForm, Fin.sum_univ_castSucc,
    Function.comp_apply, quotaProjectivePoint, Fin.lastCases_castSucc,
    Fin.lastCases_last, Fin.coe_castSucc, Fin.val_last, mul_one] using h

theorem quotaProjectivePoint_zero_factor (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (hα : Function.Injective α)
    (s : ∀ e, Factor (degree e))
    (hquota : ∀ b, Fintype.card (Selected degree s b) = dim b) (e : E) :
    eval (quotaProjectivePoint dim degree α s hquota)
      (homogeneousFactor dim degree α e (s e)) = 0 :=
  quotaProjectivePoint_zero_selected dim degree α hα s hquota (factorBlock (s e)) ⟨e,rfl⟩

/-- The split system has a concrete solution for every quota choice. -/
theorem quotaProjectivePoint_zero_system (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (hα : Function.Injective α)
    (s : ∀ e, Factor (degree e))
    (hquota : ∀ b, Fintype.card (Selected degree s b) = dim b) (e : E) :
    eval (quotaProjectivePoint dim degree α s hquota) (splitEquation dim degree α e) = 0 := by
  simp only [splitEquation, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ (s e))
    (quotaProjectivePoint_zero_factor dim degree α hα s hquota e)

theorem quotaProjectivePoint_nonzero_blocks (dim : Fin 3 → ℕ) (degree : E → Degree)
    (α : FactorIndex degree → k₀) (s : ∀ e, Factor (degree e))
    (hquota : ∀ b, Fintype.card (Selected degree s b) = dim b) (b : Fin 3) :
    ∃ j, quotaProjectivePoint dim degree α s hquota ⟨b,j⟩ ≠ 0 := by
  refine ⟨Fin.last (dim b), ?_⟩
  simp [quotaProjectivePoint]

end Sheshadri.FieldBezoutSplitSystem
