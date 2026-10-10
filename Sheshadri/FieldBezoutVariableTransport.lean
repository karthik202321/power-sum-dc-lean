/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldBezoutSplitHilbert

noncomputable section
open Sheshadri.MultiProjective
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false

namespace Sheshadri.FieldBezoutVariableTransport
variable {k₀ : Type*} [Field k₀] [CharZero k₀]
open MvPolynomial FieldMultiProjective FieldBezoutSplitSystem ProjectivePointInterpolation

section General
variable {σ τ K D : Type*} [CommRing K] [AddCommMonoid D]

theorem weight_mapDomain (e : σ → τ) (w : σ → D) (w' : τ → D)
    (hw : ∀ i, w' (e i) = w i) (s : σ →₀ ℕ) :
    Finsupp.weight w' (Finsupp.mapDomain e s) = Finsupp.weight w s := by
  classical
  induction s using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [Finsupp.mapDomain_add, map_add, hf, hg]
  | single i k => simp [Finsupp.mapDomain_single, Finsupp.weight_single, hw]

theorem homogeneous_rename (e : σ → τ) (w : σ → D) (w' : τ → D)
    (hw : ∀ i, w' (e i) = w i) (f : MvPolynomial σ K) (d : D)
    (hf : f.IsWeightedHomogeneous w d) : (rename e f).IsWeightedHomogeneous w' d := by
  intro s hs
  obtain ⟨r,rfl,hr⟩ := coeff_rename_ne_zero e f s hs
  rw [weight_mapDomain e w w' hw, hf hr]

def quotientRenameEquiv (e : σ ≃ τ) (I : Ideal (MvPolynomial σ K)) :
    (MvPolynomial σ K ⧸ I) ≃ₐ[K]
      (MvPolynomial τ K ⧸ I.map (rename e).toRingHom) :=
  Ideal.quotientEquivAlg I _ (renameEquiv K e) rfl

theorem map_coordinatePiece (e : σ ≃ τ) (w : σ → D) (w' : τ → D)
    (hw : ∀ i, w' (e i) = w i) (I : Ideal (MvPolynomial σ K)) (d : D) :
    (coordinatePiece w I d).map (quotientRenameEquiv e I).toLinearMap =
      coordinatePiece w' (I.map (rename e).toRingHom) d := by
  ext x
  constructor
  · rintro ⟨y,⟨p,hp,rfl⟩,rfl⟩
    exact ⟨rename e p, homogeneous_rename e w w' hw p d hp, rfl⟩
  · rintro ⟨p,hp,rfl⟩
    have hw' : ∀ j, w (e.symm j) = w' j := by
      intro j
      simpa using (hw (e.symm j)).symm
    refine ⟨Ideal.Quotient.mk I (rename e.symm p),
      ⟨rename e.symm p, homogeneous_rename e.symm w' w hw' p d hp, rfl⟩, ?_⟩
    change Ideal.Quotient.mk _ (rename e (rename e.symm p)) = Ideal.Quotient.mk _ p
    congr 1
    simpa only [rename_rename, Equiv.apply_symm_apply, Function.comp_def] using
      congrArg (fun f : MvPolynomial τ K →ₐ[K] MvPolynomial τ K => f p) rename_id

def coordinatePieceRenameEquiv (e : σ ≃ τ) (w : σ → D) (w' : τ → D)
    (hw : ∀ i, w' (e i) = w i) (I : Ideal (MvPolynomial σ K)) (d : D) :
    coordinatePiece w I d ≃ₗ[K] coordinatePiece w' (I.map (rename e).toRingHom) d :=
  (quotientRenameEquiv e I).toLinearEquiv.ofSubmodules _ _
    (map_coordinatePiece e w w' hw I d)

end General

theorem coordinatePiece_finrank_rename {σ τ K D : Type*} [Field K] [AddCommMonoid D]
    (e : σ ≃ τ) (w : σ → D) (w' : τ → D) (hw : ∀ i, w' (e i) = w i)
    (I : Ideal (MvPolynomial σ K)) (d : D) :
    Module.finrank K (coordinatePiece w I d) =
      Module.finrank K (coordinatePiece w' (I.map (rename e).toRingHom) d) :=
  (coordinatePieceRenameEquiv e w w' hw I d).finrank_eq

section Blocks
universe u
variable (X U V : Type u) [Fintype X] [Fintype U] [Fintype V]
    [Nonempty X] [Nonempty U] [Nonempty V]

def dimensions : Fin 3 → ℕ := ![Fintype.card X-1, Fintype.card U-1, Fintype.card V-1]

def blockEquiv (T : Type*) [Fintype T] [Nonempty T] : T ≃ Fin (Fintype.card T-1+1) :=
  (Fintype.equivFin T).trans (finCongr (by have := Fintype.card_pos (α := T); omega))

def toVariables : ∀ b : Fin 3, Fin (dimensions X U V b + 1) → Variables X U V :=
  Fin.cases (fun j => .inl ((blockEquiv X).symm j))
    (Fin.cases (fun j => .inr (.inl ((blockEquiv U).symm j)))
      (Fin.cases (fun j => .inr (.inr ((blockEquiv V).symm j)))
        (fun i => Fin.elim0 i)))

def variablesEquiv : ProjectiveVariables (dimensions X U V) ≃ Variables X U V where
  toFun v := toVariables X U V v.1 v.2
  invFun := Sum.elim (fun x => ⟨0,blockEquiv X x⟩)
    (Sum.elim (fun u => ⟨1,blockEquiv U u⟩) (fun v => ⟨2,blockEquiv V v⟩))
  left_inv := by
    rintro ⟨b,j⟩
    fin_cases b
    · change (⟨0, (blockEquiv X) ((blockEquiv X).symm j)⟩ :
        ProjectiveVariables (dimensions X U V)) = ⟨0,j⟩
      rw [Equiv.apply_symm_apply]
    · change (⟨1, (blockEquiv U) ((blockEquiv U).symm j)⟩ :
        ProjectiveVariables (dimensions X U V)) = ⟨1,j⟩
      rw [Equiv.apply_symm_apply]
    · change (⟨2, (blockEquiv V) ((blockEquiv V).symm j)⟩ :
        ProjectiveVariables (dimensions X U V)) = ⟨2,j⟩
      rw [Equiv.apply_symm_apply]
  right_inv := by
    rintro (x | (u | v))
    · change Sum.inl ((blockEquiv X).symm (blockEquiv X x)) = Sum.inl x
      rw [Equiv.symm_apply_apply]
    · change Sum.inr (Sum.inl ((blockEquiv U).symm (blockEquiv U u))) = Sum.inr (Sum.inl u)
      rw [Equiv.symm_apply_apply]
    · change Sum.inr (Sum.inr ((blockEquiv V).symm (blockEquiv V v))) = Sum.inr (Sum.inr v)
      rw [Equiv.symm_apply_apply]

theorem variablesEquiv_weight (i : ProjectiveVariables (dimensions X U V)) :
    weight X U V (variablesEquiv X U V i) = blockWeight (dimensions X U V) i := by
  rcases i with ⟨b,j⟩
  fin_cases b <;> rfl

omit [Nonempty X] [Nonempty U] [Nonempty V] in
theorem sum_dimensions : (∑ b, dimensions X U V b) =
    (Fintype.card X-1) + (Fintype.card U-1) + (Fintype.card V-1) := by
  simp [dimensions, Fin.sum_univ_succ, add_assoc]

variable {E : Type*} [Fintype E]

/-- An actual comparison equation on the original coordinate types. -/
def transportedSplitEquation (degree : E → Degree) (e : E) :
    MvPolynomial (Variables X U V) k₀ :=
  rename (variablesEquiv X U V)
    (splitEquation (dimensions X U V) degree (fieldParameters (k₀ := k₀) degree) e)

theorem transportedSplitEquation_homogeneous (degree : E → Degree) (e : E) :
    (transportedSplitEquation (k₀ := k₀) X U V degree e).IsWeightedHomogeneous
      (weight X U V) (degree e) :=
  homogeneous_rename (variablesEquiv X U V) _ _ (variablesEquiv_weight X U V) _ _
    (splitEquation_homogeneous (dimensions X U V) degree (fieldParameters (k₀ := k₀) degree) e)

/-- The split-system Hilbert function is unchanged by transport into the
arbitrary finite variable types used by the final theorem. -/
theorem transportedSplitEquation_piece_finrank (degree : E → Degree) (d : Degree) :
    Module.finrank k₀ (coordinatePiece (weight X U V)
      (Ideal.span (Set.range (transportedSplitEquation (k₀ := k₀) X U V degree))) d) =
    Module.finrank k₀ (coordinatePiece (blockWeight (dimensions X U V))
      (Ideal.span (Set.range (splitEquation (dimensions X U V) degree
        (fieldParameters (k₀ := k₀) degree)))) d) := by
  have h := coordinatePiece_finrank_rename (variablesEquiv X U V)
    (blockWeight (dimensions X U V)) (weight X U V) (variablesEquiv_weight X U V)
    (Ideal.span (Set.range (splitEquation (dimensions X U V) degree
      (fieldParameters (k₀ := k₀) degree)))) d
  have hI : (Ideal.span (Set.range (splitEquation (dimensions X U V) degree
      (fieldParameters (k₀ := k₀) degree)))).map (rename (variablesEquiv X U V)).toRingHom =
      Ideal.span (Set.range (transportedSplitEquation (k₀ := k₀) X U V degree)) := by
    rw [Ideal.map_span]
    congr 1
    exact (Set.range_comp _ _).symm
  rw [hI] at h
  exact h.symm

end Blocks
end Sheshadri.FieldBezoutVariableTransport
