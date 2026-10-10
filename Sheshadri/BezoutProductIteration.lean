/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ProjectiveChartHilbertBound
import Sheshadri.BezoutExcessProducts
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Iterating product inequalities without regular-sequence assumptions

An eventual bound refers to the dimensions of actual multigraded quotient
pieces. Splitting a homogeneous product equation adds the bounds for its
factors, even when multiplication has a kernel and excess components occur.
-/

noncomputable section
namespace Sheshadri.BezoutProductIteration
open MvPolynomial ProjectivePointInterpolation FlatMultiGradedHilbert
  ProjectiveChartHilbertBound BezoutExcessProducts
open scoped Classical

variable {σ K : Type*} [Field K]
abbrev Degree := ℕ × ℕ × ℕ

def EventualBound (w : σ → Degree) (I : Ideal (MvPolynomial σ K)) (B : ℕ) : Prop :=
  ∃ N : ℕ, ∀ a b c : ℕ, N ≤ a → N ≤ b → N ≤ c →
    Module.finrank K (coordinatePiece w I (a,b,c)) ≤ B

theorem eventualBound_top (w : σ → Degree) (B : ℕ) :
    EventualBound w (⊤ : Ideal (MvPolynomial σ K)) B := by
  refine ⟨0, ?_⟩
  intro a b c _ _ _
  haveI : Subsingleton (MvPolynomial σ K ⧸ (⊤ : Ideal (MvPolynomial σ K))) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  simp [Module.finrank_zero_of_subsingleton]

/-- The shift introduced by multiplication disappears after increasing the
explicit threshold in all three grading coordinates. -/
theorem eventualBound_mul (w : σ → Degree)
    (hfinite : ∀ (I : Ideal (MvPolynomial σ K)) (d : Degree),
      Module.Finite K (coordinatePiece w I d))
    (I : Ideal (MvPolynomial σ K)) (hI : IsHomogeneous w I)
    (a b : MvPolynomial σ K) {da : Degree}
    (ha : IsWeightedHomogeneous w a da) {A B : ℕ}
    (hA : EventualBound w (I ⊔ Ideal.span {a}) A)
    (hB : EventualBound w (I ⊔ Ideal.span {b}) B) :
    EventualBound w (I ⊔ Ideal.span {a*b}) (A+B) := by
  obtain ⟨NA, hA⟩ := hA
  obtain ⟨NB, hB⟩ := hB
  refine ⟨NA + NB + da.1 + da.2.1 + da.2.2, ?_⟩
  intro x y z hx hy hz
  let k : Degree := (x-da.1, y-da.2.1, z-da.2.2)
  have hk : da+k = (x,y,z) := by
    ext <;> dsimp [k] <;> omega
  letI := hfinite (I ⊔ Ideal.span {a*b}) (da+k)
  letI := hfinite (I ⊔ Ideal.span {b}) k
  have h := piece_finrank_mul_le w I a b hI ha k
  rw [hk] at h
  apply h.trans
  apply Nat.add_le_add
  · exact hA x y z (by omega) (by omega) (by omega)
  · exact hB k.1 k.2.1 k.2.2 (by dsimp [k]; omega)
      (by dsimp [k]; omega) (by dsimp [k]; omega)

/-- Splitting all factors in a single equation. Empty factor lists give
the unit ideal and contribute zero. -/
theorem eventualBound_finset_prod (w : σ → Degree)
    (hfinite : ∀ (I : Ideal (MvPolynomial σ K)) (d : Degree),
      Module.Finite K (coordinatePiece w I d))
    (I : Ideal (MvPolynomial σ K)) (hI : IsHomogeneous w I)
    {J : Type*} (s : Finset J) (f : J → MvPolynomial σ K) (d : J → Degree)
    (B : J → ℕ) (hf : ∀ j ∈ s, IsWeightedHomogeneous w (f j) (d j))
    (hB : ∀ j ∈ s, EventualBound w (I ⊔ Ideal.span {f j}) (B j)) :
    EventualBound w (I ⊔ Ideal.span {∏ j ∈ s, f j}) (∑ j ∈ s, B j) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using eventualBound_top (K := K) w 0
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact eventualBound_mul w hfinite I hI (f j) (∏ k ∈ s, f k)
      (hf j (Finset.mem_insert_self _ _))
      (hB j (Finset.mem_insert_self _ _))
      (ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
        (fun k hk => hB k (Finset.mem_insert_of_mem hk)))

theorem eventualBound_prod (w : σ → Degree)
    (hfinite : ∀ (I : Ideal (MvPolynomial σ K)) (d : Degree),
      Module.Finite K (coordinatePiece w I d))
    (I : Ideal (MvPolynomial σ K)) (hI : IsHomogeneous w I)
    {J : Type*} [Fintype J] (f : J → MvPolynomial σ K) (d : J → Degree)
    (B : J → ℕ) (hf : ∀ j, IsWeightedHomogeneous w (f j) (d j))
    (hB : ∀ j, EventualBound w (I ⊔ Ideal.span {f j}) (B j)) :
    EventualBound w (I ⊔ Ideal.span {∏ j, f j}) (∑ j, B j) :=
  eventualBound_finset_prod w hfinite I hI Finset.univ f d B
    (fun j _ => hf j) (fun j _ => hB j)

theorem productIdeal_fin_succ {n : ℕ} {D : Fin (n+1) → Type*}
    [∀ e, Fintype (D e)] (f : ∀ e, D e → MvPolynomial σ K) :
    productIdeal f = Ideal.span {∏ j, f 0 j} ⊔
      productIdeal (fun e : Fin n => f e.succ) := by
  rw [productIdeal, Fin.range_fin_succ, Ideal.span_insert]
  rfl

theorem branchIdeal_fin_succ {n : ℕ} {D : Fin (n+1) → Type*}
    [∀ e, Fintype (D e)] (f : ∀ e, D e → MvPolynomial σ K)
    (c : ∀ e, D e) :
    branchIdeal f c = Ideal.span {f 0 (c 0)} ⊔
      branchIdeal (fun e : Fin n => f e.succ) (Fin.tail c) := by
  rw [branchIdeal, Fin.range_fin_succ, Ideal.span_insert]
  rfl

theorem homogeneous_sup_productIdeal_fin (w : σ → Degree)
    (n : ℕ) {D : Fin n → Type*} [∀ e, Fintype (D e)]
    (I : Ideal (MvPolynomial σ K)) (hI : IsHomogeneous w I)
    (f : ∀ e, D e → MvPolynomial σ K) (d : ∀ e, D e → Degree)
    (hf : ∀ e j, IsWeightedHomogeneous w (f e j) (d e j)) :
    IsHomogeneous w (I ⊔ productIdeal f) := by
  induction n generalizing I with
  | zero => simpa [productIdeal] using hI
  | succ n ih =>
    rw [productIdeal_fin_succ, ← sup_assoc]
    exact ih (I ⊔ Ideal.span {∏ j, f 0 j})
      (homogeneous_sup_span w I hI _
        (IsWeightedHomogeneous.prod Finset.univ (f 0) (d 0) (fun j _ => hf 0 j)))
      (fun e => f e.succ) (fun e => d e.succ) (fun e j => hf e.succ j)

/-- Iteration through all equations. The conclusion bounds the actual
product-system quotient by the sum of the actual branch bounds. -/
theorem eventualBound_productSystem_fin (w : σ → Degree)
    (hfinite : ∀ (I : Ideal (MvPolynomial σ K)) (d : Degree),
      Module.Finite K (coordinatePiece w I d))
    (n : ℕ) {D : Fin n → Type*} [∀ e, Fintype (D e)]
    (I : Ideal (MvPolynomial σ K)) (hI : IsHomogeneous w I)
    (f : ∀ e, D e → MvPolynomial σ K) (d : ∀ e, D e → Degree)
    (B : (∀ e, D e) → ℕ)
    (hf : ∀ e j, IsWeightedHomogeneous w (f e j) (d e j))
    (hB : ∀ c, EventualBound w (I ⊔ branchIdeal f c) (B c)) :
    EventualBound w (I ⊔ productIdeal f) (∑ c : ∀ e, D e, B c) := by
  induction n generalizing I with
  | zero =>
    simpa [productIdeal, branchIdeal] using hB (fun e => Fin.elim0 e)
  | succ n ih =>
    let J := I ⊔ productIdeal (fun e : Fin n => f e.succ)
    have hJ : IsHomogeneous w J := homogeneous_sup_productIdeal_fin w n I hI
      (fun e => f e.succ) (fun e => d e.succ) (fun e j => hf e.succ j)
    have hsplit : EventualBound w (J ⊔ Ideal.span {∏ j, f 0 j})
        (∑ j : D 0, ∑ c : ∀ e : Fin n, D e.succ, B (Fin.cons j c)) := by
      apply eventualBound_prod w hfinite J hJ (f 0) (d 0)
        (fun j => ∑ c : ∀ e : Fin n, D e.succ, B (Fin.cons j c)) (hf 0)
      intro j
      have heq : J ⊔ Ideal.span {f 0 j} =
          (I ⊔ Ideal.span {f 0 j}) ⊔ productIdeal (fun e : Fin n => f e.succ) := by
        dsimp [J]
        ac_rfl
      rw [heq]
      apply ih (I ⊔ Ideal.span {f 0 j}) (homogeneous_sup_span w I hI _ (hf 0 j))
        (fun e => f e.succ) (fun e => d e.succ)
        (fun c => B (Fin.cons j c)) (fun e k => hf e.succ k)
      intro c
      have h := hB (Fin.cons j c)
      rw [branchIdeal_fin_succ] at h
      simpa only [Fin.cons_zero, Fin.tail_cons, sup_assoc] using h
    have hideal : J ⊔ Ideal.span {∏ j, f 0 j} = I ⊔ productIdeal f := by
      rw [productIdeal_fin_succ]
      dsimp [J]
      ac_rfl
    rw [hideal] at hsplit
    have hsum : (∑ j : D 0, ∑ c : ∀ e : Fin n, D e.succ, B (Fin.cons j c)) =
        ∑ c : ∀ e, D e, B c := by
      calc
        _ = ∑ p : D 0 × (∀ e : Fin n, D e.succ), B (Fin.cons p.1 p.2) :=
          (Fintype.sum_prod_type (fun p : D 0 × (∀ e : Fin n, D e.succ) =>
            B (Fin.cons p.1 p.2))).symm
        _ = _ := Equiv.sum_comp (Fin.consEquiv D) B
    rwa [hsum] at hsplit

theorem productIdeal_reindex {E F : Type*} {D : E → Type*}
    [∀ e, Fintype (D e)] (e : F ≃ E) (f : ∀ i, D i → MvPolynomial σ K) :
    productIdeal (fun i : F => f (e i)) = productIdeal f := by
  unfold productIdeal
  congr 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, rfl⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    exact ⟨j, rfl⟩

theorem branchIdeal_reindex {E F : Type*} {D : E → Type*}
    [∀ e, Fintype (D e)] (e : F ≃ E) (f : ∀ i, D i → MvPolynomial σ K)
    (c : ∀ i : F, D (e i)) :
    branchIdeal (fun i : F => f (e i)) c =
      branchIdeal f (Equiv.piCongrLeft D e c) := by
  unfold branchIdeal
  congr 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, by simp only [Equiv.piCongrLeft_apply_apply]⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    exact ⟨j, by simp only [Equiv.piCongrLeft_apply_apply]⟩

/-- Full finite-system version, with arbitrary equation and factor index
types. This is a bound for the actual quotient, not an abstract count rule. -/
theorem eventualBound_productSystem (w : σ → Degree)
    (hfinite : ∀ (I : Ideal (MvPolynomial σ K)) (d : Degree),
      Module.Finite K (coordinatePiece w I d))
    {E : Type*} [Fintype E] {D : E → Type*} [∀ e, Fintype (D e)]
    (I : Ideal (MvPolynomial σ K)) (hI : IsHomogeneous w I)
    (f : ∀ e, D e → MvPolynomial σ K) (d : ∀ e, D e → Degree)
    (B : (∀ e, D e) → ℕ)
    (hf : ∀ e j, IsWeightedHomogeneous w (f e j) (d e j))
    (hB : ∀ c, EventualBound w (I ⊔ branchIdeal f c) (B c)) :
    EventualBound w (I ⊔ productIdeal f) (∑ c : ∀ e, D e, B c) := by
  let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
  let q := Equiv.piCongrLeft D e
  have h := eventualBound_productSystem_fin w hfinite (Fintype.card E) I hI
    (fun i => f (e i)) (fun i => d (e i)) (fun c => B (q c))
    (fun i j => hf (e i) j) (fun c => by
      rw [branchIdeal_reindex e f c]
      exact hB (q c))
  rw [productIdeal_reindex e f, Equiv.sum_comp q B] at h
  exact h

end Sheshadri.BezoutProductIteration
