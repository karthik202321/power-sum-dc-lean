/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FieldSingularBezout
import Sheshadri.IncidenceMultiplicity

/-! # Actual ordinary and symmetric incidence multiplicities over characteristic-zero fields

The coefficients may live in the generic representation field of a DVR family.
No complex embedding or geometric count input is required.
-/
noncomputable section
open Sheshadri.MultiProjective
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Sheshadri.FieldBezoutArity
variable {k₀ : Type*} [Field k₀] [CharZero k₀]

open MvPolynomial FieldMultiProjective IncidenceDifferential

def embed {X U : Type*} : X ⊕ U → Variables X U Unit
  | .inl x => .inl x
  | .inr u => .inr (.inl u)

def extendPoint {X U : Type*} (p : X ⊕ U → k₀) : Variables X U Unit → k₀
  | .inl x => p (.inl x)
  | .inr (.inl u) => p (.inr u)
  | .inr (.inr _) => 1

theorem extendPoint_comp_embed {X U : Type*} (p : X ⊕ U → k₀) :
    extendPoint p ∘ embed = p := by
  funext i
  cases i <;> rfl

theorem embed_weight {X U : Type*} (d : (X ⊕ U) →₀ ℕ) :
    Finsupp.weight (weight X U Unit) (Finsupp.mapDomain embed d) =
      ((Finsupp.weight (biWeight X U) d).1,
        (Finsupp.weight (biWeight X U) d).2, 0) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [Finsupp.mapDomain_add, map_add, hf, hg]
  | single i k =>
    cases i <;> simp [Finsupp.mapDomain_single, Finsupp.weight_single,
      embed, weight, biWeight]

theorem homogeneous_embed {X U : Type*} (f : MvPolynomial (X ⊕ U) k₀)
    (d : ℕ × ℕ) (hf : IsWeightedHomogeneous (biWeight X U) f d) :
    IsWeightedHomogeneous (weight X U Unit) (rename embed f) (d.1, d.2, 0) := by
  intro s hs
  obtain ⟨r, rfl, hr⟩ := coeff_rename_ne_zero embed f s hs
  rw [embed_weight, hf hr]


end Sheshadri.FieldBezoutArity

namespace Sheshadri.FieldBiProjectiveLocalMultiplicity
variable {k₀ : Type*} [Field k₀] [CharZero k₀]
open MvPolynomial FieldMultiProjective FieldBezoutArity
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

variable {X U E : Type*}

structure Chart (p : X ⊕ U → k₀) where
  ix : X
  iu : U
  hx : p (.inl ix) ≠ 0
  hu : p (.inr iu) ≠ 0

def Chart.extend {p : X ⊕ U → k₀} (c : Chart p) :
    FieldProjectiveLocalMultiplicity.Chart (extendPoint p) :=
  ⟨c.ix, c.iu, (), c.hx, c.hu, one_ne_zero⟩

def chartEquations (f : E → MvPolynomial (X ⊕ U) k₀)
    (p : X ⊕ U → k₀) (c : Chart p) : E ⊕ Fin 2 → MvPolynomial (X ⊕ U) k₀
  | .inl e => f e
  | .inr 0 => MvPolynomial.X (.inl c.ix) - C (p (.inl c.ix))
  | .inr 1 => MvPolynomial.X (.inr c.iu) - C (p (.inr c.iu))

def chartIdeal (f : E → MvPolynomial (X ⊕ U) k₀)
    (p : X ⊕ U → k₀) (c : Chart p) := Ideal.span (Set.range (chartEquations f p c))

theorem chartIdeal_le_pointIdeal (f : E → MvPolynomial (X ⊕ U) k₀)
    (p : X ⊕ U → k₀) (c : Chart p) (hz : ∀ e, eval p (f e) = 0) :
    chartIdeal f p c ≤ IsolatedLocalMultiplicity.pointIdeal p := by
  apply Ideal.span_le.mpr
  rintro _ ⟨e,rfl⟩
  rcases e with e | i
  · exact hz e
  · fin_cases i <;> simp [chartEquations]

abbrev LocalRing (f : E → MvPolynomial (X ⊕ U) k₀)
    (p : X ⊕ U → k₀) (c : Chart p) (hz : ∀ e, eval p (f e) = 0) :=
  IsolatedLocalMultiplicity.LocalIntersectionRing (chartIdeal f p c) p
    (chartIdeal_le_pointIdeal f p c hz)

def multiplicity (f : E → MvPolynomial (X ⊕ U) k₀)
    (p : X ⊕ U → k₀) (c : Chart p) (hz : ∀ e, eval p (f e) = 0) : ℕ∞ :=
  Module.length (LocalRing f p c hz) (LocalRing f p c hz)

def retract : MvPolynomial (Variables X U Unit) k₀ →ₐ[k₀] MvPolynomial (X ⊕ U) k₀ :=
  aeval (fun i => match i with
    | .inl x => MvPolynomial.X (.inl x)
    | .inr (.inl u) => MvPolynomial.X (.inr u)
    | .inr (.inr _) => 1)

@[simp] theorem retract_rename (q : MvPolynomial (X ⊕ U) k₀) :
    retract (rename embed q) = q := by
  have he : (retract (X := X) (U := U)).comp (rename embed) = AlgHom.id k₀ _ := by
    ext i
    cases i <;> simp [retract, embed]
  exact DFunLike.congr_fun he q

theorem rename_chart_mem (f : E → MvPolynomial (X ⊕ U) k₀)
    (p : X ⊕ U → k₀) (c : Chart p) :
    chartIdeal f p c ≤ (FieldProjectiveLocalMultiplicity.chartIdeal
      (fun e => rename embed (f e)) (extendPoint p) c.extend).comap (rename embed) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨e,rfl⟩
  apply Ideal.subset_span
  rcases e with e | i
  · exact ⟨.inl e, rfl⟩
  · fin_cases i
    · exact ⟨.inr 0, by simp [chartEquations, FieldProjectiveLocalMultiplicity.chartEquations,
        FieldProjectiveLocalMultiplicity.Chart.coordinate, Chart.extend, embed, extendPoint]⟩
    · exact ⟨.inr 1, by simp [chartEquations, FieldProjectiveLocalMultiplicity.chartEquations,
        FieldProjectiveLocalMultiplicity.Chart.coordinate, Chart.extend, embed, extendPoint]⟩

theorem retract_chart_mem (f : E → MvPolynomial (X ⊕ U) k₀)
    (p : X ⊕ U → k₀) (c : Chart p) :
    FieldProjectiveLocalMultiplicity.chartIdeal (fun e => rename embed (f e))
      (extendPoint p) c.extend ≤ (chartIdeal f p c).comap retract := by
  apply Ideal.span_le.mpr
  rintro _ ⟨e,rfl⟩
  rcases e with e | i
  · change retract (rename embed (f e)) ∈ chartIdeal f p c
    rw [retract_rename]
    exact Ideal.subset_span ⟨.inl e, rfl⟩
  · fin_cases i
    · have he : chartEquations f p c (.inr 0) ∈ chartIdeal f p c :=
        Ideal.subset_span ⟨.inr 0, rfl⟩
      simpa [Ideal.mem_comap, retract, chartEquations,
        FieldProjectiveLocalMultiplicity.chartEquations, FieldProjectiveLocalMultiplicity.Chart.coordinate,
        Chart.extend, extendPoint] using he
    · have he : chartEquations f p c (.inr 1) ∈ chartIdeal f p c :=
        Ideal.subset_span ⟨.inr 1, rfl⟩
      simpa [Ideal.mem_comap, retract, chartEquations,
        FieldProjectiveLocalMultiplicity.chartEquations, FieldProjectiveLocalMultiplicity.Chart.coordinate,
        Chart.extend, extendPoint] using he
    · simp [Ideal.mem_comap, retract, FieldProjectiveLocalMultiplicity.chartEquations,
        FieldProjectiveLocalMultiplicity.Chart.coordinate, Chart.extend, extendPoint]

def chartRingEquiv (f : E → MvPolynomial (X ⊕ U) k₀)
    (p : X ⊕ U → k₀) (c : Chart p) :
    (MvPolynomial (Variables X U Unit) k₀ ⧸ FieldProjectiveLocalMultiplicity.chartIdeal
      (fun e => rename embed (f e)) (extendPoint p) c.extend) ≃ₐ[k₀]
        (MvPolynomial (X ⊕ U) k₀ ⧸ chartIdeal f p c) := by
  let I := chartIdeal f p c
  let J := FieldProjectiveLocalMultiplicity.chartIdeal (fun e => rename embed (f e))
    (extendPoint p) c.extend
  let a := Ideal.quotientMapₐ I retract (retract_chart_mem f p c)
  let b := Ideal.quotientMapₐ J (rename embed) (rename_chart_mem f p c)
  apply AlgEquiv.ofAlgHom a b
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change Ideal.Quotient.mk I (retract (rename embed (MvPolynomial.X i))) =
      Ideal.Quotient.mk I (MvPolynomial.X i)
    rw [retract_rename]
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with i | (i | i)
    · change Ideal.Quotient.mk J (rename embed (retract (MvPolynomial.X (.inl i)))) = _
      simp [retract, embed, J]
    · change Ideal.Quotient.mk J (rename embed (retract (MvPolynomial.X (.inr (.inl i))))) = _
      simp [retract, embed, J]
    · cases i
      have he : Ideal.Quotient.mk J (MvPolynomial.X (.inr (.inr ())) - C 1) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨.inr 2, rfl⟩)
      have hz : Ideal.Quotient.mk J (MvPolynomial.X (.inr (.inr ()))) = 1 := by
        simpa only [map_sub, map_one, C_1, sub_eq_zero] using he
      change Ideal.Quotient.mk J (rename embed (retract (MvPolynomial.X (.inr (.inr ()))))) = _
      simpa [retract, embed] using hz.symm

@[simp] theorem chartRingEquiv_mk (f : E → MvPolynomial (X ⊕ U) k₀)
    (p : X ⊕ U → k₀) (c : Chart p) (q : MvPolynomial (Variables X U Unit) k₀) :
    chartRingEquiv f p c (Ideal.Quotient.mk _ q) =
      Ideal.Quotient.mk (chartIdeal f p c) (retract q) := rfl

theorem eval_retract (p : X ⊕ U → k₀) (q : MvPolynomial (Variables X U Unit) k₀) :
    eval p (retract q) = eval (extendPoint p) q := by
  have he : (aeval (R := k₀) p).comp retract = aeval (R := k₀) (extendPoint p) := by
    ext i
    rcases i with i | (i | i) <;> simp [retract, extendPoint]
  exact DFunLike.congr_fun he q

theorem extend_zero (f : E → MvPolynomial (X ⊕ U) k₀) (p : X ⊕ U → k₀)
    (hz : ∀ e, eval p (f e) = 0) :
    ∀ e, eval (extendPoint p) (rename embed (f e)) = 0 := by
  intro e
  simpa only [eval_rename, extendPoint_comp_embed] using hz e

/-- Localizing the explicit chart equivalence at the actual evaluation
points removes the dummy factor from the actual local rings. -/
def localRingEquiv (f : E → MvPolynomial (X ⊕ U) k₀)
    (p : X ⊕ U → k₀) (c : Chart p) (hz : ∀ e, eval p (f e) = 0) :
    FieldProjectiveLocalMultiplicity.LocalRing (fun e => rename embed (f e))
      (extendPoint p) c.extend (extend_zero f p hz) ≃+* LocalRing f p c hz := by
  let e := (chartRingEquiv f p c).toRingEquiv
  let P := IsolatedLocalMultiplicity.quotientPointIdeal
    (FieldProjectiveLocalMultiplicity.chartIdeal (fun e => rename embed (f e))
      (extendPoint p) c.extend) (extendPoint p)
      (FieldProjectiveLocalMultiplicity.chartIdeal_le_pointIdeal _ _ _ (extend_zero f p hz))
  let Q := IsolatedLocalMultiplicity.quotientPointIdeal (chartIdeal f p c) p
    (chartIdeal_le_pointIdeal f p c hz)
  have he : P = Q.comap e := by
    ext x
    obtain ⟨q,rfl⟩ := Ideal.Quotient.mk_surjective x
    change eval (extendPoint p) q = 0 ↔ eval p (retract q) = 0
    rw [eval_retract]
  apply IsLocalization.ringEquivOfRingEquiv (M := P.primeCompl) (T := Q.primeCompl)
    _ _ e
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change e x ∉ Q
    change x ∉ P at hx
    rwa [he] at hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change e.symm y ∉ P
    rw [he]
    change e (e.symm y) ∉ Q
    simpa using hy

theorem multiplicity_extend (f : E → MvPolynomial (X ⊕ U) k₀)
    (p : X ⊕ U → k₀) (c : Chart p) (hz : ∀ e, eval p (f e) = 0) :
    FieldProjectiveLocalMultiplicity.multiplicity (fun e => rename embed (f e))
      (extendPoint p) c.extend (extend_zero f p hz) = multiplicity f p c hz :=
  ProjectiveCycleLengths.ringEquiv_length (localRingEquiv f p c hz)

end Sheshadri.FieldBiProjectiveLocalMultiplicity

namespace Sheshadri.FieldIncidence
variable {k₀ : Type*} [Field k₀] [CharZero k₀]
open Incidence
open Matrix MvPolynomial FieldMultiProjective FieldProjectiveLocalMultiplicity
open scoped BigOperators

theorem ordinary_incidence_multiplicity_bound
    {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) {P : Type} [Fintype P]
    (A : PencilCoefficients n m k₀) (Λ : Matrix (Fin (m - 1)) (Fin m) k₀)
    (flags : Fin (n - 2) → Fin (n + 1) → k₀) (M : Fin (n + 1) → k₀)
    (points : P → OrdinaryVar n m → k₀) (charts : ∀ p, Chart (points p))
    (hzero : ∀ p e, eval (points p) (ordinarySystem A Λ flags M e) = 0)
    [∀ p, IsArtinianRing (LocalRing (ordinarySystem A Λ flags M)
      (points p) (charts p) (hzero p))]
    (hdistinct : ∀ p q, ProjectivelyEquivalent (points p) (points q) → p = q) :
    (∑ p, multiplicity (ordinarySystem A Λ flags M) (points p) (charts p) (hzero p)) ≤
      (ordinaryBezout m n : ℕ∞) := by
  letI : NeZero m := ⟨by omega⟩
  have hc : Fintype.card (OrdinaryEquationIndex n m) =
      (Fintype.card (Fin (n + 1)) - 1) + (Fintype.card (Fin m) - 1) +
        (Fintype.card (Fin m) - 1) := by
    rw [ordinarySystem_equation_count hn hm]
    simp only [Fintype.card_fin]
    omega
  have hd : ∀ e, IsWeightedHomogeneous (weight (Fin (n + 1)) (Fin m) (Fin m))
      (ordinarySystem A Λ flags M e) (ordinaryDegree e) := by
    have hw : weight (Fin (n + 1)) (Fin m) (Fin m) =
        ordinaryWeight (n := n) (m := m) := by
      funext i
      rcases i with i | (i | i) <;> rfl
    rw [hw]
    exact ordinarySystem_multidegree A Λ flags M
  have h := FieldSingularBezoutWithExcess.isolated_multiplicity_bound
    (ordinarySystem A Λ flags M) ordinaryDegree points charts hc hd hzero hdistinct
  simpa only [Fintype.card_fin, Nat.add_sub_cancel, ordinary_budget_eq m n hm hn] using h

/-- The actual symmetric system with a projective zero-space factor.
The extra coordinate has degree zero in every incidence equation. -/
def symmetricSystemThree {n m : ℕ} (A : PencilCoefficients n m k₀)
    (flags : Fin (n - 2) → Fin (n + 1) → k₀) (M : Fin (n + 1) → k₀) :=
  fun e => rename FieldBezoutArity.embed (symmetricSystem A flags M e)

theorem symmetric_incidence_multiplicity_bound_three
    {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) {P : Type} [Fintype P]
    (A : PencilCoefficients n m k₀)
    (flags : Fin (n - 2) → Fin (n + 1) → k₀) (M : Fin (n + 1) → k₀)
    (points : P → SymmetricVar n m → k₀)
    (charts : ∀ p, Chart (FieldBezoutArity.extendPoint (points p)))
    (hzero : ∀ p e, eval (FieldBezoutArity.extendPoint (points p))
      (symmetricSystemThree A flags M e) = 0)
    [∀ p, IsArtinianRing (LocalRing (symmetricSystemThree A flags M)
      (FieldBezoutArity.extendPoint (points p)) (charts p) (hzero p))]
    (hdistinct : ∀ p q, BiProjectivelyEquivalent (points p) (points q) → p = q) :
    (∑ p, multiplicity (symmetricSystemThree A flags M)
      (FieldBezoutArity.extendPoint (points p)) (charts p) (hzero p)) ≤
      (symmetricBezout m n : ℕ∞) := by
  letI : NeZero m := ⟨by omega⟩
  have hc : Fintype.card (SymmetricEquationIndex n m) =
      (Fintype.card (Fin (n + 1)) - 1) + (Fintype.card (Fin m) - 1) +
        (Fintype.card Unit - 1) := by
    rw [symmetricSystem_equation_count hn]
    simp only [Fintype.card_fin, Fintype.card_unit]
    omega
  have hd : ∀ e, IsWeightedHomogeneous (weight (Fin (n + 1)) (Fin m) Unit)
      (symmetricSystemThree A flags M e) (symmetricDegreeThree e) := by
    intro e
    apply FieldBezoutArity.homogeneous_embed
    have hw : biWeight (Fin (n + 1)) (Fin m) = symmetricWeight (n := n) (m := m) := by
      funext i
      cases i <;> rfl
    rw [hw]
    exact symmetricSystem_multidegree A flags M e
  have hdist : ∀ p q, ProjectivelyEquivalent (FieldBezoutArity.extendPoint (points p))
      (FieldBezoutArity.extendPoint (points q)) → p = q := by
    intro p q h
    obtain ⟨a,b,c,ha,hb,_,hx,hu,_⟩ := h
    exact hdistinct p q ⟨a,b,ha,hb,hx,hu⟩
  have h := FieldSingularBezoutWithExcess.isolated_multiplicity_bound
    (symmetricSystemThree A flags M) symmetricDegreeThree
    (fun p => FieldBezoutArity.extendPoint (points p)) charts hc hd hzero hdist
  simpa only [Fintype.card_fin, Nat.add_sub_cancel, Fintype.card_unit, Nat.sub_self,
    symmetric_budget_eq m n hm hn] using h

/-- The symmetric bound for literal two-factor chart local rings. The
projective zero-space factor is removed by a proved local-ring isomorphism. -/
theorem symmetric_incidence_multiplicity_bound
    {n m : ℕ} (hn : 2 ≤ n) (hm : 1 ≤ m) {P : Type} [Fintype P]
    (A : PencilCoefficients n m k₀)
    (flags : Fin (n - 2) → Fin (n + 1) → k₀) (M : Fin (n + 1) → k₀)
    (points : P → SymmetricVar n m → k₀)
    (charts : ∀ p, FieldBiProjectiveLocalMultiplicity.Chart (points p))
    (hzero : ∀ p e, eval (points p) (symmetricSystem A flags M e) = 0)
    [∀ p, IsArtinianRing (FieldBiProjectiveLocalMultiplicity.LocalRing
      (symmetricSystem A flags M) (points p) (charts p) (hzero p))]
    (hdistinct : ∀ p q, BiProjectivelyEquivalent (points p) (points q) → p = q) :
    (∑ p, FieldBiProjectiveLocalMultiplicity.multiplicity (symmetricSystem A flags M)
      (points p) (charts p) (hzero p)) ≤ (symmetricBezout m n : ℕ∞) := by
  let hz := fun p => FieldBiProjectiveLocalMultiplicity.extend_zero
    (symmetricSystem A flags M) (points p) (hzero p)
  letI (p : P) : IsArtinianRing (LocalRing (symmetricSystemThree A flags M)
      (FieldBezoutArity.extendPoint (points p)) (charts p).extend (hz p)) :=
    (FieldBiProjectiveLocalMultiplicity.localRingEquiv (symmetricSystem A flags M)
      (points p) (charts p) (hzero p)).symm.isArtinianRing
  have h := symmetric_incidence_multiplicity_bound_three hn hm A flags M points
    (fun p => (charts p).extend) hz hdistinct
  have he : (∑ p, FieldBiProjectiveLocalMultiplicity.multiplicity (symmetricSystem A flags M)
      (points p) (charts p) (hzero p)) =
      ∑ p, multiplicity (symmetricSystemThree A flags M)
        (FieldBezoutArity.extendPoint (points p)) (charts p).extend (hz p) := by
    apply Finset.sum_congr rfl
    intro p _
    exact (FieldBiProjectiveLocalMultiplicity.multiplicity_extend
      (symmetricSystem A flags M) (points p) (charts p) (hzero p)).symm
  rwa [he]

end Sheshadri.FieldIncidence
