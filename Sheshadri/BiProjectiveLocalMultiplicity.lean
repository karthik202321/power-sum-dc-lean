/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.BezoutArity
import Sheshadri.ProjectiveLocalMultiplicity

/-!
# Removing the projective zero-space factor from local multiplicities

The normalized three-factor chart quotient is explicitly isomorphic to the
literal two-factor chart quotient. The added coordinate is eliminated by its
equation `z = 1`; all remaining equations and nilpotents are retained.
-/

noncomputable section
namespace Sheshadri.BiProjectiveLocalMultiplicity
open MvPolynomial MultiProjective BezoutArity
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

variable {X U E : Type*}

structure Chart (p : X ⊕ U → ℂ) where
  ix : X
  iu : U
  hx : p (.inl ix) ≠ 0
  hu : p (.inr iu) ≠ 0

def Chart.extend {p : X ⊕ U → ℂ} (c : Chart p) :
    ProjectiveLocalMultiplicity.Chart (extendPoint p) :=
  ⟨c.ix, c.iu, (), c.hx, c.hu, one_ne_zero⟩

def chartEquations (f : E → MvPolynomial (X ⊕ U) ℂ)
    (p : X ⊕ U → ℂ) (c : Chart p) : E ⊕ Fin 2 → MvPolynomial (X ⊕ U) ℂ
  | .inl e => f e
  | .inr 0 => MvPolynomial.X (.inl c.ix) - C (p (.inl c.ix))
  | .inr 1 => MvPolynomial.X (.inr c.iu) - C (p (.inr c.iu))

def chartIdeal (f : E → MvPolynomial (X ⊕ U) ℂ)
    (p : X ⊕ U → ℂ) (c : Chart p) := Ideal.span (Set.range (chartEquations f p c))

theorem chartIdeal_le_pointIdeal (f : E → MvPolynomial (X ⊕ U) ℂ)
    (p : X ⊕ U → ℂ) (c : Chart p) (hz : ∀ e, eval p (f e) = 0) :
    chartIdeal f p c ≤ IsolatedLocalMultiplicity.pointIdeal p := by
  apply Ideal.span_le.mpr
  rintro _ ⟨e,rfl⟩
  rcases e with e | i
  · exact hz e
  · fin_cases i <;> simp [chartEquations]

abbrev LocalRing (f : E → MvPolynomial (X ⊕ U) ℂ)
    (p : X ⊕ U → ℂ) (c : Chart p) (hz : ∀ e, eval p (f e) = 0) :=
  IsolatedLocalMultiplicity.LocalIntersectionRing (chartIdeal f p c) p
    (chartIdeal_le_pointIdeal f p c hz)

def multiplicity (f : E → MvPolynomial (X ⊕ U) ℂ)
    (p : X ⊕ U → ℂ) (c : Chart p) (hz : ∀ e, eval p (f e) = 0) : ℕ∞ :=
  Module.length (LocalRing f p c hz) (LocalRing f p c hz)

def retract : MvPolynomial (Variables X U Unit) ℂ →ₐ[ℂ] MvPolynomial (X ⊕ U) ℂ :=
  aeval (fun i => match i with
    | .inl x => MvPolynomial.X (.inl x)
    | .inr (.inl u) => MvPolynomial.X (.inr u)
    | .inr (.inr _) => 1)

@[simp] theorem retract_rename (q : MvPolynomial (X ⊕ U) ℂ) :
    retract (rename embed q) = q := by
  have he : (retract (X := X) (U := U)).comp (rename embed) = AlgHom.id ℂ _ := by
    ext i
    cases i <;> simp [retract, embed]
  exact DFunLike.congr_fun he q

theorem rename_chart_mem (f : E → MvPolynomial (X ⊕ U) ℂ)
    (p : X ⊕ U → ℂ) (c : Chart p) :
    chartIdeal f p c ≤ (ProjectiveLocalMultiplicity.chartIdeal
      (fun e => rename embed (f e)) (extendPoint p) c.extend).comap (rename embed) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨e,rfl⟩
  apply Ideal.subset_span
  rcases e with e | i
  · exact ⟨.inl e, rfl⟩
  · fin_cases i
    · exact ⟨.inr 0, by simp [chartEquations, ProjectiveLocalMultiplicity.chartEquations,
        ProjectiveLocalMultiplicity.Chart.coordinate, Chart.extend, embed, extendPoint]⟩
    · exact ⟨.inr 1, by simp [chartEquations, ProjectiveLocalMultiplicity.chartEquations,
        ProjectiveLocalMultiplicity.Chart.coordinate, Chart.extend, embed, extendPoint]⟩

theorem retract_chart_mem (f : E → MvPolynomial (X ⊕ U) ℂ)
    (p : X ⊕ U → ℂ) (c : Chart p) :
    ProjectiveLocalMultiplicity.chartIdeal (fun e => rename embed (f e))
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
        ProjectiveLocalMultiplicity.chartEquations, ProjectiveLocalMultiplicity.Chart.coordinate,
        Chart.extend, extendPoint] using he
    · have he : chartEquations f p c (.inr 1) ∈ chartIdeal f p c :=
        Ideal.subset_span ⟨.inr 1, rfl⟩
      simpa [Ideal.mem_comap, retract, chartEquations,
        ProjectiveLocalMultiplicity.chartEquations, ProjectiveLocalMultiplicity.Chart.coordinate,
        Chart.extend, extendPoint] using he
    · simp [Ideal.mem_comap, retract, ProjectiveLocalMultiplicity.chartEquations,
        ProjectiveLocalMultiplicity.Chart.coordinate, Chart.extend, extendPoint]

def chartRingEquiv (f : E → MvPolynomial (X ⊕ U) ℂ)
    (p : X ⊕ U → ℂ) (c : Chart p) :
    (MvPolynomial (Variables X U Unit) ℂ ⧸ ProjectiveLocalMultiplicity.chartIdeal
      (fun e => rename embed (f e)) (extendPoint p) c.extend) ≃ₐ[ℂ]
        (MvPolynomial (X ⊕ U) ℂ ⧸ chartIdeal f p c) := by
  let I := chartIdeal f p c
  let J := ProjectiveLocalMultiplicity.chartIdeal (fun e => rename embed (f e))
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

@[simp] theorem chartRingEquiv_mk (f : E → MvPolynomial (X ⊕ U) ℂ)
    (p : X ⊕ U → ℂ) (c : Chart p) (q : MvPolynomial (Variables X U Unit) ℂ) :
    chartRingEquiv f p c (Ideal.Quotient.mk _ q) =
      Ideal.Quotient.mk (chartIdeal f p c) (retract q) := rfl

theorem eval_retract (p : X ⊕ U → ℂ) (q : MvPolynomial (Variables X U Unit) ℂ) :
    eval p (retract q) = eval (extendPoint p) q := by
  have he : (aeval p).comp retract = aeval (extendPoint p) := by
    ext i
    rcases i with i | (i | i) <;> simp [retract, extendPoint]
  exact DFunLike.congr_fun he q

theorem extend_zero (f : E → MvPolynomial (X ⊕ U) ℂ) (p : X ⊕ U → ℂ)
    (hz : ∀ e, eval p (f e) = 0) :
    ∀ e, eval (extendPoint p) (rename embed (f e)) = 0 := by
  intro e
  simpa only [eval_rename, extendPoint_comp_embed] using hz e

/-- Localizing the explicit chart equivalence at the actual evaluation
points removes the dummy factor from the actual local rings. -/
def localRingEquiv (f : E → MvPolynomial (X ⊕ U) ℂ)
    (p : X ⊕ U → ℂ) (c : Chart p) (hz : ∀ e, eval p (f e) = 0) :
    ProjectiveLocalMultiplicity.LocalRing (fun e => rename embed (f e))
      (extendPoint p) c.extend (extend_zero f p hz) ≃+* LocalRing f p c hz := by
  let e := (chartRingEquiv f p c).toRingEquiv
  let P := IsolatedLocalMultiplicity.quotientPointIdeal
    (ProjectiveLocalMultiplicity.chartIdeal (fun e => rename embed (f e))
      (extendPoint p) c.extend) (extendPoint p)
      (ProjectiveLocalMultiplicity.chartIdeal_le_pointIdeal _ _ _ (extend_zero f p hz))
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

theorem multiplicity_extend (f : E → MvPolynomial (X ⊕ U) ℂ)
    (p : X ⊕ U → ℂ) (c : Chart p) (hz : ∀ e, eval p (f e) = 0) :
    ProjectiveLocalMultiplicity.multiplicity (fun e => rename embed (f e))
      (extendPoint p) c.extend (extend_zero f p hz) = multiplicity f p c hz :=
  ProjectiveCycleLengths.ringEquiv_length (localRingEquiv f p c hz)

end Sheshadri.BiProjectiveLocalMultiplicity
