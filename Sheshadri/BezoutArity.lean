/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.MultiProjectiveBezout
import Sheshadri.IncidenceDifferential

/-!
# The two-factor Bezout principle follows from the three-factor principle

The third factor is projective zero-space. Polynomials are renamed into the
first two variable blocks, the third coordinate is fixed to 1, and the third
degree is zero. Homogeneity, tangent simplicity, distinctness, and the budget
are all transported explicitly. No additional axiom is used.
-/

noncomputable section
namespace Sheshadri.BezoutArity

open MvPolynomial MultiProjective IncidenceDifferential

def embed {X U : Type*} : X ⊕ U → Variables X U Unit
  | .inl x => .inl x
  | .inr u => .inr (.inl u)

def extendPoint {X U : Type*} (p : X ⊕ U → ℂ) : Variables X U Unit → ℂ
  | .inl x => p (.inl x)
  | .inr (.inl u) => p (.inr u)
  | .inr (.inr _) => 1

theorem extendPoint_comp_embed {X U : Type*} (p : X ⊕ U → ℂ) :
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

theorem homogeneous_embed {X U : Type*} (f : MvPolynomial (X ⊕ U) ℂ)
    (d : ℕ × ℕ) (hf : IsWeightedHomogeneous (biWeight X U) f d) :
    IsWeightedHomogeneous (weight X U Unit) (rename embed f) (d.1, d.2, 0) := by
  intro s hs
  obtain ⟨r, rfl, hr⟩ := coeff_rename_ne_zero embed f s hs
  rw [embed_weight, hf hr]

theorem directional_rename {σ τ : Type*} [Fintype σ] [Fintype τ]
    (e : σ → τ) (f : MvPolynomial σ ℂ) (p v : τ → ℂ) :
    directional (rename e f) p v = directional f (p ∘ e) (v ∘ e) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f j hf => simp [hf, eval_rename, Function.comp_apply]

theorem simple_extend {X U E : Type*} [Fintype X] [Fintype U]
    (f : E → MvPolynomial (X ⊕ U) ℂ) (p : X ⊕ U → ℂ)
    (hp : BiSimpleInCharts f p) :
    SimpleInCharts (fun e => rename embed (f e)) (extendPoint p) := by
  obtain ⟨ix, iu, hx, hu, hs⟩ := hp
  refine ⟨ix, iu, (), hx, hu, one_ne_zero, ?_⟩
  intro v hvx hvu hvone hv
  have hw : v ∘ embed = 0 := by
    apply hs (v ∘ embed) hvx hvu
    intro e
    simpa only [directional_rename, extendPoint_comp_embed] using hv e
  funext i
  rcases i with i | (i | i)
  · exact congrFun hw (.inl i)
  · exact congrFun hw (.inr i)
  · cases i
    exact hvone

/-- One universal three-factor simple-point Bezout proposition suffices for
both ordinary and symmetric incidence applications. -/
theorem universal_bi_of_universal (h : UniversalSimpleBezout) : UniversalBiSimpleBezout := by
  intro X U E P _ _ _ _ _ _ f degree points hcard hdeg hzero hsimple hdistinct
  have hc : Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
      (Fintype.card Unit - 1) := by simpa using hcard
  have result := h X U Unit E P (fun e => rename embed (f e))
    (fun e => ((degree e).1, (degree e).2, 0)) (fun p => extendPoint (points p)) hc
    (fun e => homogeneous_embed (f e) (degree e) (hdeg e))
    (fun p e => by simpa only [eval_rename, extendPoint_comp_embed] using hzero p e)
    (fun p => simple_extend f (points p) (hsimple p))
    (fun p q hpq => by
      obtain ⟨a, b, c, ha, hb, _, hx, hu, _⟩ := hpq
      exact hdistinct p q ⟨a, b, ha, hb, hx, hu⟩)
  simpa using result

end Sheshadri.BezoutArity
