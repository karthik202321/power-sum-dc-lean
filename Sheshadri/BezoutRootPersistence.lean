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
import Sheshadri.ConormalPersistence
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Module.Cardinality
import Sheshadri.SaturatedFlatFamily
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.MvPolynomial.Equiv
import Sheshadri.GeneralHomogeneousBaseChange

/-!
# Simultaneous persistence in projective charts, allowing excess components

The selected zeros need only be simple in their own charts. No condition is
placed on any other point or component of the original zero locus. The
implicit-function theorem constructs actual roots of the perturbed equations;
cross-products prove that they remain projectively distinct.
-/

noncomputable section
namespace Sheshadri.BezoutRootPersistence
open MvPolynomial Filter Function MultiProjective
open scoped Topology

theorem proportional_of_cross_products {Z : Type*} (p q : Z → ℂ)
    (hp : ∃ i, p i ≠ 0) (hq : ∃ i, q i ≠ 0)
    (hcross : ∀ i j, p i * q j = p j * q i) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ i, p i = a * q i := by
  obtain ⟨i, hi⟩ := hq
  have hpi : p i ≠ 0 := by
    obtain ⟨j, hj⟩ := hp
    intro he
    have h := hcross j i
    rw [he, zero_mul] at h
    exact (mul_ne_zero hj hi) h
  refine ⟨p i / q i, div_ne_zero hpi hi, ?_⟩
  intro j
  apply (mul_right_cancel₀ hi)
  calc
    p j * q i = p i * q j := hcross j i
    _ = (p i / q i * q j) * q i := by field_simp

abbrev CrossIndex (X U V : Type*) := (X × X) ⊕ ((U × U) ⊕ (V × V))

def cross {X U V : Type*} (p q : Variables X U V → ℂ) : CrossIndex X U V → ℂ
  | .inl (i,j) => p (.inl i) * q (.inl j) - p (.inl j) * q (.inl i)
  | .inr (.inl (i,j)) => p (.inr (.inl i)) * q (.inr (.inl j)) -
      p (.inr (.inl j)) * q (.inr (.inl i))
  | .inr (.inr (i,j)) => p (.inr (.inr i)) * q (.inr (.inr j)) -
      p (.inr (.inr j)) * q (.inr (.inr i))

theorem cross_eq_zero_of_equivalent {X U V : Type*}
    {p q : Variables X U V → ℂ} (h : ProjectivelyEquivalent p q)
    (k : CrossIndex X U V) : cross p q k = 0 := by
  obtain ⟨a,b,c,ha,hb,hc,hX,hU,hV⟩ := h
  rcases k with ⟨i,j⟩ | (⟨i,j⟩ | ⟨i,j⟩)
  · simp only [cross, hX]; ring
  · simp only [cross, hU]; ring
  · simp only [cross, hV]; ring

theorem equivalent_of_cross_eq_zero {X U V : Type*}
    {p q : Variables X U V → ℂ} (hp : HasNonzeroBlocks p) (hq : HasNonzeroBlocks q)
    (h : ∀ k, cross p q k = 0) : ProjectivelyEquivalent p q := by
  obtain ⟨a,ha,hX⟩ := proportional_of_cross_products
    (fun i => p (.inl i)) (fun i => q (.inl i)) hp.1 hq.1
    (fun i j => sub_eq_zero.mp (h (.inl (i,j))))
  obtain ⟨b,hb,hU⟩ := proportional_of_cross_products
    (fun i => p (.inr (.inl i))) (fun i => q (.inr (.inl i))) hp.2.1 hq.2.1
    (fun i j => sub_eq_zero.mp (h (.inr (.inl (i,j)))))
  obtain ⟨c,hc,hV⟩ := proportional_of_cross_products
    (fun i => p (.inr (.inr i))) (fun i => q (.inr (.inr i))) hp.2.2 hq.2.2
    (fun i j => sub_eq_zero.mp (h (.inr (.inr (i,j)))))
  exact ⟨a,b,c,ha,hb,hc,hX,hU,hV⟩

theorem continuous_cross {T X U V : Type*} [TopologicalSpace T]
    (b c : T → Variables X U V → ℂ) (t : T)
    (hb : ContinuousAt b t) (hc : ContinuousAt c t) (k : CrossIndex X U V) :
    ContinuousAt (fun s => cross (b s) (c s) k) t := by
  rcases k with ⟨i,j⟩ | (⟨i,j⟩ | ⟨i,j⟩) <;>
    exact (((continuous_apply _).continuousAt.comp hb).mul
      ((continuous_apply _).continuousAt.comp hc)).sub
      (((continuous_apply _).continuousAt.comp hb).mul
      ((continuous_apply _).continuousAt.comp hc))

/-- Projective distinctness persists even when different roots use different
charts. Affine distinctness alone would not justify this conclusion. -/
theorem eventually_projectively_distinct {P T X U V : Type*}
    [Finite P] [TopologicalSpace T] (b : P → T → Variables X U V → ℂ) (t : T)
    (hb : ∀ p, ContinuousAt (b p) t)
    (hn : ∀ p, HasNonzeroBlocks (b p t))
    (hd : ∀ p q, ProjectivelyEquivalent (b p t) (b q t) → p = q) :
    ∀ᶠ s in 𝓝 t, ∀ p q, ProjectivelyEquivalent (b p s) (b q s) → p = q := by
  apply Filter.eventually_all.mpr
  intro p
  apply Filter.eventually_all.mpr
  intro q
  by_cases hpq : p = q
  · exact Eventually.of_forall (fun _ _ => hpq)
  have hx : ∃ k, cross (b p t) (b q t) k ≠ 0 := by
    by_contra! h
    exact hpq (hd p q (equivalent_of_cross_eq_zero (hn p) (hn q) h))
  obtain ⟨k,hk⟩ := hx
  filter_upwards [(continuous_cross (b p) (b q) t (hb p) (hb q) k).eventually_ne hk]
    with s hs
  intro he
  exact False.elim (hs (cross_eq_zero_of_equivalent he k))

section Chart
variable {A Z E J : Type*} [Fintype A] [Fintype Z] [Fintype E] [Fintype J]

def augmentedSystem (F : E → MvPolynomial (A ⊕ Z) ℂ)
    (chart : J → Z) (z : Z → ℂ) (e : Z ≃ E ⊕ J) :
    Z → MvPolynomial (A ⊕ Z) ℂ :=
  fun i => Sum.elim F (fun j => X (Sum.inr (chart j)) - C (z (chart j))) (e i)

omit [Fintype A] [Fintype Z] [Fintype E] [Fintype J] in
theorem augmentedSystem_root (F : E → MvPolynomial (A ⊕ Z) ℂ)
    (chart : J → Z) (a : A → ℂ) (z : Z → ℂ) (e : Z ≃ E ⊕ J)
    (hr : ∀ i, eval z (ConormalPersistence.specialize a (F i)) = 0) :
    PolynomialFamilies.family (augmentedSystem F chart z e) a z = 0 := by
  funext i
  simp only [PolynomialFamilies.family, augmentedSystem, Pi.zero_apply]
  rcases h : e i with k | k
  · simpa only [h, Sum.elim_inl, ConormalPersistence.eval_specialize] using hr k
  · simp

omit [Fintype A] [Fintype E] [Fintype J] in
theorem augmentedSystem_regular (F : E → MvPolynomial (A ⊕ Z) ℂ)
    (chart : J → Z) (a : A → ℂ) (z : Z → ℂ) (e : Z ≃ E ⊕ J)
    (hker : ∀ v : Z → ℂ, (∀ j, v (chart j) = 0) →
      (∀ i, directional (ConormalPersistence.specialize a (F i)) z v = 0) → v = 0) :
    PolynomialFamilies.Regular (augmentedSystem F chart z e) a z := by
  classical
  intro v hv
  apply hker v
  · intro j
    have h := hv (e.symm (.inr j))
    simpa [augmentedSystem, Pi.single_apply] using h
  · intro i
    have h := hv (e.symm (.inl i))
    simpa only [augmentedSystem, Equiv.apply_symm_apply, Sum.elim_inl,
      directional, ← ConormalPersistence.specialize_pderiv,
      ConormalPersistence.eval_specialize] using h

omit [Fintype E] [Fintype J] in
/-- A branch in an actual polynomial family, with the selected projective
chart coordinates fixed to their original nonzero values. -/
theorem exists_chart_root_branch (F : E → MvPolynomial (A ⊕ Z) ℂ)
    (chart : J → Z) (a : A → ℂ) (z : Z → ℂ) (e : Z ≃ E ⊕ J)
    (hr : ∀ i, eval z (ConormalPersistence.specialize a (F i)) = 0)
    (hker : ∀ v : Z → ℂ, (∀ j, v (chart j) = 0) →
      (∀ i, directional (ConormalPersistence.specialize a (F i)) z v = 0) → v = 0) :
    ∃ b : (A → ℂ) → Z → ℂ, b a = z ∧ ContinuousAt b a ∧
      ∀ᶠ s in 𝓝 a,
        (∀ i, eval (b s) (ConormalPersistence.specialize s (F i)) = 0) ∧
        (∀ j, b s (chart j) = z (chart j)) := by
  let G := augmentedSystem F chart z e
  obtain ⟨D,hD⟩ := PolynomialFamilies.exists_total_equiv_derivative G a z
    (augmentedSystem_regular F chart a z e hker)
  obtain ⟨b,hb,hc,hrb⟩ := StableFiniteFibres.exists_local_root_branch
    (PolynomialFamilies.family G) a z D (augmentedSystem_root F chart a z e hr) hD
  refine ⟨b,hb,hc,?_⟩
  filter_upwards [hrb] with s hs
  constructor
  · intro i
    have h := congrFun hs (e.symm (.inl i))
    simpa [G, PolynomialFamilies.family, augmentedSystem,
      ConormalPersistence.eval_specialize] using h
  · intro j
    have h := congrFun hs (e.symm (.inr j))
    simpa [G, PolynomialFamilies.family, augmentedSystem, sub_eq_zero] using h

end Chart

section MultiProjective
variable {A X U V E : Type*} [Fintype A] [Fintype X] [Fintype U]
    [Fintype V] [Fintype E] [Nonempty X] [Nonempty U] [Nonempty V]

theorem chart_equation_cardinality
    (hcard : Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
      (Fintype.card V - 1)) :
    Fintype.card (Variables X U V) = Fintype.card (E ⊕ Fin 3) := by
  have hx : 0 < Fintype.card X := Fintype.card_pos
  have hu : 0 < Fintype.card U := Fintype.card_pos
  have hv : 0 < Fintype.card V := Fintype.card_pos
  simp only [Variables, Fintype.card_sum, Fintype.card_fin]
  omega

/-- Each selected simple projective root has an actual continuous branch.
The three normalization coordinates can depend on the selected root. -/
theorem simple_projective_root_persists
    (F : E → MvPolynomial (A ⊕ Variables X U V) ℂ)
    (a : A → ℂ) (z : Variables X U V → ℂ)
    (hcard : Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
      (Fintype.card V - 1))
    (hr : ∀ i, eval z (ConormalPersistence.specialize a (F i)) = 0)
    (hs : SimpleInCharts (fun i => ConormalPersistence.specialize a (F i)) z) :
    ∃ b : (A → ℂ) → Variables X U V → ℂ, b a = z ∧ ContinuousAt b a ∧
      ∀ᶠ s in 𝓝 a,
        (∀ i, eval (b s) (ConormalPersistence.specialize s (F i)) = 0) ∧
        HasNonzeroBlocks (b s) := by
  classical
  obtain ⟨ix,iu,iv,hx,hu,hv,hker⟩ := hs
  let chart : Fin 3 → Variables X U V := ![.inl ix, .inr (.inl iu), .inr (.inr iv)]
  let e : Variables X U V ≃ E ⊕ Fin 3 :=
    Fintype.equivOfCardEq (chart_equation_cardinality hcard)
  have hk : ∀ v : Variables X U V → ℂ, (∀ j, v (chart j) = 0) →
      (∀ i, directional (ConormalPersistence.specialize a (F i)) z v = 0) → v = 0 := by
    intro v hn he
    exact hker v (by simpa [chart] using hn 0)
      (by simpa [chart] using hn 1) (by simpa [chart] using hn 2) he
  obtain ⟨b,hb,hc,he⟩ := exists_chart_root_branch F chart a z e hr hk
  refine ⟨b,hb,hc,?_⟩
  filter_upwards [he] with s h
  refine ⟨h.1, ⟨ix,?_⟩, ⟨iu,?_⟩, ⟨iv,?_⟩⟩
  · have hn : b s (.inl ix) = z (.inl ix) := by simpa [chart] using h.2 0
    simpa only [hn] using hx
  · have hn : b s (.inr (.inl iu)) = z (.inr (.inl iu)) := by
      simpa [chart] using h.2 1
    simpa only [hn] using hu
  · have hn : b s (.inr (.inr iv)) = z (.inr (.inr iv)) := by
      simpa [chart] using h.2 2
    simpa only [hn] using hv

/-- The deformation step for Bézout with excess components. Every finite
family of projectively distinct simple zeros persists simultaneously under
arbitrary polynomial coefficient perturbations. No proper-intersection or
dimension hypothesis is imposed on the original common zero locus. -/
theorem finite_projective_roots_persist {P : Type*} [Finite P]
    (F : E → MvPolynomial (A ⊕ Variables X U V) ℂ)
    (a : A → ℂ) (z : P → Variables X U V → ℂ)
    (hcard : Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
      (Fintype.card V - 1))
    (hr : ∀ p i, eval (z p) (ConormalPersistence.specialize a (F i)) = 0)
    (hs : ∀ p, SimpleInCharts (fun i => ConormalPersistence.specialize a (F i)) (z p))
    (hd : ∀ p q, ProjectivelyEquivalent (z p) (z q) → p = q) :
    ∃ b : P → (A → ℂ) → Variables X U V → ℂ,
      (∀ p, b p a = z p) ∧ (∀ p, ContinuousAt (b p) a) ∧
      ∀ᶠ s in 𝓝 a,
        (∀ p i, eval (b p s) (ConormalPersistence.specialize s (F i)) = 0) ∧
        (∀ p, HasNonzeroBlocks (b p s)) ∧
        (∀ p q, ProjectivelyEquivalent (b p s) (b q s) → p = q) := by
  choose b hb hc he using fun p => simple_projective_root_persists
    F a (z p) hcard (hr p) (hs p)
  have hn : ∀ p, HasNonzeroBlocks (b p a) := by
    intro p
    rw [hb]
    obtain ⟨ix,iu,iv,hx,hu,hv,hrest⟩ := hs p
    exact ⟨⟨ix,hx⟩, ⟨iu,hu⟩, ⟨iv,hv⟩⟩
  have hdist := eventually_projectively_distinct b a hc hn
    (fun p q h => hd p q (by simpa only [hb] using h))
  refine ⟨b,hb,hc,?_⟩
  filter_upwards [Filter.eventually_all.mpr he, hdist] with s hs hd
  exact ⟨fun p => (hs p).1, fun p => (hs p).2, hd⟩

end MultiProjective

section Saturation
variable {Z E : Type*} [Fintype Z]

/-- The actual scalar parameter polynomial in the larger polynomial ring. -/
def parameterPolynomial (q : Polynomial ℂ) : MvPolynomial (Unit ⊕ Z) ℂ :=
  Polynomial.eval₂RingHom C (X (Sum.inl ())) q

omit [Fintype Z] in
@[simp] theorem eval_parameterPolynomial (q : Polynomial ℂ) (w : Unit ⊕ Z → ℂ) :
    eval w (parameterPolynomial q) = q.eval (w (.inl ())) := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    change eval w ((Polynomial.eval₂RingHom C (X (Sum.inl ()))) (q+r)) = _
    rw [map_add, map_add, Polynomial.eval_add]
    exact congrArg₂ (· + ·) hq hr
  | monomial k c => simp [parameterPolynomial, Polynomial.eval₂_monomial,
      Polynomial.eval_monomial]

/-- A denominator-cleared radical relation forces vanishing on the special
root of a continuous branch. Denominator zeros, including the special
parameter itself, are handled by density and continuity. -/
theorem vanishes_on_branch_of_clear_denominator
    (F : E → MvPolynomial (Unit ⊕ Z) ℂ)
    (G : MvPolynomial (Unit ⊕ Z) ℂ) (q : Polynomial ℂ) (hq : q ≠ 0) (N : ℕ)
    (hmem : parameterPolynomial q * G ^ N ∈ Ideal.span (Set.range F))
    (a : ℂ) (b : ℂ → Z → ℂ) (hb : ContinuousAt b a)
    (hr : ∀ᶠ t in 𝓝 a, ∀ i, eval (Sum.elim (fun _ : Unit => t) (b t)) (F i) = 0) :
    eval (Sum.elim (fun _ : Unit => a) (b a)) G = 0 := by
  let w : ℂ → Unit ⊕ Z → ℂ := fun t => Sum.elim (fun _ => t) (b t)
  have hw : ContinuousAt w a := by
    apply continuousAt_pi.mpr
    rintro (i|i)
    · exact continuousAt_id
    · exact (continuous_apply i).continuousAt.comp hb
  have hc : ContinuousAt (fun t => eval (w t) G) a :=
    (PolynomialAnalytic.hasStrictFDerivAt_eval G (w a)).continuousAt.comp hw
  have hd : Dense {t : ℂ | q.eval t ≠ 0} :=
    (Polynomial.finite_setOf_isRoot hq).countable.dense_compl ℂ
  letI : NeBot (𝓝[{t : ℂ | q.eval t ≠ 0}] a) :=
    mem_closure_iff_nhdsWithin_neBot.mp (hd a)
  have hv : ∀ᶠ t in 𝓝[{t : ℂ | q.eval t ≠ 0}] a, eval (w t) G = 0 := by
    filter_upwards [self_mem_nhdsWithin, hr.filter_mono nhdsWithin_le_nhds] with t ht hrt
    have hk : Ideal.span (Set.range F) ≤ RingHom.ker (eval (w t)) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hrt i
    have h := hk hmem
    change eval (w t) (parameterPolynomial q * G ^ N) = 0 at h
    rw [map_mul, map_pow, eval_parameterPolynomial] at h
    exact pow_eq_zero ((mul_eq_zero.mp h).resolve_left ht)
  exact isClosed_singleton.mem_of_tendsto
    (hc.tendsto.mono_left nhdsWithin_le_nhds) hv

/-- Direct application to a selected simple multiprojective zero. This is
the inclusion needed when the deformed family is replaced by the contraction
of its radical generic-fibre ideal: any cleared-denominator element still
vanishes at the original simple zero. Excess components are unrestricted. -/
theorem simple_root_vanishes_of_clear_denominator
    {X U V : Type*} [Fintype X] [Fintype U] [Fintype V] [Fintype E]
    [Nonempty X] [Nonempty U] [Nonempty V]
    (F : E → MvPolynomial (Unit ⊕ Variables X U V) ℂ)
    (a : ℂ) (z : Variables X U V → ℂ)
    (hcard : Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
      (Fintype.card V - 1))
    (hr : ∀ i, eval z (ConormalPersistence.specialize (fun _ => a) (F i)) = 0)
    (hs : SimpleInCharts (fun i => ConormalPersistence.specialize (fun _ => a) (F i)) z)
    (G : MvPolynomial (Unit ⊕ Variables X U V) ℂ)
    (q : Polynomial ℂ) (hq : q ≠ 0) (N : ℕ)
    (hmem : parameterPolynomial q * G ^ N ∈ Ideal.span (Set.range F)) :
    eval z (ConormalPersistence.specialize (fun _ => a) G) = 0 := by
  obtain ⟨b,hb,hc,he⟩ := simple_projective_root_persists F (fun _ => a) z hcard hr hs
  let par : ℂ → Unit → ℂ := fun t _ => t
  have hp : Continuous par := continuous_pi (fun _ => continuous_id)
  have hbc : ContinuousAt (fun t => b (par t)) a := hc.comp hp.continuousAt
  have her : ∀ᶠ t in 𝓝 a,
      ∀ i, eval (Sum.elim (par t) (b (par t))) (F i) = 0 := by
    filter_upwards [hp.continuousAt.tendsto.eventually he] with t ht
    intro i
    simpa only [ConormalPersistence.eval_specialize] using ht.1 i
  have h := vanishes_on_branch_of_clear_denominator F G q hq N hmem a
    (fun t => b (par t)) hbc her
  simpa only [par, hb, ConormalPersistence.eval_specialize] using h

end Saturation

section Horizontal
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {R K Z : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K]

/-- Membership in the actual contracted generic radical yields a concrete
nonzero scalar denominator and power relation in the original ideal. -/
theorem clear_denominator_of_mem_horizontal
    (I : Ideal (MvPolynomial Z R)) (p : MvPolynomial Z R)
    (hp : p ∈ SaturatedFlatFamily.horizontalIdeal R K
      (I.map (algebraMap (MvPolynomial Z R) (MvPolynomial Z K)))) :
    ∃ q : R, q ≠ 0 ∧ ∃ N : ℕ, C q * p ^ N ∈ I := by
  rw [SaturatedFlatFamily.horizontalIdeal_eq_comap] at hp
  obtain ⟨N,hN⟩ := Ideal.mem_radical_iff.mp hp
  change (algebraMap (MvPolynomial Z R) (MvPolynomial Z K) p)^N ∈ _ at hN
  rw [← map_pow] at hN
  obtain ⟨s,hs,hsp⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((nonZeroDivisors R).map (C (σ := Z))) (MvPolynomial Z K) I (p^N)).mp hN
  obtain ⟨q,hq,rfl⟩ := hs
  exact ⟨q, mem_nonZeroDivisors_iff_ne_zero.mp hq, N, hsp⟩

end Horizontal

section CoefficientPresentation
variable {Z : Type*}

def parameterCoordinates : Unit ⊕ Z ≃ Option Z where
  toFun := Sum.elim (fun _ => none) some
  invFun := fun i => Option.elim i (Sum.inl ()) Sum.inr
  left_inv := by rintro (⟨⟩ | i) <;> rfl
  right_inv := by rintro (⟨⟩ | i) <;> rfl

def coefficientEquiv : MvPolynomial (Unit ⊕ Z) ℂ ≃ₐ[ℂ] MvPolynomial Z (Polynomial ℂ) :=
  (renameEquiv ℂ parameterCoordinates).trans (optionEquivRight ℂ Z)

@[simp] theorem coefficientEquiv_C (c : ℂ) :
    coefficientEquiv (Z := Z) (C c) = C (Polynomial.C c) := by
  simp [coefficientEquiv, optionEquivRight_C]

@[simp] theorem coefficientEquiv_parameter :
    coefficientEquiv (Z := Z) (X (Sum.inl ())) = C Polynomial.X := by
  simp [coefficientEquiv, parameterCoordinates, optionEquivRight_X_none]

@[simp] theorem coefficientEquiv_spatial (i : Z) :
    coefficientEquiv (X (Sum.inr i)) = X i := by
  simp [coefficientEquiv, parameterCoordinates, optionEquivRight_X_some]

theorem coefficientEquiv_parameterPolynomial (q : Polynomial ℂ) :
    coefficientEquiv (Z := Z) (parameterPolynomial q) = C q := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr =>
    change coefficientEquiv ((Polynomial.eval₂RingHom C (X (Sum.inl ()))) (q+r)) = _
    rw [map_add, map_add, map_add]
    exact congrArg₂ (· + ·) hq hr
  | monomial n c =>
    change coefficientEquiv ((Polynomial.monomial n c).eval₂ C (X (Sum.inl ()))) = _
    rw [Polynomial.eval₂_monomial, map_mul, map_pow,
      coefficientEquiv_C, coefficientEquiv_parameter]
    rw [← map_pow, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]

theorem coefficientEquiv_rename (f : MvPolynomial Z ℂ) :
    coefficientEquiv (rename Sum.inr f) = MvPolynomial.map Polynomial.C f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg]
  | mul_X f i hf => simp [hf]

theorem eval_coefficientEquiv (a : ℂ) (z : Z → ℂ) (G : MvPolynomial (Unit ⊕ Z) ℂ) :
    eval₂ (Polynomial.evalRingHom a) z (coefficientEquiv G) =
      eval (Sum.elim (fun _ => a) z) G := by
  induction G using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf,hg]
  | mul_X f i hf =>
    cases i with
    | inl u => cases u; simp [hf]
    | inr i => simp [hf]

/-- Linear interpolation between the original and split systems, with an
actual coefficient variable rather than an abstract family certificate. -/
def interpolation (f g : MvPolynomial Z ℂ) : MvPolynomial (Unit ⊕ Z) ℂ :=
  (1 - X (Sum.inl ())) * rename Sum.inr f + X (Sum.inl ()) * rename Sum.inr g

@[simp] theorem specialize_interpolation (f g : MvPolynomial Z ℂ) (t : ℂ) :
    ConormalPersistence.specialize (fun _ => t) (interpolation f g) =
      C (1-t) * f + C t * g := by
  simp [interpolation]

@[simp] theorem specialize_interpolation_zero (f g : MvPolynomial Z ℂ) :
    ConormalPersistence.specialize (fun _ => (0 : ℂ)) (interpolation f g) = f := by simp

@[simp] theorem specialize_interpolation_one (f g : MvPolynomial Z ℂ) :
    ConormalPersistence.specialize (fun _ => (1 : ℂ)) (interpolation f g) = g := by simp

theorem coefficientEquiv_interpolation (f g : MvPolynomial Z ℂ) :
    coefficientEquiv (interpolation f g) =
      C (1-Polynomial.X) * MvPolynomial.map Polynomial.C f +
        C Polynomial.X * MvPolynomial.map Polynomial.C g := by
  simp [interpolation, coefficientEquiv_rename]

/-- The coefficient interpolation has exactly the same multidegree as its
endpoints; the parameter is part of the coefficient ring and has degree zero. -/
theorem coefficient_interpolation_homogeneous {Γ : Type*} [AddCommMonoid Γ]
    (w : Z → Γ) (d : Γ) (f g : MvPolynomial Z ℂ)
    (hf : f.IsWeightedHomogeneous w d) (hg : g.IsWeightedHomogeneous w d) :
    (coefficientEquiv (interpolation f g)).IsWeightedHomogeneous w d := by
  rw [coefficientEquiv_interpolation]
  have hf' := GeneralHomogeneousBaseChange.weightedHomogeneous_map Polynomial.C w hf
  have hg' := GeneralHomogeneousBaseChange.weightedHomogeneous_map Polynomial.C w hg
  have h₁ := (isWeightedHomogeneous_C w (1-Polynomial.X : Polynomial ℂ)).mul hf'
  have h₂ := (isWeightedHomogeneous_C w (Polynomial.X : Polynomial ℂ)).mul hg'
  simpa only [zero_add] using h₁.add h₂

end CoefficientPresentation

section ActualHorizontalContainment
attribute [local instance] MvPolynomial.algebraMvPolynomial
variable {K X U V E : Type*} [Field K] [Algebra (Polynomial ℂ) K]
    [IsFractionRing (Polynomial ℂ) K]
    [Fintype X] [Fintype U] [Fintype V] [Fintype E]
    [Nonempty X] [Nonempty U] [Nonempty V]

/-- Every actual simple special root belongs to the fibre of the actual
contracted generic radical. This derives the family-specific containment
from localization, ideal membership and the analytic branch construction. -/
theorem simple_root_annihilates_horizontal_ideal
    (F : E → MvPolynomial (Unit ⊕ Variables X U V) ℂ)
    (a : ℂ) (z : Variables X U V → ℂ)
    (hcard : Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
      (Fintype.card V - 1))
    (hr : ∀ i, eval z (ConormalPersistence.specialize (fun _ => a) (F i)) = 0)
    (hs : SimpleInCharts (fun i => ConormalPersistence.specialize (fun _ => a) (F i)) z)
    (p : MvPolynomial (Variables X U V) (Polynomial ℂ))
    (hp : p ∈ SaturatedFlatFamily.horizontalIdeal (Polynomial ℂ) K
      (((Ideal.span (Set.range F)).map coefficientEquiv.toRingHom).map
        (algebraMap (MvPolynomial (Variables X U V) (Polynomial ℂ))
          (MvPolynomial (Variables X U V) K)))) :
    eval₂ (Polynomial.evalRingHom a) z p = 0 := by
  obtain ⟨q,hq,N,hN⟩ := clear_denominator_of_mem_horizontal _ p hp
  obtain ⟨G,hG,hEq⟩ := (Ideal.mem_map_iff_of_surjective
    coefficientEquiv.toRingHom coefficientEquiv.surjective).mp hN
  have hGEq : G = parameterPolynomial q * (coefficientEquiv.symm p)^N := by
    apply coefficientEquiv.injective
    rw [map_mul, map_pow, coefficientEquiv_parameterPolynomial,
      AlgEquiv.apply_symm_apply]
    exact hEq
  rw [hGEq] at hG
  have h := simple_root_vanishes_of_clear_denominator F a z hcard hr hs
    (coefficientEquiv.symm p) q hq N hG
  rw [ConormalPersistence.eval_specialize] at h
  simpa only [← eval_coefficientEquiv, AlgEquiv.apply_symm_apply] using h

/-- The same actual containment for the nonreduced generic ideal, sufficient
for excess Bézout. Radicalization is not required in this corollary. -/
theorem simple_root_annihilates_contracted_ideal
    (F : E → MvPolynomial (Unit ⊕ Variables X U V) ℂ)
    (a : ℂ) (z : Variables X U V → ℂ)
    (hcard : Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
      (Fintype.card V - 1))
    (hr : ∀ i, eval z (ConormalPersistence.specialize (fun _ => a) (F i)) = 0)
    (hs : SimpleInCharts (fun i => ConormalPersistence.specialize (fun _ => a) (F i)) z)
    (p : MvPolynomial (Variables X U V) (Polynomial ℂ))
    (hp : MvPolynomial.map (algebraMap (Polynomial ℂ) K) p ∈
      ((Ideal.span (Set.range F)).map coefficientEquiv.toRingHom).map
        (MvPolynomial.map (algebraMap (Polynomial ℂ) K))) :
    eval₂ (Polynomial.evalRingHom a) z p = 0 := by
  apply simple_root_annihilates_horizontal_ideal (K := K) F a z hcard hr hs p
  rw [SaturatedFlatFamily.horizontalIdeal_eq_comap]
  exact Ideal.le_radical hp

/-- Concrete interpolation form of special-fibre containment. -/
theorem original_simple_root_annihilates_interpolation_contraction
    (f g : E → MvPolynomial (Variables X U V) ℂ)
    (z : Variables X U V → ℂ)
    (hcard : Fintype.card E = (Fintype.card X - 1) + (Fintype.card U - 1) +
      (Fintype.card V - 1))
    (hr : ∀ i, eval z (f i) = 0) (hs : SimpleInCharts f z)
    (p : MvPolynomial (Variables X U V) (Polynomial ℂ))
    (hp : MvPolynomial.map (algebraMap (Polynomial ℂ) K) p ∈
      (Ideal.span (Set.range (fun i => coefficientEquiv (interpolation (f i) (g i))))).map
        (MvPolynomial.map (algebraMap (Polynomial ℂ) K))) :
    eval₂ (Polynomial.evalRingHom 0) z p = 0 := by
  apply simple_root_annihilates_contracted_ideal (K := K)
    (fun i => interpolation (f i) (g i)) 0 z hcard
    (by simpa using hr) (by simpa using hs) p
  simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def] using hp

end ActualHorizontalContainment
end Sheshadri.BezoutRootPersistence
