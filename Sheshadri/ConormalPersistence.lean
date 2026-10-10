/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.PolynomialFamilies
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Smooth Gauss points persist under coefficient perturbations

This is the analytic argument of Section 8: at an arbitrary smooth zero,
fix every coordinate except one with nonzero partial derivative and apply
the inverse function theorem. No Fermat polar slice or counted points occur.
All branches and derivative/nonvanishing facts are proved from actual
polynomial evaluation and formal partial derivatives.
-/

noncomputable section

namespace Sheshadri.ConormalPersistence

open MvPolynomial Filter Function
open scoped Topology

section PolynomialFamily
variable {A Z : Type*} [Fintype A] [Fintype Z]

/-- Scalar evaluation of a polynomial with separate parameter and point variables. -/
def value (F : MvPolynomial (A ⊕ Z) ℂ) (a : A → ℂ) (z : Z → ℂ) : ℂ :=
  eval (Sum.elim a z) F

/-- Every entry is an actual point-variable partial derivative. -/
def gradient (F : MvPolynomial (A ⊕ Z) ℂ) (a : A → ℂ) (z : Z → ℂ) : Z → ℂ :=
  fun i => value (pderiv (Sum.inr i) F) a z

/-- A square system encoding a transverse coordinate line through `z₀`. -/
def transverseSystem [DecidableEq Z] (F : MvPolynomial (A ⊕ Z) ℂ)
    (z₀ : Z → ℂ) (j : Z) : Z → MvPolynomial (A ⊕ Z) ℂ :=
  fun i => if i = j then F else X (Sum.inr i) - C (z₀ i)

omit [Fintype A] [Fintype Z] in
theorem transverseSystem_root [DecidableEq Z]
    (F : MvPolynomial (A ⊕ Z) ℂ) (a₀ : A → ℂ) (z₀ : Z → ℂ) (j : Z)
    (hroot : value F a₀ z₀ = 0) :
    PolynomialFamilies.family (transverseSystem F z₀ j) a₀ z₀ = 0 := by
  funext i
  by_cases hij : i = j
  · simpa [PolynomialFamilies.family, transverseSystem, hij, value] using hroot
  · simp [PolynomialFamilies.family, transverseSystem, hij]

omit [Fintype A] in
theorem transverseSystem_regular [DecidableEq Z]
    (F : MvPolynomial (A ⊕ Z) ℂ) (a₀ : A → ℂ) (z₀ : Z → ℂ) (j : Z)
    (hpartial : gradient F a₀ z₀ j ≠ 0) :
    PolynomialFamilies.Regular (transverseSystem F z₀ j) a₀ z₀ := by
  classical
  intro v hv
  have hother : ∀ i, i ≠ j → v i = 0 := by
    intro i hij
    have hi := hv i
    simpa [transverseSystem, hij, pderiv_C, Pi.single_apply] using hi
  have hj := hv j
  simp only [transverseSystem, ↓reduceIte] at hj
  have hsum : (∑ i, eval (Sum.elim a₀ z₀) (pderiv (Sum.inr i) F) * v i) =
      gradient F a₀ z₀ j * v j := by
    rw [Finset.sum_eq_single j]
    · rfl
    · intro i hi hij
      rw [hother i hij, mul_zero]
    · simp
  rw [hsum] at hj
  have hvj : v j = 0 := (mul_eq_zero.mp hj).resolve_left hpartial
  funext i
  by_cases hij : i = j
  · simpa [hij] using hvj
  · exact hother i hij

theorem continuous_value (F : MvPolynomial (A ⊕ Z) ℂ) :
    Continuous (fun q : (A → ℂ) × (Z → ℂ) => value F q.1 q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  exact ContinuousAt.comp
    (f := fun r : (A → ℂ) × (Z → ℂ) => Sum.elim r.1 r.2)
    (PolynomialAnalytic.hasStrictFDerivAt_eval F (Sum.elim q.1 q.2)).continuousAt
    PolynomialFamilies.split.symm.continuous.continuousAt

theorem continuous_gradient (F : MvPolynomial (A ⊕ Z) ℂ) :
    Continuous (fun q : (A → ℂ) × (Z → ℂ) => gradient F q.1 q.2) := by
  apply continuous_pi
  intro i
  exact continuous_value (pderiv (Sum.inr i) F)

/-- The homogeneous tangent covector in the affine chart `x₀ = 1`.
Euler's identity below identifies this with the homogeneous differential at roots. -/
def gaussCovector (F : MvPolynomial (A ⊕ Z) ℂ)
    (a : A → ℂ) (z : Z → ℂ) : Option Z → ℂ
  | none => - ∑ i, z i * gradient F a z i
  | some i => gradient F a z i

theorem continuous_gaussCovector (F : MvPolynomial (A ⊕ Z) ℂ) :
    Continuous (fun q : (A → ℂ) × (Z → ℂ) => gaussCovector F q.1 q.2) := by
  apply continuous_pi
  intro i
  cases i with
  | none =>
    exact (continuous_finset_sum _ (fun i _ =>
      ((continuous_apply i).comp continuous_snd).mul
        (continuous_value (pderiv (Sum.inr i) F)))).neg
  | some i => exact continuous_value (pderiv (Sum.inr i) F)

/-- Section 8's local persistence statement at any smooth zero. The branch
fixes all but one coordinate. All gradient entries and the entire homogeneous
Gauss covector converge, and a specified partial remains nonzero. -/
theorem smooth_zero_gauss_persistence
    (F : MvPolynomial (A ⊕ Z) ℂ) (a₀ : A → ℂ) (z₀ : Z → ℂ) (j : Z)
    (hroot : value F a₀ z₀ = 0) (hpartial : gradient F a₀ z₀ j ≠ 0) :
    ∃ b : (A → ℂ) → (Z → ℂ),
      b a₀ = z₀ ∧ ContinuousAt b a₀ ∧
      Tendsto (fun a => gradient F a (b a)) (𝓝 a₀) (𝓝 (gradient F a₀ z₀)) ∧
      Tendsto (fun a => gaussCovector F a (b a)) (𝓝 a₀) (𝓝 (gaussCovector F a₀ z₀)) ∧
      ∀ᶠ a in 𝓝 a₀,
        value F a (b a) = 0 ∧ gradient F a (b a) j ≠ 0 ∧
        (∀ i, i ≠ j → b a i = z₀ i) := by
  classical
  let S := transverseSystem F z₀ j
  obtain ⟨e, he⟩ := PolynomialFamilies.exists_total_equiv_derivative S a₀ z₀
    (transverseSystem_regular F a₀ z₀ j hpartial)
  obtain ⟨b, hb0, hbc, hbr⟩ := StableFiniteFibres.exists_local_root_branch
    (PolynomialFamilies.family S) a₀ z₀ e
    (transverseSystem_root F a₀ z₀ j hroot) he
  have hp : Tendsto (fun a => (a, b a)) (𝓝 a₀) (𝓝 (a₀, z₀)) := by
    simpa [hb0] using (continuousAt_id.prodMk hbc).tendsto
  have hg := (continuous_gradient F).continuousAt.tendsto.comp hp
  have hG := (continuous_gaussCovector F).continuousAt.tendsto.comp hp
  have hgn : ∀ᶠ a in 𝓝 a₀, gradient F a (b a) j ≠ 0 :=
    (((continuous_apply j).tendsto (gradient F a₀ z₀)).comp hg).eventually
      (isOpen_ne.mem_nhds hpartial)
  refine ⟨b, hb0, hbc, hg, hG, ?_⟩
  filter_upwards [hbr, hgn] with a ha hn
  refine ⟨?_, hn, ?_⟩
  · have h := congrFun ha j
    simpa [S, PolynomialFamilies.family, transverseSystem, value] using h
  · intro i hij
    have h := congrFun ha i
    simpa [S, PolynomialFamilies.family, transverseSystem, hij, sub_eq_zero] using h

/-- The closed-family step in the original conormal-specialization proof.
The parameter space is arbitrary; `c₀ ∈ closure U` replaces choosing an
analytic sequence. Any closed total family containing the actual smooth
Gauss graph over `U` contains the Gauss point at every smooth limiting zero. -/
theorem limiting_gauss_point_mem_closed_family
    {C : Type*} [TopologicalSpace C]
    (F : MvPolynomial (A ⊕ Z) ℂ) (a : C → A → ℂ)
    (c₀ : C) (U : Set C) (z₀ : Z → ℂ) (j : Z)
    (ha : ContinuousAt a c₀) (hc : c₀ ∈ closure U)
    (hroot : value F (a c₀) z₀ = 0)
    (hpartial : gradient F (a c₀) z₀ j ≠ 0)
    (W : Set (C × (Z → ℂ) × (Option Z → ℂ))) (hW : IsClosed W)
    (hgraph : ∀ c ∈ U, ∀ z : Z → ℂ,
      value F (a c) z = 0 → (∃ i, gradient F (a c) z i ≠ 0) →
      (c, z, gaussCovector F (a c) z) ∈ W) :
    (c₀, z₀, gaussCovector F (a c₀) z₀) ∈ W := by
  obtain ⟨b, hb0, hbc, hg, hG, hb⟩ :=
    smooth_zero_gauss_persistence F (a c₀) z₀ j hroot hpartial
  have hbt : Tendsto (fun c => b (a c)) (𝓝 c₀) (𝓝 z₀) := by
    simpa only [hb0] using hbc.tendsto.comp ha.tendsto
  have hGt := hG.comp ha.tendsto
  have ht : Tendsto (fun c => (c, b (a c), gaussCovector F (a c) (b (a c))))
      (𝓝 c₀) (𝓝 (c₀, z₀, gaussCovector F (a c₀) z₀)) :=
    tendsto_id.prodMk_nhds (hbt.prodMk_nhds hGt)
  haveI : NeBot (𝓝[U] c₀) := mem_closure_iff_nhdsWithin_neBot.mp hc
  apply hW.mem_of_tendsto (b := 𝓝[U] c₀) (ht.mono_left nhdsWithin_le_nhds)
  filter_upwards [(ha.tendsto.eventually hb).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with c hp hcu
  exact hgraph c hcu (b (a c)) hp.1 ⟨j, hp.2.1⟩

end PolynomialFamily

section Coefficients
variable {A Z : Type*} [Fintype A]

/-- Specialization of parameter variables to actual coefficients. -/
def specialize (a : A → ℂ) : MvPolynomial (A ⊕ Z) ℂ →ₐ[ℂ] MvPolynomial Z ℂ :=
  aeval (Sum.elim (fun i => C (a i)) X)

omit [Fintype A] in
@[simp] theorem specialize_C (a : A → ℂ) (c : ℂ) : specialize (Z := Z) a (C c) = C c := by
  simp [specialize]

omit [Fintype A] in
@[simp] theorem specialize_X_inl (a : A → ℂ) (i : A) :
    specialize (Z := Z) a (X (Sum.inl i)) = C (a i) := by simp [specialize]

omit [Fintype A] in
@[simp] theorem specialize_X_inr (a : A → ℂ) (i : Z) :
    specialize a (X (Sum.inr i)) = X i := by simp [specialize]

omit [Fintype A] in
@[simp] theorem specialize_rename (a : A → ℂ) (f : MvPolynomial Z ℂ) :
    specialize a (rename Sum.inr f) = f := by
  simpa [specialize, aeval_rename, Function.comp_def] using aeval_X_left_apply f

omit [Fintype A] in
theorem specialize_pderiv (a : A → ℂ) (f : MvPolynomial (A ⊕ Z) ℂ) (j : Z) :
    specialize a (pderiv (Sum.inr j) f) = pderiv j (specialize a f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c => simp [pderiv_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p q hp =>
    simp only [pderiv_mul, map_add, map_mul, hp]
    cases q <;> simp [Pi.single_apply, pderiv_C]

omit [Fintype A] in
theorem eval_specialize (a : A → ℂ) (z : Z → ℂ) (f : MvPolynomial (A ⊕ Z) ℂ) :
    eval z (specialize a f) = eval (Sum.elim a z) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p q hp => cases q <;> simp [hp]

def perturbation (f : MvPolynomial Z ℂ) (basis : A → MvPolynomial Z ℂ) :
    MvPolynomial (A ⊕ Z) ℂ :=
  rename Sum.inr f + ∑ i, X (Sum.inl i) * rename Sum.inr (basis i)

def perturbed (f : MvPolynomial Z ℂ) (basis : A → MvPolynomial Z ℂ) (a : A → ℂ) :
    MvPolynomial Z ℂ := f + ∑ i, C (a i) * basis i

@[simp] theorem specialize_perturbation (f : MvPolynomial Z ℂ)
    (basis : A → MvPolynomial Z ℂ) (a : A → ℂ) :
    specialize a (perturbation f basis) = perturbed f basis a := by
  simp [perturbation, perturbed]

@[simp] theorem perturbed_zero (f : MvPolynomial Z ℂ)
    (basis : A → MvPolynomial Z ℂ) : perturbed f basis 0 = f := by
  simp [perturbed]

variable [Fintype Z]

omit [Fintype Z] in
theorem perturbation_value (f : MvPolynomial Z ℂ)
    (basis : A → MvPolynomial Z ℂ) (a : A → ℂ) (z : Z → ℂ) :
    value (perturbation f basis) a z = eval z (perturbed f basis a) := by
  simp only [value, ← eval_specialize, specialize_perturbation]

omit [Fintype Z] in
theorem perturbation_gradient (f : MvPolynomial Z ℂ)
    (basis : A → MvPolynomial Z ℂ) (a : A → ℂ) (z : Z → ℂ) (i : Z) :
    gradient (perturbation f basis) a z i = eval z (pderiv i (perturbed f basis a)) := by
  simp only [gradient, value, ← eval_specialize, specialize_pderiv, specialize_perturbation]

/-- Smooth points persist for arbitrary finite polynomial-basis coefficient
perturbations, not only for homogeneous or Fermat polynomials. -/
theorem coefficient_smooth_zero_persistence
    (f : MvPolynomial Z ℂ) (basis : A → MvPolynomial Z ℂ) (z₀ : Z → ℂ) (j : Z)
    (hroot : eval z₀ f = 0) (hpartial : eval z₀ (pderiv j f) ≠ 0) :
    ∃ b : (A → ℂ) → (Z → ℂ),
      b 0 = z₀ ∧ ContinuousAt b 0 ∧
      Tendsto (fun a i => eval (b a) (pderiv i (perturbed f basis a))) (𝓝 0)
        (𝓝 (fun i => eval z₀ (pderiv i f))) ∧
      ∀ᶠ a in 𝓝 0,
        eval (b a) (perturbed f basis a) = 0 ∧
        eval (b a) (pderiv j (perturbed f basis a)) ≠ 0 ∧
        (∀ i, i ≠ j → b a i = z₀ i) := by
  obtain ⟨b, hb0, hbc, hg, hG, hb⟩ := smooth_zero_gauss_persistence
    (perturbation f basis) 0 z₀ j
    (by simpa [perturbation_value] using hroot)
    (by simpa [perturbation_gradient] using hpartial)
  refine ⟨b, hb0, hbc, ?_, ?_⟩
  · change Tendsto (fun a i => gradient (perturbation f basis) a (b a) i) _
      (𝓝 (fun i => gradient (perturbation f basis) 0 z₀ i)) at hg
    simpa only [perturbation_gradient, perturbed_zero] using hg
  · simpa only [perturbation_value, perturbation_gradient] using hb

end Coefficients

section HomogeneousCovector
variable {Z : Type*} [Fintype Z]

/-- Homogeneous coordinates of the affine chart with zeroth coordinate one. -/
def affineLift (z : Z → ℂ) : Option Z → ℂ
  | none => 1
  | some i => z i

/-- Restriction of an actual homogeneous polynomial to the chart `x₀ = 1`. -/
def dehomogenize : MvPolynomial (Option Z) ℂ →ₐ[ℂ] MvPolynomial Z ℂ :=
  aeval (fun i => i.elim 1 X)

omit [Fintype Z] in
@[simp] theorem dehomogenize_C (c : ℂ) :
    dehomogenize (Z := Z) (C c) = C c := by simp [dehomogenize]

omit [Fintype Z] in
@[simp] theorem dehomogenize_X_none :
    dehomogenize (Z := Z) (X none) = 1 := by simp [dehomogenize]

omit [Fintype Z] in
@[simp] theorem dehomogenize_X_some (j : Z) :
    dehomogenize (X (some j)) = X j := by simp [dehomogenize]

omit [Fintype Z] in
theorem eval_dehomogenize (q : MvPolynomial (Option Z) ℂ) (z : Z → ℂ) :
    eval z (dehomogenize q) = eval (affineLift z) q := by
  induction q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp => cases j <;> simp [hp, affineLift]

omit [Fintype Z] in
theorem dehomogenize_pderiv (q : MvPolynomial (Option Z) ℂ) (j : Z) :
    dehomogenize (pderiv (some j) q) = pderiv j (dehomogenize q) := by
  classical
  induction q using MvPolynomial.induction_on with
  | C c => simp [pderiv_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [pderiv_mul, map_add, map_mul, hp]
    cases i <;> simp [Pi.single_apply, pderiv_C]

/-- Euler's identity gives the actual zeroth homogeneous derivative at a root,
for every homogenizing degree. This includes degree-padding at infinity. -/
theorem homogeneous_zeroth_partial_at_root
    (q : MvPolynomial (Option Z) ℂ) (m : ℕ) (hq : q.IsHomogeneous m)
    (z : Z → ℂ) (hroot : eval (affineLift z) q = 0) :
    eval (affineLift z) (pderiv none q) =
      - ∑ i, z i * eval (affineLift z) (pderiv (some i) q) := by
  classical
  have h := congrArg (MvPolynomial.eval (affineLift z)) hq.sum_X_mul_pderiv
  simp only [map_sum, map_add, map_mul, eval_X, map_nsmul, hroot, smul_zero,
    Fintype.sum_option, affineLift, Option.elim_none, Option.elim_some, one_mul] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Identification of the persisting covector with the differential of any
homogeneous polynomial having the given affine restriction. No choice of
homogenizing degree changes the covector along the zero locus in this chart. -/
theorem homogeneous_differential_eq_gaussCovector
    {A : Type*} [Fintype A] (F : MvPolynomial (A ⊕ Z) ℂ) (a : A → ℂ)
    (q : MvPolynomial (Option Z) ℂ) (m : ℕ) (hq : q.IsHomogeneous m)
    (hrestriction : dehomogenize q = specialize a F)
    (z : Z → ℂ) (hroot : value F a z = 0) :
    (fun i => eval (affineLift z) (pderiv i q)) = gaussCovector F a z := by
  have hentry : ∀ i, eval (affineLift z) (pderiv (some i) q) = gradient F a z i := by
    intro i
    rw [← eval_dehomogenize, dehomogenize_pderiv, hrestriction,
      ← specialize_pderiv, eval_specialize]
    rfl
  have hqroot : eval (affineLift z) q = 0 := by
    rw [← eval_dehomogenize, hrestriction, eval_specialize]
    exact hroot
  funext i
  cases i with
  | none =>
    rw [homogeneous_zeroth_partial_at_root q m hq z hqroot]
    simp only [gaussCovector, hentry]
  | some i => exact hentry i

end HomogeneousCovector

end Sheshadri.ConormalPersistence
