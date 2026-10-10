/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalZariski
import Sheshadri.ConormalTopology
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# The actual closed total Gauss family

The total family is constructed here as the polynomial Zariski closure of the
smooth Gauss representatives at the good parameters. Its closedness, algebraic
fibres and special-fibre containment are proved, rather than supplied as
certificate fields. The parameter space is a finite affine complex space;
one may choose the good parameters inside an embedded algebraic curve.

The construction gives the reduced affine closure of homogeneous
representatives. It does not assert projective flatness, purity, or a cycle
degree formula. Those are separate obligations.
-/

noncomputable section
namespace Sheshadri.ActualGaussFamily

open MvPolynomial Set
open ZariskiBridge ConormalZariski
open scoped Topology

variable {A Z : Type*} [Fintype A] [Fintype Z]

abbrev TotalCoordinates (A Z : Type*) := A ⊕ (Option Z ⊕ Option Z)
abbrev TotalAmbient (A Z : Type*) := TotalCoordinates A Z → ℂ

/-- The literal smooth graph, with two independently rescaled homogeneous
coordinate blocks, over the chosen good parameters. -/
def totalGraph (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) :
    Set (TotalAmbient A Z) :=
  {q | ∃ a ∈ U, ∃ p ∈ smoothGaussRepresentatives F a, q = Sum.elim a p}

/-- The actual polynomial-closed total family, not an arbitrary supplied set. -/
def totalFamily (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) :
    Set (TotalAmbient A Z) := zariskiClosure (totalGraph F U)

/-- Its fibre at the displayed parameter, with no independent choice of
special-fibre support. -/
def fibre (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ) :
    Set (Ambient Z) := {p | Sum.elim a p ∈ totalFamily F U}

theorem totalFamily_euclidean_isClosed
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) :
    IsClosed (totalFamily F U) :=
  ConormalZariski.isClosed_zariskiClosure _

theorem totalFamily_algebraic_isClosed
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) :
    @IsClosed (TotalAmbient A Z)
      (ConormalTopology.algebraicTopology (TotalCoordinates A Z)) (totalFamily F U) :=
  ConormalTopology.isClosed_zariskiClosure _

theorem smooth_graph_mem_totalFamily
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ))
    {a : A → ℂ} (ha : a ∈ U) {p : Ambient Z}
    (hp : p ∈ smoothGaussRepresentatives F a) :
    Sum.elim a p ∈ totalFamily F U :=
  ConormalZariski.subset_zariskiClosure _ ⟨a, ha, p, hp, rfl⟩

/-- Substitute the parameter coordinates in a total-space polynomial. -/
def specialize (a : A → ℂ) :
    MvPolynomial (TotalCoordinates A Z) ℂ →+* MvPolynomial (Option Z ⊕ Option Z) ℂ :=
  eval₂Hom C (Sum.elim (fun i => C (a i)) X)

@[simp] theorem eval_specialize (a : A → ℂ) (p : Ambient Z)
    (q : MvPolynomial (TotalCoordinates A Z) ℂ) :
    eval p (specialize a q) = eval (Sum.elim a p) q := by
  change eval p (eval₂ C (Sum.elim (fun i => C (a i)) X) q) = _
  rw [← eval_assoc]
  have he : (eval p) ∘ Sum.elim (fun i : A => C (a i))
      (X : (Option Z ⊕ Option Z) → MvPolynomial (Option Z ⊕ Option Z) ℂ) =
      Sum.elim a p := by
    funext i
    cases i <;> simp
  rw [he]

/-- Fibre algebraicity follows by specializing each defining polynomial. -/
theorem zariskiClosure_fibre
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ) :
    zariskiClosure (fibre F U a) = fibre F U a := by
  apply Set.Subset.antisymm
  · intro p hp q hq
    have hs : ∀ r ∈ fibre F U a, eval r (specialize a q) = 0 := by
      intro r hr
      rw [eval_specialize]
      exact hr q hq
    simpa using hp (specialize a q) hs
  · exact ConormalZariski.subset_zariskiClosure _

theorem fibre_algebraic_isClosed
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ) :
    @IsClosed (Ambient Z) (ConormalTopology.algebraicTopology (Option Z ⊕ Option Z))
      (fibre F U a) :=
  (ConormalTopology.isClosed_algebraicTopology_iff _).mpr (zariskiClosure_fibre F U a)

theorem fibre_euclidean_isClosed
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ) :
    IsClosed (fibre F U a) :=
  ConormalTopology.euclidean_isClosed_of_algebraic_isClosed (fibre_algebraic_isClosed F U a)

theorem continuous_join :
    Continuous (fun q : (A → ℂ) × Ambient Z => Sum.elim q.1 q.2) := by
  apply continuous_pi
  intro i
  cases i with
  | inl i => exact (continuous_apply i).comp continuous_fst
  | inr i => exact (continuous_apply i).comp continuous_snd

/-- The complete special-fibre containment for this constructed family.
No total-family, closedness, graph-inclusion, or fibre-algebraicity hypothesis
is supplied. The remaining assumption says the chosen good parameters
approach the target parameter in the ordinary complex topology. -/
theorem conormalClosure_subset_fibre
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ))
    (a₀ : A → ℂ) (ha₀ : a₀ ∈ closure U) :
    conormalClosure F a₀ ⊆ fibre F U a₀ := by
  exact ConormalZariski.conormalClosure_subset_special_fibre
    F id a₀ continuousAt_id U ha₀
    ((fun q : (A → ℂ) × Ambient Z => Sum.elim q.1 q.2) ⁻¹' totalFamily F U)
    ((totalFamily_euclidean_isClosed F U).preimage continuous_join)
    (fun _ ha _ hp => smooth_graph_mem_totalFamily F U ha hp)
    (zariskiClosure_fibre F U a₀).le

/-- A continuously parametrized curve gives the required affine parameter
closure. The family remains the explicit polynomial closure above. -/
theorem conormalClosure_subset_fibre_of_curve
    {C : Type*} [TopologicalSpace C]
    (F : MvPolynomial (A ⊕ Z) ℂ) (a : C → A → ℂ)
    (c₀ : C) (ha : ContinuousAt a c₀) (U : Set C)
    (hU : c₀ ∈ closure U) :
    conormalClosure F (a c₀) ⊆ fibre F (a '' U) (a c₀) := by
  apply conormalClosure_subset_fibre
  exact mem_closure_image ha hU

theorem totalFamily_mono
    (F : MvPolynomial (A ⊕ Z) ℂ) {U V : Set (A → ℂ)} (hUV : U ⊆ V) :
    totalFamily F U ⊆ totalFamily F V := by
  apply ConormalZariski.zariskiClosure_mono
  rintro q ⟨a, ha, p, hp, rfl⟩
  exact ⟨a, hUV ha, p, hp, rfl⟩

/-- Shrinking the good parameter set does not change the total closure when
every old good parameter is an ordinary limit of the retained parameters.
This is a proved closure comparison using smooth persistence, not a general
Zariski/Euclidean closure equivalence assumption. -/
theorem totalFamily_eq_of_pointwise_closure
    (F : MvPolynomial (A ⊕ Z) ℂ) {U V : Set (A → ℂ)} (hVU : V ⊆ U)
    (hdense : ∀ a ∈ U, a ∈ closure V) :
    totalFamily F U = totalFamily F V := by
  apply Set.Subset.antisymm
  · have hgraph : totalGraph F U ⊆ totalFamily F V := by
      rintro q ⟨a, ha, p, hp, rfl⟩
      exact conormalClosure_subset_fibre F V a (hdense a ha)
        (ConormalZariski.subset_zariskiClosure _ hp)
    have h := ConormalZariski.zariskiClosure_mono hgraph
    exact h.trans (ConormalZariski.zariskiClosure_idempotent _).le
  · exact totalFamily_mono F hVU

/-- Independent scaling of the two homogeneous blocks, leaving all
parameter coordinates fixed. -/
def rescaleTotal (mu nu : ℂ) (q : TotalAmbient A Z) : TotalAmbient A Z :=
  Sum.elim (fun i => q (Sum.inl i))
    (Sum.elim (fun i => mu * q (Sum.inr (Sum.inl i)))
      (fun i => nu * q (Sum.inr (Sum.inr i))))

theorem rescaleTotal_gaussPoint
    (F : MvPolynomial (A ⊕ Z) ℂ) (a : A → ℂ) (z : Z → ℂ)
    (mu nu lambda kappa : ℂ) :
    rescaleTotal lambda kappa (Sum.elim a (gaussPoint F a z mu nu)) =
      Sum.elim a (gaussPoint F a z (lambda * mu) (kappa * nu)) := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    cases i <;> simp [rescaleTotal, gaussPoint, mul_assoc]

theorem rescaleTotal_mem_totalGraph
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ))
    (lambda kappa : ℂ) (hlambda : lambda ≠ 0) (hkappa : kappa ≠ 0)
    {q : TotalAmbient A Z} (hq : q ∈ totalGraph F U) :
    rescaleTotal lambda kappa q ∈ totalGraph F U := by
  obtain ⟨a, ha, p, hp, rfl⟩ := hq
  obtain ⟨z, mu, nu, hz, hj, hmu, hnu, rfl⟩ := hp
  rw [rescaleTotal_gaussPoint]
  exact ⟨a, ha, _,
    ⟨z, lambda * mu, kappa * nu, hz, hj,
      mul_ne_zero hlambda hmu, mul_ne_zero hkappa hnu, rfl⟩, rfl⟩

/-- The total family cannot acquire parameters outside the algebraic closure
of its good parameters. This follows from pulling back every base equation. -/
theorem parameter_mem_zariskiClosure
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ))
    {q : TotalAmbient A Z} (hq : q ∈ totalFamily F U) :
    (fun i => q (Sum.inl i)) ∈ zariskiClosure U := by
  intro f hf
  have hvan : ∀ r ∈ totalGraph F U,
      eval r (rename (Sum.inl : A → TotalCoordinates A Z) f) = 0 := by
    rintro r ⟨a, ha, p, hp, rfl⟩
    simpa only [eval_rename, Function.comp_def, Sum.elim_inl] using hf a ha
  simpa only [eval_rename, Function.comp_def] using
    hq (rename (Sum.inl : A → TotalCoordinates A Z) f) hvan

/-- In particular, if the good parameters lie on an algebraic curve (or any
algebraic base), the constructed total family still lies over that base. -/
theorem parameter_mem_algebraic_base
    (F : MvPolynomial (A ⊕ Z) ℂ) (U C : Set (A → ℂ))
    (hUC : U ⊆ C)
    (hC : @IsClosed (A → ℂ) (ConormalTopology.algebraicTopology A) C)
    {q : TotalAmbient A Z} (hq : q ∈ totalFamily F U) :
    (fun i => q (Sum.inl i)) ∈ C := by
  have hc := ConormalTopology.zariskiClosure_mono hUC
    (parameter_mem_zariskiClosure F U hq)
  rwa [(ConormalTopology.isClosed_algebraicTopology_iff C).mp hC] at hc

/-- The actual ideal defining the reduced total closure consists of all
polynomials vanishing on the displayed smooth graph. -/
def totalIdeal (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) :
    Ideal (MvPolynomial (TotalCoordinates A Z) ℂ) where
  carrier := {f | ∀ q ∈ totalGraph F U, eval q f = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg q hq
    simp [hf q hq, hg q hq]
  smul_mem' := by
    intro f g hg q hq
    change eval q (f * g) = 0
    simp [hg q hq]

theorem totalIdeal_isRadical
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) :
    (totalIdeal F U).IsRadical := by
  intro f hf
  obtain ⟨k, hk⟩ := hf
  intro q hq
  have he : eval q f ^ k = 0 := by simpa using hk q hq
  exact pow_eq_zero he

/-- The constructed total support is exactly the common zero locus of its
constructed radical ideal; this identification uses no Nullstellensatz axiom. -/
theorem mem_totalFamily_iff_vanishes_totalIdeal
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (q : TotalAmbient A Z) :
    q ∈ totalFamily F U ↔ ∀ f ∈ totalIdeal F U, eval q f = 0 := Iff.rfl

/-- A concrete reduced coordinate ring for the affine total closure. -/
abbrev CoordinateRing (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) :=
  MvPolynomial (TotalCoordinates A Z) ℂ ⧸ totalIdeal F U

instance coordinateRing_isReduced
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) :
    IsReduced (CoordinateRing F U) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (totalIdeal_isRadical F U)

/-- Specialize the actual total ideal without taking a radical. This retains
possible special-fibre multiplicities; reducedness of the total ring does not
imply reducedness of a fibre. -/
def fibreIdeal (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ) :
    Ideal (MvPolynomial (Option Z ⊕ Option Z) ℂ) :=
  Ideal.map (specialize a) (totalIdeal F U)

/-- The support used above is precisely the zero locus of the specialized
ideal, not an independently supplied special-fibre set. -/
theorem mem_fibre_iff_vanishes_fibreIdeal
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ) (p : Ambient Z) :
    p ∈ fibre F U a ↔ ∀ f ∈ fibreIdeal F U a, eval p f = 0 := by
  change (∀ f ∈ totalIdeal F U, eval (Sum.elim a p) f = 0) ↔
    Ideal.map (specialize a) (totalIdeal F U) ≤ RingHom.ker (eval p)
  rw [Ideal.map_le_iff_le_comap]
  change (∀ f ∈ totalIdeal F U, eval (Sum.elim a p) f = 0) ↔
    (∀ f ∈ totalIdeal F U, eval p (specialize a f) = 0)
  simp only [eval_specialize]

/-- A concrete fibre coordinate ring. No reducedness instance is asserted. -/
abbrev FibreCoordinateRing
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ) :=
  MvPolynomial (Option Z ⊕ Option Z) ℂ ⧸ fibreIdeal F U a

theorem target_conormal_vanishes_fibreIdeal
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ))
    (a₀ : A → ℂ) (ha₀ : a₀ ∈ closure U)
    {p : Ambient Z} (hp : p ∈ conormalClosure F a₀)
    {f : MvPolynomial (Option Z ⊕ Option Z) ℂ} (hf : f ∈ fibreIdeal F U a₀) :
    eval p f = 0 :=
  (mem_fibre_iff_vanishes_fibreIdeal F U a₀ p).mp
    (conormalClosure_subset_fibre F U a₀ ha₀ hp) f hf

end Sheshadri.ActualGaussFamily
