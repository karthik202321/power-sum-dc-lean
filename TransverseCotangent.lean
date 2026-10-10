/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.Isolatedness
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# From genuine cotangent transversality to a reduced isolated cut

The cotangent module here is Mathlib's `Ideal.Cotangent`, the actual quotient
`m / m²`, with its quotient map `m.toCotangent`. We prove the first-order ideal
containment from spanning cotangent classes, rather than assume that containment.
For a Noetherian local ring, independence of as many classes as the cotangent
dimension supplies the spanning hypothesis. Nakayama then proves the cutting
ideal is the maximal ideal, so its quotient is the residue field.

This does not assert that a particular geometric flag is transverse. It gives
the fully checked algebraic implication from the precise linear-algebra input.
-/

namespace Sheshadri

section Ring
variable {R : Type*} [CommRing R] {ι : Type*}

/-- Spanning classes in the actual quotient `m/m²` imply the first-order
ideal containment needed by Nakayama. -/
theorem cotangent_span_implies_first_order
    (m J : Ideal R) (f : ι → m)
    (hmem : ∀ i, (f i : R) ∈ J)
    (hspan : Submodule.span R (Set.range (fun i => m.toCotangent (f i))) = ⊤) :
    m ≤ J ⊔ m • m := by
  let P : Submodule R m := Submodule.span R (Set.range f)
  have hmap : P.map m.toCotangent = ⊤ := by
    change (Submodule.span R (Set.range f)).map m.toCotangent = ⊤
    rw [Submodule.map_span, ← Set.range_comp']
    exact hspan
  intro x hx
  let x' : m := ⟨x, hx⟩
  have hxmap : m.toCotangent x' ∈ P.map m.toCotangent := by
    rw [hmap]
    exact Submodule.mem_top
  obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp hxmap
  have hyJ : (y : R) ∈ J := by
    change y ∈ Submodule.comap m.subtype (J : Submodule R R)
    apply (Submodule.span_le.mpr ?_) hy
    rintro _ ⟨i, rfl⟩
    exact hmem i
  have hdiff : x - (y : R) ∈ m • m := by
    rw [smul_eq_mul, ← pow_two]
    exact m.toCotangent_eq.mp he.symm
  have hdiff' : x - (y : R) ∈ J ⊔ m • m := Ideal.mem_sup_right hdiff
  have hyJ' : (y : R) ∈ J ⊔ m • m := Ideal.mem_sup_left hyJ
  simpa only [sub_add_cancel] using (J ⊔ m • m).add_mem hdiff' hyJ'

/-- Coefficients agreeing at the point give the same first-order multiplication
on a vanishing function. This is the cotangent form of `d(af)=a(p) df` at `f(p)=0`.
-/
theorem cotangent_coefficient_congr (m : Ideal R) (a b : R) (f : m)
    (hab : a - b ∈ m) :
    m.toCotangent (a • f) = b • m.toCotangent f := by
  rw [map_smul]
  have hz := Ideal.Cotangent.smul_eq_zero_of_mem hab (m.toCotangent f)
  rwa [sub_smul, sub_eq_zero] at hz

end Ring

section LocalRing
variable {R : Type*} [CommRing R] [IsLocalRing R] {ι : Type*}

/-- Multiplication of each vanishing equation by a unit preserves independence
of its differential at the point. No derivative of the unit contributes in
`m/m²`; the surviving scalar is its image in the residue field. -/
theorem unit_rescaled_cotangent_independent
    (f : ι → IsLocalRing.maximalIdeal R) (a : ι → Rˣ)
    (hind : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent (f i))) :
    LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent ((a i : R) • f i)) := by
  let u : ι → (IsLocalRing.ResidueField R)ˣ :=
    fun i => Units.map (algebraMap R (IsLocalRing.ResidueField R)).toMonoidHom (a i)
  simpa only [map_smul, u, Units.smul_def, Units.coe_map, MonoidHom.coe_coe,
    algebraMap_smul] using hind.units_smul u

/-- Spanning over the residue field is equivalent to spanning over the ring
for the cotangent module, because the quotient map on scalars is surjective. -/
theorem cotangent_residue_span_to_ring_span
    (f : ι → IsLocalRing.maximalIdeal R)
    (hspan : Submodule.span (IsLocalRing.ResidueField R)
      (Set.range (fun i => (IsLocalRing.maximalIdeal R).toCotangent (f i))) = ⊤) :
    Submodule.span R
      (Set.range (fun i => (IsLocalRing.maximalIdeal R).toCotangent (f i))) = ⊤ := by
  rw [← Submodule.restrictScalars_span R (IsLocalRing.ResidueField R)
    Ideal.Quotient.mk_surjective, hspan]
  simp

/-- Actual residue-field cotangent spanning supplies the ideal containment. -/
theorem residue_cotangent_span_implies_first_order
    (J : Ideal R) (f : ι → IsLocalRing.maximalIdeal R)
    (hmem : ∀ i, (f i : R) ∈ J)
    (hspan : Submodule.span (IsLocalRing.ResidueField R)
      (Set.range (fun i => (IsLocalRing.maximalIdeal R).toCotangent (f i))) = ⊤) :
    IsLocalRing.maximalIdeal R ≤ J ⊔
      IsLocalRing.maximalIdeal R • IsLocalRing.maximalIdeal R :=
  cotangent_span_implies_first_order _ J f hmem
    (cotangent_residue_span_to_ring_span f hspan)

variable [IsNoetherianRing R]

/-- A cut whose vanishing equations span the cotangent space is precisely the
maximal ideal. The ring's Noetherian hypothesis supplies finite generation. -/
theorem cotangent_span_cut_eq_maximal
    (J : Ideal R) (f : ι → IsLocalRing.maximalIdeal R)
    (hmem : ∀ i, (f i : R) ∈ J)
    (hvanish : J ≤ IsLocalRing.maximalIdeal R)
    (hspan : Submodule.span (IsLocalRing.ResidueField R)
      (Set.range (fun i => (IsLocalRing.maximalIdeal R).toCotangent (f i))) = ⊤) :
    J = IsLocalRing.maximalIdeal R := by
  apply transverse_cut_eq_maximal J (IsLocalRing.maximalIdeal R)
    (IsNoetherian.noetherian _) ?_ hvanish
    (residue_cotangent_span_implies_first_order J f hmem hspan)
  exact (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge

/-- Linear independence plus the correct number of equations proves the
cotangent spanning condition, hence the reduced isolated-cut conclusion. -/
theorem independent_cotangent_cut_eq_maximal [Fintype ι]
    (J : Ideal R) (f : ι → IsLocalRing.maximalIdeal R)
    (hmem : ∀ i, (f i : R) ∈ J)
    (hvanish : J ≤ IsLocalRing.maximalIdeal R)
    (hind : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent (f i)))
    (hdim : Fintype.card ι = Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.CotangentSpace R)) :
    J = IsLocalRing.maximalIdeal R :=
  cotangent_span_cut_eq_maximal J f hmem hvanish
    (hind.span_eq_top_of_card_eq_finrank' hdim)

/-- The quotient of a cut by a full independent family of cotangent classes
is a field; this proves reducedness as well as isolatedness. -/
theorem independent_cotangent_cut_quotient_isField [Fintype ι]
    (J : Ideal R) (f : ι → IsLocalRing.maximalIdeal R)
    (hmem : ∀ i, (f i : R) ∈ J)
    (hvanish : J ≤ IsLocalRing.maximalIdeal R)
    (hind : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent (f i)))
    (hdim : Fintype.card ι = Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.CotangentSpace R)) :
    IsField (R ⧸ J) := by
  rw [independent_cotangent_cut_eq_maximal J f hmem hvanish hind hdim]
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp
    (IsLocalRing.maximalIdeal.isMaximal R)

/-- A convenient formulation with exactly `n` equations and cotangent
dimension `n`, matching transverse cuts in a smooth ambient `n`-fold. -/
theorem n_independent_cotangent_equations_isField (n : ℕ)
    (f : Fin n → IsLocalRing.maximalIdeal R)
    (hind : LinearIndependent (IsLocalRing.ResidueField R)
      (fun i => (IsLocalRing.maximalIdeal R).toCotangent (f i)))
    (hdim : Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.CotangentSpace R) = n) :
    IsField (R ⧸ equationIdeal (fun i => (f i : R))) := by
  apply independent_cotangent_cut_quotient_isField _ f
  · intro i
    exact Ideal.subset_span ⟨i, rfl⟩
  · rw [equationIdeal_le_iff]
    exact fun i => (f i).property
  · exact hind
  · simpa using hdim.symm

end LocalRing
end Sheshadri
