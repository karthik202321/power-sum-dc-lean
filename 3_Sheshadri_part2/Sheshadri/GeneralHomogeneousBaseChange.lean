/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FlatGradedHilbert
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

/-!
# Homogeneous ideals under arbitrary coefficient extension

Extending coefficients preserves homogeneous equations even when the
coefficient homomorphism is not surjective. The proof uses homogeneous
generators, not a false claim that every element of the extended ideal
is the image of one original equation.
-/

noncomputable section
namespace Sheshadri.GeneralHomogeneousBaseChange

open MvPolynomial

variable {σ R S Γ : Type*} [CommRing R] [CommRing S]
variable [AddCommMonoid Γ] [DecidableEq Γ]

omit [DecidableEq Γ] in
theorem weightedHomogeneous_map (f : R →+* S) (w : σ → Γ)
    {p : MvPolynomial σ R} {d : Γ} (hp : p.IsWeightedHomogeneous w d) :
    (MvPolynomial.map f p).IsWeightedHomogeneous w d := by
  intro e he
  apply hp
  intro hzero
  apply he
  simp only [coeff_map, hzero, map_zero]

/-- Coefficient extension commutes with each actual weighted projection. -/
theorem weightedComponent_map (f : R →+* S) (w : σ → Γ)
    (d : Γ) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w d (MvPolynomial.map f p) =
      MvPolynomial.map f (weightedHomogeneousComponent w d p) := by
  classical
  ext e
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp

/-- Arbitrary coefficient extension preserves the homogeneous-component
closure condition defining a homogeneous ideal. -/
theorem weightedIdeal_map (f : R →+* S) (w : σ → Γ)
    (I : Ideal (MvPolynomial σ R))
    (hI : ∀ d p, p ∈ I → weightedHomogeneousComponent w d p ∈ I) :
    ∀ d p, p ∈ I.map (MvPolynomial.map f) →
      weightedHomogeneousComponent w d p ∈ I.map (MvPolynomial.map f) := by
  classical
  letI : GradedAlgebra (weightedHomogeneousSubmodule R w) := weightedGradedAlgebra R w
  letI : GradedAlgebra (weightedHomogeneousSubmodule S w) := weightedGradedAlgebra S w
  have hi : I.IsHomogeneous (weightedHomogeneousSubmodule R w) := by
    intro d p hp
    change (MvPolynomial.decompose' R w p d : MvPolynomial σ R) ∈ I
    rw [MvPolynomial.decompose'_apply]
    exact hI d p hp
  have hm : (I.map (MvPolynomial.map f)).IsHomogeneous
      (weightedHomogeneousSubmodule S w) := by
    obtain ⟨T, hT⟩ := (Ideal.IsHomogeneous.iff_exists
      (weightedHomogeneousSubmodule R w) I).mp hi
    rw [hT, Ideal.map_span]
    apply Ideal.homogeneous_span (weightedHomogeneousSubmodule S w)
    rintro _ ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    obtain ⟨d, hd⟩ := q.property
    exact ⟨d, weightedHomogeneous_map f w hd⟩
  intro d p hp
  have h := hm d hp
  change (MvPolynomial.decompose' S w p d : MvPolynomial σ S) ∈ _ at h
  rwa [MvPolynomial.decompose'_apply] at h

/-- In particular, extending an ideal's coefficients preserves its
actual two-projective-block homogeneity. -/
theorem bihomogeneous_map [Finite σ] (f : R →+* S) (block : σ → Bool)
    (I : Ideal (MvPolynomial σ R))
    (hI : FlatGradedHilbert.IsBihomogeneous σ R block I) :
    FlatGradedHilbert.IsBihomogeneous σ S block (I.map (MvPolynomial.map f)) := by
  intro a b p hp
  apply weightedIdeal_map f (FlatGradedHilbert.twoBlockWeight σ block) I _ (a, b) p hp
  rintro ⟨c, d⟩ q hq
  exact hI c d q hq

end Sheshadri.GeneralHomogeneousBaseChange
