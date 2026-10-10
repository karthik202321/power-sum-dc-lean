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
import Sheshadri.GeneralConormalFlatFamily
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Actual normalized affine coordinate charts of a bihomogeneous cone

The chart ring is the literal quotient obtained by setting one coordinate
in each projective block to one. Bihomogeneity supplies its map into the
localized affine cone, via the actual coordinate ratios. The constructions
in this file are ring homomorphisms, not point-set chart certificates.
-/

noncomputable section
namespace Sheshadri.ConormalProjectiveCharts

open MvPolynomial
open scoped BigOperators

section Scaling
variable {σ R K : Type*} [CommRing R] [CommRing K]

def biScale (w : σ → ℕ × ℕ) (s t : K) (v : σ → K) : σ → K :=
  fun i => s ^ (w i).1 * t ^ (w i).2 * v i

theorem eval₂_monomial_biScale (f : R →+* K) (w : σ → ℕ × ℕ)
    (s t : K) (v : σ → K) (e : σ →₀ ℕ) (r : R) :
    eval₂ f (biScale w s t v) (monomial e r) =
      s ^ (Finsupp.weight w e).1 * t ^ (Finsupp.weight w e).2 *
        eval₂ f v (monomial e r) := by
  classical
  simp only [eval₂_monomial, biScale, Finsupp.prod, mul_pow,
    Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum,
    Finsupp.weight_apply, Finsupp.sum, Prod.fst_sum, Prod.snd_sum,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have hleft : (∑ i ∈ e.support, (w i).1 * e i) = ∑ i ∈ e.support, e i * (w i).1 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Nat.mul_comm _ _
  have hright : (∑ i ∈ e.support, (w i).2 * e i) = ∑ i ∈ e.support, e i * (w i).2 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact Nat.mul_comm _ _
  rw [hleft, hright]
  ring

/-- The exact scaling formula for an actually bihomogeneous polynomial,
over arbitrary coefficient and target commutative rings. -/
theorem eval₂_biScale_of_homogeneous (f : R →+* K) (w : σ → ℕ × ℕ)
    (s t : K) (v : σ → K) (p : MvPolynomial σ R) (a b : ℕ)
    (hp : p.IsWeightedHomogeneous w (a, b)) :
    eval₂ f (biScale w s t v) p = s ^ a * t ^ b * eval₂ f v p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [eval₂_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval₂_monomial_biScale]
  have hw := hp (mem_support_iff.mp he)
  rw [hw]

/-- If every bihomogeneous component of an equation remains in the ideal,
then arbitrary independent scalings preserve vanishing of all its equations. -/
theorem ideal_vanishing_biScale [Finite σ] (block : σ → Bool)
    (I : Ideal (MvPolynomial σ R)) (hI : FlatGradedHilbert.IsBihomogeneous σ R block I)
    (f : R →+* K) (v : σ → K) (hv : ∀ p ∈ I, eval₂ f v p = 0)
    (s t : K) (p : MvPolynomial σ R) (hp : p ∈ I) :
    eval₂ f (biScale (FlatGradedHilbert.twoBlockWeight σ block) s t v) p = 0 := by
  let w := FlatGradedHilbert.twoBlockWeight σ block
  rw [← sum_weightedHomogeneousComponent w p]
  change (eval₂Hom f (biScale w s t v)).toAddMonoidHom
    (∑ᶠ d, weightedHomogeneousComponent w d p) = 0
  rw [AddMonoidHom.map_finsum _ (weightedHomogeneousComponent_finsupp p)]
  have hz : ∀ d : ℕ × ℕ,
      eval₂ f (biScale w s t v) (weightedHomogeneousComponent w d p) = 0 := by
    intro d
    rw [eval₂_biScale_of_homogeneous f w s t v _ d.1 d.2
      (weightedHomogeneousComponent_mem w p d)]
    rw [hv _ (hI d.1 d.2 p hp), mul_zero]
  change (∑ᶠ d : ℕ × ℕ, eval₂ f (biScale w s t v)
    (weightedHomogeneousComponent w d p)) = 0
  simp only [hz, finsum_zero]

end Scaling



section Chart
variable {X Y R : Type*} [Finite X] [Finite Y] [CommRing R]

def block : X ⊕ Y → Bool := Sum.elim (fun _ => true) (fun _ => false)

variable (I : Ideal (MvPolynomial (X ⊕ Y) R)) (i : X) (j : Y)

abbrev ConeRing := MvPolynomial (X ⊕ Y) R ⧸ I

def leftCoordinate (k : X) : ConeRing I := Ideal.Quotient.mk I (MvPolynomial.X (Sum.inl k))
def rightCoordinate (k : Y) : ConeRing I := Ideal.Quotient.mk I (MvPolynomial.X (Sum.inr k))

/-- The literal standard chart equations: the original homogeneous ideal
and one normalization equation in each projective coordinate block. -/
def normalizedIdeal : Ideal (MvPolynomial (X ⊕ Y) R) :=
  I ⊔ Ideal.span {MvPolynomial.X (Sum.inl i) - 1, MvPolynomial.X (Sum.inr j) - 1}

abbrev NormalizedChart := MvPolynomial (X ⊕ Y) R ⧸ normalizedIdeal I i j

abbrev ConeOpen := GeneralConormalFlatFamily.OpenChartRing (leftCoordinate I) (rightCoordinate I) i j

abbrev RatioChart := GeneralConormalFlatFamily.ratioChart R (leftCoordinate I) (rightCoordinate I) i j

def ratioVariables : X ⊕ Y → ConeOpen I i j :=
  Sum.elim (GeneralConormalFlatFamily.leftRatio (leftCoordinate I) (rightCoordinate I) i j)
    (GeneralConormalFlatFamily.rightRatio (leftCoordinate I) (rightCoordinate I) i j)

def ratioEvaluation : MvPolynomial (X ⊕ Y) R →+* ConeOpen I i j :=
  eval₂Hom (algebraMap R (ConeOpen I i j)) (ratioVariables I i j)

def leftInverseCoordinate : ConeOpen I i j :=
  algebraMap (ConeRing I) (ConeOpen I i j) (rightCoordinate I j) *
    IsLocalization.Away.invSelf (leftCoordinate I i * rightCoordinate I j)

def rightInverseCoordinate : ConeOpen I i j :=
  algebraMap (ConeRing I) (ConeOpen I i j) (leftCoordinate I i) *
    IsLocalization.Away.invSelf (leftCoordinate I i * rightCoordinate I j)

def originalVariables : X ⊕ Y → ConeOpen I i j :=
  fun k => algebraMap (ConeRing I) (ConeOpen I i j) (Ideal.Quotient.mk I (MvPolynomial.X k))

theorem ratioVariables_eq_biScale :
    ratioVariables I i j = biScale (FlatGradedHilbert.twoBlockWeight (X ⊕ Y) block)
      (leftInverseCoordinate I i j) (rightInverseCoordinate I i j) (originalVariables I i j) := by
  funext k
  cases k <;>
    simp [ratioVariables, biScale, FlatGradedHilbert.twoBlockWeight, block,
      GeneralConormalFlatFamily.leftRatio, GeneralConormalFlatFamily.rightRatio,
      GeneralConormalFlatFamily.chartDenominator, leftInverseCoordinate, rightInverseCoordinate,
      originalVariables, leftCoordinate, rightCoordinate, map_mul] <;> ring

theorem originalEvaluation (p : MvPolynomial (X ⊕ Y) R) :
    eval₂ (algebraMap R (ConeOpen I i j)) (originalVariables I i j) p =
      algebraMap (ConeRing I) (ConeOpen I i j) (Ideal.Quotient.mk I p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [eval₂_C, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
    exact IsScalarTower.algebraMap_apply R (ConeRing I) (ConeOpen I i j) r
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp => simp [hp, originalVariables]

theorem ratioEvaluation_vanishes_originalIdeal
    (hI : FlatGradedHilbert.IsBihomogeneous (X ⊕ Y) R block I)
    (p : MvPolynomial (X ⊕ Y) R) (hp : p ∈ I) : ratioEvaluation I i j p = 0 := by
  change eval₂ _ (ratioVariables I i j) p = 0
  rw [ratioVariables_eq_biScale]
  apply ideal_vanishing_biScale block I hI _ _ ?_ _ _ p hp
  intro q hq
  rw [originalEvaluation, Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]

theorem normalizedIdeal_le_ker_ratioEvaluation
    (hI : FlatGradedHilbert.IsBihomogeneous (X ⊕ Y) R block I) :
    normalizedIdeal I i j ≤ RingHom.ker (ratioEvaluation I i j) := by
  apply sup_le
  · exact ratioEvaluation_vanishes_originalIdeal I i j hI
  · apply Ideal.span_le.mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl <;>
      simp [RingHom.mem_ker, ratioEvaluation, ratioVariables]

/-- The normalization quotient has a genuine ring homomorphism into the
principal-open cone ring, with coordinates equal to the usual ratios. -/
def normalizedChartToConeOpen
    (hI : FlatGradedHilbert.IsBihomogeneous (X ⊕ Y) R block I) :
    NormalizedChart I i j →+* ConeOpen I i j :=
  Ideal.Quotient.lift (normalizedIdeal I i j) (ratioEvaluation I i j)
    (normalizedIdeal_le_ker_ratioEvaluation I i j hI)

@[simp] theorem normalizedChartToConeOpen_mk
    (hI : FlatGradedHilbert.IsBihomogeneous (X ⊕ Y) R block I)
    (p : MvPolynomial (X ⊕ Y) R) :
    normalizedChartToConeOpen I i j hI (Ideal.Quotient.mk (normalizedIdeal I i j) p) =
      ratioEvaluation I i j p := rfl



@[simp] theorem normalized_left_coordinate :
    Ideal.Quotient.mk (normalizedIdeal I i j) (MvPolynomial.X (Sum.inl i)) = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk (normalizedIdeal I i j)), ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (show Ideal.span {MvPolynomial.X (Sum.inl i) - 1,
      MvPolynomial.X (Sum.inr j) - 1} ≤ normalizedIdeal I i j from le_sup_right)
  exact Ideal.subset_span (Set.mem_insert _ _)

@[simp] theorem normalized_right_coordinate :
    Ideal.Quotient.mk (normalizedIdeal I i j) (MvPolynomial.X (Sum.inr j)) = 1 := by
  apply sub_eq_zero.mp
  rw [← map_one (Ideal.Quotient.mk (normalizedIdeal I i j)), ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (show Ideal.span {MvPolynomial.X (Sum.inl i) - 1,
      MvPolynomial.X (Sum.inr j) - 1} ≤ normalizedIdeal I i j from le_sup_right)
  exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- Set the two chosen homogeneous coordinates to one in the cone ring. -/
def coneToNormalizedChart : ConeRing I →+* NormalizedChart I i j :=
  Ideal.Quotient.lift I (Ideal.Quotient.mk (normalizedIdeal I i j))
    (fun p hp => Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show I ≤ normalizedIdeal I i j from le_sup_left) hp))

@[simp] theorem coneToNormalizedChart_mk (p : MvPolynomial (X ⊕ Y) R) :
    coneToNormalizedChart I i j (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk (normalizedIdeal I i j) p := rfl

theorem coneToNormalizedChart_denominator :
    coneToNormalizedChart I i j (leftCoordinate I i * rightCoordinate I j) = 1 := by
  simp [leftCoordinate, rightCoordinate]

/-- The normalization map extends over the coordinate open because its
denominator maps to one. This will give a left inverse to the ratio map. -/
def coneOpenToNormalizedChart : ConeOpen I i j →+* NormalizedChart I i j :=
  IsLocalization.Away.lift (leftCoordinate I i * rightCoordinate I j)
    (g := coneToNormalizedChart I i j)
    (by rw [coneToNormalizedChart_denominator]; exact isUnit_one)

@[simp] theorem coneOpenToNormalizedChart_algebraMap (q : ConeRing I) :
    coneOpenToNormalizedChart I i j (algebraMap (ConeRing I) (ConeOpen I i j) q) =
      coneToNormalizedChart I i j q :=
  IsLocalization.Away.lift_eq _ _ q

@[simp] theorem coneOpenToNormalizedChart_invSelf :
    coneOpenToNormalizedChart I i j
      (IsLocalization.Away.invSelf (leftCoordinate I i * rightCoordinate I j)) = 1 := by
  have h := congrArg (coneOpenToNormalizedChart I i j)
    (IsLocalization.Away.mul_invSelf
      (S := ConeOpen I i j) (leftCoordinate I i * rightCoordinate I j))
  simpa [leftCoordinate, rightCoordinate] using h

@[simp] theorem coneOpenToNormalizedChart_ratioVariables (k : X ⊕ Y) :
    coneOpenToNormalizedChart I i j (ratioVariables I i j k) =
      Ideal.Quotient.mk (normalizedIdeal I i j) (MvPolynomial.X k) := by
  cases k <;>
    simp only [ratioVariables, Sum.elim_inl, Sum.elim_inr,
      GeneralConormalFlatFamily.leftRatio, GeneralConormalFlatFamily.rightRatio,
      map_mul, coneOpenToNormalizedChart_algebraMap,
      coneOpenToNormalizedChart_invSelf, mul_one] <;>
    simp [leftCoordinate, rightCoordinate]

/-- The normalized quotient embeds in the actual coordinate-open ring.
The proof constructs an actual retraction by setting both torus coordinates
to one; no injectivity or projective-chart identification is assumed. -/
theorem normalizedChart_leftInverse
    (hI : FlatGradedHilbert.IsBihomogeneous (X ⊕ Y) R block I) :
    Function.LeftInverse (coneOpenToNormalizedChart I i j)
      (normalizedChartToConeOpen I i j hI) := by
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [normalizedChartToConeOpen_mk]
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [ratioEvaluation, eval₂Hom_C,
      IsScalarTower.algebraMap_apply R (ConeRing I) (ConeOpen I i j),
      coneOpenToNormalizedChart_algebraMap]
    rw [← Ideal.Quotient.mk_algebraMap R I, MvPolynomial.algebraMap_eq]
    rfl
  | add p q hp hq => simpa only [map_add] using congrArg₂ (· + ·) hp hq
  | mul_X p k hp =>
    simp only [map_mul]
    rw [hp]
    congr 1
    simpa only [ratioEvaluation, eval₂Hom_X'] using
      coneOpenToNormalizedChart_ratioVariables I i j k

theorem normalizedChartToConeOpen_injective
    (hI : FlatGradedHilbert.IsBihomogeneous (X ⊕ Y) R block I) :
    Function.Injective (normalizedChartToConeOpen I i j hI) :=
  (normalizedChart_leftInverse I i j hI).injective

/-- The ratio map respects the actual base-ring algebra structures. -/
def normalizedChartToConeOpenAlg
    (hI : FlatGradedHilbert.IsBihomogeneous (X ⊕ Y) R block I) :
    NormalizedChart I i j →ₐ[R] ConeOpen I i j :=
  { normalizedChartToConeOpen I i j hI with
    commutes' := by
      intro r
      change normalizedChartToConeOpen I i j hI
        (algebraMap R (NormalizedChart I i j) r) = _
      rw [← Ideal.Quotient.mk_algebraMap R (normalizedIdeal I i j),
        MvPolynomial.algebraMap_eq, normalizedChartToConeOpen_mk]
      exact eval₂Hom_C _ _ _ }

/-- The image of the normalization quotient is exactly the subalgebra
 generated by the standard coordinate ratios. -/
theorem normalizedChart_range
    (hI : FlatGradedHilbert.IsBihomogeneous (X ⊕ Y) R block I) :
    (normalizedChartToConeOpenAlg I i j hI).range = RatioChart I i j := by
  have hvars : Set.range (ratioVariables I i j) =
      Set.range (GeneralConormalFlatFamily.leftRatio (leftCoordinate I) (rightCoordinate I) i j) ∪
      Set.range (GeneralConormalFlatFamily.rightRatio (leftCoordinate I) (rightCoordinate I) i j) := by
    exact Set.Sum.elim_range _ _
  change _ = Algebra.adjoin R _
  rw [← hvars, Algebra.adjoin_range_eq_range_aeval]
  ext q
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨Ideal.Quotient.mk (normalizedIdeal I i j) p, rfl⟩

/-- A genuine base-algebra equivalence between the literal normalized
quotient and the standard projective coordinate-ratio chart. -/
def normalizedChartEquivRatioChart
    (hI : FlatGradedHilbert.IsBihomogeneous (X ⊕ Y) R block I) :
    NormalizedChart I i j ≃ₐ[R] RatioChart I i j :=
  (AlgEquiv.ofInjective (normalizedChartToConeOpenAlg I i j hI)
    (normalizedChartToConeOpen_injective I i j hI)).trans
      (Subalgebra.equivOfEq _ _ (normalizedChart_range I i j hI))



/-- Exact scheme-theoretic chart ideal: the ratio map has no extra kernel
beyond the original equations and the two normalization equations. -/
theorem ker_ratioEvaluation
    (hI : FlatGradedHilbert.IsBihomogeneous (X ⊕ Y) R block I) :
    RingHom.ker (ratioEvaluation I i j) = normalizedIdeal I i j := by
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply normalizedChartToConeOpen_injective I i j hI
    rw [normalizedChartToConeOpen_mk, map_zero]
    exact hp
  · exact normalizedIdeal_le_ker_ratioEvaluation I i j hI

/-- The literal affine scheme of the normalized chart equations. -/
def normalizedChartScheme : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of (NormalizedChart I i j))

end Chart
end Sheshadri.ConormalProjectiveCharts
