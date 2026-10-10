/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalProjectiveCharts

/-!
# The coordinate-open cone is a two-dimensional torus over its chart

All rings and maps are explicit. The torus algebra is the localization of
a two-variable polynomial algebra over the normalized chart at the product
of its two variables. Its comparison with the cone open uses the proved
bihomogeneity of the original equations.
-/
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

noncomputable section
namespace Sheshadri.ConormalChartTorus

open MvPolynomial ConormalProjectiveCharts

variable {X Y R : Type*} [Finite X] [Finite Y] [CommRing R]
variable (I : Ideal (MvPolynomial (X ⊕ Y) R)) (i : X) (j : Y)
variable (hI : FlatGradedHilbert.IsBihomogeneous (X ⊕ Y) R block I)

abbrev TorusPolynomial := MvPolynomial Bool (NormalizedChart I i j)
def torusDenominator : TorusPolynomial I i j := MvPolynomial.X true * MvPolynomial.X false
abbrev TorusRing := Localization.Away (torusDenominator I i j)

def torusVariable (b : Bool) : TorusRing I i j :=
  algebraMap (TorusPolynomial I i j) (TorusRing I i j) (MvPolynomial.X b)

def chartVariables (k : X ⊕ Y) : TorusRing I i j :=
  algebraMap (NormalizedChart I i j) (TorusRing I i j)
    (Ideal.Quotient.mk (normalizedIdeal I i j) (MvPolynomial.X k))

def scaledVariables : X ⊕ Y → TorusRing I i j :=
  biScale (FlatGradedHilbert.twoBlockWeight (X ⊕ Y) block)
    (torusVariable I i j true) (torusVariable I i j false) (chartVariables I i j)

@[simp] theorem scaledVariables_left (k : X) : scaledVariables I i j (Sum.inl k) =
    torusVariable I i j true * chartVariables I i j (Sum.inl k) := by
  simp [scaledVariables, biScale, FlatGradedHilbert.twoBlockWeight, block]

@[simp] theorem scaledVariables_right (k : Y) : scaledVariables I i j (Sum.inr k) =
    torusVariable I i j false * chartVariables I i j (Sum.inr k) := by
  simp [scaledVariables, biScale, FlatGradedHilbert.twoBlockWeight, block]

@[simp] theorem chartVariables_left_selected : chartVariables I i j (Sum.inl i) = 1 := by
  simp [chartVariables]

@[simp] theorem chartVariables_right_selected : chartVariables I i j (Sum.inr j) = 1 := by
  simp [chartVariables]

theorem chartEvaluation (p : MvPolynomial (X ⊕ Y) R) :
    eval₂ (algebraMap R (TorusRing I i j)) (chartVariables I i j) p =
      algebraMap (NormalizedChart I i j) (TorusRing I i j)
        (Ideal.Quotient.mk (normalizedIdeal I i j) p) := by
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [eval₂_C, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
    exact IsScalarTower.algebraMap_apply R (NormalizedChart I i j) (TorusRing I i j) r
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp => simp [hp, chartVariables]

include hI in
/-- Rescaling normalized coordinates satisfies the original equations. -/
theorem scaledEvaluation_vanishes (p : MvPolynomial (X ⊕ Y) R) (hp : p ∈ I) :
    eval₂ (algebraMap R (TorusRing I i j)) (scaledVariables I i j) p = 0 := by
  apply ideal_vanishing_biScale block I hI _ _ ?_ _ _ p hp
  intro q hq
  rw [chartEvaluation, Ideal.Quotient.eq_zero_iff_mem.mpr
    ((show I ≤ normalizedIdeal I i j from le_sup_left) hq), map_zero]

def coneToTorus : ConeRing I →+* TorusRing I i j :=
  Ideal.Quotient.lift I (eval₂Hom (algebraMap R (TorusRing I i j)) (scaledVariables I i j))
    (scaledEvaluation_vanishes I i j hI)

@[simp] theorem coneToTorus_mk (p : MvPolynomial (X ⊕ Y) R) :
    coneToTorus I i j hI (Ideal.Quotient.mk I p) =
      eval₂ (algebraMap R (TorusRing I i j)) (scaledVariables I i j) p := rfl

@[simp] theorem coneToTorus_left (k : X) :
    coneToTorus I i j hI (leftCoordinate I k) =
      torusVariable I i j true * chartVariables I i j (Sum.inl k) := by
  simp [leftCoordinate]

@[simp] theorem coneToTorus_right (k : Y) :
    coneToTorus I i j hI (rightCoordinate I k) =
      torusVariable I i j false * chartVariables I i j (Sum.inr k) := by
  simp [rightCoordinate]

@[simp] theorem coneToTorus_denominator :
    coneToTorus I i j hI (leftCoordinate I i * rightCoordinate I j) =
      algebraMap (TorusPolynomial I i j) (TorusRing I i j) (torusDenominator I i j) := by
  simp [torusDenominator, torusVariable]

/-- The cone-to-torus map extends to the actual selected coordinate open. -/
def coneOpenToTorus : ConeOpen I i j →+* TorusRing I i j :=
  IsLocalization.Away.lift (leftCoordinate I i * rightCoordinate I j)
    (g := coneToTorus I i j hI) (by
      rw [coneToTorus_denominator]
      exact IsLocalization.Away.algebraMap_isUnit _)

@[simp] theorem coneOpenToTorus_algebraMap (q : ConeRing I) :
    coneOpenToTorus I i j hI (algebraMap (ConeRing I) (ConeOpen I i j) q) =
      coneToTorus I i j hI q :=
  IsLocalization.Away.lift_eq _ _ q

/-- The inverse map sends the torus variables to the two selected cone coordinates. -/
def torusCoordinates : Bool → ConeOpen I i j :=
  fun b => if b then algebraMap (ConeRing I) (ConeOpen I i j) (leftCoordinate I i)
    else algebraMap (ConeRing I) (ConeOpen I i j) (rightCoordinate I j)

def torusPolynomialToConeOpen : TorusPolynomial I i j →+* ConeOpen I i j :=
  eval₂Hom (normalizedChartToConeOpen I i j hI) (torusCoordinates I i j)

@[simp] theorem torusPolynomialToConeOpen_denominator :
    torusPolynomialToConeOpen I i j hI (torusDenominator I i j) =
      algebraMap (ConeRing I) (ConeOpen I i j) (leftCoordinate I i * rightCoordinate I j) := by
  simp [torusPolynomialToConeOpen, torusDenominator, torusCoordinates]

def torusToConeOpen : TorusRing I i j →+* ConeOpen I i j :=
  IsLocalization.Away.lift (torusDenominator I i j)
    (g := torusPolynomialToConeOpen I i j hI) (by
      rw [torusPolynomialToConeOpen_denominator]
      exact IsLocalization.Away.algebraMap_isUnit _)

@[simp] theorem torusToConeOpen_algebraMap (p : TorusPolynomial I i j) :
    torusToConeOpen I i j hI (algebraMap (TorusPolynomial I i j) (TorusRing I i j) p) =
      torusPolynomialToConeOpen I i j hI p :=
  IsLocalization.Away.lift_eq _ _ p

@[simp] theorem torusToConeOpen_variable (b : Bool) :
    torusToConeOpen I i j hI (torusVariable I i j b) = torusCoordinates I i j b := by
  simp [torusVariable, torusPolynomialToConeOpen]

@[simp] theorem torusToConeOpen_chartAlgebraMap (q : NormalizedChart I i j) :
    torusToConeOpen I i j hI (algebraMap (NormalizedChart I i j) (TorusRing I i j) q) =
      normalizedChartToConeOpen I i j hI q := by
  rw [IsScalarTower.algebraMap_apply (NormalizedChart I i j)
    (TorusPolynomial I i j) (TorusRing I i j), torusToConeOpen_algebraMap]
  exact eval₂Hom_C _ _ _

@[simp] theorem torusToConeOpen_chartVariables (k : X ⊕ Y) :
    torusToConeOpen I i j hI (chartVariables I i j k) = ratioVariables I i j k := by
  simp [chartVariables, ratioEvaluation]

theorem selected_left_mul_ratio (k : X) :
    algebraMap (ConeRing I) (ConeOpen I i j) (leftCoordinate I i) *
      ratioVariables I i j (Sum.inl k) =
      algebraMap (ConeRing I) (ConeOpen I i j) (leftCoordinate I k) := by
  dsimp [ratioVariables, GeneralConormalFlatFamily.leftRatio]
  calc
    _ = algebraMap (ConeRing I) (ConeOpen I i j) (leftCoordinate I k) *
        (algebraMap (ConeRing I) (ConeOpen I i j) (leftCoordinate I i * rightCoordinate I j) *
          IsLocalization.Away.invSelf (leftCoordinate I i * rightCoordinate I j)) := by
      simp only [map_mul]
      ring
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, mul_one]

theorem selected_right_mul_ratio (k : Y) :
    algebraMap (ConeRing I) (ConeOpen I i j) (rightCoordinate I j) *
      ratioVariables I i j (Sum.inr k) =
      algebraMap (ConeRing I) (ConeOpen I i j) (rightCoordinate I k) := by
  dsimp [ratioVariables, GeneralConormalFlatFamily.rightRatio]
  calc
    _ = algebraMap (ConeRing I) (ConeOpen I i j) (rightCoordinate I k) *
        (algebraMap (ConeRing I) (ConeOpen I i j) (leftCoordinate I i * rightCoordinate I j) *
          IsLocalization.Away.invSelf (leftCoordinate I i * rightCoordinate I j)) := by
      simp only [map_mul]
      ring
    _ = _ := by rw [IsLocalization.Away.mul_invSelf, mul_one]

@[simp] theorem torusToConeOpen_scaledVariables (k : X ⊕ Y) :
    torusToConeOpen I i j hI (scaledVariables I i j k) = originalVariables I i j k := by
  cases k with
  | inl k =>
    simp only [scaledVariables_left, map_mul, torusToConeOpen_variable,
      torusToConeOpen_chartVariables, torusCoordinates, ↓reduceIte]
    exact selected_left_mul_ratio I i j k
  | inr k =>
    simp only [scaledVariables_right, map_mul, torusToConeOpen_variable,
      torusToConeOpen_chartVariables, torusCoordinates, Bool.false_eq_true, ↓reduceIte]
    exact selected_right_mul_ratio I i j k

@[simp] theorem torusToConeOpen_base (r : R) :
    torusToConeOpen I i j hI (algebraMap R (TorusRing I i j) r) =
      algebraMap R (ConeOpen I i j) r := by
  rw [IsScalarTower.algebraMap_apply R (NormalizedChart I i j) (TorusRing I i j),
    torusToConeOpen_chartAlgebraMap]
  exact (normalizedChartToConeOpenAlg I i j hI).commutes r

@[simp] theorem coneOpenToTorus_base (r : R) :
    coneOpenToTorus I i j hI (algebraMap R (ConeOpen I i j) r) =
      algebraMap R (TorusRing I i j) r := by
  rw [IsScalarTower.algebraMap_apply R (ConeRing I) (ConeOpen I i j),
    coneOpenToTorus_algebraMap, ← Ideal.Quotient.mk_algebraMap R I,
    MvPolynomial.algebraMap_eq, coneToTorus_mk, eval₂_C]

theorem torusToConeOpen_coneToTorus (q : ConeRing I) :
    torusToConeOpen I i j hI (coneToTorus I i j hI q) =
      algebraMap (ConeRing I) (ConeOpen I i j) q := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [coneToTorus_mk, ← originalEvaluation I i j p]
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp => simp [hp]

theorem cone_leftInverse :
    Function.LeftInverse (torusToConeOpen I i j hI) (coneOpenToTorus I i j hI) := by
  have h : (torusToConeOpen I i j hI).comp (coneOpenToTorus I i j hI) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (leftCoordinate I i * rightCoordinate I j))
    apply RingHom.ext
    intro q
    simp only [RingHom.comp_apply, RingHom.id_apply, coneOpenToTorus_algebraMap,
      torusToConeOpen_coneToTorus]
  intro q
  exact DFunLike.congr_fun h q

@[simp] theorem coneOpenToTorus_invSelf :
    coneOpenToTorus I i j hI
      (IsLocalization.Away.invSelf (leftCoordinate I i * rightCoordinate I j)) =
      IsLocalization.Away.invSelf (torusDenominator I i j) := by
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := TorusRing I i j) (torusDenominator I i j)).mul_left_cancel
  have h := congrArg (coneOpenToTorus I i j hI)
    (IsLocalization.Away.mul_invSelf (S := ConeOpen I i j)
      (leftCoordinate I i * rightCoordinate I j))
  rw [map_mul, coneOpenToTorus_algebraMap, coneToTorus_denominator, map_one] at h
  rw [h, IsLocalization.Away.mul_invSelf]

@[simp] theorem coneOpenToTorus_ratioVariables (k : X ⊕ Y) :
    coneOpenToTorus I i j hI (ratioVariables I i j k) = chartVariables I i j k := by
  have ht : torusVariable I i j true * torusVariable I i j false *
      IsLocalization.Away.invSelf (torusDenominator I i j) = 1 := by
    simpa only [torusVariable, ← map_mul, torusDenominator] using
      (IsLocalization.Away.mul_invSelf (S := TorusRing I i j) (torusDenominator I i j))
  cases k with
  | inl k =>
    simp only [ratioVariables, Sum.elim_inl, GeneralConormalFlatFamily.leftRatio,
      map_mul, coneOpenToTorus_algebraMap, coneToTorus_left, coneToTorus_right,
      chartVariables_right_selected, mul_one, coneOpenToTorus_invSelf]
    calc
      _ = chartVariables I i j (Sum.inl k) * (torusVariable I i j true *
          torusVariable I i j false * IsLocalization.Away.invSelf (torusDenominator I i j)) := by ring
      _ = _ := by rw [ht, mul_one]
  | inr k =>
    simp only [ratioVariables, Sum.elim_inr, GeneralConormalFlatFamily.rightRatio,
      map_mul, coneOpenToTorus_algebraMap, coneToTorus_left, coneToTorus_right,
      chartVariables_left_selected, mul_one, coneOpenToTorus_invSelf]
    calc
      _ = chartVariables I i j (Sum.inr k) * (torusVariable I i j true *
          torusVariable I i j false * IsLocalization.Away.invSelf (torusDenominator I i j)) := by ring
      _ = _ := by rw [ht, mul_one]

@[simp] theorem coneOpenToTorus_normalized (q : NormalizedChart I i j) :
    coneOpenToTorus I i j hI (normalizedChartToConeOpen I i j hI q) =
      algebraMap (NormalizedChart I i j) (TorusRing I i j) q := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [normalizedChartToConeOpen_mk, ← chartEvaluation I i j p]
  induction p using MvPolynomial.induction_on with
  | C r => simp [ratioEvaluation]
  | add p q hp hq => simpa only [map_add, eval₂_add] using congrArg₂ (· + ·) hp hq
  | mul_X p k hp =>
    simp only [map_mul, eval₂_mul, eval₂_X]
    rw [hp]
    congr 1
    simpa only [ratioEvaluation, eval₂Hom_X'] using
      coneOpenToTorus_ratioVariables I i j hI k

theorem torus_rightInverse :
    Function.RightInverse (torusToConeOpen I i j hI) (coneOpenToTorus I i j hI) := by
  have h : (coneOpenToTorus I i j hI).comp (torusToConeOpen I i j hI) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (torusDenominator I i j))
    apply MvPolynomial.ringHom_ext
    · intro q
      simp only [RingHom.comp_apply, RingHom.id_apply, torusToConeOpen_algebraMap,
        torusPolynomialToConeOpen, eval₂Hom_C, coneOpenToTorus_normalized]
      exact IsScalarTower.algebraMap_apply (NormalizedChart I i j)
        (TorusPolynomial I i j) (TorusRing I i j) q
    · intro b
      cases b <;>
        simp [torusPolynomialToConeOpen, torusCoordinates, torusVariable]
  intro q
  exact DFunLike.congr_fun h q

/-- The actual coordinate-open cone decomposes as the actual normalized
chart times two multiplicative groups, at the level of coordinate algebras. -/
def coneOpenEquivTorus : ConeOpen I i j ≃+* TorusRing I i j :=
  { coneOpenToTorus I i j hI with
    invFun := torusToConeOpen I i j hI
    left_inv := cone_leftInverse I i j hI
    right_inv := torus_rightInverse I i j hI }

end Sheshadri.ConormalChartTorus
