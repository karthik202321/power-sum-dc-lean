/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FatPointInterpolation
import Sheshadri.ProjectiveChartHilbertBound
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Hilbert functions of finite projective schemes in an actual common chart

The boundary condition is an ideal-theoretic support condition: all Segre
coordinates belong to the radical of the ideal obtained by adjoining the
chart denominator. It is not a numerical degree or multiplicity assumption.
-/

noncomputable section
namespace Sheshadri.FiniteProjectiveHilbert
open MvPolynomial MultiProjective ProjectivePointInterpolation
open FlatMultiGradedHilbert FatPointInterpolation ProjectiveChartHilbertBound

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

section Boundary
variable {X U V K : Type*} [Fintype X] [Fintype U] [Fintype V] [Field K]

def segreCoordinate (i : X) (j : U) (k : V) :
    MvPolynomial (Variables X U V) K :=
  MvPolynomial.X (.inl i) * MvPolynomial.X (.inr (.inl j)) *
    MvPolynomial.X (.inr (.inr k))

theorem weight_coordinates (e : Variables X U V →₀ ℕ) :
    Finsupp.weight (weight X U V) e =
      (∑ i : X, e (.inl i), ∑ j : U, e (.inr (.inl j)),
        ∑ k : V, e (.inr (.inr k))) := by
  classical
  ext <;> simp [Finsupp.weight_apply, Finsupp.sum_fintype, weight,
    Prod.fst_sum, Prod.snd_sum]

theorem exists_exponent_large {T : Type*} [Fintype T] (e : T → ℕ) (M n : ℕ)
    (hn : Fintype.card T * M < n) (he : ∑ i, e i = n) : ∃ i, M ≤ e i := by
  classical
  by_contra h
  push_neg at h
  have hsum : ∑ i, e i ≤ ∑ _ : T, M :=
    Finset.sum_le_sum (fun i _ => (h i).le)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  omega

theorem segre_power_dvd_monomial (e : Variables X U V →₀ ℕ) (a : K)
    (i : X) (j : U) (k : V) (M : ℕ)
    (hi : M ≤ e (.inl i)) (hj : M ≤ e (.inr (.inl j)))
    (hk : M ≤ e (.inr (.inr k))) :
    segreCoordinate (K := K) i j k ^ M ∣ monomial e a := by
  classical
  have he : Finsupp.single (.inl i) M + Finsupp.single (.inr (.inl j)) M +
      Finsupp.single (.inr (.inr k)) M ≤ e := by
    rintro (x | (x | x))
    · by_cases hx : x = i <;> simp_all [Finsupp.single_apply, eq_comm]
    · by_cases hx : x = j <;> simp_all [Finsupp.single_apply, eq_comm]
    · by_cases hx : x = k <;> simp_all [Finsupp.single_apply, eq_comm]
  simpa [segreCoordinate, mul_pow, X_pow_eq_monomial, monomial_mul] using
    (monomial_dvd_monomial.mpr ⟨Or.inr he, one_dvd a⟩ :
      monomial (Finsupp.single (.inl i) M + Finsupp.single (.inr (.inl j)) M +
        Finsupp.single (.inr (.inr k)) M) (1 : K) ∣ monomial e a)

/-- The whole projective support avoids the boundary precisely in the
algebraic sense needed below. No projective point enumeration is assumed. -/
def BoundaryAvoidance (I : Ideal (MvPolynomial (Variables X U V) K))
    (l : MvPolynomial (Variables X U V) K) : Prop :=
  ∀ i j k, segreCoordinate (K := K) i j k ∈ (I ⊔ Ideal.span {l}).radical

/-- Radical boundary avoidance kills every sufficiently high actual
diagonal homogeneous piece of the boundary quotient. -/
theorem boundary_eventually_homogeneous_mem
    (J : Ideal (MvPolynomial (Variables X U V) K))
    (hJ : ∀ i j k, segreCoordinate (K := K) i j k ∈ J.radical) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ f : MvPolynomial (Variables X U V) K,
      IsWeightedHomogeneous (weight X U V) f (n, n, n) → f ∈ J := by
  classical
  choose q hq using fun t : X × U × V =>
    Ideal.mem_radical_iff.mp (hJ t.1 t.2.1 t.2.2)
  let M := Finset.univ.sup q
  have hpow (i : X) (j : U) (k : V) : segreCoordinate (K := K) i j k ^ M ∈ J := by
    have hle : q (i, j, k) ≤ M := Finset.le_sup (Finset.mem_univ _)
    have hd : segreCoordinate (K := K) i j k ^ q (i, j, k) ∣
        segreCoordinate (K := K) i j k ^ M := pow_dvd_pow _ hle
    exact J.mem_of_dvd hd (hq (i, j, k))
  let N := (Fintype.card X + Fintype.card U + Fintype.card V) * M + 1
  refine ⟨N, fun n hn f hf => ?_⟩
  rw [← f.support_sum_monomial_coeff]
  apply J.sum_mem
  intro e he
  have hd := hf (mem_support_iff.mp he)
  rw [weight_coordinates] at hd
  have hx : ∑ i : X, e (.inl i) = n := congrArg Prod.fst hd
  have hu : ∑ j : U, e (.inr (.inl j)) = n := congrArg (fun d : Degree => d.2.1) hd
  have hv : ∑ k : V, e (.inr (.inr k)) = n := congrArg (fun d : Degree => d.2.2) hd
  have hnX : Fintype.card X * M < n := by dsimp [N] at hn; nlinarith
  have hnU : Fintype.card U * M < n := by dsimp [N] at hn; nlinarith
  have hnV : Fintype.card V * M < n := by dsimp [N] at hn; nlinarith
  obtain ⟨i, hi⟩ := exists_exponent_large _ M n hnX hx
  obtain ⟨j, hj⟩ := exists_exponent_large _ M n hnU hu
  obtain ⟨k, hk⟩ := exists_exponent_large _ M n hnV hv
  exact J.mem_of_dvd (segre_power_dvd_monomial e (coeff e f) i j k M hi hj hk)
    (hpow i j k)

end Boundary

section DiagonalTransition
variable {σ K : Type*} [Field K]
variable (w : σ → Degree) (I : Ideal (MvPolynomial σ K))
  (l : MvPolynomial σ K) (hl : IsWeightedHomogeneous w l (1, 1, 1))

def diagonalMultiplication (hl : IsWeightedHomogeneous w l (1, 1, 1)) (n : ℕ) :
    coordinatePiece w I (n, n, n) →ₗ[K] coordinatePiece w I (n + 1, n + 1, n + 1) :=
  (((LinearMap.mulLeft K (Ideal.Quotient.mk I l)).comp
    (coordinatePiece w I (n, n, n)).subtype).codRestrict _ (by
      rintro ⟨x, f, hf, hfx⟩
      refine ⟨l * f, ?_, ?_⟩
      · have hdeg : (1, 1, 1) + (n, n, n) = (n + 1, n + 1, n + 1) := by
          ext <;> dsimp <;> omega
        exact hdeg ▸ hl.mul hf
      · change Ideal.Quotient.mk I (l * f) = Ideal.Quotient.mk I l * x
        change Ideal.Quotient.mk I f = x at hfx
        rw [map_mul, hfx]))

@[simp] theorem diagonalMultiplication_apply (n : ℕ)
    (x : coordinatePiece w I (n, n, n)) :
    (diagonalMultiplication w I l hl n x : MvPolynomial σ K ⧸ I) =
      Ideal.Quotient.mk I l * (x : MvPolynomial σ K ⧸ I) := rfl

/-- If the boundary piece vanishes, multiplication by its homogeneous
denominator is onto the next actual coordinate piece. -/
theorem diagonalMultiplication_surjective (hI : IsHomogeneous w I) (n : ℕ)
    (hvanish : ∀ f : MvPolynomial σ K,
      IsWeightedHomogeneous w f (n + 1, n + 1, n + 1) → f ∈ I ⊔ Ideal.span {l}) :
    Function.Surjective (diagonalMultiplication w I l hl n) := by
  rintro ⟨x, f, hf, hfx⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hvanish f hf)
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hb
  have hc := congrArg (weightedHomogeneousComponent w (n + 1, n + 1, n + 1)) hab
  rw [map_add, hq, IsWeightedHomogeneous.weightedHomogeneousComponent_same hf] at hc
  have hn : (n + 1, n + 1, n + 1) = (1, 1, 1) + (n, n, n) := by
    ext <;> dsimp <;> omega
  rw [hn, component_mul_left w hl] at hc
  let qn := weightedHomogeneousComponent w (n, n, n) q
  refine ⟨⟨Ideal.Quotient.mk I qn, qn, weightedHomogeneousComponent_mem _ q _, rfl⟩, ?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk I l * Ideal.Quotient.mk I qn = x
  change Ideal.Quotient.mk I f = x at hfx
  rw [← map_mul, ← hfx, ← hc, map_add,
    Ideal.Quotient.eq_zero_iff_mem.mpr (hI _ _ ha), zero_add]

/-- A tail of surjective maps between finite vector spaces eventually
consists of isomorphisms. This uses the minimum of the actual dimensions. -/
theorem eventually_diagonalMultiplication_bijective
    [∀ n, Module.Finite K (coordinatePiece w I (n, n, n))]
    (N : ℕ) (hN : ∀ n, N ≤ n → Function.Surjective (diagonalMultiplication w I l hl n)) :
    ∃ M : ℕ, N ≤ M ∧ ∀ n, M ≤ n →
      Function.Bijective (diagonalMultiplication w I l hl n) := by
  classical
  let dim := fun n => Module.finrank K (coordinatePiece w I (n, n, n))
  have hstep (n : ℕ) (hn : N ≤ n) : dim (n + 1) ≤ dim n := by
    have h := (diagonalMultiplication w I l hl n).finrank_range_le
    rw [LinearMap.range_eq_top.mpr (hN n hn), finrank_top] at h
    exact h
  have hex : ∃ d : ℕ, ∃ n, N ≤ n ∧ dim n = d := ⟨dim N, N, le_rfl, rfl⟩
  obtain ⟨M, hNM, hM⟩ := Nat.find_spec hex
  have hmin (n : ℕ) (hn : N ≤ n) : Nat.find hex ≤ dim n :=
    Nat.find_min' hex ⟨n, hn, rfl⟩
  have hconst (n : ℕ) (hn : M ≤ n) : dim n = Nat.find hex := by
    apply le_antisymm _ (hmin n (hNM.trans hn))
    rw [← hM]
    induction n, hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih => exact (hstep n (hNM.trans hn)).trans ih
  refine ⟨M, hNM, fun n hn => ⟨?_, hN n (hNM.trans hn)⟩⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (show dim n = dim (n + 1) by rw [hconst n hn, hconst (n + 1) (by omega)])).mpr
  exact hN n (hNM.trans hn)

theorem homogeneous_mem_of_denominator_power_mem
    (M : ℕ) (hinj : ∀ n, M ≤ n → Function.Injective (diagonalMultiplication w I l hl n))
    (n : ℕ) (hn : M ≤ n) (f : MvPolynomial σ K)
    (hf : IsWeightedHomogeneous w f (n, n, n)) (r : ℕ)
    (hr : l ^ r * f ∈ I) : f ∈ I := by
  induction r generalizing n f with
  | zero => simpa using hr
  | succ r ih =>
    have hlf : l * f ∈ I := by
      apply ih (n + 1) (by omega) (l * f)
      · have hdeg : (1, 1, 1) + (n, n, n) = (n + 1, n + 1, n + 1) := by
          ext <;> dsimp <;> omega
        exact hdeg ▸ hl.mul hf
      · simpa [pow_succ, mul_assoc] using hr
    have heq : diagonalMultiplication w I l hl n
        ⟨Ideal.Quotient.mk I f, f, hf, rfl⟩ = 0 := by
      apply Subtype.ext
      change Ideal.Quotient.mk I l * Ideal.Quotient.mk I f = 0
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hlf
    have hz := (hinj n hn) (heq.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hz)

theorem lower_homogeneous_degree {A : Type*} [CommRing A] [Algebra K A]
    (φ : MvPolynomial σ K →ₐ[K] A) (hI : ∀ f ∈ I, φ f = 0)
    (hφl : φ l = 1) (N : ℕ)
    (hN : ∀ n, N ≤ n → Function.Surjective (diagonalMultiplication w I l hl n))
    (n m : ℕ) (hNn : N ≤ n) (hnm : n ≤ m)
    (f : MvPolynomial σ K) (hf : IsWeightedHomogeneous w f (m, m, m)) :
    ∃ g : MvPolynomial σ K, IsWeightedHomogeneous w g (n, n, n) ∧ φ g = φ f := by
  induction m, hnm using Nat.le_induction generalizing f with
  | base => exact ⟨f, hf, rfl⟩
  | succ m hm ih =>
    obtain ⟨z, hz⟩ := hN m (hNn.trans hm) ⟨Ideal.Quotient.mk I f, f, hf, rfl⟩
    obtain ⟨q, hq, hqz⟩ := z.property
    have hclass : Ideal.Quotient.mk I (l * q) = Ideal.Quotient.mk I f := by
      have h := congrArg Subtype.val hz
      change Ideal.Quotient.mk I l * (z : MvPolynomial σ K ⧸ I) = Ideal.Quotient.mk I f at h
      change Ideal.Quotient.mk I q = (z : MvPolynomial σ K ⧸ I) at hqz
      rw [map_mul, hqz]
      exact h
    have hval : φ q = φ f := by
      have h := hI _ (Ideal.Quotient.eq.mp hclass)
      simpa [map_sub, map_mul, hφl, sub_eq_zero] using h
    obtain ⟨g, hg, hgf⟩ := ih q hq
    exact ⟨g, hg, hgf.trans hval⟩

/-- High-piece surjectivity follows from boundary avoidance without any
advance finite-dimensionality assumption on the chart algebra. -/
theorem quotientPieceMap_surjective_of_transitions {A : Type*} [CommRing A] [Algebra K A]
    (lx lu lv : MvPolynomial σ K)
    (hx : IsWeightedHomogeneous w lx (1, 0, 0))
    (hu : IsWeightedHomogeneous w lu (0, 1, 0))
    (hv : IsWeightedHomogeneous w lv (0, 0, 1))
    (φ : MvPolynomial σ K →ₐ[K] A) (hφ : Function.Surjective φ)
    (hI : ∀ f ∈ I, φ f = 0) (hφl : φ l = 1)
    (hφx : φ lx = 1) (hφu : φ lu = 1) (hφv : φ lv = 1)
    (N : ℕ) (hN : ∀ n, N ≤ n → Function.Surjective (diagonalMultiplication w I l hl n))
    (n : ℕ) (hn : N ≤ n) :
    Function.Surjective (quotientPieceMap w I φ hI (n, n, n)) := by
  intro y
  obtain ⟨f, rfl⟩ := hφ y
  let m := max n (degreeBound w f)
  let g := homogenizeForms w lx lu lv f m
  have hg : IsWeightedHomogeneous w g (m, m, m) :=
    homogenizeForms_homogeneous w lx lu lv hx hu hv f m (le_max_right _ _)
  obtain ⟨q, hq, hqg⟩ := lower_homogeneous_degree w I l hl φ hI hφl N hN n m hn
    (le_max_left _ _) g hg
  refine ⟨⟨Ideal.Quotient.mk I q, q, hq, rfl⟩, ?_⟩
  change φ q = φ f
  rw [hqg]
  exact map_homogenizeForms w lx lu lv φ hφx hφu hφv f m

end DiagonalTransition

section ActualChart
variable {X U V K : Type*} [Field K]
variable (I : Ideal (MvPolynomial (Variables X U V) K))
  (lx lu lv : MvPolynomial (Variables X U V) K)

def chartIdeal : Ideal (MvPolynomial (Variables X U V) K) :=
  I ⊔ Ideal.span {lx - 1, lu - 1, lv - 1}

abbrev ChartAlgebra := MvPolynomial (Variables X U V) K ⧸ chartIdeal I lx lu lv

def chartMap : MvPolynomial (Variables X U V) K →ₐ[K] ChartAlgebra I lx lu lv :=
  Ideal.Quotient.mkₐ K _

theorem chartMap_kills (f : MvPolynomial (Variables X U V) K) (hf : f ∈ I) :
    chartMap I lx lu lv f = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show I ≤ chartIdeal I lx lu lv from le_sup_left) hf)

@[simp] theorem chartMap_first : chartMap I lx lu lv lx = 1 := by
  apply Ideal.Quotient.eq.mpr
  exact (show Ideal.span {lx - 1, lu - 1, lv - 1} ≤ chartIdeal I lx lu lv from le_sup_right)
    (Ideal.subset_span (by simp))

@[simp] theorem chartMap_second : chartMap I lx lu lv lu = 1 := by
  apply Ideal.Quotient.eq.mpr
  exact (show Ideal.span {lx - 1, lu - 1, lv - 1} ≤ chartIdeal I lx lu lv from le_sup_right)
    (Ideal.subset_span (by simp))

@[simp] theorem chartMap_third : chartMap I lx lu lv lv = 1 := by
  apply Ideal.Quotient.eq.mpr
  exact (show Ideal.span {lx - 1, lu - 1, lv - 1} ≤ chartIdeal I lx lu lv from le_sup_right)
    (Ideal.subset_span (by simp))

abbrev DenominatorLocalization := Localization.Away (Ideal.Quotient.mk I (lx * lu * lv))

def localizationPolynomialMap :
    MvPolynomial (Variables X U V) K →ₐ[K] DenominatorLocalization I lx lu lv :=
  (IsScalarTower.toAlgHom K (MvPolynomial (Variables X U V) K ⧸ I)
    (DenominatorLocalization I lx lu lv)).comp (Ideal.Quotient.mkₐ K I)

theorem localizationPolynomialMap_kills (f : MvPolynomial (Variables X U V) K) (hf : f ∈ I) :
    localizationPolynomialMap I lx lu lv f = 0 := by
  change algebraMap (MvPolynomial (Variables X U V) K ⧸ I) _ (Ideal.Quotient.mk I f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]

theorem localizationPolynomialMap_forms_isUnit :
    IsUnit (localizationPolynomialMap I lx lu lv lx) ∧
    IsUnit (localizationPolynomialMap I lx lu lv lu) ∧
    IsUnit (localizationPolynomialMap I lx lu lv lv) := by
  have h : IsUnit (localizationPolynomialMap I lx lu lv (lx * lu * lv)) :=
    IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk I (lx * lu * lv))
  simpa only [map_mul, IsUnit.mul_iff, and_assoc] using h

def chartUnits : Fin 3 → (DenominatorLocalization I lx lu lv)ˣ :=
  ![(localizationPolynomialMap_forms_isUnit I lx lu lv).1.unit,
    (localizationPolynomialMap_forms_isUnit I lx lu lv).2.1.unit,
    (localizationPolynomialMap_forms_isUnit I lx lu lv).2.2.unit]

theorem chartUnits_values :
    (chartUnits I lx lu lv 0 : DenominatorLocalization I lx lu lv) =
      localizationPolynomialMap I lx lu lv lx ∧
    (chartUnits I lx lu lv 1 : DenominatorLocalization I lx lu lv) =
      localizationPolynomialMap I lx lu lv lu ∧
    (chartUnits I lx lu lv 2 : DenominatorLocalization I lx lu lv) =
      localizationPolynomialMap I lx lu lv lv := by
  exact ⟨(localizationPolynomialMap_forms_isUnit I lx lu lv).1.unit_spec,
    (localizationPolynomialMap_forms_isUnit I lx lu lv).2.1.unit_spec,
    (localizationPolynomialMap_forms_isUnit I lx lu lv).2.2.unit_spec⟩

def normalizedLocalizationMap :
    MvPolynomial (Variables X U V) K →ₐ[K] DenominatorLocalization I lx lu lv :=
  normalizedMap (localizationPolynomialMap I lx lu lv) blockIndex (chartUnits I lx lu lv)

theorem normalizedLocalizationMap_kills_chartIdeal
    (hI : IsHomogeneous (weight X U V) I)
    (hx : IsWeightedHomogeneous (weight X U V) lx (1, 0, 0))
    (hu : IsWeightedHomogeneous (weight X U V) lu (0, 1, 0))
    (hv : IsWeightedHomogeneous (weight X U V) lv (0, 0, 1)) :
    ∀ f ∈ chartIdeal I lx lu lv, normalizedLocalizationMap I lx lu lv f = 0 := by
  have hx' : normalizedLocalizationMap I lx lu lv lx = 1 :=
    normalizedMap_first_form _ _ lx hx (chartUnits_values I lx lu lv).1.symm
  have hu' : normalizedLocalizationMap I lx lu lv lu = 1 :=
    normalizedMap_second_form _ _ lu hu (chartUnits_values I lx lu lv).2.1.symm
  have hv' : normalizedLocalizationMap I lx lu lv lv = 1 :=
    normalizedMap_third_form _ _ lv hv (chartUnits_values I lx lu lv).2.2.symm
  have hle : chartIdeal I lx lu lv ≤
      RingHom.ker (normalizedLocalizationMap I lx lu lv).toRingHom := by
    apply sup_le
    · exact normalizedMap_kills_homogeneous_ideal _ _ I hI
        (localizationPolynomialMap_kills I lx lu lv)
    · apply Ideal.span_le.mpr
      intro f hf
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl | rfl <;>
        simp [RingHom.mem_ker, map_sub, hx', hu', hv']
  exact hle

/-- The kernel of the literal chart quotient, on homogeneous elements,
is exactly torsion killed by a power of the chart denominator. This proof
uses the actual localization and retains nonreduced structure. -/
theorem homogeneous_chart_kernel_power
    (hI : IsHomogeneous (weight X U V) I)
    (hx : IsWeightedHomogeneous (weight X U V) lx (1, 0, 0))
    (hu : IsWeightedHomogeneous (weight X U V) lu (0, 1, 0))
    (hv : IsWeightedHomogeneous (weight X U V) lv (0, 0, 1))
    (f : MvPolynomial (Variables X U V) K) (d : Degree)
    (hf : IsWeightedHomogeneous (weight X U V) f d)
    (hzero : chartMap I lx lu lv f = 0) :
    ∃ r : ℕ, (lx * lu * lv) ^ r * f ∈ I := by
  have hz := normalizedLocalizationMap_kills_chartIdeal I lx lu lv hI hx hu hv f
    (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  rw [normalizedLocalizationMap, normalizedMap_homogeneous _ _ f d hf] at hz
  have hunit : IsUnit (normalizationCharacter (chartUnits I lx lu lv) (Multiplicative.ofAdd d)) := by
    exact ((((chartUnits I lx lu lv 0)⁻¹).isUnit.pow d.1).mul
      (((chartUnits I lx lu lv 1)⁻¹).isUnit.pow d.2.1)).mul
      (((chartUnits I lx lu lv 2)⁻¹).isUnit.pow d.2.2)
  have hraw : localizationPolynomialMap I lx lu lv f = 0 := by
    exact hunit.mul_right_cancel (hz.trans (zero_mul _).symm)
  change algebraMap (MvPolynomial (Variables X U V) K ⧸ I)
    (DenominatorLocalization I lx lu lv) (Ideal.Quotient.mk I f) = 0 at hraw
  obtain ⟨⟨_, r, rfl⟩, hr⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk I (lx * lu * lv)))
      (DenominatorLocalization I lx lu lv) (Ideal.Quotient.mk I f)).mp hraw
  refine ⟨r, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  simpa only [map_mul, map_pow] using hr

def chartPieceMap (n : ℕ) :
    coordinatePiece (weight X U V) I (n, n, n) →ₗ[K] ChartAlgebra I lx lu lv :=
  quotientPieceMap (weight X U V) I (chartMap I lx lu lv) (chartMap_kills I lx lu lv)
    (n, n, n)

/-- Whole-support chart avoidance identifies every sufficiently high
actual homogeneous piece with the literal normalized chart quotient.
Embedded and nilpotent structures are retained. -/
theorem eventually_chartPieceMap_bijective [Fintype X] [Fintype U] [Fintype V]
    (hI : IsHomogeneous (weight X U V) I)
    (hx : IsWeightedHomogeneous (weight X U V) lx (1, 0, 0))
    (hu : IsWeightedHomogeneous (weight X U V) lu (0, 1, 0))
    (hv : IsWeightedHomogeneous (weight X U V) lv (0, 0, 1))
    (hboundary : BoundaryAvoidance I (lx * lu * lv)) :
    ∃ N : ℕ, ∀ n, N ≤ n → Function.Bijective (chartPieceMap I lx lu lv n) := by
  let l := lx * lu * lv
  have hl : IsWeightedHomogeneous (weight X U V) l (1, 1, 1) := by
    simpa only [Prod.mk_add_mk, Nat.reduceAdd] using (hx.mul hu).mul hv
  obtain ⟨N, hN⟩ := boundary_eventually_homogeneous_mem (I ⊔ Ideal.span {l}) hboundary
  have htrans (n : ℕ) (hn : N ≤ n) :
      Function.Surjective (diagonalMultiplication (weight X U V) I l hl n) :=
    diagonalMultiplication_surjective (weight X U V) I l hl hI n (hN (n + 1) (by omega))
  obtain ⟨M, hNM, hM⟩ := eventually_diagonalMultiplication_bijective
    (weight X U V) I l hl N htrans
  refine ⟨M, fun n hn => ⟨?_, ?_⟩⟩
  · apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨f, hf, hfz⟩ := z.property
    change Ideal.Quotient.mk I f = (z : MvPolynomial (Variables X U V) K ⧸ I) at hfz
    have hzero : chartMap I lx lu lv f = 0 := by
      change (Ideal.Quotient.liftₐ I (chartMap I lx lu lv) (chartMap_kills I lx lu lv))
        (z : MvPolynomial (Variables X U V) K ⧸ I) = 0 at hz
      rwa [← hfz] at hz
    obtain ⟨r, hr⟩ := homogeneous_chart_kernel_power I lx lu lv hI hx hu hv f (n, n, n) hf hzero
    have hfI := homogeneous_mem_of_denominator_power_mem (weight X U V) I l hl M
      (fun k hk => (hM k hk).1) n hn f hf r hr
    apply Subtype.ext
    exact hfz.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hfI)
  · exact quotientPieceMap_surjective_of_transitions (weight X U V) I l hl lx lu lv hx hu hv
      (chartMap I lx lu lv) (Ideal.Quotient.mk_surjective)
      (chartMap_kills I lx lu lv) (by simp [l])
      (chartMap_first I lx lu lv) (chartMap_second I lx lu lv) (chartMap_third I lx lu lv)
      N htrans n (hNM.trans hn)

/-- Finite-dimensionality of the actual chart algebra is a conclusion of
the support hypothesis, not a replacement for the geometric argument. -/
theorem chartAlgebra_finite [Fintype X] [Fintype U] [Fintype V]
    (hI : IsHomogeneous (weight X U V) I)
    (hx : IsWeightedHomogeneous (weight X U V) lx (1, 0, 0))
    (hu : IsWeightedHomogeneous (weight X U V) lu (0, 1, 0))
    (hv : IsWeightedHomogeneous (weight X U V) lv (0, 0, 1))
    (hboundary : BoundaryAvoidance I (lx * lu * lv)) :
    Module.Finite K (ChartAlgebra I lx lu lv) := by
  obtain ⟨N, hN⟩ := eventually_chartPieceMap_bijective I lx lu lv hI hx hu hv hboundary
  exact Module.Finite.of_surjective (chartPieceMap I lx lu lv N) (hN N le_rfl).2

/-- The eventual Hilbert value equals the dimension of the actual finite
chart algebra, with no assumed degree or length equality. -/
theorem eventually_finrank_piece_eq_chart [Fintype X] [Fintype U] [Fintype V]
    (hI : IsHomogeneous (weight X U V) I)
    (hx : IsWeightedHomogeneous (weight X U V) lx (1, 0, 0))
    (hu : IsWeightedHomogeneous (weight X U V) lu (0, 1, 0))
    (hv : IsWeightedHomogeneous (weight X U V) lv (0, 0, 1))
    (hboundary : BoundaryAvoidance I (lx * lu * lv)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      Module.finrank K (coordinatePiece (weight X U V) I (n, n, n)) =
        Module.finrank K (ChartAlgebra I lx lu lv) := by
  obtain ⟨N, hN⟩ := eventually_chartPieceMap_bijective I lx lu lv hI hx hu hv hboundary
  exact ⟨N, fun n hn => (LinearEquiv.ofBijective (chartPieceMap I lx lu lv n) (hN n hn)).finrank_eq⟩

end ActualChart
end Sheshadri.FiniteProjectiveHilbert
