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
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Polynomial.HilbertPoly

/-! The actual homogeneous multiplication exact sequence.
For a homogeneous polynomial regular modulo a homogeneous ideal, adjoining
that polynomial gives the expected difference of the dimensions of the
actual homogeneous coordinate pieces. -/

noncomputable section
namespace Sheshadri.HomogeneousQuotientExact
open MvPolynomial FlatGradedHilbert

variable {Z K : Type*} [Finite Z] [Field K]

theorem homogeneousComponent_mul_left {g : MvPolynomial Z K} {d : ℕ}
    (hg : g.IsHomogeneous d) (p : MvPolynomial Z K) (k : ℕ) :
    homogeneousComponent (d + k) (g * p) = g * homogeneousComponent k p := by
  classical
  ext e
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  trans ∑ uv ∈ Finset.antidiagonal e,
    if e.degree = d + k then coeff uv.1 g * coeff uv.2 p else 0
  · split_ifs <;> simp
  apply Finset.sum_congr rfl
  intro uv huv
  have he : uv.1 + uv.2 = e := Finset.mem_antidiagonal.mp huv
  rw [coeff_homogeneousComponent]
  by_cases hgu : coeff uv.1 g = 0
  · simp [hgu]
  have hud : uv.1.degree = d := by simpa only [Finsupp.degree_eq_weight_one] using hg hgu
  have hdeg : e.degree = d + uv.2.degree := by
    rw [← he, Finsupp.degree_add, hud]
  simp only [hdeg, Nat.add_left_cancel_iff]
  split_ifs <;> simp_all

theorem homogeneousComponent_mul_left_eq_zero {g : MvPolynomial Z K} {d k : ℕ}
    (hg : g.IsHomogeneous d) (hk : k < d) (p : MvPolynomial Z K) :
    homogeneousComponent k (g * p) = 0 := by
  classical
  ext e
  rw [coeff_homogeneousComponent, coeff_zero]
  split_ifs with he
  · rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro uv huv
    by_cases hgu : coeff uv.1 g = 0
    · simp [hgu]
    have hud : uv.1.degree = d := by
      simpa only [Finsupp.degree_eq_weight_one] using hg hgu
    have hsum : uv.1 + uv.2 = e := Finset.mem_antidiagonal.mp huv
    have hdeg : d + uv.2.degree = k := by rw [← hud, ← Finsupp.degree_add, hsum, he]
    omega
  · rfl

abbrev QuotientRing (I : Ideal (MvPolynomial Z K)) := MvPolynomial Z K ⧸ I

def enlargedIdeal (I : Ideal (MvPolynomial Z K)) (g : MvPolynomial Z K) :=
  I ⊔ Ideal.span {g}

theorem enlargedIdeal_homogeneous (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I)
    (g : MvPolynomial Z K) {d : ℕ} (hg : g.IsHomogeneous d) :
    ∀ k p, p ∈ enlargedIdeal I g → homogeneousComponent k p ∈ enlargedIdeal I g := by
  intro k p hp
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hp
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp hv
  rw [map_add]
  apply (enlargedIdeal I g).add_mem
  · exact (show I ≤ enlargedIdeal I g from le_sup_left) (hI _ _ hu)
  · by_cases hdk : d ≤ k
    · have he : k = d + (k - d) := by omega
      rw [he, homogeneousComponent_mul_left hg]
      exact (enlargedIdeal I g).mul_mem_right _
        ((show Ideal.span {g} ≤ enlargedIdeal I g from le_sup_right)
          (Ideal.subset_span (Set.mem_singleton g)))
    · rw [homogeneousComponent_mul_left_eq_zero hg (by omega)]
      exact Ideal.zero_mem _

def quotientProjection (I : Ideal (MvPolynomial Z K)) (g : MvPolynomial Z K) :
    QuotientRing I →ₐ[K] QuotientRing (enlargedIdeal I g) :=
  Ideal.quotientMapₐ (enlargedIdeal I g) (AlgHom.id K _) (by exact le_sup_left)

@[simp] theorem quotientProjection_mk (I : Ideal (MvPolynomial Z K))
    (g p : MvPolynomial Z K) :
    quotientProjection I g (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk (enlargedIdeal I g) p := rfl

def pieceProjection (I : Ideal (MvPolynomial Z K)) (g : MvPolynomial Z K) (k : ℕ) :
    coordinatePiece Z K I k →ₗ[K] coordinatePiece Z K (enlargedIdeal I g) k :=
  (((quotientProjection I g).toLinearMap.comp (coordinatePiece Z K I k).subtype).codRestrict _
    (by
      rintro ⟨x, p, hp, hpx⟩
      refine ⟨p, hp, ?_⟩
      change Ideal.Quotient.mk (enlargedIdeal I g) p = quotientProjection I g x
      change Ideal.Quotient.mk I p = x at hpx
      rw [← hpx, quotientProjection_mk]))

theorem pieceProjection_surjective (I : Ideal (MvPolynomial Z K))
    (g : MvPolynomial Z K) (k : ℕ) : Function.Surjective (pieceProjection I g k) := by
  rintro ⟨x, p, hp, hpx⟩
  refine ⟨⟨Ideal.Quotient.mk I p, p, hp, rfl⟩, ?_⟩
  apply Subtype.ext
  change Ideal.Quotient.mk (enlargedIdeal I g) p = x
  exact hpx

theorem pieceProjection_injective_of_lt (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I)
    (g : MvPolynomial Z K) {d k : ℕ} (hg : g.IsHomogeneous d) (hk : k < d) :
    Function.Injective (pieceProjection I g k) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  obtain ⟨p, hp, hpx⟩ := x.property
  change Ideal.Quotient.mk I p = (x : QuotientRing I) at hpx
  have hpJ : p ∈ enlargedIdeal I g := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hx0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    change quotientProjection I g (x : QuotientRing I) = 0 at hx0
    rwa [← hpx, quotientProjection_mk] at hx0
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hpJ
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hv
  have he : homogeneousComponent k u = p := by
    have hc := congrArg (homogeneousComponent k) huv
    rw [map_add, hq, homogeneousComponent_mul_left_eq_zero hg hk,
      add_zero, homogeneousComponent_of_mem hp, if_pos rfl] at hc
    exact hc
  apply Subtype.ext
  change (x : QuotientRing I) = 0
  rw [← hpx]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact he ▸ hI _ _ hu

def pieceMultiplication (I : Ideal (MvPolynomial Z K)) (g : MvPolynomial Z K)
    {d : ℕ} (hg : g.IsHomogeneous d) (k : ℕ) :
    coordinatePiece Z K I k →ₗ[K] coordinatePiece Z K I (d + k) :=
  (((LinearMap.mulLeft K (Ideal.Quotient.mk I g)).comp
    (coordinatePiece Z K I k).subtype).codRestrict _ (by
      rintro ⟨x, p, hp, hpx⟩
      refine ⟨g * p, hg.mul hp, ?_⟩
      change Ideal.Quotient.mk I (g * p) = Ideal.Quotient.mk I g * x
      change Ideal.Quotient.mk I p = x at hpx
      rw [← hpx, map_mul]))

theorem pieceMultiplication_injective (I : Ideal (MvPolynomial Z K))
    (g : MvPolynomial Z K) {d : ℕ} (hg : g.IsHomogeneous d)
    (hreg : IsRegular (Ideal.Quotient.mk I g)) (k : ℕ) :
    Function.Injective (pieceMultiplication I g hg k) := by
  intro x y hxy
  apply Subtype.ext
  exact hreg.left (congrArg Subtype.val hxy)

theorem piece_kernel_eq_range (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I)
    (g : MvPolynomial Z K) {d : ℕ} (hg : g.IsHomogeneous d) (k : ℕ) :
    LinearMap.ker (pieceProjection I g (d + k)) =
      LinearMap.range (pieceMultiplication I g hg k) := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hpx⟩ := x.property
    change Ideal.Quotient.mk I p = (x : QuotientRing I) at hpx
    have hpJ : p ∈ enlargedIdeal I g := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hx0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      change quotientProjection I g (x : QuotientRing I) = 0 at hx0
      rwa [← hpx, quotientProjection_mk] at hx0
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hpJ
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hv
    have he : p = homogeneousComponent (d + k) u + g * homogeneousComponent k q := by
      have hc := congrArg (homogeneousComponent (d + k)) huv
      rw [map_add, hq, homogeneousComponent_mul_left hg,
        homogeneousComponent_of_mem hp, if_pos rfl] at hc
      exact hc.symm
    refine ⟨⟨Ideal.Quotient.mk I (homogeneousComponent k q),
      homogeneousComponent k q, homogeneousComponent_mem k q, rfl⟩, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk I g * Ideal.Quotient.mk I (homogeneousComponent k q) = x
    rw [← hpx, he, map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hI _ _ hu), zero_add]
  · rintro ⟨y, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    obtain ⟨p, hp, hpy⟩ := y.property
    change Ideal.Quotient.mk I p = (y : QuotientRing I) at hpy
    change quotientProjection I g (Ideal.Quotient.mk I g * (y : QuotientRing I)) = 0
    rw [← hpy, ← map_mul, quotientProjection_mk]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (enlargedIdeal I g).mul_mem_right _
      ((show Ideal.span {g} ≤ enlargedIdeal I g from le_sup_right)
        (Ideal.subset_span (Set.mem_singleton g)))

/-- Hilbert-function difference for actual coordinate pieces. The regular
element assumption has its standard ring-theoretic meaning, multiplication
by its quotient class is injective. -/
theorem coordinate_finrank_difference (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I)
    (g : MvPolynomial Z K) {d : ℕ} (hg : g.IsHomogeneous d)
    (hreg : IsRegular (Ideal.Quotient.mk I g)) (k : ℕ) :
    Module.finrank K (coordinatePiece Z K (enlargedIdeal I g) (d + k)) +
      Module.finrank K (coordinatePiece Z K I k) =
        Module.finrank K (coordinatePiece Z K I (d + k)) := by
  have h := (pieceProjection I g (d + k)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (pieceProjection_surjective I g (d + k)),
    finrank_top, piece_kernel_eq_range I hI g hg k,
    LinearMap.finrank_range_of_inj (pieceMultiplication_injective I g hg hreg k)] at h
  exact h

/-- The generating series of actual homogeneous coordinate dimensions. -/
def coordinateHilbertSeries (I : Ideal (MvPolynomial Z K)) : PowerSeries ℚ :=
  PowerSeries.mk fun k => (Module.finrank K (coordinatePiece Z K I k) : ℚ)

@[simp] theorem coeff_coordinateHilbertSeries (I : Ideal (MvPolynomial Z K)) (k : ℕ) :
    PowerSeries.coeff ℚ k (coordinateHilbertSeries I) =
      (Module.finrank K (coordinatePiece Z K I k) : ℚ) := by
  simp [coordinateHilbertSeries]

/-- The complete Hilbert-series identity, including the low degrees.
This is proved for the actual quotient, not postulated as a numerical rule. -/
theorem coordinateHilbertSeries_enlarged (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I)
    (g : MvPolynomial Z K) {d : ℕ} (hg : g.IsHomogeneous d)
    (hreg : IsRegular (Ideal.Quotient.mk I g)) :
    coordinateHilbertSeries (enlargedIdeal I g) =
      (1 - PowerSeries.X ^ d) * coordinateHilbertSeries I := by
  ext k
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  simp only [coeff_coordinateHilbertSeries]
  by_cases hdk : d ≤ k
  · rw [if_pos hdk]
    have h := coordinate_finrank_difference I hI g hg hreg (k - d)
    rw [Nat.add_sub_of_le hdk] at h
    apply eq_sub_iff_add_eq.mpr
    exact_mod_cast h
  · rw [if_neg hdk, sub_zero]
    have h := (LinearEquiv.ofBijective (pieceProjection I g k)
      ⟨pieceProjection_injective_of_lt I hI g hg (by omega),
       pieceProjection_surjective I g k⟩).finrank_eq
    exact_mod_cast h.symm

/-- Successively adjoining actual equations. -/
def idealSequence (I : Ideal (MvPolynomial Z K)) (g : ℕ → MvPolynomial Z K) :
    ℕ → Ideal (MvPolynomial Z K)
  | 0 => I
  | r + 1 => enlargedIdeal (idealSequence I g r) (g r)

theorem idealSequence_homogeneous (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I)
    (g : ℕ → MvPolynomial Z K) (d : ℕ → ℕ) (r : ℕ)
    (hg : ∀ j < r, (g j).IsHomogeneous (d j)) :
    ∀ k p, p ∈ idealSequence I g r → homogeneousComponent k p ∈ idealSequence I g r := by
  induction r with
  | zero => exact hI
  | succ r ih =>
    exact enlargedIdeal_homogeneous _ (ih (fun j hj => hg j (by omega)))
      (g r) (hg r (by omega))

/-- Hilbert-series numerator for a sequence of homogeneous regular
equations. The hypotheses express only the standard nonzerodivisor condition
in each actual intermediate quotient. -/
theorem coordinateHilbertSeries_regular_sequence
    (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I)
    (g : ℕ → MvPolynomial Z K) (d : ℕ → ℕ) (r : ℕ)
    (hg : ∀ j < r, (g j).IsHomogeneous (d j))
    (hreg : ∀ j < r, IsRegular (Ideal.Quotient.mk (idealSequence I g j) (g j))) :
    coordinateHilbertSeries (idealSequence I g r) =
      (∏ j ∈ Finset.range r, (1 - PowerSeries.X ^ d j)) * coordinateHilbertSeries I := by
  induction r with
  | zero => simp [idealSequence]
  | succ r ih =>
    rw [idealSequence, coordinateHilbertSeries_enlarged _
      (idealSequence_homogeneous I hI g d r (fun j hj => hg j (by omega)))
      (g r) (hg r (by omega)) (hreg r (by omega)),
      ih (fun j hj => hg j (by omega)) (fun j hj => hreg j (by omega)),
      Finset.prod_range_succ]
    ring

/-- The Hilbert-polynomial recurrence follows from the actual exact
sequence. The two polynomials are required only to agree eventually with
the actual coordinate dimensions; their existence can be established by
the independent standard-monomial construction. -/
theorem hilbert_polynomial_difference (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I)
    (g : MvPolynomial Z K) {d : ℕ} (hg : g.IsHomogeneous d)
    (hreg : IsRegular (Ideal.Quotient.mk I g))
    (P Q : Polynomial ℚ)
    (hP : ∃ N : ℕ, ∀ k > N,
      (Module.finrank K (coordinatePiece Z K I k) : ℚ) = P.eval (k : ℚ))
    (hQ : ∃ N : ℕ, ∀ k > N,
      (Module.finrank K (coordinatePiece Z K (enlargedIdeal I g) k) : ℚ) = Q.eval (k : ℚ)) :
    Q = P - P.comp (Polynomial.X - Polynomial.C (d : ℚ)) := by
  obtain ⟨N, hP⟩ := hP
  obtain ⟨M, hQ⟩ := hQ
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Ioi_infinite (max N M + d)).image
    (Nat.cast_injective (R := ℚ)).injOn).mono
  rintro x ⟨k, hk, rfl⟩
  change max N M + d < k at hk
  have hdk : d ≤ k := by omega
  have hnk : N < k := by omega
  have hmk : M < k := by omega
  have hnk' : N < k - d := by omega
  have hrec := coordinate_finrank_difference I hI g hg hreg (k - d)
  rw [Nat.add_sub_of_le hdk] at hrec
  have heq : (Module.finrank K (coordinatePiece Z K (enlargedIdeal I g) k) : ℚ) +
      (Module.finrank K (coordinatePiece Z K I (k - d)) : ℚ) =
      (Module.finrank K (coordinatePiece Z K I k) : ℚ) := by exact_mod_cast hrec
  rw [hQ k hmk, hP (k - d) hnk', hP k hnk, Nat.cast_sub hdk] at heq
  simpa only [Set.mem_setOf_eq, Polynomial.eval_sub, Polynomial.eval_comp,
    Polynomial.eval_X, Polynomial.eval_C] using (eq_sub_iff_add_eq.mpr heq)

end Sheshadri.HomogeneousQuotientExact
