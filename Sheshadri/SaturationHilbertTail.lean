/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.GenericHomogeneousSections
import Sheshadri.IrrelevantSaturation
import Mathlib.RingTheory.Ideal.Operations

/-!
# Irrelevant torsion vanishes in high homogeneous degrees

An inclusion of homogeneous ideals whose quotient is killed by a power of
the irrelevant ideal induces equal high-degree homogeneous pieces. The proof
constructs a bound on homogeneous generators and uses actual ideal membership.
This is the algebraic step needed to replace a projective section ideal by
its saturation without changing its Hilbert polynomial.
-/

noncomputable section
namespace Sheshadri.SaturationHilbertTail
open MvPolynomial FlatGradedHilbert HomogeneousQuotientExact

variable {Z K : Type*} [Field K]

/-- A monomial of total degree `d` lies in the `d`th power of the
coordinate-generated irrelevant ideal. -/
theorem monomial_mem_coordinateIdeal_pow (e : Z →₀ ℕ) (a : K) :
    monomial e a ∈ (Ideal.span (Set.range (X : Z → MvPolynomial Z K))) ^ e.degree := by
  classical
  have h := Ideal.prod_mem_prod (s := e.support)
    (I := fun i => (Ideal.span (Set.range (X : Z → MvPolynomial Z K))) ^ e i)
    (x := fun i => (X i : MvPolynomial Z K) ^ e i)
    (fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) (e i))
  rw [Finset.prod_pow_eq_pow_sum] at h
  change (∏ i ∈ e.support, (X i : MvPolynomial Z K) ^ e i) ∈
    (Ideal.span (Set.range (X : Z → MvPolynomial Z K))) ^ e.degree at h
  rw [monomial_eq]
  exact Ideal.mul_mem_left _ _ h

theorem homogeneous_mem_coordinateIdeal_pow (f : MvPolynomial Z K) {d N : ℕ}
    (hf : f.IsHomogeneous d) (hN : N ≤ d) :
    f ∈ (Ideal.span (Set.range (X : Z → MvPolynomial Z K))) ^ N := by
  classical
  rw [← f.support_sum_monomial_coeff]
  apply Ideal.sum_mem
  intro e he
  have hd : e.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one] using hf (mem_support_iff.mp he)
  exact Ideal.pow_le_pow_right (hd ▸ hN) (monomial_mem_coordinateIdeal_pow e (coeff e f))

variable [Finite Z]

/-- Noetherianness provides an actual bound on homogeneous generators of
any homogeneous ideal; no bound is assumed as external data. -/
theorem exists_bounded_homogeneous_generators (J : Ideal (MvPolynomial Z K))
    (hJ : ∀ k f, f ∈ J → homogeneousComponent k f ∈ J) :
    ∃ D : ℕ, Ideal.span {g | g ∈ J ∧ ∃ d ≤ D, g.IsHomogeneous d} = J := by
  classical
  obtain ⟨G, hG⟩ := IsNoetherian.noetherian J
  let D := G.sup (fun f => f.totalDegree)
  refine ⟨D, le_antisymm (Ideal.span_le.mpr (fun _ h => h.1)) ?_⟩
  apply le_trans hG.ge
  apply Ideal.span_le.mpr
  intro g hg
  have hgJ : g ∈ J := by rw [← hG]; exact Ideal.subset_span hg
  rw [← sum_homogeneousComponent g]
  apply Ideal.sum_mem
  intro d hd
  apply Ideal.subset_span
  refine ⟨hJ d g hgJ, d, ?_, homogeneousComponent_mem d g⟩
  exact (Nat.le_of_lt_succ (Finset.mem_range.mp hd)).trans
    (Finset.le_sup (f := fun f => f.totalDegree) hg)

/-- A uniform irrelevant annihilator forces an inclusion of homogeneous
ideals to be equality on every sufficiently high homogeneous component. -/
theorem eventually_homogeneous_mem_of_irrelevant_annihilation
    (I J : Ideal (MvPolynomial Z K))
    (hJ : ∀ k f, f ∈ J → homogeneousComponent k f ∈ J) (N : ℕ)
    (hkill : (Ideal.span (Set.range (X : Z → MvPolynomial Z K))) ^ N * J ≤ I) :
    ∃ B : ℕ, ∀ k, B ≤ k → ∀ f : MvPolynomial Z K,
      f.IsHomogeneous k → f ∈ J → f ∈ I := by
  classical
  obtain ⟨D, hD⟩ := exists_bounded_homogeneous_generators J hJ
  let H : Set (MvPolynomial Z K) := {g | g ∈ J ∧ ∃ d ≤ D, g.IsHomogeneous d}
  have hall : ∀ q ∈ Ideal.span H, ∀ (r : MvPolynomial Z K) (k : ℕ), D + N ≤ k →
      homogeneousComponent k (r * q) ∈ I := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem g hg =>
      intro r k hk
      obtain ⟨hgJ, d, hd, hgd⟩ := hg
      have hdk : d ≤ k := by omega
      have he : k = d + (k-d) := by omega
      rw [mul_comm r g, he, homogeneousComponent_mul_left hgd]
      apply hkill
      apply Ideal.mul_mem_mul_rev
      · exact homogeneous_mem_coordinateIdeal_pow _ (homogeneousComponent_mem (k-d) r)
          (by omega)
      · exact hgJ
    | zero => intro r k hk; simp
    | add q q' hq hq' ih ih' =>
      intro r k hk
      rw [mul_add, map_add]
      exact I.add_mem (ih r k hk) (ih' r k hk)
    | smul a q hq ih =>
      intro r k hk
      simpa only [smul_eq_mul, mul_assoc] using ih (r*a) k hk
  refine ⟨D+N, fun k hk f hf hfJ => ?_⟩
  have h := hall f (by simpa only [H, hD] using hfJ) 1 k hk
  simpa only [one_mul, homogeneousComponent_of_mem hf, if_pos rfl] using h

def comparisonPieceMap (I J : Ideal (MvPolynomial Z K)) (hIJ : I ≤ J) (k : ℕ) :
    coordinatePiece Z K I k →ₗ[K] coordinatePiece Z K J k :=
  (((Ideal.quotientMapₐ J (AlgHom.id K _) hIJ).toLinearMap.comp
    (coordinatePiece Z K I k).subtype).codRestrict _ (by
      rintro ⟨x, f, hf, hfx⟩
      refine ⟨f, hf, ?_⟩
      change Ideal.Quotient.mk J f = Ideal.quotientMapₐ J (AlgHom.id K _) hIJ x
      change Ideal.Quotient.mk I f = x at hfx
      rw [← hfx]
      rfl))

omit [Finite Z] in
theorem comparisonPieceMap_surjective (I J : Ideal (MvPolynomial Z K))
    (hIJ : I ≤ J) (k : ℕ) : Function.Surjective (comparisonPieceMap I J hIJ k) := by
  rintro ⟨x, f, hf, hfx⟩
  refine ⟨⟨Ideal.Quotient.mk I f, f, hf, rfl⟩, ?_⟩
  apply Subtype.ext
  exact hfx

omit [Finite Z] in
theorem comparisonPieceMap_injective (I J : Ideal (MvPolynomial Z K))
    (hIJ : I ≤ J) (k : ℕ)
    (htail : ∀ f : MvPolynomial Z K, f.IsHomogeneous k → f ∈ J → f ∈ I) :
    Function.Injective (comparisonPieceMap I J hIJ k) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  obtain ⟨f, hf, hfx⟩ := x.property
  change Ideal.Quotient.mk I f = (x : QuotientRing I) at hfx
  have hfJ : f ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    change Ideal.quotientMapₐ J (AlgHom.id K _) hIJ (x : QuotientRing I) = 0 at h
    simpa only [← hfx] using h
  apply Subtype.ext
  change (x : QuotientRing I) = 0
  rw [← hfx]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (htail f hf hfJ)

/-- Killing the ideal quotient by an irrelevant power preserves the actual
Hilbert dimensions eventually, including every nonreduced structure. -/
theorem eventually_finrank_eq_of_irrelevant_annihilation
    (I J : Ideal (MvPolynomial Z K)) (hIJ : I ≤ J)
    (hJ : ∀ k f, f ∈ J → homogeneousComponent k f ∈ J) (N : ℕ)
    (hkill : (Ideal.span (Set.range (X : Z → MvPolynomial Z K))) ^ N * J ≤ I) :
    ∃ B : ℕ, ∀ k, B ≤ k →
      Module.finrank K (coordinatePiece Z K I k) =
        Module.finrank K (coordinatePiece Z K J k) := by
  obtain ⟨B, hB⟩ := eventually_homogeneous_mem_of_irrelevant_annihilation I J hJ N hkill
  refine ⟨B, fun k hk => ?_⟩
  exact (LinearEquiv.ofBijective (comparisonPieceMap I J hIJ k)
    ⟨comparisonPieceMap_injective I J hIJ k (hB k hk),
      comparisonPieceMap_surjective I J hIJ k⟩).finrank_eq

omit [Finite Z] in
/-- Actual regularity on the saturated quotient transfers to filter
regularity on the original equation quotient, once high pieces agree. -/
theorem filterRegular_of_regular_mod_larger_ideal
    (I J : Ideal (MvPolynomial Z K)) (hIJ : I ≤ J)
    (htail : ∃ B : ℕ, ∀ k, B ≤ k → ∀ f : MvPolynomial Z K,
      f.IsHomogeneous k → f ∈ J → f ∈ I)
    (g : MvPolynomial Z K) {d : ℕ} (hg : g.IsHomogeneous d)
    (hreg : IsRegular (Ideal.Quotient.mk J g)) :
    GenericHomogeneousSections.FilterRegular I g hg := by
  obtain ⟨B, hB⟩ := htail
  refine ⟨B, fun k hk => ?_⟩
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  obtain ⟨f, hf, hfx⟩ := x.property
  change Ideal.Quotient.mk I f = (x : QuotientRing I) at hfx
  have hgf : g*f ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    change Ideal.Quotient.mk I g * (x : QuotientRing I) = 0 at h
    simpa only [← hfx, map_mul] using h
  have hfJ : f ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hreg.left
    simpa only [mul_zero, ← map_mul] using Ideal.Quotient.eq_zero_iff_mem.mpr (hIJ hgf)
  apply Subtype.ext
  change (x : QuotientRing I) = 0
  rw [← hfx]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hB k hk f hf hfJ)

/-- The actual irrelevant saturation agrees with the original homogeneous
ideal in every sufficiently large homogeneous degree. -/
theorem eventually_mem_saturation (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k f, f ∈ I → homogeneousComponent k f ∈ I) :
    ∃ B : ℕ, ∀ k, B ≤ k → ∀ f : MvPolynomial Z K,
      f.IsHomogeneous k → f ∈ IrrelevantSaturation.saturation I → f ∈ I := by
  obtain ⟨N, hN⟩ := IrrelevantSaturation.exists_irrelevant_power_annihilates I
  exact eventually_homogeneous_mem_of_irrelevant_annihilation I _
    (IrrelevantSaturation.saturation_homogeneous I hI) N (Ideal.mul_le.mpr hN)

/-- Equality of actual eventual Hilbert functions under projective
saturation is proved, not supplied as a closure hypothesis. -/
theorem eventually_finrank_saturation (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k f, f ∈ I → homogeneousComponent k f ∈ I) :
    ∃ B : ℕ, ∀ k, B ≤ k →
      Module.finrank K (coordinatePiece Z K I k) =
        Module.finrank K (coordinatePiece Z K (IrrelevantSaturation.saturation I) k) := by
  obtain ⟨N, hN⟩ := IrrelevantSaturation.exists_irrelevant_power_annihilates I
  exact eventually_finrank_eq_of_irrelevant_annihilation I _
    (IrrelevantSaturation.le_saturation I)
    (IrrelevantSaturation.saturation_homogeneous I hI) N (Ideal.mul_le.mpr hN)

theorem filterRegular_of_regular_saturation (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k f, f ∈ I → homogeneousComponent k f ∈ I)
    (g : MvPolynomial Z K) {d : ℕ} (hg : g.IsHomogeneous d)
    (hreg : IsRegular (Ideal.Quotient.mk (IrrelevantSaturation.saturation I) g)) :
    GenericHomogeneousSections.FilterRegular I g hg :=
  filterRegular_of_regular_mod_larger_ideal I _ (IrrelevantSaturation.le_saturation I)
    (eventually_mem_saturation I hI) g hg hreg

/-- Every homogeneous quotient over an infinite field has an actual
filter-regular hyperplane. No genericity or saturation premise is supplied. -/
theorem exists_filterRegular_hyperplane [Infinite K]
    (I : Ideal (MvPolynomial Z K))
    (hI : ∀ k f, f ∈ I → homogeneousComponent k f ∈ I) :
    ∃ g : MvPolynomial Z K, ∃ hg : g.IsHomogeneous 1,
      GenericHomogeneousSections.FilterRegular I g hg := by
  obtain ⟨g, hg, hreg⟩ := GenericHomogeneousSections.exists_regular_hyperplane
    (IrrelevantSaturation.saturation I) (IrrelevantSaturation.saturation_isSaturated I)
  exact ⟨g, hg, filterRegular_of_regular_saturation I hI g hg hreg⟩

end Sheshadri.SaturationHilbertTail
