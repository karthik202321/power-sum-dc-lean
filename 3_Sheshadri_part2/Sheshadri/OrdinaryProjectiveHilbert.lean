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
import Sheshadri.FatPointInterpolation
import Sheshadri.ArtinianLocalDecomposition

/-!
# Ordinary projective Hilbert values and actual chart lengths

An eventually constant homogeneous Hilbert function and a filter-regular
linear form identify the actual high-degree pieces with the literal quotient
by `l - 1`. No reducedness or prior finite-dimensionality is assumed.
-/

noncomputable section
namespace Sheshadri.OrdinaryProjectiveHilbert
open MvPolynomial FlatGradedHilbert HomogeneousQuotientExact GenericHomogeneousSections
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

variable {Z K : Type*} [Finite Z] [Field K]

def chartIdeal (I : Ideal (MvPolynomial Z K)) (l : MvPolynomial Z K) :=
  I ⊔ Ideal.span {l - 1}

abbrev ChartAlgebra (I : Ideal (MvPolynomial Z K)) (l : MvPolynomial Z K) :=
  MvPolynomial Z K ⧸ chartIdeal I l

def chartMap (I : Ideal (MvPolynomial Z K)) (l : MvPolynomial Z K) :
    MvPolynomial Z K →ₐ[K] ChartAlgebra I l := Ideal.Quotient.mkₐ K _

omit [Finite Z] in
theorem chartMap_kills (I : Ideal (MvPolynomial Z K)) (l f : MvPolynomial Z K)
    (hf : f ∈ I) : chartMap I l f = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr ((show I ≤ chartIdeal I l from le_sup_left) hf)

omit [Finite Z] in
@[simp] theorem chartMap_linear (I : Ideal (MvPolynomial Z K)) (l : MvPolynomial Z K) :
    chartMap I l l = 1 := by
  apply Ideal.Quotient.eq.mpr
  exact (show Ideal.span {l - 1} ≤ chartIdeal I l from le_sup_right)
    (Ideal.subset_span (Set.mem_singleton _))

def chartPieceMap (I : Ideal (MvPolynomial Z K)) (l : MvPolynomial Z K) (n : ℕ) :
    coordinatePiece Z K I n →ₗ[K] ChartAlgebra I l :=
  (Ideal.Quotient.liftₐ I (chartMap I l) (chartMap_kills I l)).toLinearMap.comp
    (coordinatePiece Z K I n).subtype

section Normalization
variable {A : Type*} [CommRing A] [Algebra K A]

def scaledMap (φ : MvPolynomial Z K →ₐ[K] A) (a : A) : MvPolynomial Z K →ₐ[K] A :=
  aeval (fun i => φ (X i) * a)

omit [Finite Z] in
theorem scaledMap_homogeneous (φ : MvPolynomial Z K →ₐ[K] A) (a : A)
    (f : MvPolynomial Z K) (d : ℕ) (hf : f.IsHomogeneous d) :
    scaledMap φ a f = φ f * a ^ d := by
  classical
  have hφ : φ = aeval (fun i => φ (X i)) := by ext i; simp
  have hprod (e : Z →₀ ℕ) :
      e.prod (fun i n => (φ (X i) * a)^n) =
        e.prod (fun i n => φ (X i)^n) * a^e.degree := by
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Finsupp.degree]
  change aeval (fun i => φ (X i) * a) f = φ f * a^d
  conv_rhs => rw [hφ]
  rw [← f.support_sum_monomial_coeff, map_sum, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  have hd : e.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one] using hf (mem_support_iff.mp he)
  simp only [aeval_def, eval₂_monomial]
  rw [hprod, hd, mul_assoc]

theorem scaledMap_kills (φ : MvPolynomial Z K →ₐ[K] A) (a : A)
    (I : Ideal (MvPolynomial Z K))
    (hI : ∀ d f, f ∈ I → homogeneousComponent d f ∈ I)
    (hφ : ∀ f ∈ I, φ f = 0) (f : MvPolynomial Z K) (hf : f ∈ I) :
    scaledMap φ a f = 0 := by
  classical
  rw [← sum_homogeneousComponent f, map_sum]
  apply Finset.sum_eq_zero
  intro d hd
  rw [scaledMap_homogeneous φ a _ d (homogeneousComponent_mem d f),
    hφ _ (hI d f hf), zero_mul]

end Normalization

/-- On homogeneous elements, the actual chart kernel consists of powers
of the linear denominator. This retains nilpotents. -/
theorem homogeneous_chart_kernel_power
    (I : Ideal (MvPolynomial Z K)) (l : MvPolynomial Z K)
    (hI : ∀ d f, f ∈ I → homogeneousComponent d f ∈ I) (hl : l.IsHomogeneous 1)
    (f : MvPolynomial Z K) (d : ℕ) (hf : f.IsHomogeneous d)
    (hzero : chartMap I l f = 0) : ∃ r : ℕ, l ^ r * f ∈ I := by
  let B := Localization.Away (Ideal.Quotient.mk I l)
  let φ : MvPolynomial Z K →ₐ[K] B :=
    (IsScalarTower.toAlgHom K (MvPolynomial Z K ⧸ I) B).comp (Ideal.Quotient.mkₐ K I)
  have hφ : ∀ f ∈ I, φ f = 0 := by
    intro f hf
    change algebraMap (MvPolynomial Z K ⧸ I) B (Ideal.Quotient.mk I f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
  have hu : IsUnit (φ l) := IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk I l)
  let u : Bˣ := hu.unit
  have huval : (u : B) = φ l := hu.unit_spec
  let ψ := scaledMap φ (↑(u⁻¹) : B)
  have hψl : ψ l = 1 := by
    rw [scaledMap_homogeneous φ _ l 1 hl, pow_one, ← huval]
    exact u.mul_inv
  have hψ : chartIdeal I l ≤ RingHom.ker ψ := by
    apply sup_le
    · exact scaledMap_kills φ _ I hI hφ
    · apply Ideal.span_le.mpr
      intro g hg
      rcases Set.mem_singleton_iff.mp hg with rfl
      simp [RingHom.mem_ker, hψl]
  have hz : ψ f = 0 := hψ (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  rw [scaledMap_homogeneous φ _ f d hf] at hz
  have hraw : φ f = 0 := ((u⁻¹).isUnit.pow d).mul_right_cancel
    (hz.trans (zero_mul _).symm)
  change algebraMap (MvPolynomial Z K ⧸ I) B (Ideal.Quotient.mk I f) = 0 at hraw
  obtain ⟨⟨_, r, rfl⟩, hr⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (Ideal.Quotient.mk I l))
      B (Ideal.Quotient.mk I f)).mp hraw
  exact ⟨r, Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [map_mul, map_pow] using hr)⟩

omit [Finite Z] in
theorem homogeneous_mem_of_power_mem
    (I : Ideal (MvPolynomial Z K)) (l : MvPolynomial Z K) (hl : l.IsHomogeneous 1)
    (N : ℕ) (hinj : ∀ n, N ≤ n → Function.Injective (pieceMultiplication I l hl n))
    (n : ℕ) (hn : N ≤ n) (f : MvPolynomial Z K) (hf : f.IsHomogeneous n)
    (r : ℕ) (hr : l ^ r * f ∈ I) : f ∈ I := by
  induction r generalizing n f with
  | zero => simpa using hr
  | succ r ih =>
    have hlf : l * f ∈ I := ih (1+n) (by omega) (l*f) (hl.mul hf)
      (by simpa [pow_succ, mul_assoc] using hr)
    have heq : pieceMultiplication I l hl n
        ⟨Ideal.Quotient.mk I f, f, hf, rfl⟩ = 0 := by
      apply Subtype.ext
      change Ideal.Quotient.mk I l * Ideal.Quotient.mk I f = 0
      rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hlf
    have hz := hinj n hn (heq.trans (map_zero _).symm)
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val hz)

theorem lower_homogeneous_degree
    (I : Ideal (MvPolynomial Z K)) (l : MvPolynomial Z K) (hl : l.IsHomogeneous 1)
    (N : ℕ) (hsurj : ∀ n, N ≤ n → Function.Surjective (pieceMultiplication I l hl n))
    (n m : ℕ) (hNn : N ≤ n) (hnm : n ≤ m)
    (f : MvPolynomial Z K) (hf : f.IsHomogeneous m) :
    ∃ g : MvPolynomial Z K, g.IsHomogeneous n ∧ chartMap I l g = chartMap I l f := by
  induction m, hnm using Nat.le_induction generalizing f with
  | base => exact ⟨f, hf, rfl⟩
  | succ m hm ih =>
    have hf' : f.IsHomogeneous (1+m) := by simpa only [Nat.add_comm] using hf
    obtain ⟨z, hz⟩ := hsurj m (hNn.trans hm) ⟨Ideal.Quotient.mk I f, f, hf', rfl⟩
    obtain ⟨q, hq, hqz⟩ := z.property
    have hclass : Ideal.Quotient.mk I (l*q) = Ideal.Quotient.mk I f := by
      have h := congrArg Subtype.val hz
      change Ideal.Quotient.mk I l * (z : MvPolynomial Z K ⧸ I) = Ideal.Quotient.mk I f at h
      change Ideal.Quotient.mk I q = (z : MvPolynomial Z K ⧸ I) at hqz
      rwa [map_mul, hqz]
    have hval : chartMap I l q = chartMap I l f := by
      have h := chartMap_kills I l _ (Ideal.Quotient.eq.mp hclass)
      simpa only [map_sub, map_mul, chartMap_linear, one_mul, sub_eq_zero] using h
    obtain ⟨g, hg, hgf⟩ := ih q hq
    exact ⟨g, hg, hgf.trans hval⟩

theorem chartPieceMap_surjective
    (I : Ideal (MvPolynomial Z K)) (l : MvPolynomial Z K) (hl : l.IsHomogeneous 1)
    (N : ℕ) (hsurj : ∀ n, N ≤ n → Function.Surjective (pieceMultiplication I l hl n))
    (n : ℕ) (hn : N ≤ n) : Function.Surjective (chartPieceMap I l n) := by
  classical
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hrep (d : ℕ) : ∃ g : MvPolynomial Z K, g.IsHomogeneous n ∧
      chartMap I l g = chartMap I l (homogeneousComponent d f) := by
    by_cases hdn : d ≤ n
    · refine ⟨l^(n-d) * homogeneousComponent d f, ?_, ?_⟩
      · simpa only [Nat.one_mul, Nat.sub_add_cancel hdn] using
          (hl.pow (n-d)).mul (homogeneousComponent_mem d f)
      · simp only [map_mul, map_pow, chartMap_linear, one_pow, one_mul]
    · exact lower_homogeneous_degree I l hl N hsurj n d hn (by omega)
        _ (homogeneousComponent_mem d f)
  choose g hg hgv using hrep
  let q := ∑ d ∈ Finset.range (f.totalDegree+1), g d
  have hq : q.IsHomogeneous n := by
    apply IsHomogeneous.sum
    intro d hd
    exact hg d
  refine ⟨⟨Ideal.Quotient.mk I q, q, hq, rfl⟩, ?_⟩
  change chartMap I l q = chartMap I l f
  dsimp only [q]
  rw [map_sum]
  simp_rw [hgv]
  rw [← map_sum, sum_homogeneousComponent]

/-- Actual high-degree pieces identify with the literal normalized chart.
Both finite-dimensionality and retention of every local multiplicity follow. -/
theorem eventually_chartPieceMap_bijective
    (I : Ideal (MvPolynomial Z K)) (l : MvPolynomial Z K)
    (hI : ∀ d f, f ∈ I → homogeneousComponent d f ∈ I) (hl : l.IsHomogeneous 1)
    (D : ℕ) (hconst : ∃ N : ℕ, ∀ k > N, Module.finrank K (coordinatePiece Z K I k) = D)
    (hreg : FilterRegular I l hl) :
    ∃ N : ℕ, ∀ n, N ≤ n → Function.Bijective (chartPieceMap I l n) := by
  obtain ⟨N, hN⟩ := hconst
  obtain ⟨B, hB⟩ := hreg
  let M := max (N+1) B
  have hinj (n : ℕ) (hn : M ≤ n) := hB n ((le_max_right _ _).trans hn)
  have hsurj (n : ℕ) (hn : M ≤ n) : Function.Surjective (pieceMultiplication I l hl n) := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp (hinj n hn)
    rw [hN n (by dsimp [M] at hn; omega), hN (1+n) (by dsimp [M] at hn; omega)]
  refine ⟨M, fun n hn => ⟨?_, chartPieceMap_surjective I l hl M hsurj n hn⟩⟩
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨f, hf, hfx⟩ := x.property
  change Ideal.Quotient.mk I f = (x : MvPolynomial Z K ⧸ I) at hfx
  have hfzero : chartMap I l f = 0 := by
    change (Ideal.Quotient.liftₐ I (chartMap I l) (chartMap_kills I l))
      (x : MvPolynomial Z K ⧸ I) = 0 at hx
    rwa [← hfx] at hx
  obtain ⟨r, hr⟩ := homogeneous_chart_kernel_power I l hI hl f n hf hfzero
  have hfI := homogeneous_mem_of_power_mem I l hl M hinj n hn f hf r hr
  apply Subtype.ext
  exact hfx.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hfI)

theorem chartAlgebra_finite
    (I : Ideal (MvPolynomial Z K)) (l : MvPolynomial Z K)
    (hI : ∀ d f, f ∈ I → homogeneousComponent d f ∈ I) (hl : l.IsHomogeneous 1)
    (D : ℕ) (hconst : ∃ N : ℕ, ∀ k > N, Module.finrank K (coordinatePiece Z K I k) = D)
    (hreg : FilterRegular I l hl) : Module.Finite K (ChartAlgebra I l) := by
  obtain ⟨N, hN⟩ := eventually_chartPieceMap_bijective I l hI hl D hconst hreg
  exact Module.Finite.of_surjective (chartPieceMap I l N) (hN N le_rfl).2

theorem chartAlgebra_finrank
    (I : Ideal (MvPolynomial Z K)) (l : MvPolynomial Z K)
    (hI : ∀ d f, f ∈ I → homogeneousComponent d f ∈ I) (hl : l.IsHomogeneous 1)
    (D : ℕ) (hconst : ∃ N : ℕ, ∀ k > N, Module.finrank K (coordinatePiece Z K I k) = D)
    (hreg : FilterRegular I l hl) : Module.finrank K (ChartAlgebra I l) = D := by
  obtain ⟨N, hN⟩ := eventually_chartPieceMap_bijective I l hI hl D hconst hreg
  obtain ⟨B, hB⟩ := hconst
  rw [← (LinearEquiv.ofBijective (chartPieceMap I l (max N (B+1)))
    (hN _ (le_max_left _ _))).finrank_eq]
  exact hB _ (by omega)

theorem chart_sum_local_lengths [IsAlgClosed K]
    (I : Ideal (MvPolynomial Z K)) (l : MvPolynomial Z K)
    (hI : ∀ d f, f ∈ I → homogeneousComponent d f ∈ I) (hl : l.IsHomogeneous 1)
    (D : ℕ) (hconst : ∃ N : ℕ, ∀ k > N, Module.finrank K (coordinatePiece Z K I k) = D)
    (hreg : FilterRegular I l hl) :
    (∑ᶠ p : MaximalSpectrum (ChartAlgebra I l),
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) =
        (D : ℕ∞) := by
  letI := chartAlgebra_finite I l hI hl D hconst hreg
  letI : IsArtinianRing (ChartAlgebra I l) := IsArtinianRing.of_finite K _
  letI := Fintype.ofFinite (MaximalSpectrum (ChartAlgebra I l))
  rw [finsum_eq_sum_of_fintype,
    ← ArtinianLocalDecomposition.finrank_eq_sum_local_length K,
    chartAlgebra_finrank I l hI hl D hconst hreg]

end Sheshadri.OrdinaryProjectiveHilbert
