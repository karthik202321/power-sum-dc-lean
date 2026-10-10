/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SaturatedRegularSequence

/-!
# Smoothness of the actual finite saturated chart

A homogeneous regular element remains a non-zero-divisor after setting a
linear homogeneous chart coordinate to one. In a finite chart algebra it
is therefore a unit. Applying associated-prime avoidance to the displayed
system proves that the final saturated chart has no common zero of that
system. No smoothness or reducedness certificate is supplied as an input.
-/
noncomputable section
namespace Sheshadri.SaturatedChartSmoothness
open MvPolynomial HomogeneousSystemSaturation GenericHomogeneousSections
open OrdinaryProjectiveHilbert
set_option maxHeartbeats 500000

variable {Z E K : Type*} [Fintype Z] [Field K]

/-- Every polynomial on a linear chart has a homogeneous representative,
obtained by padding its pieces with powers of the chart coordinate. -/
theorem exists_homogeneous_representative
    (I : Ideal (MvPolynomial Z K)) (l : MvPolynomial Z K) (hl : l.IsHomogeneous 1)
    (f : MvPolynomial Z K) :
    ∃ q : MvPolynomial Z K, q.IsHomogeneous f.totalDegree ∧
      chartMap I l q = chartMap I l f := by
  classical
  let q := ∑ d ∈ Finset.range (f.totalDegree+1),
    l ^ (f.totalDegree-d) * homogeneousComponent d f
  refine ⟨q,?_,?_⟩
  · apply IsHomogeneous.sum
    intro d hd
    have hdf : d ≤ f.totalDegree := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hd)
    simpa only [Nat.one_mul, Nat.sub_add_cancel hdf] using
      (hl.pow (f.totalDegree-d)).mul (homogeneousComponent_mem d f)
  · dsimp only [q]
    rw [map_sum]
    simp only [map_mul,map_pow,chartMap_linear,one_pow,one_mul]
    rw [← map_sum,sum_homogeneousComponent]

/-- Homogeneous regularity descends to any homogeneous linear chart.
This is proved on the actual quotient, retaining all nilpotents. -/
theorem chart_nonZeroDivisor_of_homogeneous_regular
    (I : Ideal (MvPolynomial Z K))
    (hI : ∀ d f, f ∈ I → homogeneousComponent d f ∈ I)
    (l : MvPolynomial Z K) (hl : l.IsHomogeneous 1)
    (g : MvPolynomial Z K) (e : ℕ) (hg : g.IsHomogeneous e)
    (hreg : IsRegular (Ideal.Quotient.mk I g)) :
    chartMap I l g ∈ nonZeroDivisors (ChartAlgebra I l) := by
  apply mem_nonZeroDivisors_iff.mpr
  intro y hy
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨q,hq,hqf⟩ := exists_homogeneous_representative I l hl f
  have hzero : chartMap I l (g*q) = 0 := by
    rw [map_mul,hqf,mul_comm]
    exact hy
  obtain ⟨r,hr⟩ := homogeneous_chart_kernel_power I l hI hl (g*q) (e+f.totalDegree)
    (hg.mul hq) hzero
  have hz : Ideal.Quotient.mk I g * Ideal.Quotient.mk I (l^r*q) = 0 := by
    rw [← map_mul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa [mul_assoc,mul_comm,mul_left_comm] using hr
  have hmem : l^r*q ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp
    (hreg.left.mul_left_eq_zero_iff.mp hz)
  have hh := chartMap_kills I l _ hmem
  simpa only [map_mul,map_pow,chartMap_linear,one_pow,one_mul,hqf] using hh

/-- In the literal finite section algebra, homogeneous regular elements
become units, whether or not the section is reduced. -/
theorem chart_isUnit_of_homogeneous_regular
    (I : Ideal (MvPolynomial Z K))
    (hI : ∀ d f, f ∈ I → homogeneousComponent d f ∈ I)
    (l : MvPolynomial Z K) (hl : l.IsHomogeneous 1)
    [Module.Finite K (ChartAlgebra I l)]
    (g : MvPolynomial Z K) (e : ℕ) (hg : g.IsHomogeneous e)
    (hreg : IsRegular (Ideal.Quotient.mk I g)) : IsUnit (chartMap I l g) := by
  letI : IsArtinianRing (ChartAlgebra I l) := IsArtinianRing.of_finite K _
  exact IsArtinianRing.isUnit_of_mem_nonZeroDivisors
    (chart_nonZeroDivisor_of_homogeneous_regular I hI l hl g e hg hreg)

variable [Fintype E] [Infinite K]

/-- The displayed saturated system contains an actual homogeneous scalar
combination which is a unit on the entire finite chart. -/
theorem exists_unit_system_combination
    (J : Ideal (MvPolynomial Z K))
    (hJ : ∀ d f, f ∈ J → homogeneousComponent d f ∈ J)
    (l : MvPolynomial Z K) (hl : l.IsHomogeneous 1)
    (fs : E → MvPolynomial Z K) (d : ℕ)
    (hfs : ∀ i, (fs i).IsHomogeneous d)
    [Module.Finite K (ChartAlgebra (saturation J (fun i => l*fs i)) l)] :
    ∃ g : MvPolynomial Z K, g ∈ Submodule.span K (Set.range fs) ∧
      g.IsHomogeneous d ∧
      IsUnit (chartMap (saturation J (fun i => l*fs i)) l g) := by
  classical
  let I := saturation J (fun i => l*fs i)
  let L := (Finset.univ.toList : List E).map fs
  have hL : ∀ f ∈ L, f.IsHomogeneous d := by
    intro f hf
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    exact hfs i
  have havoid : ∀ p ∈ associatedPrimes _ (HomogeneousQuotientExact.QuotientRing I),
      ¬ Ideal.ofList L ≤ p := by
    intro p hp hle
    obtain ⟨i,hi⟩ := associatedPrime_omits_system_factor J l fs p hp
    exact hi (hle (Ideal.subset_span (List.mem_map.mpr ⟨i,by simp,rfl⟩)))
  obtain ⟨g,hgspan,hg,hreg⟩ := exists_regular_homogeneous_combination_of_avoid I L d hL havoid
  refine ⟨g,?_,hg,?_⟩
  · apply (Submodule.span_mono ?_) hgspan
    intro f hf
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    exact Set.mem_range_self i
  · exact chart_isUnit_of_homogeneous_regular I
      (saturation_homogeneous J _ (fun _ => 1+d) (fun i => hl.mul (hfs i)) hJ)
      l hl g d hg hreg

/-- Explicit scalar coefficients for the unit combination, suitable for
one actual principal smooth open in a deformation. -/
theorem exists_unit_system_coefficients
    (J : Ideal (MvPolynomial Z K))
    (hJ : ∀ d f, f ∈ J → homogeneousComponent d f ∈ J)
    (l : MvPolynomial Z K) (hl : l.IsHomogeneous 1)
    (fs : E → MvPolynomial Z K) (d : ℕ)
    (hfs : ∀ i, (fs i).IsHomogeneous d)
    [Module.Finite K (ChartAlgebra (saturation J (fun i => l*fs i)) l)] :
    ∃ b : E → K, IsUnit (chartMap (saturation J (fun i => l*fs i)) l
      (∑ i, C (b i) * fs i)) := by
  obtain ⟨g,hspan,_,hunit⟩ := exists_unit_system_combination J hJ l hl fs d hfs
  obtain ⟨b,hb⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hspan
  refine ⟨b,?_⟩
  convert hunit using 1
  exact congrArg (chartMap (saturation J (fun i => l*fs i)) l)
    (by simpa only [Algebra.smul_def,MvPolynomial.algebraMap_eq] using hb)

/-- The same constructed smooth open works at points over every field
extension; no commutation of saturation and base change is assumed. -/
theorem chart_system_nonvanishing_eval₂ {L : Type*} [Field L]
    (J : Ideal (MvPolynomial Z K))
    (hJ : ∀ d f, f ∈ J → homogeneousComponent d f ∈ J)
    (l : MvPolynomial Z K) (hl : l.IsHomogeneous 1)
    (fs : E → MvPolynomial Z K) (d : ℕ)
    (hfs : ∀ i, (fs i).IsHomogeneous d)
    [Module.Finite K (ChartAlgebra (saturation J (fun i => l*fs i)) l)]
    (φ : K →+* L) (p : Z → L)
    (hp : chartIdeal (saturation J (fun i => l*fs i)) l ≤ RingHom.ker (eval₂Hom φ p)) :
    ∃ i, eval₂ φ p (fs i) ≠ 0 := by
  classical
  obtain ⟨b,hunit⟩ := exists_unit_system_coefficients J hJ l hl fs d hfs
  let χ : ChartAlgebra (saturation J (fun i => l*fs i)) l →+* L :=
    Ideal.Quotient.lift _ (eval₂Hom φ p) hp
  have hgne : eval₂ φ p (∑ i, C (b i) * fs i) ≠ 0 := (hunit.map χ).ne_zero
  by_contra hall
  push_neg at hall
  apply hgne
  change (eval₂Hom φ p) (∑ i, C (b i) * fs i) = 0
  simp only [map_sum,map_mul,eval₂Hom_C]
  apply Finset.sum_eq_zero
  intro i _
  change φ (b i) * eval₂ φ p (fs i) = 0
  rw [hall i,mul_zero]

/-- Every actual root of the finite saturated chart lies on one of the
specified smooth opens. Smoothness is a conclusion of saturation and
finiteness, rather than an additional assumption about the family. -/
theorem chart_system_nonvanishing
    (J : Ideal (MvPolynomial Z K))
    (hJ : ∀ d f, f ∈ J → homogeneousComponent d f ∈ J)
    (l : MvPolynomial Z K) (hl : l.IsHomogeneous 1)
    (fs : E → MvPolynomial Z K) (d : ℕ)
    (hfs : ∀ i, (fs i).IsHomogeneous d)
    [Module.Finite K (ChartAlgebra (saturation J (fun i => l*fs i)) l)]
    (p : Z → K)
    (hp : chartIdeal (saturation J (fun i => l*fs i)) l ≤ RingHom.ker (eval p)) :
    ∃ i, eval p (fs i) ≠ 0 := by
  classical
  obtain ⟨g,hspan,_,hunit⟩ := exists_unit_system_combination J hJ l hl fs d hfs
  let χ : ChartAlgebra (saturation J (fun i => l*fs i)) l →+* K :=
    Ideal.Quotient.lift _ (eval p) hp
  have hgne : eval p g ≠ 0 := (hunit.map χ).ne_zero
  by_contra hall
  push_neg at hall
  have hk : Submodule.span K (Set.range fs) ≤
      LinearMap.ker (aeval p : MvPolynomial Z K →ₐ[K] K).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro f ⟨i,rfl⟩
    simpa only [LinearMap.mem_ker,AlgHom.toLinearMap_apply,aeval_def,
      MvPolynomial.algebraMap_eq] using hall i
  have hz := hk hspan
  apply hgne
  simpa only [LinearMap.mem_ker,AlgHom.toLinearMap_apply,aeval_def,
    MvPolynomial.algebraMap_eq] using hz

end Sheshadri.SaturatedChartSmoothness
