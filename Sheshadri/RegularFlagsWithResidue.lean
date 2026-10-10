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

/-!
# Regular flags with prescribed residue coefficients

Bad parameters are a finite union of root sets over the constant field.
Perturbing the desired coefficients by a scalar killed in the residue field
therefore preserves the special flag while making its generic image regular.
The generic quotient and the flag polynomial are literal algebraic objects.
-/

noncomputable section
namespace Sheshadri.RegularFlagsWithResidue
open MvPolynomial GenericHomogeneousSections

set_option maxHeartbeats 800000

section Combinations
variable {σ C R : Type*} [CommRing C] [CommRing R] [Algebra C R]

def combination (fs : List (MvPolynomial σ R)) (a : C) : MvPolynomial σ R :=
  Polynomial.eval (MvPolynomial.C (algebraMap C R a)) (RegularPrimeAvoidance.listPolynomial fs)

@[simp] theorem combination_nil (a : C) : combination ([] : List (MvPolynomial σ R)) a = 0 := by
  simp [combination, RegularPrimeAvoidance.listPolynomial]

@[simp] theorem combination_cons (f : MvPolynomial σ R) (fs : List (MvPolynomial σ R)) (a : C) :
    combination (f :: fs) a = f + MvPolynomial.C (algebraMap C R a) * combination fs a := by
  simp [combination, RegularPrimeAvoidance.listPolynomial]

theorem combination_map {S : Type*} [CommRing S] [Algebra C S]
    (φ : R →ₐ[C] S) (fs : List (MvPolynomial σ R)) (a : C) :
    MvPolynomial.map φ.toRingHom (combination fs a) =
      combination (fs.map (MvPolynomial.map φ.toRingHom)) a := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    have hφ : φ.toRingHom (algebraMap C R a) = algebraMap C S a := φ.commutes a
    simp only [combination_cons, List.map_cons, map_add, map_mul, map_C, hφ, ih]

theorem combination_smul (fs : List (MvPolynomial σ R)) (r : R) (a : C) :
    combination (fs.map (fun f => MvPolynomial.C r * f)) a =
      MvPolynomial.C r * combination fs a := by
  induction fs with
  | nil => simp
  | cons f fs ih => simp only [List.map_cons, combination_cons, ih]; ring

def perturbation (π : R) (g : MvPolynomial σ R) (fs : List (MvPolynomial σ R))
    (a : C) : MvPolynomial σ R :=
  combination (g :: fs.map (fun f => MvPolynomial.C π * f)) a

theorem perturbation_eq (π : R) (g : MvPolynomial σ R) (fs : List (MvPolynomial σ R))
    (a : C) :
    perturbation π g fs a =
      g + MvPolynomial.C (algebraMap C R a) * MvPolynomial.C π * combination fs a := by
  simp only [perturbation, combination_cons, combination_smul, mul_assoc]

theorem perturbation_residue (ε : R →ₐ[C] C) (π : R) (hπ : ε π = 0)
    (g : MvPolynomial σ R) (fs : List (MvPolynomial σ R)) (a : C) :
    MvPolynomial.map ε.toRingHom (perturbation π g fs a) = MvPolynomial.map ε.toRingHom g := by
  rw [perturbation_eq]
  have hπ' : ε.toRingHom π = 0 := hπ
  simp only [map_add, map_mul, map_C, hπ', C_0, mul_zero, zero_mul, add_zero]

theorem perturbation_homogeneous (π : R) (g : MvPolynomial σ R)
    (fs : List (MvPolynomial σ R)) (a : C) (d : ℕ)
    (hg : g.IsHomogeneous d) (hfs : ∀ f ∈ fs, f.IsHomogeneous d) :
    (perturbation π g fs a).IsHomogeneous d := by
  have hcomb : (combination fs a).IsHomogeneous d := by
    induction fs with
    | nil => simp only [combination_nil]; exact isHomogeneous_zero _ _ _
    | cons f fs ih =>
      rw [combination_cons]
      apply (hfs f (by simp)).add
      simpa only [zero_add] using (isHomogeneous_C σ (algebraMap C R a)).mul
        (ih (fun q hq => hfs q (by simp [hq])))
  rw [perturbation_eq]
  apply hg.add
  simpa only [zero_add] using
    ((isHomogeneous_C σ (algebraMap C R a)).mul (isHomogeneous_C σ π)).mul hcomb

end Combinations

section Regular
variable {σ C R K : Type*} [Finite σ] [Field C] [Infinite C]
    [CommRing R] [Algebra C R] [Field K] [Algebra C K]

/-- One constant-field parameter produces a regular generic flag while
retaining its complete special polynomial. The only avoidance hypothesis
is about the displayed full linear system, not the chosen flag. -/
theorem exists_regular_perturbation (φ : R →ₐ[C] K) (π : R) (hπ : φ π ≠ 0)
    (g : MvPolynomial σ R) (fs : List (MvPolynomial σ R))
    (I : Ideal (MvPolynomial σ K))
    (havoid : ∀ p ∈ associatedPrimes _ (HomogeneousQuotientExact.QuotientRing I),
      ¬ Ideal.ofList (fs.map (MvPolynomial.map φ.toRingHom)) ≤ p) :
    ∃ a : C, IsRegular (Ideal.Quotient.mk I
      (MvPolynomial.map φ.toRingHom (perturbation π g fs a))) := by
  classical
  let gs := (MvPolynomial.map φ.toRingHom g) ::
    (fs.map (fun f => MvPolynomial.C (φ π) * MvPolynomial.map φ.toRingHom f))
  have hav : ∀ p ∈ associatedPrimes _ (HomogeneousQuotientExact.QuotientRing I),
      ¬ Ideal.ofList gs ≤ p := by
    intro p hp hle
    apply havoid p hp
    apply Ideal.span_le.mpr
    intro f hf
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hf
    have hmem : MvPolynomial.C (φ π) * MvPolynomial.map φ.toRingHom q ∈ p :=
      hle (Ideal.subset_span (by
        change _ ∈ gs
        exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q, hq, rfl⟩)))
    have hh := p.mul_mem_left (MvPolynomial.C ((φ π)⁻¹)) hmem
    simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hπ, map_one, one_mul] using hh
  let bad (p : Ideal (MvPolynomial σ K)) : Set C :=
    {a | combination gs a ∈ p}
  have hfinite : (⋃ p ∈ associatedPrimes _ (HomogeneousQuotientExact.QuotientRing I), bad p).Finite :=
    (RegularPrimeAvoidance.finite_associatedPrimes (R := MvPolynomial σ K)
      (M := HomogeneousQuotientExact.QuotientRing I)).biUnion fun p hp => by
        simpa only [bad, combination, MvPolynomial.algebraMap_eq,
          IsScalarTower.algebraMap_apply C K (MvPolynomial σ K)] using
          RegularPrimeAvoidance.finite_bad_scalars C p hp.isPrime gs (hav p hp)
  obtain ⟨a, ha⟩ := hfinite.exists_not_mem
  have hreg : IsSMulRegular (HomogeneousQuotientExact.QuotientRing I) (combination gs a) := by
    by_contra hh
    have hin : combination gs a ∈ ⋃ p ∈ associatedPrimes (MvPolynomial σ K)
        (HomogeneousQuotientExact.QuotientRing I),
        (p : Set (MvPolynomial σ K)) := by
      rw [biUnion_associatedPrimes_eq_compl_regular]
      exact hh
    obtain ⟨p, hp, hh⟩ := Set.mem_iUnion₂.mp hin
    exact ha (Set.mem_iUnion₂.mpr ⟨p, hp, hh⟩)
  refine ⟨a, ?_⟩
  have he : MvPolynomial.map φ.toRingHom (perturbation π g fs a) = combination gs a := by
    rw [perturbation, combination_map]
    congr 1
    simp only [List.map_cons, List.map_map, Function.comp_def, map_mul, map_C, gs]
    rfl
  rw [he]
  exact quotient_regular_of_smulRegular I _ hreg

end Regular

section Coefficients
variable {σ E C R K : Type*} [Finite σ] [Fintype E] [Field C] [Infinite C]
    [CommRing R] [Algebra C R] [Field K] [Algebra C K]

def linearCombination (fs : E → MvPolynomial σ R) (b : E → R) : MvPolynomial σ R :=
  ∑ i, MvPolynomial.C (b i) * fs i

theorem linearCombination_homogeneous (fs : E → MvPolynomial σ R) (b : E → R)
    (d : ℕ) (hfs : ∀ i, (fs i).IsHomogeneous d) :
    (linearCombination fs b).IsHomogeneous d := by
  apply IsHomogeneous.sum
  intro i hi
  simpa only [zero_add] using (isHomogeneous_C σ (b i)).mul (hfs i)

theorem combination_mem_span (fs : List (MvPolynomial σ R)) (a : C) :
    combination fs a ∈ Submodule.span R {f | f ∈ fs} := by
  induction fs with
  | nil => simp
  | cons f fs ih =>
    rw [combination_cons]
    apply Submodule.add_mem
    · exact Submodule.subset_span (by simp)
    · have hmem : combination fs a ∈ Submodule.span R {q | q ∈ f :: fs} :=
        (Submodule.span_mono (by intro q hq; simp_all)) ih
      simpa only [Algebra.smul_def, MvPolynomial.algebraMap_eq] using
        (Submodule.smul_mem (Submodule.span R {q | q ∈ f :: fs}) (algebraMap C R a) hmem)

/-- Coefficients themselves, rather than just the polynomial they define,
retain their prescribed residues. This permits direct reuse of the
previously constructed special Gauss flags. -/
theorem exists_regular_coefficients (φ : R →ₐ[C] K) (ε : R →ₐ[C] C)
    (π : R) (hπ : φ π ≠ 0) (hεπ : ε π = 0)
    (fs : E → MvPolynomial σ R) (b₀ : E → R)
    (I : Ideal (MvPolynomial σ K))
    (havoid : ∀ p ∈ associatedPrimes (MvPolynomial σ K) (MvPolynomial σ K ⧸ I),
      ¬ Ideal.span (Set.range (fun i => MvPolynomial.map φ.toRingHom (fs i))) ≤ p) :
    ∃ b : E → R, (∀ i, ε (b i) = ε (b₀ i)) ∧
      IsRegular (Ideal.Quotient.mk I (MvPolynomial.map φ.toRingHom (linearCombination fs b))) := by
  classical
  let l := (Finset.univ.toList : List E).map fs
  have hl : {f | f ∈ l} = Set.range fs := by ext q; simp [l]
  have hmap : Ideal.ofList (l.map (MvPolynomial.map φ.toRingHom)) =
      Ideal.span (Set.range (fun i => MvPolynomial.map φ.toRingHom (fs i))) := by
    unfold Ideal.ofList
    congr 1
    ext q
    simp [l]
  obtain ⟨a, ha⟩ := exists_regular_perturbation φ π hπ (linearCombination fs b₀) l I (by
    intro p hp
    rw [hmap]
    exact havoid p hp)
  have hspan := combination_mem_span l a
  rw [hl, Submodule.mem_span_range_iff_exists_fun] at hspan
  obtain ⟨c, hc⟩ := hspan
  let b : E → R := fun i => b₀ i + (algebraMap C R a * π) * c i
  refine ⟨b, ?_, ?_⟩
  · intro i
    simp only [b, map_add, map_mul, hεπ, mul_zero, zero_mul, add_zero]
  · have he : linearCombination fs b = perturbation π (linearCombination fs b₀) l a := by
      rw [perturbation_eq, ← hc]
      simp only [linearCombination, b, map_add, map_mul, add_mul, Finset.sum_add_distrib,
        Algebra.smul_def, MvPolynomial.algebraMap_eq, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he]
    exact ha

end Coefficients
end Sheshadri.RegularFlagsWithResidue
