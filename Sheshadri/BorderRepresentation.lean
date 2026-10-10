/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.PolynomialModel
import Sheshadri.DegreeBound
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.ClusterPt

/-!
# Literal border representations in a finite coefficient space

A fixed finite set of exponent vectors supplies a finite-dimensional complex
coefficient space with its usual topology. Its representable locus consists
of coefficients whose polynomial is literally an affine determinant of the
stated size. Border membership is ordinary topological closure of that locus.

No family-selection, conormal specialization, or semicontinuity assertion is
postulated. The closure transfer below is proved directly from neighborhoods.
The passage from a Zariski-closure definition to this Euclidean-closure
definition is not asserted by this module.
-/

noncomputable section
namespace Sheshadri.BorderRepresentation

open MvPolynomial PolynomialModel
open scoped BigOperators Topology

abbrev Exponent (n : ℕ) := Fin n →₀ ℕ
abbrev Coefficients {n : ℕ} (S : Finset (Exponent n)) := S → ℂ

def polynomialOfCoefficients {n : ℕ} (S : Finset (Exponent n))
    (c : Coefficients S) : MvPolynomial (Fin n) ℂ :=
  ∑ s : S, C (c s) * monomial s.val 1

@[simp] theorem polynomialOfCoefficients_zero {n : ℕ} (S : Finset (Exponent n)) :
    polynomialOfCoefficients S 0 = 0 := by
  simp [polynomialOfCoefficients]

theorem polynomialOfCoefficients_add {n : ℕ} (S : Finset (Exponent n))
    (c d : Coefficients S) :
    polynomialOfCoefficients S (c + d) =
      polynomialOfCoefficients S c + polynomialOfCoefficients S d := by
  simp [polynomialOfCoefficients, map_add, add_mul, Finset.sum_add_distrib]

theorem polynomialOfCoefficients_sub {n : ℕ} (S : Finset (Exponent n))
    (c d : Coefficients S) :
    polynomialOfCoefficients S (c - d) =
      polynomialOfCoefficients S c - polynomialOfCoefficients S d := by
  simp [polynomialOfCoefficients, map_sub, sub_mul, Finset.sum_sub_distrib]

/-- The actual coefficients of a polynomial on the chosen support. -/
def canonicalCoefficients {n : ℕ} (S : Finset (Exponent n))
    (f : MvPolynomial (Fin n) ℂ) : Coefficients S := fun s => coeff s.val f

theorem coeff_polynomialOfCoefficients {n : ℕ} (S : Finset (Exponent n))
    (c : Coefficients S) (d : Exponent n) :
    coeff d (polynomialOfCoefficients S c) =
      if h : d ∈ S then c ⟨d, h⟩ else 0 := by
  classical
  simp only [polynomialOfCoefficients, coeff_sum, C_mul_monomial, mul_one, coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨d, h⟩ : S)]
    · simp
    · intro j _ hj
      have hdj : d ≠ j.val := by
        intro he
        apply hj
        exact Subtype.ext he.symm
      simp [hdj, Ne.symm hdj]
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    have hdj : d ≠ j.val := by
      intro he
      apply h
      simpa only [he] using j.property
    simp [hdj, Ne.symm hdj]

@[simp] theorem canonicalCoefficients_polynomialOfCoefficients {n : ℕ}
    (S : Finset (Exponent n)) (c : Coefficients S) :
    canonicalCoefficients S (polynomialOfCoefficients S c) = c := by
  funext s
  simp [canonicalCoefficients, coeff_polynomialOfCoefficients, s.property]

theorem polynomialOfCoefficients_injective {n : ℕ} (S : Finset (Exponent n)) :
    Function.Injective (polynomialOfCoefficients S) := by
  intro c d h
  have hh := congrArg (canonicalCoefficients S) h
  simpa using hh

/-- Exact reconstruction when the finite support contains the polynomial's support. -/
theorem polynomialOfCoefficients_canonical {n : ℕ} (S : Finset (Exponent n))
    (f : MvPolynomial (Fin n) ℂ) (hf : f.support ⊆ S) :
    polynomialOfCoefficients S (canonicalCoefficients S f) = f := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_polynomialOfCoefficients]
  split_ifs with hd
  · rfl
  · apply Eq.symm
    exact not_mem_support_iff.mp (fun h => hd (hf h))

/-- The exact ordinary determinant locus, inside this literal coefficient space. -/
def ordinaryLocus (n m : ℕ) (S : Finset (Exponent n)) : Set (Coefficients S) :=
  {c | ∃ A : Incidence.PencilCoefficients n m ℂ,
    determinant A = polynomialOfCoefficients S c}

/-- The exact symmetric determinant locus in the same coefficient space. -/
def symmetricLocus (n m : ℕ) (S : Finset (Exponent n)) : Set (Coefficients S) :=
  {c | ∃ A : Incidence.PencilCoefficients n m ℂ,
    (∀ i, (A i).transpose = A i) ∧ determinant A = polynomialOfCoefficients S c}

/-- Ordinary border membership with the Fermat target and support explicit. -/
def OrdinaryBorder (n m : ℕ) (S : Finset (Exponent n)) : Prop :=
  ∃ c₀ : Coefficients S,
    polynomialOfCoefficients S c₀ = PolynomialModel.fermat n ∧
    c₀ ∈ closure (ordinaryLocus n m S)

/-- Symmetric border membership with the Fermat target and support explicit. -/
def SymmetricBorder (n m : ℕ) (S : Finset (Exponent n)) : Prop :=
  ∃ c₀ : Coefficients S,
    polynomialOfCoefficients S c₀ = PolynomialModel.fermat n ∧
    c₀ ∈ closure (symmetricLocus n m S)

theorem ordinaryBorder_iff_canonical {n m : ℕ} (S : Finset (Exponent n))
    (hS : (PolynomialModel.fermat n : MvPolynomial (Fin n) ℂ).support ⊆ S) :
    OrdinaryBorder n m S ↔
      canonicalCoefficients S (PolynomialModel.fermat n) ∈ closure (ordinaryLocus n m S) := by
  constructor
  · rintro ⟨c₀, h₀, hcl⟩
    have hc := congrArg (canonicalCoefficients S) h₀
    simp only [canonicalCoefficients_polynomialOfCoefficients] at hc
    rwa [← hc]
  · intro hcl
    exact ⟨_, polynomialOfCoefficients_canonical S _ hS, hcl⟩

theorem symmetricBorder_iff_canonical {n m : ℕ} (S : Finset (Exponent n))
    (hS : (PolynomialModel.fermat n : MvPolynomial (Fin n) ℂ).support ⊆ S) :
    SymmetricBorder n m S ↔
      canonicalCoefficients S (PolynomialModel.fermat n) ∈ closure (symmetricLocus n m S) := by
  constructor
  · rintro ⟨c₀, h₀, hcl⟩
    have hc := congrArg (canonicalCoefficients S) h₀
    simp only [canonicalCoefficients_polynomialOfCoefficients] at hc
    rwa [← hc]
  · intro hcl
    exact ⟨_, polynomialOfCoefficients_canonical S _ hS, hcl⟩

/-- Existential finite-support version, allowing any common coefficient space. -/
def OrdinaryFiniteSupportBorder (n m : ℕ) : Prop :=
  ∃ S : Finset (Exponent n), OrdinaryBorder n m S

def SymmetricFiniteSupportBorder (n m : ℕ) : Prop :=
  ∃ S : Finset (Exponent n), SymmetricBorder n m S

/-- A canonical finite coefficient space containing the target and every
size-m determinant. Its support does not restrict the representation locus. -/
def coefficientSupport (n m : ℕ) : Finset (Exponent n) :=
  DegreeBound.exponentBox (Fin n) (max n m)

theorem fermat_support_subset (n m : ℕ) :
    (PolynomialModel.fermat n : MvPolynomial (Fin n) ℂ).support ⊆ coefficientSupport n m :=
  (DegreeBound.common_coefficient_support n m).1

theorem determinant_support_subset {n m : ℕ}
    (A : Incidence.PencilCoefficients n m ℂ) :
    (determinant A).support ⊆ coefficientSupport n m :=
  (DegreeBound.common_coefficient_support n m).2 A

/-- In the canonical space the exact locus is the coefficient image of
*all* size-m pencils, with no unproved degree or support restriction. -/
theorem ordinaryLocus_eq_range (n m : ℕ) :
    ordinaryLocus n m (coefficientSupport n m) =
      Set.range (fun A : Incidence.PencilCoefficients n m ℂ =>
        canonicalCoefficients (coefficientSupport n m) (determinant A)) := by
  ext c
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨A, ?_⟩
    change canonicalCoefficients (coefficientSupport n m) (determinant A) = c
    rw [hA, canonicalCoefficients_polynomialOfCoefficients]
  · rintro ⟨A, rfl⟩
    refine ⟨A, ?_⟩
    exact (polynomialOfCoefficients_canonical _ _ (determinant_support_subset A)).symm

/-- The analogous image description for all symmetric pencils. -/
theorem symmetricLocus_eq_range (n m : ℕ) :
    symmetricLocus n m (coefficientSupport n m) =
      Set.range (fun A : {A : Incidence.PencilCoefficients n m ℂ //
        ∀ i, (A i).transpose = A i} =>
        canonicalCoefficients (coefficientSupport n m) (determinant A.val)) := by
  ext c
  constructor
  · rintro ⟨A, hsym, hA⟩
    refine ⟨⟨A, hsym⟩, ?_⟩
    change canonicalCoefficients (coefficientSupport n m) (determinant A) = c
    rw [hA, canonicalCoefficients_polynomialOfCoefficients]
  · rintro ⟨A, rfl⟩
    exact ⟨A.val, A.property,
      (polynomialOfCoefficients_canonical _ _ (determinant_support_subset A.val)).symm⟩

/-- Ordinary Euclidean border membership in the canonical full coefficient space. -/
def OrdinaryBorderAtSize (n m : ℕ) : Prop :=
  OrdinaryBorder n m (coefficientSupport n m)

/-- Symmetric Euclidean border membership in the canonical full coefficient space. -/
def SymmetricBorderAtSize (n m : ℕ) : Prop :=
  SymmetricBorder n m (coefficientSupport n m)

theorem ordinaryBorderAtSize_iff (n m : ℕ) :
    OrdinaryBorderAtSize n m ↔
      canonicalCoefficients (coefficientSupport n m) (PolynomialModel.fermat n) ∈
        closure (Set.range (fun A : Incidence.PencilCoefficients n m ℂ =>
          canonicalCoefficients (coefficientSupport n m) (determinant A))) := by
  rw [OrdinaryBorderAtSize, ordinaryBorder_iff_canonical _ (fermat_support_subset n m),
    ordinaryLocus_eq_range]

theorem symmetricBorderAtSize_iff (n m : ℕ) :
    SymmetricBorderAtSize n m ↔
      canonicalCoefficients (coefficientSupport n m) (PolynomialModel.fermat n) ∈
        closure (Set.range (fun A : {A : Incidence.PencilCoefficients n m ℂ //
          ∀ i, (A i).transpose = A i} =>
          canonicalCoefficients (coefficientSupport n m) (determinant A.val))) := by
  rw [SymmetricBorderAtSize, symmetricBorder_iff_canonical _ (fermat_support_subset n m),
    symmetricLocus_eq_range]

/-- Elementary closure transfer, independent of determinant geometry. -/
theorem closure_transfer {X : Type*} [TopologicalSpace X] {s : Set X} {x : X}
    {P : Prop} (hx : x ∈ closure s)
    (h : ∀ᶠ y in 𝓝 x, y ∈ s → P) : P := by
  obtain ⟨y, hys, hy⟩ := ((mem_closure_iff_frequently.mp hx).and_eventually h).exists
  exact hy hys

/-- A closed-limit coefficient point can be approximated inside any prescribed
neighborhood of the zero perturbation, with actual representable coefficients. -/
theorem closure_meets_perturbation {n : ℕ} (S : Finset (Exponent n))
    {s : Set (Coefficients S)} {c₀ : Coefficients S}
    (hcl : c₀ ∈ closure s) {Q : Coefficients S → Prop}
    (hQ : ∀ᶠ d in 𝓝 (0 : Coefficients S), Q d) :
    ∃ c : Coefficients S, c ∈ s ∧ Q (c - c₀) := by
  have ht : Filter.Tendsto (fun c : Coefficients S => c - c₀) (𝓝 c₀) (𝓝 0) := by
    simpa using ((continuous_id.sub (continuous_const :
      Continuous (fun _ : Coefficients S => c₀))).tendsto c₀)
  obtain ⟨c, hcs, hqc⟩ := ((mem_closure_iff_frequently.mp hcl).and_eventually
    (ht.eventually hQ)).exists
  exact ⟨c, hcs, hqc⟩

/-- Translating coefficients gives precisely the polynomial perturbation
family used by the implicit-function argument. -/
theorem polynomialOfCoefficients_shift {n : ℕ} (S : Finset (Exponent n))
    (c₀ c : Coefficients S)
    (h₀ : polynomialOfCoefficients S c₀ = PolynomialModel.fermat n) :
    polynomialOfCoefficients S c = PolynomialModel.fermat n +
      ∑ s : S, C ((c - c₀) s) * monomial s.val 1 := by
  change polynomialOfCoefficients S c =
    PolynomialModel.fermat n + polynomialOfCoefficients S (c - c₀)
  rw [polynomialOfCoefficients_sub, h₀]
  abel

/-- A property forced by all exact determinants in a neighborhood of the
Fermat perturbation is forced by actual ordinary border membership. -/
theorem ordinary_border_transfer {n m : ℕ} (S : Finset (Exponent n))
    {P : Prop} (hborder : OrdinaryBorder n m S)
    (hlocal : ∀ᶠ d in 𝓝 (0 : Coefficients S),
      (∃ A : Incidence.PencilCoefficients n m ℂ,
        determinant A = PolynomialModel.fermat n + polynomialOfCoefficients S d) → P) : P := by
  obtain ⟨c₀, h₀, hcl⟩ := hborder
  obtain ⟨c, ⟨A, hA⟩, hnear⟩ := closure_meets_perturbation S hcl hlocal
  apply hnear
  refine ⟨A, ?_⟩
  rw [hA]
  exact polynomialOfCoefficients_shift S c₀ c h₀

/-- Symmetric version of the same proved neighborhood transfer. -/
theorem symmetric_border_transfer {n m : ℕ} (S : Finset (Exponent n))
    {P : Prop} (hborder : SymmetricBorder n m S)
    (hlocal : ∀ᶠ d in 𝓝 (0 : Coefficients S),
      (∃ A : Incidence.PencilCoefficients n m ℂ,
        (∀ i, (A i).transpose = A i) ∧
        determinant A = PolynomialModel.fermat n + polynomialOfCoefficients S d) → P) : P := by
  obtain ⟨c₀, h₀, hcl⟩ := hborder
  obtain ⟨c, ⟨A, hsym, hA⟩, hnear⟩ := closure_meets_perturbation S hcl hlocal
  apply hnear
  refine ⟨A, hsym, ?_⟩
  rw [hA]
  exact polynomialOfCoefficients_shift S c₀ c h₀

end Sheshadri.BorderRepresentation
