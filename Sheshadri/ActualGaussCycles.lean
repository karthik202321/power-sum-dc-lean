/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ActualGaussFamily
import Sheshadri.AffineFundamentalCycle
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Actual affine cycles of the constructed Gauss family

The rings are the literal quotients constructed in `ActualGaussFamily`.
Their cycles use actual minimal prime ideals and actual generic local-ring
lengths. In particular special-fibre multiplicities are not replaced by one.
The total ring is reduced, and its generic multiplicities are proved to be one.

The module also places each target conormal representative in the spectrum
of the actual fibre ring, by constructing its evaluation homomorphism.
No projective gluing, purity, or intersection-degree assertion is made here.
-/

noncomputable section
namespace Sheshadri.ActualGaussCycles

open MvPolynomial ActualGaussFamily
open scoped Topology

variable {A Z : Type*} [Fintype A] [Fintype Z]

theorem coordinateRing_finiteType
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) :
    Algebra.FiniteType ℂ (CoordinateRing F U) := by
  letI : Algebra.FiniteType ℂ (MvPolynomial (TotalCoordinates A Z) ℂ) :=
    Algebra.FiniteType.mvPolynomial ℂ _
  infer_instance

theorem coordinateRing_noetherian
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) :
    IsNoetherianRing (CoordinateRing F U) := inferInstance

theorem fibreCoordinateRing_finiteType
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ) :
    Algebra.FiniteType ℂ (FibreCoordinateRing F U a) := by
  letI : Algebra.FiniteType ℂ (MvPolynomial (Option Z ⊕ Option Z) ℂ) :=
    Algebra.FiniteType.mvPolynomial ℂ _
  infer_instance

theorem fibreCoordinateRing_noetherian
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ) :
    IsNoetherianRing (FibreCoordinateRing F U a) := inferInstance

/-- Every actual generic local length is used as the corresponding weight. -/
def totalCycle (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) :
    ConormalCycles.EffectiveCycle (AffineFundamentalCycle.Component (CoordinateRing F U)) :=
  AffineFundamentalCycle.cycle _

/-- The special fibre may be nonreduced, and this cycle retains its lengths. -/
def fibreCycle (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ) :
    ConormalCycles.EffectiveCycle
      (AffineFundamentalCycle.Component (FibreCoordinateRing F U a)) :=
  AffineFundamentalCycle.cycle _

theorem fibreCycle_coefficient_pos
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ)
    (p : AffineFundamentalCycle.Component (FibreCoordinateRing F U a)) :
    0 < fibreCycle F U a p :=
  AffineFundamentalCycle.multiplicity_pos _ p

theorem fibreCycle_support_eq_univ
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ) :
    ConormalCycles.supportSet
      (AffineFundamentalCycle.componentSet (FibreCoordinateRing F U a))
      (fibreCycle F U a) = Set.univ :=
  AffineFundamentalCycle.supportSet_eq_univ _

theorem totalCycle_coefficient_one
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ))
    (p : AffineFundamentalCycle.Component (CoordinateRing F U)) :
    totalCycle F U p = 1 :=
  AffineFundamentalCycle.cycle_apply_eq_one _ p

theorem totalCycle_support_eq_univ
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) :
    ConormalCycles.supportSet
      (AffineFundamentalCycle.componentSet (CoordinateRing F U))
      (totalCycle F U) = Set.univ :=
  AffineFundamentalCycle.supportSet_eq_univ _

/-- Evaluation at an actual representative in the fibre factors through
the literal specialized coordinate ring. -/
def fibreEvaluation
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ)
    (p : ConormalZariski.Ambient Z) (hp : p ∈ fibre F U a) :
    FibreCoordinateRing F U a →+* ℂ :=
  Ideal.Quotient.lift (fibreIdeal F U a) (eval p)
    ((mem_fibre_iff_vanishes_fibreIdeal F U a p).mp hp)

theorem fibreEvaluation_surjective
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ)
    (p : ConormalZariski.Ambient Z) (hp : p ∈ fibre F U a) :
    Function.Surjective (fibreEvaluation F U a p hp) := by
  intro c
  refine ⟨Ideal.Quotient.mk _ (C c), ?_⟩
  simp [fibreEvaluation]

/-- An actual closed point of the fibre scheme, obtained from evaluation. -/
def fibrePoint
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ)
    (p : ConormalZariski.Ambient Z) (hp : p ∈ fibre F U a) :
    PrimeSpectrum (FibreCoordinateRing F U a) :=
  ⟨RingHom.ker (fibreEvaluation F U a p hp), RingHom.ker_isPrime _⟩

theorem fibrePoint_isMaximal
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ)
    (p : ConormalZariski.Ambient Z) (hp : p ∈ fibre F U a) :
    (fibrePoint F U a p hp).asIdeal.IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (fibreEvaluation F U a p hp)
    (fibreEvaluation_surjective F U a p hp)

/-- Distinct complex coordinate points remain distinct scheme points. -/
theorem fibrePoint_injective
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ)) (a : A → ℂ) :
    Function.Injective (fun p : fibre F U a => fibrePoint F U a p.val p.property) := by
  intro p q hpq
  apply Subtype.ext
  funext i
  have hkernel := congrArg PrimeSpectrum.asIdeal hpq
  let f : FibreCoordinateRing F U a :=
    Ideal.Quotient.mk _ (X i - C (p.val i))
  have hpzero : f ∈ (fibrePoint F U a p.val p.property).asIdeal := by
    change fibreEvaluation F U a p.val p.property f = 0
    simp [f, fibreEvaluation]
  rw [hkernel] at hpzero
  change fibreEvaluation F U a q.val q.property f = 0 at hpzero
  have he : q.val i - p.val i = 0 := by simpa [f, fibreEvaluation] using hpzero
  exact (sub_eq_zero.mp he).symm

/-- Every target conormal representative produces a genuine scheme point
in the support of the constructed special-fibre fundamental cycle. -/
theorem targetPoint_mem_fibreCycle_support
    (F : MvPolynomial (A ⊕ Z) ℂ) (U : Set (A → ℂ))
    (a₀ : A → ℂ) (ha₀ : a₀ ∈ closure U)
    (p : ConormalZariski.Ambient Z) (hp : p ∈ ConormalZariski.conormalClosure F a₀) :
    fibrePoint F U a₀ p (conormalClosure_subset_fibre F U a₀ ha₀ hp) ∈
      ConormalCycles.supportSet
        (AffineFundamentalCycle.componentSet (FibreCoordinateRing F U a₀))
        (fibreCycle F U a₀) := by
  rw [fibreCycle_support_eq_univ]
  exact Set.mem_univ _

end Sheshadri.ActualGaussCycles
