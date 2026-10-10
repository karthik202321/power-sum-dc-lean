/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628

Legacy interface: its module discussion predates the completed endpoints in
ConormalBorderMultiplicity; see README.md for the current verification scope.
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalExact
import Sheshadri.ActualConormalSpecialization
import Sheshadri.ConormalFlatness
import Sheshadri.MultiplicityOne
import Sheshadri.FermatConormalIrreducible

/-!
# Original border route: explicit family obligations and final consequences

This file assembles the original argument from a geometric family certificate.
It DOES NOT construct this certificate from border membership. The certificate
records the still-unformalized scheme-to-cycle and degree identifications;
it is not a textbook theorem or a hidden assumption of the final count bound.

What the proof does derive is smooth Gauss containment, positive component
comparison, numerical conservation from independently supplied Euler data,
the determinant incidence bound, and both quadratic constants.

No original-route theorem in this release starts from bare border membership.
In particular there is no claim that the remaining scheme obligations have
been discharged merely because the conditional conclusions compile.
-/

noncomputable section
namespace Sheshadri.ConormalBorder

open MvPolynomial ConormalExact ConormalZariski ConormalTopology
open ConormalCycles ConormalSpecialization PolynomialModel Incidence MultiProjective
open scoped Topology

def polarIndex (n : ℕ) : Fin ((n - 1) + 1) := ⟨n - 2, by omega⟩

variable {A C : Type} [Fintype A] [TopologicalSpace C] {n m : ℕ}

/-- A transparent list of unresolved geometric construction obligations.
The smooth-point containment and specialization inequality are not fields:
they are proved below from the individual premises.

`cycles.dimension` must be interpreted as affine support dimension, while
`cycles.degree` and its Hilbert data refer to the projectivized cycles.
The bridge between those representations is part of the supplied geometry.
-/
structure FamilyCertificate (A C : Type) [Fintype A] [TopologicalSpace C]
    (n : ℕ) (geometry : GaussDegreeTheory n) where
  family : MvPolynomial (A ⊕ Fin n) ℂ
  parameter : C → A → ℂ
  base : C
  continuous_parameter : ContinuousAt parameter base
  target_polynomial : ConormalPersistence.specialize (parameter base) family = fermat n
  good : Set C
  base_in_closure : base ∈ closure good
  cycles : FamilyCycleData C (Fin n) (n - 1)
  special_support : supportSet cycles.componentSet (cycles.cycle base) =
    ActualGaussFamily.fibre family (parameter '' good) (parameter base)
  components_closed : ∀ i ∈ (cycles.cycle base).support,
    @IsClosed (Ambient (Fin n)) (algebraicTopology (Option (Fin n) ⊕ Option (Fin n)))
      (cycles.componentSet i)
  pure_dimension : ∀ i ∈ (cycles.cycle base).support,
    cycles.dimension (conormalClosure family (parameter base)) =
      cycles.dimension (cycles.componentSet i)
  dimension_drop : ∀ i ∈ (cycles.cycle base).support,
    conormalClosure family (parameter base) ⊂ cycles.componentSet i →
    cycles.dimension (conormalClosure family (parameter base)) <
      cycles.dimension (cycles.componentSet i)
  euler_characteristics_constant : ∀ c q t,
    cycles.hilbert.eulerCharacteristic c q t = cycles.hilbert.eulerCharacteristic base q t
  target_degree_identification :
    cycles.degree (polarIndex n) (conormalClosure family (parameter base)) =
      geometry.degree (ConormalPersistence.specialize (parameter base) family)
  generic_degree_identification : ∀ c ∈ good,
    cycles.totalDegree c (polarIndex n) =
      geometry.degree (ConormalPersistence.specialize (parameter c) family)

namespace FamilyCertificate

variable {geometry : GaussDegreeTheory n}

theorem good_nonempty (D : FamilyCertificate A C n geometry) : D.good.Nonempty := by
  by_contra h
  have he : D.good = ∅ := Set.not_nonempty_iff_eq_empty.mp h
  have hc := D.base_in_closure
  simp [he] at hc

/-- This proves the paper's specialization comparison from the certificate's
individual geometric obligations; the comparison itself was not assumed. -/
theorem degree_specializes (D : FamilyCertificate A C n geometry) (hn : 3 ≤ n)
    (c : C) (hc : c ∈ D.good) :
    geometry.degree (fermat n) ≤
      geometry.degree (ConormalPersistence.specialize (D.parameter c) D.family) := by
  have h := ActualConormalSpecialization.target_degree_le_generic
    D.family D.parameter D.base D.continuous_parameter
    D.good D.base_in_closure D.cycles D.special_support
    (FermatConormalIrreducible.fermat_conormalClosure_isIrreducible
      hn D.family (D.parameter D.base) D.target_polynomial)
    D.components_closed D.pure_dimension D.dimension_drop
    D.euler_characteristics_constant c (polarIndex n)
  rw [D.target_degree_identification, D.generic_degree_identification c hc,
    D.target_polynomial] at h
  exact h

end FamilyCertificate

/-- Ordinary border count, conditional on a supplied family certificate
and fibrewise matrix representations. No coherent matrix family is required. -/
theorem ordinary_count_from_family
    (geometry : GaussDegreeTheory n) (hn : 3 ≤ n) (hm : 0 < m)
    (D : FamilyCertificate A C n geometry)
    (hrepresentations : ∀ c ∈ D.good, ∃ M : PencilCoefficients n m ℂ,
      determinant M = ConormalPersistence.specialize (D.parameter c) D.family) :
    fermatCount n ≤ ordinaryBezout m n := by
  obtain ⟨c, hc⟩ := D.good_nonempty
  obtain ⟨M, hM⟩ := hrepresentations c hc
  rw [← fermat_degree geometry hn]
  exact (D.degree_specializes hn c hc).trans
    (ordinary_degree_bound geometry (by omega) hm M _ hM)

/-- Symmetric analogue through the same conormal specialization argument. -/
theorem symmetric_count_from_family
    (geometry : GaussDegreeTheory n) (hn : 3 ≤ n) (hm : 0 < m)
    (D : FamilyCertificate A C n geometry)
    (hrepresentations : ∀ c ∈ D.good, ∃ M : PencilCoefficients n m ℂ,
      (∀ i, (M i).transpose = M i) ∧
      determinant M = ConormalPersistence.specialize (D.parameter c) D.family) :
    fermatCount n ≤ symmetricBezout m n := by
  obtain ⟨c, hc⟩ := D.good_nonempty
  obtain ⟨M, hsym, hM⟩ := hrepresentations c hc
  rw [← fermat_degree geometry hn]
  exact (D.degree_specializes hn c hc).trans
    (symmetric_degree_bound geometry (by omega) hm M hsym _ hM)

theorem ordinary_quadratic_from_family
    (geometry : GaussDegreeTheory n) (hn : 3 ≤ n) (hm : 0 < m)
    (D : FamilyCertificate A C n geometry)
    (hrepresentations : ∀ c ∈ D.good, ∃ M : PencilCoefficients n m ℂ,
      determinant M = ConormalPersistence.specialize (D.parameter c) D.family) :
    ((n : ℝ) - 1) ^ 2 / (4 * Real.exp 1) ≤ (m : ℝ) :=
  ordinary_quadratic_bound n m hn
    (ordinary_count_from_family geometry hn hm D hrepresentations)

theorem symmetric_quadratic_from_family
    (geometry : GaussDegreeTheory n) (hn : 3 ≤ n) (hm : 0 < m)
    (D : FamilyCertificate A C n geometry)
    (hrepresentations : ∀ c ∈ D.good, ∃ M : PencilCoefficients n m ℂ,
      (∀ i, (M i).transpose = M i) ∧
      determinant M = ConormalPersistence.specialize (D.parameter c) D.family) :
    ((n : ℝ) - 1) ^ 2 / (2 * Real.exp 1) ≤ (m : ℝ) :=
  symmetric_quadratic_bound n m hn
    (symmetric_count_from_family geometry hn hm D hrepresentations)

end Sheshadri.ConormalBorder
