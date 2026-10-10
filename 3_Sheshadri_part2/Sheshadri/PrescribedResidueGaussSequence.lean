/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.RegularFlagsWithResidue
import Sheshadri.SaturatedRegularSequence
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Gauss flags constructed over the base with their prescribed special values

Each generic flag is selected on the actual preceding saturated quotient.
Its coefficients lie in the base ring and have exactly the requested
residues. The final primal flag is normalized in the base ring itself.
-/

noncomputable section
namespace Sheshadri.PrescribedResidueGaussSequence
open MvPolynomial RegularFlagsWithResidue HomogeneousSystemSaturation
open HomogeneousQuotientExact

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 150000

section Sequence
variable {σ E C R K : Type*} [Fintype σ] [Fintype E] [Field C] [Infinite C]
    [CommRing R] [Algebra C R] [Field K] [Algebra C K]

/-- The system itself supplies the avoidance condition on every saturated
ideal; no generic-position hypothesis for the chosen coefficients remains. -/
theorem exists_regular_coefficients_on_saturation (φ : R →ₐ[C] K) (ε : R →ₐ[C] C)
    (π : R) (hπ : φ π ≠ 0) (hεπ : ε π = 0)
    (fs : E → MvPolynomial σ R) (b₀ : E → R)
    (u : MvPolynomial σ K) (I : Ideal (MvPolynomial σ K)) :
    ∃ b : E → R, (∀ i, ε (b i) = ε (b₀ i)) ∧
      IsRegular (Ideal.Quotient.mk
        (saturation I (fun i => u * MvPolynomial.map φ.toRingHom (fs i)))
        (MvPolynomial.map φ.toRingHom (linearCombination fs b))) := by
  apply exists_regular_coefficients φ ε π hπ hεπ fs b₀
  intro p hp hle
  obtain ⟨i, hi⟩ := associatedPrime_omits_system_factor I u
    (fun i => MvPolynomial.map φ.toRingHom (fs i)) p hp
  exact hi (hle (Ideal.subset_span (Set.mem_range_self i)))

/-- All derivative flags are constructed simultaneously with their exact
residues, and are regular on their actual recursively constructed ideals. -/
theorem exists_regular_sequence (φ : R →ₐ[C] K) (ε : R →ₐ[C] C)
    (π : R) (hπ : φ π ≠ 0) (hεπ : ε π = 0)
    (fs : E → MvPolynomial σ R) (b₀ : ℕ → E → R)
    (u : MvPolynomial σ K) (I : Ideal (MvPolynomial σ K)) :
    ∃ b : ℕ → E → R, (∀ j i, ε (b j i) = ε (b₀ j i)) ∧
      ∀ j, IsRegular (Ideal.Quotient.mk
        (SaturatedRegularSequence.sequence I
          (fun i => u * MvPolynomial.map φ.toRingHom (fs i))
          (fun j => MvPolynomial.map φ.toRingHom (linearCombination fs (b j))) j)
        (MvPolynomial.map φ.toRingHom (linearCombination fs (b j)))) := by
  classical
  let h := fun i => u * MvPolynomial.map φ.toRingHom (fs i)
  have hex (J : Ideal (MvPolynomial σ K)) (j : ℕ) :=
    exists_regular_coefficients_on_saturation φ ε π hπ hεπ fs (b₀ j) u J
  choose coeff hres hreg using hex
  let states : ℕ → Ideal (MvPolynomial σ K) := fun j =>
    Nat.rec I (fun j J => saturation J h ⊔ Ideal.span {
      MvPolynomial.map φ.toRingHom (linearCombination fs (coeff J j))}) j
  let b : ℕ → E → R := fun j => coeff (states j) j
  refine ⟨b, fun j i => hres (states j) j i, ?_⟩
  have hstates (j : ℕ) : saturation (states j) h =
      SaturatedRegularSequence.sequence I h
        (fun j => MvPolynomial.map φ.toRingHom (linearCombination fs (b j))) j := by
    induction j with
    | zero => rfl
    | succ j ih =>
      change saturation (saturation (states j) h ⊔ Ideal.span {
        MvPolynomial.map φ.toRingHom (linearCombination fs (b j))}) h = _
      rw [ih]
      rfl
  intro j
  rw [← hstates j]
  exact hreg (states j) j

end Sequence

section Primal
variable {n : ℕ} {E C R K : Type*} [Field C] [Infinite C]
    [CommRing R] [IsLocalRing R] [Algebra C R] [Field K] [Algebra C K]

def primalPolynomial (a : Fin n → R) : MvPolynomial (Fin (n+1)) R :=
  linearCombination X (Fin.cons (-1) a)

theorem primalPolynomial_eq (a : Fin n → R) :
    primalPolynomial a = (∑ i : Fin n, MvPolynomial.C (a i) * X i.succ) - X 0 := by
  simp only [primalPolynomial, linearCombination, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, map_neg, map_one, neg_one_mul]
  ring

/-- The final primal flag has constant coefficient exactly `-1` over the
base ring. Normalization divides only by a proved unit whose residue is
`-1`, so every requested special coefficient is retained. -/
theorem exists_normalized_primal (φ : R →ₐ[C] K) (ε : R →ₐ[C] C)
    [IsLocalHom ε.toRingHom] (π : R) (hπ : φ π ≠ 0) (hεπ : ε π = 0)
    (fs : E → MvPolynomial (Fin (n+1)) K) (a₀ : Fin n → R)
    (I : Ideal (MvPolynomial (Fin (n+1)) K)) :
    ∃ a : Fin n → R, (∀ i, ε (a i) = ε (a₀ i)) ∧
      IsRegular (Ideal.Quotient.mk (saturation I (fun i => X 0 * fs i))
        (MvPolynomial.map φ.toRingHom (primalPolynomial a))) := by
  classical
  let J := saturation I (fun i => X 0 * fs i)
  obtain ⟨b, hres, hreg⟩ := exists_regular_coefficients φ ε π hπ hεπ
    (X : Fin (n+1) → MvPolynomial (Fin (n+1)) R) (Fin.cons (-1) a₀) J (by
      intro p hp hle
      have hnot := associatedPrime_omits_common_factor I (X 0) fs p hp
      apply hnot
      exact hle (Ideal.subset_span ⟨0, by simp⟩))
  have hb0 : ε (b 0) = -1 := by simpa using hres 0
  have hu : IsUnit (b 0) := isUnit_of_map_unit ε.toRingHom (b 0) (by
    change IsUnit (ε (b 0))
    rw [hb0]
    exact isUnit_neg_one)
  let u : Rˣ := hu.unit
  have huval : (u : R) = b 0 := hu.unit_spec
  have hinv : ε (↑(u⁻¹) : R) = -1 := by
    have hh := congrArg ε u.inv_mul
    rw [map_mul, huval, hb0, map_one, mul_neg, mul_one] at hh
    exact neg_eq_iff_eq_neg.mp hh
  let c : R := -(↑(u⁻¹) : R)
  have hc : ε c = 1 := by simp only [c, map_neg, hinv, neg_neg]
  have hcb : c * b 0 = -1 := by
    change -(↑(u⁻¹) : R) * b 0 = -1
    rw [← huval, neg_mul, u.inv_mul]
  let a : Fin n → R := fun i => c * b i.succ
  refine ⟨a, ?_, ?_⟩
  · intro i
    simpa only [a, map_mul, hc, one_mul, Fin.cons_succ] using hres i.succ
  · have hpoly : primalPolynomial a =
        MvPolynomial.C c * linearCombination (X : Fin (n+1) → MvPolynomial (Fin (n+1)) R) b := by
      simp only [primalPolynomial, linearCombination, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ, a, map_mul, Finset.mul_sum, mul_add]
      rw [← mul_assoc, ← map_mul, hcb]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => mul_assoc _ _ _)
    rw [hpoly, map_mul, map_mul]
    have hunit : IsUnit c := (u⁻¹).isUnit.neg
    exact ((hunit.map MvPolynomial.C).map (MvPolynomial.map φ.toRingHom)
      |>.map (Ideal.Quotient.mk J)).isRegular.mul hreg

end Primal
end Sheshadri.PrescribedResidueGaussSequence
