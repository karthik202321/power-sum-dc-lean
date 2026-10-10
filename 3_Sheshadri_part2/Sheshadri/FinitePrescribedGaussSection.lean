/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.PrescribedResidueGaussSequence
import Sheshadri.SaturatedChartSmoothness

/-!
# Finite Gauss sections with prescribed special flags

The derivative flags and normalized primal flag are constructed in the base
ring, preserving all prescribed residues. Their actual generic section is
finite, and one actual derivative combination is a unit on its complete
scheme. No genericity, finite-section, or smoothness certificate is input.
-/
noncomputable section
namespace Sheshadri.FinitePrescribedGaussSection
open MvPolynomial RegularFlagsWithResidue PrescribedResidueGaussSequence
open HomogeneousSystemSaturation HomogeneousQuotientExact FlatGradedHilbert
open HomogeneousHilbertDegree SaturatedSectionHilbert SaturatedRegularSequence

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 150000

variable {n : ℕ} {E C R K : Type*} [Fintype E] [Field C] [Infinite C]
    [CommRing R] [IsLocalRing R] [Algebra C R] [Field K] [Algebra C K]

/-- The literal generic derivative combination. -/
def dualEquation (φ : R →ₐ[C] K) (fs : E → MvPolynomial (Fin (n+1)) R)
    (b : E → R) : MvPolynomial (Fin (n+1)) K :=
  MvPolynomial.map φ.toRingHom (linearCombination fs b)

/-- Original hypersurface and all cuts, before discarding boundary components. -/
def rawIdeal (φ : R →ₐ[C] K) (I : Ideal (MvPolynomial (Fin (n+1)) K))
    (fs : E → MvPolynomial (Fin (n+1)) R) (b : ℕ → E → R)
    (a : Fin n → R) (r : ℕ) : Ideal (MvPolynomial (Fin (n+1)) K) :=
  idealSequence I (fun j => dualEquation φ fs (b j)) r ⊔
    Ideal.span {MvPolynomial.map φ.toRingHom (primalPolynomial a)}

/-- The actual derivative-open finite section, retaining nilpotents. -/
def sectionIdeal (φ : R →ₐ[C] K) (I : Ideal (MvPolynomial (Fin (n+1)) K))
    (fs : E → MvPolynomial (Fin (n+1)) R) (b : ℕ → E → R)
    (a : Fin n → R) (r : ℕ) : Ideal (MvPolynomial (Fin (n+1)) K) :=
  saturation (rawIdeal φ I fs b a r)
    (fun i => X 0 * MvPolynomial.map φ.toRingHom (fs i))

/-- Homogeneity of every literal equation in the final unsaturated system. -/
theorem rawIdeal_homogeneous (φ : R →ₐ[C] K)
    (I : Ideal (MvPolynomial (Fin (n+1)) K))
    (hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I)
    (fs : E → MvPolynomial (Fin (n+1)) R) (d : ℕ)
    (hfs : ∀ i, (fs i).IsHomogeneous d)
    (b : ℕ → E → R) (a : Fin n → R) (r : ℕ) :
    ∀ k p, p ∈ rawIdeal φ I fs b a r → homogeneousComponent k p ∈ rawIdeal φ I fs b a r := by
  apply enlargedIdeal_homogeneous
  · exact idealSequence_homogeneous I hI _ (fun _ => d) r
      (fun j _ => (linearCombination_homogeneous fs (b j) d hfs).map _)
  · exact (linearCombination_homogeneous X (Fin.cons (-1) a) 1
      (fun i => isHomogeneous_X R i)).map _

/-- Construct all flags with their prescribed residues, then prove finite
scheme length and smooth support from the actual regular sections. -/
theorem exists_finite_section (φ : R →ₐ[C] K) (ε : R →ₐ[C] C)
    [IsLocalHom ε.toRingHom] (π : R) (hπ : φ π ≠ 0) (hεπ : ε π = 0)
    (I : Ideal (MvPolynomial (Fin (n+1)) K))
    (hI : ∀ k p, p ∈ I → homogeneousComponent k p ∈ I)
    (fs : E → MvPolynomial (Fin (n+1)) R) (d : ℕ)
    (hfs : ∀ i, (fs i).IsHomogeneous d)
    (b₀ : ℕ → E → R) (a₀ : Fin n → R) (r : ℕ)
    (P : Polynomial ℚ) (N : ℕ)
    (hP : ∀ k : ℕ, N ≤ k → P.eval (k : ℚ) =
      (Module.finrank K (coordinatePiece (Fin (n+1)) K I k) : ℚ))
    (hdeg : P.natDegree ≤ r+1) :
    ∃ (b : ℕ → E → R) (a : Fin n → R),
      (∀ j i, ε (b j i) = ε (b₀ j i)) ∧ (∀ i, ε (a i) = ε (a₀ i)) ∧
      Module.Finite K (OrdinaryProjectiveHilbert.ChartAlgebra
        (sectionIdeal φ I fs b a r) (X 0)) ∧
      ∃ c : E → K, IsUnit (OrdinaryProjectiveHilbert.chartMap
        (sectionIdeal φ I fs b a r) (X 0)
        (∑ i, MvPolynomial.C (c i) * MvPolynomial.map φ.toRingHom (fs i))) := by
  classical
  let fsK := fun i => MvPolynomial.map φ.toRingHom (fs i)
  let opens := fun i => (X 0 : MvPolynomial (Fin (n+1)) K) * fsK i
  obtain ⟨b,hbres,hbreg⟩ := exists_regular_sequence φ ε π hπ hεπ fs b₀ (X 0) I
  let g := fun j => dualEquation φ fs (b j)
  let S := sequence I opens g
  have hg (j : ℕ) : (g j).IsHomogeneous d :=
    (linearCombination_homogeneous fs (b j) d hfs).map _
  have hopen (i : E) : (opens i).IsHomogeneous (1+d) :=
    (isHomogeneous_X K (0 : Fin (n+1))).mul ((hfs i).map _)
  have hS (j : ℕ) : ∀ k p, p ∈ S j → homogeneousComponent k p ∈ S j :=
    sequence_homogeneous I hI opens (fun _ => 1+d) hopen g (fun _ => d) j (fun j _ => hg j)
  obtain ⟨P₀,N₀,hP₀⟩ := HilbertPolynomialExistence.exists_coordinate_hilbert_polynomial (S 0) (hS 0)
  have hdeg₀ : P₀.natDegree ≤ r+1 :=
    (quotient_hilbert_natDegree_le I (S 0) (initial_le I opens g) hI (hS 0)
      P P₀ N N₀ hP hP₀).trans hdeg
  obtain ⟨Q,M,hQ,hQdeg⟩ := exists_hilbert_polynomial_of_cut_sequence S hS g (fun _ => d) r
    (fun j _ => hg j) (fun j _ => hbreg j) (fun j _ => cut_le_succ I opens g j) P₀ N₀ hP₀
  obtain ⟨a,hares,hareg⟩ := exists_normalized_primal φ ε π hπ hεπ fsK a₀ (S r)
  have hsatS : saturation (S r) opens = S r := by
    dsimp only [S]
    rw [sequence_eq_saturation_idealSequence,saturation_idempotent]
  have hprimalreg : IsRegular (Ideal.Quotient.mk (S r)
      (MvPolynomial.map φ.toRingHom (primalPolynomial a))) := by
    change IsRegular (Ideal.Quotient.mk (saturation (S r) opens)
      (MvPolynomial.map φ.toRingHom (primalPolynomial a))) at hareg
    rw [hsatS] at hareg
    exact hareg
  have hprimalhom : (MvPolynomial.map φ.toRingHom (primalPolynomial a)).IsHomogeneous 1 :=
    (linearCombination_homogeneous X (Fin.cons (-1) a) 1
      (fun i => isHomogeneous_X R i)).map _
  let J := enlargedIdeal (S r) (MvPolynomial.map φ.toRingHom (primalPolynomial a))
  have hJ := enlargedIdeal_homogeneous (S r) (hS r) _ hprimalhom
  obtain ⟨T,L,hT⟩ := HilbertPolynomialExistence.exists_coordinate_hilbert_polynomial J hJ
  have hTdeg := regular_cut_natDegree_le (S r) (hS r) _ hprimalhom hprimalreg Q T M L hQ hT
  have heq : sectionIdeal φ I fs b a r = saturation J opens := by
    dsimp only [sectionIdeal,rawIdeal,J,enlargedIdeal,S]
    rw [sequence_eq_saturation_idealSequence,saturation_sup_left]
  have hfinalhom : ∀ k p, p ∈ sectionIdeal φ I fs b a r →
      homogeneousComponent k p ∈ sectionIdeal φ I fs b a r := by
    rw [heq]
    exact saturation_homogeneous J opens (fun _ => 1+d) hopen hJ
  obtain ⟨V,B,hV⟩ := HilbertPolynomialExistence.exists_coordinate_hilbert_polynomial
    (sectionIdeal φ I fs b a r) hfinalhom
  have hle : J ≤ sectionIdeal φ I fs b a r := by rw [heq]; exact le_saturation _ _
  have hVdeg := quotient_hilbert_natDegree_le J (sectionIdeal φ I fs b a r) hle hJ hfinalhom
    T V L B hT hV
  have hVzero : V.natDegree = 0 := by omega
  obtain ⟨D,A,hA⟩ := eventually_constant_of_natDegree_eq_zero _ V B hV hVzero
  have hxreg : IsRegular (Ideal.Quotient.mk (sectionIdeal φ I fs b a r) (X 0)) :=
    common_factor_regular _ (X 0) fsK
  have hfinite := OrdinaryProjectiveHilbert.chartAlgebra_finite _ (X 0) hfinalhom
    (isHomogeneous_X K 0) D ⟨A,hA⟩
    (GenericHomogeneousSections.regular_filterRegular _ _ (isHomogeneous_X K 0) hxreg)
  letI : Module.Finite K (OrdinaryProjectiveHilbert.ChartAlgebra
      (saturation (rawIdeal φ I fs b a r) (fun i => X 0 * fsK i)) (X 0)) := hfinite
  letI : Infinite K := Infinite.of_injective (algebraMap C K) (algebraMap C K).injective
  refine ⟨b,a,hbres,hares,hfinite,?_⟩
  exact SaturatedChartSmoothness.exists_unit_system_coefficients (rawIdeal φ I fs b a r)
    (rawIdeal_homogeneous φ I hI fs d hfs b a r) (X 0) (isHomogeneous_X K 0) fsK d
    (fun i => (hfs i).map _)

end Sheshadri.FinitePrescribedGaussSection
