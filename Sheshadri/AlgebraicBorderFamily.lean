/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.GenericPolynomialLift
import Sheshadri.FiniteCurveExtension
import Sheshadri.DvrRationalEntries

/-!
# An actual algebraic boundary family with a coherent generic representation

Curve selection, a finite generic-field representation, finite normalization
and localization are applied to the original polynomial parameterization.
The coefficient functions lie in an actual DVR and specialize to the target.
The representation variables lie in its function field and can have poles.
No analytic convergence or equality of analytic and Zariski closures is claimed.
-/

noncomputable section
namespace Sheshadri.AlgebraicBorderFamily
open MvPolynomial AlgebraicCurveSelection CurveThroughBoundary
open CurveNormalization FiniteCurveExtension GenericPolynomialLift ZariskiBridge
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 250000
set_option maxSynthPendingDepth 3

variable {X Y : Type*} (F : Y → MvPolynomial X ℂ)

abbrev CurveRing (Q : PrimeSpectrum (ImageRing F)) := ImageRing F ⧸ Q.asIdeal
abbrev GenericField (Q : PrimeSpectrum (ImageRing F)) := FractionRing (CurveRing F Q)
abbrev ParameterRing (Q : PrimeSpectrum (ImageRing F)) := MvPolynomial X (GenericField F Q)
abbrev ParameterField (Q : PrimeSpectrum (ImageRing F)) (M : MaximalSpectrum (ParameterRing F Q)) :=
  ParameterRing F Q ⧸ M.asIdeal

instance parameterField_field (Q : PrimeSpectrum (ImageRing F))
    (M : MaximalSpectrum (ParameterRing F Q)) : Field (ParameterField F Q M) :=
  Ideal.Quotient.field M.asIdeal

instance parameterField_finite [Finite X] (Q : PrimeSpectrum (ImageRing F))
    (M : MaximalSpectrum (ParameterRing F Q)) :
    FiniteDimensional (GenericField F Q) (ParameterField F Q M) := by
  letI : Algebra.FiniteType (GenericField F Q) (ParameterRing F Q) :=
    Algebra.FiniteType.mvPolynomial _ _
  exact finite_of_finite_type_of_isJacobsonRing _ _

abbrev BranchNormalization (Q : PrimeSpectrum (ImageRing F))
    (M : MaximalSpectrum (ParameterRing F Q)) :=
  ExtensionNormalization (CurveRing F Q) (ParameterField F Q M)

abbrev BranchRing (Q : PrimeSpectrum (ImageRing F))
    (M : MaximalSpectrum (ParameterRing F Q)) (P : PrimeSpectrum (BranchNormalization F Q M)) :=
  Localization.AtPrime P.asIdeal

/-- The generic representation variables, all in the same finite field. -/
def parameter (Q : PrimeSpectrum (ImageRing F)) (M : MaximalSpectrum (ParameterRing F Q)) (j : X) :
    ParameterField F Q M := Ideal.Quotient.mk M.asIdeal (MvPolynomial.X j)

/-- Literal coefficient functions in the actual normalized local branch. -/
def coefficient (Q : PrimeSpectrum (ImageRing F)) (M : MaximalSpectrum (ParameterRing F Q))
    (P : PrimeSpectrum (BranchNormalization F Q M)) (i : Y) : BranchRing F Q M P :=
  algebraMap (CurveRing F Q) (BranchRing F Q M P)
    (Ideal.Quotient.mk Q.asIdeal (Ideal.Quotient.mk (imageIdeal F) (MvPolynomial.X i)))

/-- Every omitted point of the actual polynomial image's Zariski closure
has one coherent algebraic representation along a normalized branch.
Coefficient regularity, exact specialization, the generic polynomial identity,
and rationality of every representation entry are all proved. -/
theorem exists_algebraic_boundary_family [Finite X] [Finite Y] (y : Y → ℂ)
    (hy : y ∈ zariskiClosure (Set.range (polynomialMap F)))
    (hout : y ∉ Set.range (polynomialMap F)) :
    ∃ (Q : PrimeSpectrum (ImageRing F)) (M : MaximalSpectrum (ParameterRing F Q))
      (P : PrimeSpectrum (BranchNormalization F Q M)),
      ringKrullDim (CurveRing F Q) = 1 ∧
      IsDiscreteValuationRing (BranchRing F Q M P) ∧
      ∃ (ρ : BranchRing F Q M P →ₐ[ℂ] ℂ)
        (ι : BranchRing F Q M P →ₐ[ℂ] ParameterField F Q M),
        Function.Injective ι ∧
        (∀ i, ρ (coefficient F Q M P i) = y i) ∧
        (∀ i, eval₂ (algebraMap ℂ (ParameterField F Q M)) (parameter F Q M) (F i) =
          ι (coefficient F Q M P i)) ∧
        (∀ j, ∃ a b : BranchRing F Q M P, b ≠ 0 ∧ parameter F Q M j = ι a / ι b) ∧
        (∀ z : ParameterField F Q M, ∃ a b : BranchRing F Q M P,
          b ≠ 0 ∧ z = ι a / ι b) ∧
        RingHom.ker ρ = IsLocalRing.maximalIdeal (BranchRing F Q M P) ∧
        Nonempty (IsLocalRing.ResidueField (BranchRing F Q M P) ≃ₐ[ℂ] ℂ) ∧
        ∃ π : BranchRing F Q M P, Irreducible π ∧
          IsLocalRing.maximalIdeal (BranchRing F Q M P) = Ideal.span {π} := by
  obtain ⟨f, Q, hQ, hQpoint, hf, hfy, hfQ, hdim, ⟨g, hginj, hgfinite⟩, hopen, hfinite⟩ :=
    exists_curve_in_imageClosure_through_boundary F y hy hout
  letI := hQ
  let q : PrimeSpectrum (ImageRing F) := ⟨Q, hQ⟩
  have hgeneric : q ∈ Set.range (PrimeSpectrum.comap (imageEmbedding F).toRingHom) := hopen hfQ
  obtain ⟨M, hM, hMfinite, hsolution⟩ := finite_representation_of_spectrum_preimage F q hgeneric
  let m : MaximalSpectrum (ParameterRing F q) := ⟨M, hM⟩
  let T := CurveRing F q
  let L := ParameterField F q m
  letI : Field L := parameterField_field F q m
  letI : FiniteDimensional (FractionRing T) L := parameterField_finite F q m
  letI : Algebra (Polynomial ℂ) T := g.toRingHom.toAlgebra
  letI : IsScalarTower ℂ (Polynomial ℂ) T := IsScalarTower.of_algHom g
  letI : FaithfulSMul (Polynomial ℂ) T := (faithfulSMul_iff_algebraMap_injective _ _).mpr hginj
  letI : Module.Finite (Polynomial ℂ) T := hgfinite
  let pointQ : T →ₐ[ℂ] ℂ := Ideal.Quotient.liftₐ Q (closurePoint F y hy) hQpoint
  obtain ⟨P, hPne, hover, hDVR, ρ, hρ, hker, hresidue, π, hπ, hπgen⟩ :=
    exists_extension_dvr T L pointQ
  let ι : BranchRing F q m P →ₐ[ℂ] L := fractionEmbedding (k := ℂ) T L P
  refine ⟨q, m, P, hdim, hDVR, ρ, ι,
    fractionEmbedding_injective (k := ℂ) T L P, ?_, ?_, ?_, ?_, hker, hresidue, π, hπ, hπgen⟩
  · intro i
    exact (hρ _).trans (closurePoint_coordinate F y hy i)
  · intro i
    rw [show ι (coefficient F q m P i) = algebraMap T L
      (Ideal.Quotient.mk Q (Ideal.Quotient.mk (imageIdeal F) (MvPolynomial.X i))) from
      fractionEmbedding_coefficient (k := ℂ) T L P _]
    have hs := hsolution i
    exact hs.trans (IsScalarTower.algebraMap_apply T (FractionRing T) L _).symm
  · intro j
    exact fractionEmbedding_div_surjective (k := ℂ) T L P (parameter F q m j)
  · exact fractionEmbedding_div_surjective (k := ℂ) T L P

/-- The coherent generic representation has a single finite pole bound
with respect to the constructed branch's actual uniformizer. -/
theorem exists_algebraic_boundary_family_with_pole_bound [Finite X] [Finite Y] (y : Y → ℂ)
    (hy : y ∈ zariskiClosure (Set.range (polynomialMap F)))
    (hout : y ∉ Set.range (polynomialMap F)) :
    ∃ (Q : PrimeSpectrum (ImageRing F)) (M : MaximalSpectrum (ParameterRing F Q))
      (P : PrimeSpectrum (BranchNormalization F Q M)),
      ringKrullDim (CurveRing F Q) = 1 ∧
      IsDiscreteValuationRing (BranchRing F Q M P) ∧
      ∃ (ρ : BranchRing F Q M P →ₐ[ℂ] ℂ)
        (ι : BranchRing F Q M P →ₐ[ℂ] ParameterField F Q M),
        Function.Injective ι ∧
        (∀ i, ρ (coefficient F Q M P i) = y i) ∧
        (∀ i, eval₂ (algebraMap ℂ (ParameterField F Q M)) (parameter F Q M) (F i) =
          ι (coefficient F Q M P i)) ∧
        (∀ j, ∃ a b : BranchRing F Q M P, b ≠ 0 ∧ parameter F Q M j = ι a / ι b) ∧
        (∀ z : ParameterField F Q M, ∃ a b : BranchRing F Q M P,
          b ≠ 0 ∧ z = ι a / ι b) ∧
        RingHom.ker ρ = IsLocalRing.maximalIdeal (BranchRing F Q M P) ∧
        Nonempty (IsLocalRing.ResidueField (BranchRing F Q M P) ≃ₐ[ℂ] ℂ) ∧
        ∃ π : BranchRing F Q M P, Irreducible π ∧
          IsLocalRing.maximalIdeal (BranchRing F Q M P) = Ideal.span {π} ∧
          ∃ n : ℕ, ∃ a : X → BranchRing F Q M P,
            ∀ j, ι (a j) = ι π ^ n * parameter F Q M j := by
  obtain ⟨Q, M, P, hdim, hDVR, ρ, ι, hinj, hspecial, hrepresentation,
    hrational, hfraction, hker, hresidue, π, hπ, hπgen⟩ :=
    exists_algebraic_boundary_family F y hy hout
  letI := hDVR
  refine ⟨Q, M, P, hdim, hDVR, ρ, ι, hinj, hspecial, hrepresentation,
    hrational, hfraction, hker, hresidue, π, hπ, hπgen, ?_⟩
  exact DvrRationalEntries.common_pole_order_of_fractions ι.toRingHom hinj hπ
    (parameter F Q M) hrational

end Sheshadri.AlgebraicBorderFamily
