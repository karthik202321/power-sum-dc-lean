/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.DVRGaussHomogeneous
import Sheshadri.BorderDvrFamily
import Sheshadri.ConormalExact

/-!
# The constructed determinant DVR family contains the Fermat conormal

The residue, uniformizer, and actual determinant family produced by curve
selection discharge every input of algebraic smooth-Gauss containment.
These are consequences of literal border membership, without a family or
closure certificate. Numerical multidegree comparison remains separate.
-/

noncomputable section
namespace Sheshadri.DeterminantDvrGaussContainment
open MvPolynomial PolynomialModel ConormalPersistence ConormalZariski
open DeterminantDvrFamily DVRGaussContainment ZariskiBridge

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 150000

/-- The same original affine Gauss-conormal construction, applied to the
constant polynomial family with value Fermat. -/
def fermatConormal (n : ℕ) : Set (Ambient (Fin n)) :=
  conormalClosure (rename (Sum.inr : Fin n → Unit ⊕ Fin n) (fermat n))
    (fun _ : Unit => (0 : ℂ))

section Family
variable {n m : ℕ} {D L : Type*} [CommRing D] [IsDomain D]
    [Algebra ℂ D] [Field L] [Algebra ℂ L]

/-- The actual constructed family, rather than a supplied geometric
certificate, provides algebraic special-conormal containment. -/
theorem family_fermatConormal_subset (family : Family n m D L) (hn : 0 < n) :
    fermatConormal n ⊆ MvPolynomial.zeroLocus
      (specialFibreIdeal family.residue.toRingHom family.polynomial) := by
  letI := family.dvr
  apply original_conormalClosure_subset_specialFibre family.residue.toRingHom
    family.uniformizer family.uniformizer_irreducible family.residue_kernel
    family.polynomial
  · rw [family.special_eq]
    exact ConormalExact.fermat_ne_zero n hn
  · rw [specialize_rename, family.special_eq]

/-- Flatness is also derived for the family's literal horizontal Gauss ring. -/
theorem family_horizontalGauss_flat (family : Family n m D L) :
    Module.Flat D (MvPolynomial (GraphVariables (Fin n)) D ⧸
      horizontalGaussIdeal family.polynomial) := by
  letI := family.dvr
  letI : Algebra D L := family.generic.toRingHom.toAlgebra
  letI : IsFractionRing D L := family.isFractionRing
  exact horizontalGaussRing_flat L family.polynomial


/-- In the determinant family's literal residue and generic fields, all
bihomogeneous coordinate dimensions agree for the constructed Gauss family. -/
theorem family_specialFibre_bicoordinate_dimensions
    (family : Family n m D L) (a b : ℕ) :
    letI : Algebra D L := family.generic.toRingHom.toAlgebra
    letI : IsFractionRing D L := family.isFractionRing
    Module.finrank ℂ (FlatGradedHilbert.bicoordinatePiece (GraphVariables (Fin n)) ℂ
      HilbertPolynomialExistence.sumBlock
      (specialFibreIdeal family.residue.toRingHom family.polynomial) a b) =
    Module.finrank L (FlatGradedHilbert.bicoordinatePiece (GraphVariables (Fin n)) L
      HilbertPolynomialExistence.sumBlock (genericGaussIdeal L family.polynomial) a b) := by
  letI := family.dvr
  letI : Algebra D L := family.generic.toRingHom.toAlgebra
  letI : IsFractionRing D L := family.isFractionRing
  letI : Infinite L := Infinite.of_injective (algebraMap ℂ L) (algebraMap ℂ L).injective
  exact DVRGaussHomogeneous.specialFibre_bicoordinate_dimensions L
    family.residue.toRingHom family.polynomial a b

end Family

/-- Bare ordinary Zariski border membership either is exact or supplies an
actual normalized DVR determinant family whose special horizontal Gauss
fibre contains the original Fermat conormal. -/
theorem ordinary_border_exact_or_conormalFamily (n m : ℕ) (hn : 0 < n)
    (hborder : OrdinaryZariskiBorder n m) :
    ExactRepresentation n m ℂ ∨
      ∃ (Q : PrimeSpectrum (AlgebraicCurveSelection.ImageRing (ordinaryCoefficientMap n m)))
        (M : MaximalSpectrum (AlgebraicBorderFamily.ParameterRing (ordinaryCoefficientMap n m) Q))
        (P : PrimeSpectrum (AlgebraicBorderFamily.BranchNormalization (ordinaryCoefficientMap n m) Q M))
        (family : Family n m
          (AlgebraicBorderFamily.BranchRing (ordinaryCoefficientMap n m) Q M P)
          (AlgebraicBorderFamily.ParameterField (ordinaryCoefficientMap n m) Q M)),
        fermatConormal n ⊆ MvPolynomial.zeroLocus
          (specialFibreIdeal family.residue.toRingHom family.polynomial) := by
  rcases ordinary_border_exact_or_family n m hborder with h | ⟨Q,M,P,⟨family⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨Q,M,P,family,family_fermatConormal_subset family hn⟩

/-- Symmetric border membership gives the same actual containment while
retaining the literal symmetry of the generic matrix pencil. -/
theorem symmetric_border_exact_or_conormalFamily (n m : ℕ) (hn : 0 < n)
    (hborder : SymmetricZariskiBorder n m) :
    SymmetricExactRepresentation n m ℂ ∨
      ∃ (Q : PrimeSpectrum (AlgebraicCurveSelection.ImageRing (symmetricCoefficientMap n m)))
        (M : MaximalSpectrum (AlgebraicBorderFamily.ParameterRing (symmetricCoefficientMap n m) Q))
        (P : PrimeSpectrum (AlgebraicBorderFamily.BranchNormalization (symmetricCoefficientMap n m) Q M))
        (family : Family n m
          (AlgebraicBorderFamily.BranchRing (symmetricCoefficientMap n m) Q M P)
          (AlgebraicBorderFamily.ParameterField (symmetricCoefficientMap n m) Q M)),
        (∀ i, (family.pencil i).transpose = family.pencil i) ∧
        fermatConormal n ⊆ MvPolynomial.zeroLocus
          (specialFibreIdeal family.residue.toRingHom family.polynomial) := by
  rcases symmetric_border_exact_or_family n m hborder with h | ⟨Q,M,P,family,hsym⟩
  · exact Or.inl h
  · exact Or.inr ⟨Q,M,P,family,hsym,family_fermatConormal_subset family hn⟩


/-- The paper's literal Euclidean finite-support border predicate yields
an exact representation or a constructed DVR Gauss family containing the
original Fermat conormal. -/
theorem ordinary_finiteSupportBorder_exact_or_conormalFamily (n m : ℕ) (hn : 0 < n)
    (h : BorderRepresentation.OrdinaryFiniteSupportBorder n m) :
    ExactRepresentation n m ℂ ∨
      ∃ (Q : PrimeSpectrum (AlgebraicCurveSelection.ImageRing (ordinaryCoefficientMap n m)))
        (M : MaximalSpectrum (AlgebraicBorderFamily.ParameterRing (ordinaryCoefficientMap n m) Q))
        (P : PrimeSpectrum (AlgebraicBorderFamily.BranchNormalization (ordinaryCoefficientMap n m) Q M))
        (family : Family n m
          (AlgebraicBorderFamily.BranchRing (ordinaryCoefficientMap n m) Q M P)
          (AlgebraicBorderFamily.ParameterField (ordinaryCoefficientMap n m) Q M)),
        fermatConormal n ⊆ MvPolynomial.zeroLocus
          (specialFibreIdeal family.residue.toRingHom family.polynomial) :=
  ordinary_border_exact_or_conormalFamily n m hn
    (BorderDvrFamily.ordinary_finiteSupportBorder_zariski h)

theorem symmetric_finiteSupportBorder_exact_or_conormalFamily (n m : ℕ) (hn : 0 < n)
    (h : BorderRepresentation.SymmetricFiniteSupportBorder n m) :
    SymmetricExactRepresentation n m ℂ ∨
      ∃ (Q : PrimeSpectrum (AlgebraicCurveSelection.ImageRing (symmetricCoefficientMap n m)))
        (M : MaximalSpectrum (AlgebraicBorderFamily.ParameterRing (symmetricCoefficientMap n m) Q))
        (P : PrimeSpectrum (AlgebraicBorderFamily.BranchNormalization (symmetricCoefficientMap n m) Q M))
        (family : Family n m
          (AlgebraicBorderFamily.BranchRing (symmetricCoefficientMap n m) Q M P)
          (AlgebraicBorderFamily.ParameterField (symmetricCoefficientMap n m) Q M)),
        (∀ i, (family.pencil i).transpose = family.pencil i) ∧
        fermatConormal n ⊆ MvPolynomial.zeroLocus
          (specialFibreIdeal family.residue.toRingHom family.polynomial) :=
  symmetric_border_exact_or_conormalFamily n m hn
    (BorderDvrFamily.symmetric_finiteSupportBorder_zariski h)

end Sheshadri.DeterminantDvrGaussContainment
