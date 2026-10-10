/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.AlgebraicBorderFamily

/-!
# Literal determinant families over the constructed boundary DVR

The polynomial coefficients are regular on the branch and specialize to
Fermat.  The matrix pencil exists over the actual finite generic field;
its entries may have poles, with one uniformizer power clearing all of them.
-/
noncomputable section
namespace Sheshadri.DeterminantDvrFamily
open MvPolynomial PolynomialModel BorderRepresentation ZariskiBridge AlgebraicBorderFamily
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 250000
set_option maxSynthPendingDepth 3

/-- A polynomial reconstructed from a fixed finite coefficient support,
over any commutative coefficient ring. -/
def coefficientPolynomial {n : ℕ} {R : Type*} [CommRing R]
    (S : Finset (Exponent n)) (c : S → R) : MvPolynomial (Fin n) R :=
  ∑ s : S, C (c s) * monomial s.val 1

theorem coeff_coefficientPolynomial {n : ℕ} {R : Type*} [CommRing R]
    (S : Finset (Exponent n)) (c : S → R) (d : Exponent n) :
    coeff d (coefficientPolynomial S c) = if h : d ∈ S then c ⟨d, h⟩ else 0 := by
  classical
  simp only [coefficientPolynomial, coeff_sum, C_mul_monomial, mul_one, coeff_monomial]
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

theorem coefficientPolynomial_coeff {n : ℕ} {R : Type*} [CommRing R]
    (S : Finset (Exponent n)) (f : MvPolynomial (Fin n) R) (hf : f.support ⊆ S) :
    coefficientPolynomial S (fun s => coeff s.val f) = f := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_coefficientPolynomial]
  split_ifs with hd
  · rfl
  · exact (not_mem_support_iff.mp (fun h => hd (hf h))).symm

theorem map_coefficientPolynomial {n : ℕ} {R T : Type*} [CommRing R] [CommRing T]
    (φ : R →+* T) (S : Finset (Exponent n)) (c : S → R) :
    MvPolynomial.map φ (coefficientPolynomial S c) =
      coefficientPolynomial S (fun s => φ (c s)) := by
  classical
  simp [coefficientPolynomial]

/-- Every literal polynomial identity for the symbolic coefficients
reconstructs the literal determinant over the generic coefficient field. -/
theorem generic_determinant {X R L : Type*} [CommRing R] [CommRing L] [Algebra ℂ L]
    {n m : ℕ} (A : Incidence.PencilCoefficients n m (MvPolynomial X ℂ))
    (S : Finset (Exponent n)) (hS : (determinant A).support ⊆ S)
    (c : S → R) (ι : R →+* L) (x : X → L)
    (h : ∀ s, eval₂ (algebraMap ℂ L) x (coefficientMap A S s) = ι (c s)) :
    MvPolynomial.map ι (coefficientPolynomial S c) =
      determinant (fun i a b => eval₂ (algebraMap ℂ L) x (A i a b)) := by
  let φ : MvPolynomial X ℂ →+* L := eval₂Hom (algebraMap ℂ L) x
  rw [map_coefficientPolynomial]
  have hc : (fun s => ι (c s)) =
      (fun s : S => coeff s.val (MvPolynomial.map φ (determinant A))) := by
    funext s
    rw [coeff_map]
    exact (h s).symm
  rw [hc, coefficientPolynomial_coeff _ _ ((support_map_subset φ _).trans hS)]
  exact map_determinant φ A

/-- Literal specialization of the coefficient polynomial. -/
theorem special_polynomial {R : Type*} [CommRing R] {n : ℕ}
    (S : Finset (Exponent n)) (c : S → R) (ρ : R →+* ℂ)
    (f : MvPolynomial (Fin n) ℂ) (hf : f.support ⊆ S)
    (h : ∀ s, ρ (c s) = coeff s.val f) :
    MvPolynomial.map ρ (coefficientPolynomial S c) = f := by
  rw [map_coefficientPolynomial]
  simpa only [funext h] using coefficientPolynomial_coeff S f hf

theorem eval_symmetric_pencil {L : Type*} [CommRing L] [Algebra ℂ L]
    (n m : ℕ) (x : Entry n m → L) :
    (fun i u v => eval₂ (algebraMap ℂ L) x (symmetricUniversalPencil n m i u v)) =
      (fun i u v => algebraMap ℂ L (1 / 2) * (x (i, u, v) + x (i, v, u))) := by
  funext i u v
  simp only [symmetricUniversalPencil, eval₂_mul, eval₂_add, eval₂_C, eval₂_X]

theorem clear_symmetric_poles {D L : Type*} [CommRing D] [CommRing L]
    [Algebra ℂ D] [Algebra ℂ L] {n m : ℕ} (ι : D →ₐ[ℂ] L) (π : D) (r : ℕ)
    (a : Entry n m → D) (x : Entry n m → L)
    (ha : ∀ j, ι (a j) = ι π ^ r * x j) (i u v) :
    ι (algebraMap ℂ D (1 / 2) * (a (i, u, v) + a (i, v, u))) =
      ι π ^ r * (algebraMap ℂ L (1 / 2) * (x (i, u, v) + x (i, v, u))) := by
  rw [map_mul, map_add, ι.commutes, ha, ha]
  ring

/-- Concrete output needed by the original conormal specialization argument.
Its two polynomial identities are equations of literal multivariate polynomials. -/
structure Family (n m : ℕ) (D L : Type*) [CommRing D] [IsDomain D]
    [Algebra ℂ D] [Field L] [Algebra ℂ L] where
  dvr : IsDiscreteValuationRing D
  residue : D →ₐ[ℂ] ℂ
  generic : D →ₐ[ℂ] L
  generic_injective : Function.Injective generic
  generic_fractions : ∀ z : L, ∃ a b : D, b ≠ 0 ∧ z = generic a / generic b
  polynomial : MvPolynomial (Fin n) D
  pencil : Incidence.PencilCoefficients n m L
  special_eq : MvPolynomial.map residue.toRingHom polynomial = fermat n
  generic_eq : MvPolynomial.map generic.toRingHom polynomial = determinant pencil
  uniformizer : D
  uniformizer_irreducible : Irreducible uniformizer
  residue_kernel : RingHom.ker residue = Ideal.span {uniformizer}
  pole_order : ℕ
  regular_pencil : Incidence.PencilCoefficients n m D
  clear_poles : ∀ i a b, generic (regular_pencil i a b) =
    generic uniformizer ^ pole_order * pencil i a b

/-- The generic matrix field really is the fraction field of the constructed
DVR, with the algebra structure furnished by its actual embedding. -/
theorem Family.isFractionRing {n m : ℕ} {D L : Type*} [CommRing D] [IsDomain D]
    [Algebra ℂ D] [Field L] [Algebra ℂ L] (family : Family n m D L) :
    letI : Algebra D L := family.generic.toRingHom.toAlgebra
    IsFractionRing D L := by
  letI : Algebra D L := family.generic.toRingHom.toAlgebra
  letI : FaithfulSMul D L :=
    (faithfulSMul_iff_algebraMap_injective D L).mpr family.generic_injective
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a, b, hb, h⟩ := family.generic_fractions z
  exact ⟨a, b, h⟩

/-- Symmetry also holds for the regular matrix pencil obtained by clearing
poles; injectivity of the actual generic embedding proves the descent. -/
theorem Family.regular_pencil_symmetric {n m : ℕ} {D L : Type*}
    [CommRing D] [IsDomain D] [Algebra ℂ D] [Field L] [Algebra ℂ L]
    (family : Family n m D L) (hsym : ∀ i, (family.pencil i).transpose = family.pencil i) :
    ∀ i, (family.regular_pencil i).transpose = family.regular_pencil i := by
  intro i
  ext u v
  apply family.generic_injective
  simp only [Matrix.transpose_apply, family.clear_poles]
  rw [show family.pencil i v u = family.pencil i u v from congrFun (congrFun (hsym i) u) v]

def ordinaryCoefficientMap (n m : ℕ) :
    canonicalSupport n m → MvPolynomial (Entry n m) ℂ :=
  coefficientMap (universalPencil n m) (canonicalSupport n m)

def symmetricCoefficientMap (n m : ℕ) :
    canonicalSupport n m → MvPolynomial (Entry n m) ℂ :=
  coefficientMap (symmetricUniversalPencil n m) (canonicalSupport n m)

/-- Existence in the actual curve quotient, actual finite representation
field and actual normalized local branch, not an unspecified DVR certificate. -/
def HasOrdinaryFamily (n m : ℕ) : Prop :=
  ∃ (Q : PrimeSpectrum (AlgebraicCurveSelection.ImageRing (ordinaryCoefficientMap n m)))
    (M : MaximalSpectrum (ParameterRing (ordinaryCoefficientMap n m) Q))
    (P : PrimeSpectrum (BranchNormalization (ordinaryCoefficientMap n m) Q M)),
    Nonempty (Family n m (BranchRing (ordinaryCoefficientMap n m) Q M P)
      (ParameterField (ordinaryCoefficientMap n m) Q M))

def HasSymmetricFamily (n m : ℕ) : Prop :=
  ∃ (Q : PrimeSpectrum (AlgebraicCurveSelection.ImageRing (symmetricCoefficientMap n m)))
    (M : MaximalSpectrum (ParameterRing (symmetricCoefficientMap n m) Q))
    (P : PrimeSpectrum (BranchNormalization (symmetricCoefficientMap n m) Q M))
    (family : Family n m (BranchRing (symmetricCoefficientMap n m) Q M P)
      (ParameterField (symmetricCoefficientMap n m) Q M)),
    ∀ i, (family.pencil i).transpose = family.pencil i

/-- A literal ordinary determinant border point, when not already exact,
has a coherent determinant family over the constructed normalized DVR. -/
theorem ordinary_family_of_border (n m : ℕ) (hborder : OrdinaryZariskiBorder n m)
    (hexact : ¬ ExactRepresentation n m ℂ) : HasOrdinaryFamily n m := by
  classical
  let F := ordinaryCoefficientMap n m
  let S := canonicalSupport n m
  let y := canonicalCoefficients S (fermat n : MvPolynomial (Fin n) ℂ)
  have hy : y ∈ zariskiClosure (Set.range (polynomialMap F)) := by
    change y ∈ zariskiClosure (ordinaryLocus n m S) at hborder
    rwa [ordinaryLocus_eq_range n m S (ordinary_support_subset n m)] at hborder
  have hout : y ∉ Set.range (polynomialMap F) := by
    intro h
    have hmem : y ∈ ordinaryLocus n m S := by
      rwa [ordinaryLocus_eq_range n m S (ordinary_support_subset n m)]
    obtain ⟨A, hA⟩ := hmem
    exact hexact ⟨A, hA.trans (polynomialOfCoefficients_canonical S _ (fermat_support_subset n m))⟩
  obtain ⟨Q, M, P, hdim, hdvr, ρ, ι, hinj, hspecial, hgeneric, hrational, hfraction,
    hker, hresidue, π, hπ, hπgen, r, a, ha⟩ :=
    exists_algebraic_boundary_family_with_pole_bound F y hy hout
  let D := BranchRing F Q M P
  let L := ParameterField F Q M
  let A : Incidence.PencilCoefficients n m L :=
    fun i u v => parameter F Q M (i, u, v)
  have hdet : MvPolynomial.map ι.toRingHom
      (coefficientPolynomial S (coefficient F Q M P)) = determinant A := by
    convert generic_determinant (universalPencil n m) S (ordinary_support_subset n m)
      (coefficient F Q M P) ι.toRingHom (parameter F Q M) hgeneric using 1
    simp [A, universalPencil]
  refine ⟨Q, M, P, ⟨{
    dvr := hdvr
    residue := ρ
    generic := ι
    generic_injective := hinj
    generic_fractions := hfraction
    polynomial := coefficientPolynomial S (coefficient F Q M P)
    pencil := A
    special_eq := special_polynomial S _ ρ.toRingHom (fermat n)
      (fermat_support_subset n m) hspecial
    generic_eq := hdet
    uniformizer := π
    uniformizer_irreducible := hπ
    residue_kernel := hker.trans hπgen
    pole_order := r
    regular_pencil := fun i u v => a (i, u, v)
    clear_poles := fun i u v => ha (i, u, v)
  }⟩⟩

/-- Full ordinary border membership either was exact already, or yields
the constructed algebraic DVR family. No closure comparison is assumed. -/
theorem ordinary_border_exact_or_family (n m : ℕ) (hborder : OrdinaryZariskiBorder n m) :
    ExactRepresentation n m ℂ ∨ HasOrdinaryFamily n m := by
  classical
  by_cases h : ExactRepresentation n m ℂ
  · exact Or.inl h
  · exact Or.inr (ordinary_family_of_border n m hborder h)

/-- The symmetric route retains actual symmetry after passage to the
finite generic field and after the uniformizer clears the poles. -/
theorem symmetric_family_of_border (n m : ℕ) (hborder : SymmetricZariskiBorder n m)
    (hexact : ¬ SymmetricExactRepresentation n m ℂ) : HasSymmetricFamily n m := by
  classical
  let F := symmetricCoefficientMap n m
  let S := canonicalSupport n m
  let y := canonicalCoefficients S (fermat n : MvPolynomial (Fin n) ℂ)
  have hy : y ∈ zariskiClosure (Set.range (polynomialMap F)) := by
    change y ∈ zariskiClosure (symmetricLocus n m S) at hborder
    rwa [symmetricLocus_eq_range n m S (symmetric_support_subset n m)] at hborder
  have hout : y ∉ Set.range (polynomialMap F) := by
    intro h
    have hmem : y ∈ symmetricLocus n m S := by
      rwa [symmetricLocus_eq_range n m S (symmetric_support_subset n m)]
    obtain ⟨A, hsym, hA⟩ := hmem
    exact hexact ⟨A, hsym,
      hA.trans (polynomialOfCoefficients_canonical S _ (fermat_support_subset n m))⟩
  obtain ⟨Q, M, P, hdim, hdvr, ρ, ι, hinj, hspecial, hgeneric, hrational, hfraction,
    hker, hresidue, π, hπ, hπgen, r, a, ha⟩ :=
    exists_algebraic_boundary_family_with_pole_bound F y hy hout
  let D := BranchRing F Q M P
  let L := ParameterField F Q M
  let A : Incidence.PencilCoefficients n m L := fun i u v =>
    algebraMap ℂ L (1 / 2) * (parameter F Q M (i, u, v) + parameter F Q M (i, v, u))
  let B : Incidence.PencilCoefficients n m D := fun i u v =>
    algebraMap ℂ D (1 / 2) * (a (i, u, v) + a (i, v, u))
  have hdet : MvPolynomial.map ι.toRingHom
      (coefficientPolynomial S (coefficient F Q M P)) = determinant A := by
    have h := generic_determinant (symmetricUniversalPencil n m) S (symmetric_support_subset n m)
      (coefficient F Q M P) ι.toRingHom (parameter F Q M) hgeneric
    rw [eval_symmetric_pencil] at h
    exact h
  have hclear : ∀ i u v, ι (B i u v) = ι π ^ r * A i u v := by
    intro i u v
    exact clear_symmetric_poles ι π r a (parameter F Q M) ha i u v
  refine ⟨Q, M, P, {
    dvr := hdvr
    residue := ρ
    generic := ι
    generic_injective := hinj
    generic_fractions := hfraction
    polynomial := coefficientPolynomial S (coefficient F Q M P)
    pencil := A
    special_eq := special_polynomial S _ ρ.toRingHom (fermat n)
      (fermat_support_subset n m) hspecial
    generic_eq := hdet
    uniformizer := π
    uniformizer_irreducible := hπ
    residue_kernel := hker.trans hπgen
    pole_order := r
    regular_pencil := B
    clear_poles := hclear
  }, ?_⟩
  intro i
  ext u v
  simp only [Matrix.transpose_apply, A]
  ring

theorem symmetric_border_exact_or_family (n m : ℕ) (hborder : SymmetricZariskiBorder n m) :
    SymmetricExactRepresentation n m ℂ ∨ HasSymmetricFamily n m := by
  classical
  by_cases h : SymmetricExactRepresentation n m ℂ
  · exact Or.inl h
  · exact Or.inr (symmetric_family_of_border n m hborder h)

end Sheshadri.DeterminantDvrFamily
