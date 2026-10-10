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
import Sheshadri.BorderRepresentation
import Sheshadri.PolynomialAnalytic

/-!
# A visible Zariski/Euclidean closure input and actual determinant maps

The universal closure principle below is a proposition supplied as a
hypothesis, not an axiom or a proved theorem. It is the standard consequence
of constructibility for polynomial images over C. Its statement mentions no
determinants or Fermat polynomials. The remaining bridge constructs the
literal polynomial coefficient maps to which that principle applies.
-/

noncomputable section
namespace Sheshadri.ZariskiBridge

open MvPolynomial Matrix PolynomialModel BorderRepresentation
open scoped BigOperators Topology

/-- Common zeros of all polynomials vanishing on a set: the affine Zariski
closure, specified without scheme infrastructure. -/
def zariskiClosure {Y : Type*} (s : Set (Y → ℂ)) : Set (Y → ℂ) :=
  {y | ∀ q : MvPolynomial Y ℂ, (∀ x ∈ s, eval x q = 0) → eval y q = 0}

def polynomialMap {X Y : Type*} (F : Y → MvPolynomial X ℂ) :
    (X → ℂ) → (Y → ℂ) := fun x y => eval x (F y)

/-- TEXTBOOK GEOMETRIC INPUT, NOT PROVED HERE. A polynomial image over C
has the same Euclidean and Zariski closures. In particular this is not a
claim that these closures agree for arbitrary subsets of complex space. -/
def UniversalPolynomialImageClosure : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] (F : Y → MvPolynomial X ℂ),
    closure (Set.range (polynomialMap F)) = zariskiClosure (Set.range (polynomialMap F))

/-- The easy inclusion is proved, for arbitrary subsets. -/
theorem euclidean_closure_subset_zariski {Y : Type*} [Fintype Y]
    (s : Set (Y → ℂ)) : closure s ⊆ zariskiClosure s := by
  intro y hy q hq
  have hc : IsClosed {x : Y → ℂ | eval x q = 0} := by
    apply isClosed_eq
    · apply continuous_iff_continuousAt.mpr
      intro x
      exact (PolynomialAnalytic.hasStrictFDerivAt_eval q x).continuousAt
    · exact continuous_const
  exact (closure_minimal hq hc) hy

theorem polynomial_image_closure_iff
    (bridge : UniversalPolynomialImageClosure)
    {X Y : Type} [Fintype X] [Fintype Y]
    (F : Y → MvPolynomial X ℂ) (y : Y → ℂ) :
    y ∈ zariskiClosure (Set.range (polynomialMap F)) ↔
      y ∈ closure (Set.range (polynomialMap F)) := by
  rw [bridge X Y F]

/-- Entry variables for the coefficients of an affine size-m pencil. -/
abbrev Entry (n m : ℕ) := Fin (n+1) × Fin m × Fin m

def universalPencil (n m : ℕ) :
    Incidence.PencilCoefficients n m (MvPolynomial (Entry n m) ℂ) :=
  fun i a b => X (i, a, b)

def symmetricUniversalPencil (n m : ℕ) :
    Incidence.PencilCoefficients n m (MvPolynomial (Entry n m) ℂ) :=
  fun i a b => C (1 / 2 : ℂ) * (X (i, a, b) + X (i, b, a))

def specializePencil {X : Type*} {n m : ℕ}
    (A : Incidence.PencilCoefficients n m (MvPolynomial X ℂ)) (x : X → ℂ) :
    Incidence.PencilCoefficients n m ℂ :=
  fun i a b => eval x (A i a b)

/-- Applying a coefficient-ring homomorphism commutes with the actual
affine determinant construction. -/
theorem map_determinant {R S : Type*} [CommRing R] [CommRing S]
    {n m : ℕ} (φ : R →+* S) (A : Incidence.PencilCoefficients n m R) :
    MvPolynomial.map φ (determinant A) = determinant (fun i a b => φ (A i a b)) := by
  rw [determinant, RingHom.map_det]
  congr 1
  ext a b
  simp [affinePencil]

/-- Each coefficient of the determinant is a literal polynomial in the
matrix parameters. -/
def coefficientMap {X : Type*} {n m : ℕ}
    (A : Incidence.PencilCoefficients n m (MvPolynomial X ℂ))
    (S : Finset (Exponent n)) : S → MvPolynomial X ℂ :=
  fun s => coeff s.val (determinant A)

theorem eval_coefficientMap {X : Type*} {n m : ℕ}
    (A : Incidence.PencilCoefficients n m (MvPolynomial X ℂ))
    (S : Finset (Exponent n)) (x : X → ℂ) (s : S) :
    polynomialMap (coefficientMap A S) x s =
      coeff s.val (determinant (specializePencil A x)) := by
  have hd : MvPolynomial.map (eval x) (determinant A) =
      determinant (specializePencil A x) := map_determinant (eval x) A
  rw [← hd]
  exact (MvPolynomial.coeff_map (eval x) (determinant A) s.val).symm

theorem reconstruct_coefficientMap {X : Type*} {n m : ℕ}
    (A : Incidence.PencilCoefficients n m (MvPolynomial X ℂ))
    (S : Finset (Exponent n)) (hS : (determinant A).support ⊆ S) (x : X → ℂ) :
    polynomialOfCoefficients S (polynomialMap (coefficientMap A S) x) =
      determinant (specializePencil A x) := by
  have hc : polynomialMap (coefficientMap A S) x =
      canonicalCoefficients S (determinant (specializePencil A x)) := by
    funext s
    exact eval_coefficientMap A S x s
  rw [hc]
  apply polynomialOfCoefficients_canonical
  have hd : MvPolynomial.map (eval x) (determinant A) =
      determinant (specializePencil A x) := map_determinant (eval x) A
  rw [← hd]
  exact (MvPolynomial.support_map_subset (eval x) (determinant A)).trans hS

theorem specialize_universalPencil (n m : ℕ)
    (A : Incidence.PencilCoefficients n m ℂ) :
    specializePencil (universalPencil n m) (fun t : Entry n m => A t.1 t.2.1 t.2.2) = A := by
  funext i a b
  simp [specializePencil, universalPencil]

theorem specialize_symmetric_is_symmetric (n m : ℕ) (x : Entry n m → ℂ) :
    ∀ i, (specializePencil (symmetricUniversalPencil n m) x i).transpose =
      specializePencil (symmetricUniversalPencil n m) x i := by
  intro i
  ext a b
  simp only [Matrix.transpose_apply, specializePencil, symmetricUniversalPencil,
    map_mul, map_add, eval_C, eval_X]
  ring

theorem specialize_symmetricUniversalPencil (n m : ℕ)
    (A : Incidence.PencilCoefficients n m ℂ) (hA : ∀ i, (A i).transpose = A i) :
    specializePencil (symmetricUniversalPencil n m)
      (fun t : Entry n m => A t.1 t.2.1 t.2.2) = A := by
  funext i a b
  have hab : A i b a = A i a b := congrFun (congrFun (hA i) a) b
  simp only [specializePencil, symmetricUniversalPencil, map_mul, map_add, eval_C, eval_X]
  rw [hab]
  ring

/-- The whole ordinary determinant locus is a polynomial image as soon as
the coefficient support contains the symbolic determinant's support. -/
theorem ordinaryLocus_eq_range (n m : ℕ) (S : Finset (Exponent n))
    (hS : (determinant (universalPencil n m)).support ⊆ S) :
    ordinaryLocus n m S = Set.range (polynomialMap (coefficientMap (universalPencil n m) S)) := by
  ext c
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨fun t : Entry n m => A t.1 t.2.1 t.2.2, ?_⟩
    apply polynomialOfCoefficients_injective S
    rw [reconstruct_coefficientMap _ S hS, specialize_universalPencil, hA]
  · rintro ⟨x, rfl⟩
    refine ⟨specializePencil (universalPencil n m) x, ?_⟩
    exact (reconstruct_coefficientMap _ S hS x).symm

/-- Symmetrization parametrizes every complex symmetric pencil, so the
symmetric determinant locus is also a literal polynomial image. -/
theorem symmetricLocus_eq_range (n m : ℕ) (S : Finset (Exponent n))
    (hS : (determinant (symmetricUniversalPencil n m)).support ⊆ S) :
    symmetricLocus n m S =
      Set.range (polynomialMap (coefficientMap (symmetricUniversalPencil n m) S)) := by
  ext c
  constructor
  · rintro ⟨A, hsym, hA⟩
    refine ⟨fun t : Entry n m => A t.1 t.2.1 t.2.2, ?_⟩
    apply polynomialOfCoefficients_injective S
    rw [reconstruct_coefficientMap _ S hS, specialize_symmetricUniversalPencil n m A hsym, hA]
  · rintro ⟨x, rfl⟩
    refine ⟨specializePencil (symmetricUniversalPencil n m) x,
      specialize_symmetric_is_symmetric n m x, ?_⟩
    exact (reconstruct_coefficientMap _ S hS x).symm

/-- A canonical finite ambient space containing all ordinary and symmetric
size-m determinants as well as the Fermat target. This avoids any assumed
degree bound: containment follows from actual symbolic polynomial support. -/
def canonicalSupport (n m : ℕ) : Finset (Exponent n) :=
  (determinant (universalPencil n m)).support ∪
    (determinant (symmetricUniversalPencil n m)).support ∪
      (PolynomialModel.fermat n : MvPolynomial (Fin n) ℂ).support

theorem ordinary_support_subset (n m : ℕ) :
    (determinant (universalPencil n m)).support ⊆ canonicalSupport n m := by
  exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left

theorem symmetric_support_subset (n m : ℕ) :
    (determinant (symmetricUniversalPencil n m)).support ⊆ canonicalSupport n m := by
  exact Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left

theorem fermat_support_subset (n m : ℕ) :
    (PolynomialModel.fermat n : MvPolynomial (Fin n) ℂ).support ⊆ canonicalSupport n m :=
  Finset.subset_union_right

def OrdinaryZariskiBorder (n m : ℕ) : Prop :=
  canonicalCoefficients (canonicalSupport n m) (PolynomialModel.fermat n) ∈
    zariskiClosure (ordinaryLocus n m (canonicalSupport n m))

def SymmetricZariskiBorder (n m : ℕ) : Prop :=
  canonicalCoefficients (canonicalSupport n m) (PolynomialModel.fermat n) ∈
    zariskiClosure (symmetricLocus n m (canonicalSupport n m))

/-- The only unproved step is the visible universal polynomial-image closure
principle. The determinant coefficient map and its whole image were proved. -/
theorem ordinary_zariski_to_euclidean
    (bridge : UniversalPolynomialImageClosure) (n m : ℕ)
    (h : OrdinaryZariskiBorder n m) : OrdinaryBorder n m (canonicalSupport n m) := by
  refine ⟨canonicalCoefficients (canonicalSupport n m) (PolynomialModel.fermat n),
    polynomialOfCoefficients_canonical _ _ (fermat_support_subset n m), ?_⟩
  change _ ∈ zariskiClosure (ordinaryLocus n m (canonicalSupport n m)) at h
  rw [ordinaryLocus_eq_range n m _ (ordinary_support_subset n m)] at h ⊢
  exact (polynomial_image_closure_iff bridge _ _).mp h

theorem symmetric_zariski_to_euclidean
    (bridge : UniversalPolynomialImageClosure) (n m : ℕ)
    (h : SymmetricZariskiBorder n m) : SymmetricBorder n m (canonicalSupport n m) := by
  refine ⟨canonicalCoefficients (canonicalSupport n m) (PolynomialModel.fermat n),
    polynomialOfCoefficients_canonical _ _ (fermat_support_subset n m), ?_⟩
  change _ ∈ zariskiClosure (symmetricLocus n m (canonicalSupport n m)) at h
  rw [symmetricLocus_eq_range n m _ (symmetric_support_subset n m)] at h ⊢
  exact (polynomial_image_closure_iff bridge _ _).mp h

theorem ordinary_zariski_to_finite_support_border
    (bridge : UniversalPolynomialImageClosure) {n m : ℕ}
    (h : OrdinaryZariskiBorder n m) : OrdinaryFiniteSupportBorder n m :=
  ⟨canonicalSupport n m, ordinary_zariski_to_euclidean bridge n m h⟩

theorem symmetric_zariski_to_finite_support_border
    (bridge : UniversalPolynomialImageClosure) {n m : ℕ}
    (h : SymmetricZariskiBorder n m) : SymmetricFiniteSupportBorder n m :=
  ⟨canonicalSupport n m, symmetric_zariski_to_euclidean bridge n m h⟩

end Sheshadri.ZariskiBridge
