/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalFlatness
import Sheshadri.ConormalEulerHilbert
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual fibre dimensions of graded coordinate modules

Finite torsion-free modules over a PID are free. Consequently tensoring such
a module with *any* field over the PID gives the same dimension. This is the
module-theoretic conservation statement for an actual homogeneous coordinate
piece, not a hypothesis asserting numerical constancy.

The coordinate piece below is the image of the degree-`d` homogeneous
polynomials in an actual polynomial quotient. Its finite generation is proved
from the finite set of monomials of that degree. If the quotient is
torsion-free over the PID, all these pieces have constant fibre dimension.

Identifying the resulting coordinate Hilbert polynomial with the intersection
numbers of a projective scheme remains a separate geometric obligation.
-/

noncomputable section

namespace Sheshadri.FlatGradedHilbert

open scoped TensorProduct

section FibreDimension

variable (R M : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]
variable [NoZeroSMulDivisors R M]

/-- Actual dimension of a finite torsion-free module after arbitrary field
base change. This includes both the generic field and residue fields. -/
theorem finrank_fibre_eq_rank (K : Type*) [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] M) = Module.finrank R M := by
  letI : Module.Free R M := Module.free_of_finite_type_torsion_free'
  exact Module.finrank_baseChange

/-- No flatness or Hilbert-constancy certificate is assumed: both dimensions
are dimensions of explicitly formed tensor products. -/
theorem finrank_fibres_equal (K L : Type*) [Field K] [Field L]
    [Algebra R K] [Algebra R L] :
    Module.finrank K (K ⊗[R] M) = Module.finrank L (L ⊗[R] M) := by
  rw [finrank_fibre_eq_rank R M K, finrank_fibre_eq_rank R M L]

end FibreDimension

section CoordinatePieces

variable (σ R : Type*) [Finite σ] [CommRing R]

/-- There are finitely many monomials of a fixed total degree in finitely
many variables, over an arbitrary coefficient ring. -/
theorem finite_monomials_of_degree (d : ℕ) :
    {e : σ →₀ ℕ | e.degree = d}.Finite := by
  apply (Finsupp.finite_of_degree_le (σ := σ) d).subset
  intro e he
  exact le_of_eq he

/-- The full homogeneous polynomial module is finitely generated. -/
theorem homogeneous_submodule_finite (d : ℕ) :
    Module.Finite R (MvPolynomial.homogeneousSubmodule σ R d) := by
  apply Module.Finite.iff_fg.mpr
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported,
    Finsupp.supported_eq_span_single]
  exact Submodule.fg_span ((finite_monomials_of_degree σ d).image _)

/-- The actual image of homogeneous degree-`d` polynomials in a coordinate
ring. For homogeneous `I`, these are its usual graded coordinate pieces. -/
def coordinatePiece (I : Ideal (MvPolynomial σ R)) (d : ℕ) :
    Submodule R (MvPolynomial σ R ⧸ I) :=
  (MvPolynomial.homogeneousSubmodule σ R d).map
    (Ideal.Quotient.mkₐ R I).toLinearMap

instance coordinatePiece_finite (I : Ideal (MvPolynomial σ R)) (d : ℕ) :
    Module.Finite R (coordinatePiece σ R I d) := by
  letI := homogeneous_submodule_finite σ R d
  unfold coordinatePiece
  infer_instance

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Fibrewise constancy of an actual coordinate piece follows from
torsion-freeness of the total coordinate ring. -/
theorem coordinate_piece_fibre_dimensions_equal
    (I : Ideal (MvPolynomial σ R))
    [NoZeroSMulDivisors R (MvPolynomial σ R ⧸ I)]
    (K L : Type*) [Field K] [Field L] [Algebra R K] [Algebra R L] (d : ℕ) :
    Module.finrank K (K ⊗[R] coordinatePiece σ R I d) =
      Module.finrank L (L ⊗[R] coordinatePiece σ R I d) := by
  exact finrank_fibres_equal R (coordinatePiece σ R I d) K L

end CoordinatePieces

section BigradedPieces

variable (σ R : Type*) [Finite σ] [CommRing R]

/-- Standard two-block weights. `block i = true` marks a variable in the
first projective factor, and `false` one in the second factor. -/
def twoBlockWeight (block : σ → Bool) (i : σ) : ℕ × ℕ :=
  if block i then (1, 0) else (0, 1)

theorem degree_eq_sum_twoBlockWeight (block : σ → Bool) (e : σ →₀ ℕ) :
    e.degree = (Finsupp.weight (twoBlockWeight σ block) e).1 +
      (Finsupp.weight (twoBlockWeight σ block) e).2 := by
  classical
  simp only [Finsupp.degree, Finsupp.weight_apply, Finsupp.sum,
    Prod.fst_sum, Prod.snd_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : block i <;> simp [twoBlockWeight, h]

theorem finite_monomials_of_bidegree (block : σ → Bool) (a b : ℕ) :
    {e : σ →₀ ℕ | Finsupp.weight (twoBlockWeight σ block) e = (a, b)}.Finite := by
  apply (Finsupp.finite_of_degree_le (σ := σ) (a + b)).subset
  intro e he
  rw [Set.mem_setOf_eq, degree_eq_sum_twoBlockWeight σ block e, he]

theorem bihomogeneous_submodule_finite (block : σ → Bool) (a b : ℕ) :
    Module.Finite R
      (MvPolynomial.weightedHomogeneousSubmodule R (twoBlockWeight σ block) (a, b)) := by
  apply Module.Finite.iff_fg.mpr
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported,
    Finsupp.supported_eq_span_single]
  exact Submodule.fg_span ((finite_monomials_of_bidegree σ block a b).image _)

/-- The actual `(a,b)` coordinate module of a polynomial quotient. -/
def bicoordinatePiece (block : σ → Bool) (I : Ideal (MvPolynomial σ R)) (a b : ℕ) :
    Submodule R (MvPolynomial σ R ⧸ I) :=
  (MvPolynomial.weightedHomogeneousSubmodule R (twoBlockWeight σ block) (a, b)).map
    (Ideal.Quotient.mkₐ R I).toLinearMap

instance bicoordinatePiece_finite (block : σ → Bool)
    (I : Ideal (MvPolynomial σ R)) (a b : ℕ) :
    Module.Finite R (bicoordinatePiece σ R block I a b) := by
  letI := bihomogeneous_submodule_finite σ R block a b
  unfold bicoordinatePiece
  infer_instance

/-- The concrete homogeneity condition: taking any bihomogeneous component
of an equation leaves it in the defining ideal. -/
def IsBihomogeneous (block : σ → Bool) (I : Ideal (MvPolynomial σ R)) : Prop :=
  ∀ a b p, p ∈ I →
    MvPolynomial.weightedHomogeneousComponent (twoBlockWeight σ block) (a, b) p ∈ I

/-- The homogeneous projection descends to the actual quotient ring and
lands in the specified coordinate module. -/
def bicoordinateProjection (block : σ → Bool) (I : Ideal (MvPolynomial σ R))
    (hI : IsBihomogeneous σ R block I) (a b : ℕ) :
    (MvPolynomial σ R ⧸ I) →ₗ[R] bicoordinatePiece σ R block I a b := by
  let f : MvPolynomial σ R →ₗ[R] (MvPolynomial σ R ⧸ I) :=
    (Ideal.Quotient.mkₐ R I).toLinearMap.comp
      (MvPolynomial.weightedHomogeneousComponent (twoBlockWeight σ block) (a, b))
  let g : MvPolynomial σ R →ₗ[R] bicoordinatePiece σ R block I a b :=
    f.codRestrict _ (fun p => ⟨_,
      MvPolynomial.weightedHomogeneousComponent_mem _ p _, rfl⟩)
  exact (I.restrictScalars R).liftQ g (by
    intro p hp
    apply Subtype.ext
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI a b p hp))

/-- The descended projection really is a retraction of the coordinate
piece's inclusion; this prevents tensor base change from collapsing it. -/
theorem bicoordinateProjection_retract (block : σ → Bool)
    (I : Ideal (MvPolynomial σ R)) (hI : IsBihomogeneous σ R block I) (a b : ℕ) :
    (bicoordinateProjection σ R block I hI a b).comp
      (bicoordinatePiece σ R block I a b).subtype = LinearMap.id := by
  ext x
  obtain ⟨p, hp, hpx⟩ := x.property
  change (bicoordinateProjection σ R block I hI a b x : MvPolynomial σ R ⧸ I) = x
  rw [← hpx]
  change Ideal.Quotient.mk I
    (MvPolynomial.weightedHomogeneousComponent (twoBlockWeight σ block) (a, b) p) =
      Ideal.Quotient.mk I p
  rw [MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same hp]

/-- Homogeneous coordinate pieces embed in the actual fibre algebra even
at nonflat field base changes (for instance a residue field). The splitting
is what justifies reading their tensor dimensions as fibre Hilbert values. -/
theorem bicoordinate_piece_baseChange_injective (block : σ → Bool)
    (I : Ideal (MvPolynomial σ R)) (hI : IsBihomogeneous σ R block I)
    (K : Type*) [CommRing K] [Algebra R K] (a b : ℕ) :
    Function.Injective ((bicoordinatePiece σ R block I a b).subtype.baseChange K) := by
  have h := congrArg (LinearMap.baseChange K)
    (bicoordinateProjection_retract σ R block I hI a b)
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at h
  have hleft : Function.LeftInverse
      ((bicoordinateProjection σ R block I hI a b).baseChange K)
      ((bicoordinatePiece σ R block I a b).subtype.baseChange K) := by
    intro x
    exact LinearMap.congr_fun h x
  exact hleft.injective

/-- A concrete submodule of the actual fibre algebra `K ⊗[R] (R[x]/I)`:
the image of its bihomogeneous coordinate piece under base change. -/
def fibreBicoordinatePiece (block : σ → Bool) (I : Ideal (MvPolynomial σ R))
    (K : Type*) [CommRing K] [Algebra R K] (a b : ℕ) :
    Submodule K (K ⊗[R] (MvPolynomial σ R ⧸ I)) :=
  LinearMap.range ((bicoordinatePiece σ R block I a b).subtype.baseChange K)

theorem fibreBicoordinatePiece_finrank (block : σ → Bool)
    (I : Ideal (MvPolynomial σ R)) (hI : IsBihomogeneous σ R block I)
    (K : Type*) [Field K] [Algebra R K] (a b : ℕ) :
    Module.finrank K (fibreBicoordinatePiece σ R block I K a b) =
      Module.finrank K (K ⊗[R] bicoordinatePiece σ R block I a b) := by
  exact LinearMap.finrank_range_of_inj
    (bicoordinate_piece_baseChange_injective σ R block I hI K a b)

variable [IsDomain R] [IsPrincipalIdealRing R]

/-- Constancy of the actual two-graded coordinate-module fibre dimensions. -/
theorem bicoordinate_piece_fibre_dimensions_equal
    (block : σ → Bool) (I : Ideal (MvPolynomial σ R))
    [NoZeroSMulDivisors R (MvPolynomial σ R ⧸ I)]
    (K L : Type*) [Field K] [Field L] [Algebra R K] [Algebra R L] (a b : ℕ) :
    Module.finrank K (K ⊗[R] bicoordinatePiece σ R block I a b) =
      Module.finrank L (L ⊗[R] bicoordinatePiece σ R block I a b) := by
  exact finrank_fibres_equal R (bicoordinatePiece σ R block I a b) K L

/-- Equality of Hilbert values of concrete graded submodules of the two
actual fibre algebras. Homogeneity proves that base change is injective. -/
theorem fibre_bicoordinate_dimensions_equal
    (block : σ → Bool) (I : Ideal (MvPolynomial σ R))
    [NoZeroSMulDivisors R (MvPolynomial σ R ⧸ I)]
    (hI : IsBihomogeneous σ R block I)
    (K L : Type*) [Field K] [Field L] [Algebra R K] [Algebra R L] (a b : ℕ) :
    Module.finrank K (fibreBicoordinatePiece σ R block I K a b) =
      Module.finrank L (fibreBicoordinatePiece σ R block I L a b) := by
  rw [fibreBicoordinatePiece_finrank σ R block I hI K a b,
    fibreBicoordinatePiece_finrank σ R block I hI L a b]
  exact bicoordinate_piece_fibre_dimensions_equal σ R block I K L a b

end BigradedPieces

section HilbertPolynomials

open Polynomial ConormalEulerHilbert

/-- Agreement at all sufficiently large natural arguments determines a
rational polynomial; Hilbert functions need only agree eventually. -/
theorem polynomial_eq_of_nat_tail_eval_eq (p r : Polynomial ℚ) (N : ℕ)
    (h : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) = r.eval (n : ℚ)) : p = r := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun n : ℕ => ((n + N : ℕ) : ℚ)) := by
    intro n m hnm
    exact Nat.add_right_cancel (Nat.cast_injective hnm)
  apply (Set.infinite_range_of_injective hinj).mono
  rintro x ⟨n, rfl⟩
  exact h (n + N) (Nat.le_add_left N n)

/-- Eventual agreement on a rectangular tail suffices. In particular, this
applies to two-variable Hilbert polynomials after `(a,b) = (q,q*t)`. -/
theorem polynomial_eq_of_nat_grid_tail_eval_eq
    (H J : Polynomial (Polynomial ℚ)) (Q T : ℕ)
    (h : ∀ q t : ℕ, Q ≤ q → T ≤ t → gridEval H q t = gridEval J q t) : H = J := by
  have hrows : ∀ q : ℕ, Q ≤ q → H.eval (Polynomial.C (q : ℚ)) =
      J.eval (Polynomial.C (q : ℚ)) := by
    intro q hq
    exact polynomial_eq_of_nat_tail_eval_eq _ _ T (fun t ht => h q t hq ht)
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun n : ℕ => Polynomial.C ((n + Q : ℕ) : ℚ)) := by
    intro n m hnm
    exact Nat.add_right_cancel (Nat.cast_injective (Polynomial.C_injective hnm))
  apply (Set.infinite_range_of_injective hinj).mono
  rintro x ⟨n, rfl⟩
  exact hrows (n + Q) (Nat.le_add_left Q n)

variable (σ R : Type*) [Finite σ] [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (block : σ → Bool) (I : Ideal (MvPolynomial σ R))
variable [NoZeroSMulDivisors R (MvPolynomial σ R ⧸ I)]
variable (K L : Type*) [Field K] [Field L] [Algebra R K] [Algebra R L]

/-- Two candidate Hilbert polynomials representing the actual coordinate
dimensions eventually must agree. No constancy hypothesis is present:
constancy was proved from torsion-freeness of the actual quotient ring. -/
theorem fibre_hilbert_polynomials_equal
    (hI : IsBihomogeneous σ R block I)
    (H J : Polynomial (Polynomial ℚ)) (Q T : ℕ)
    (hH : ∀ q t : ℕ, Q ≤ q → T ≤ t → gridEval H q t =
      (Module.finrank K (fibreBicoordinatePiece σ R block I K q (q * t)) : ℚ))
    (hJ : ∀ q t : ℕ, Q ≤ q → T ≤ t → gridEval J q t =
      (Module.finrank L (fibreBicoordinatePiece σ R block I L q (q * t)) : ℚ)) :
    H = J := by
  apply polynomial_eq_of_nat_grid_tail_eval_eq H J Q T
  intro q t hq ht
  rw [hH q t hq ht, hJ q t hq ht,
    fibre_bicoordinate_dimensions_equal σ R block I hI K L q (q * t)]

/-- Once the classical Hilbert/intersection-coefficient identities have
been established for the actual fibre schemes, every multidegree is equal.
The identities, unlike numerical constancy, remain explicit hypotheses. -/
theorem multidegrees_equal_from_actual_coordinate_fibres
    (hI : IsBihomogeneous σ R block I)
    (H J : Polynomial (Polynomial ℚ)) (Q T d : ℕ)
    (δ ε : Fin (d + 1) → ℚ)
    (hH : ∀ q t : ℕ, Q ≤ q → T ≤ t → gridEval H q t =
      (Module.finrank K (fibreBicoordinatePiece σ R block I K q (q * t)) : ℚ))
    (hJ : ∀ q t : ℕ, Q ≤ q → T ≤ t → gridEval J q t =
      (Module.finrank L (fibreBicoordinatePiece σ R block I L q (q * t)) : ℚ))
    (hδ : H.coeff d = ConormalHilbert.topHilbertPolynomial d δ)
    (hε : J.coeff d = ConormalHilbert.topHilbertPolynomial d ε) : δ = ε := by
  have h := fibre_hilbert_polynomials_equal σ R block I K L hI H J Q T hH hJ
  apply ConormalHilbert.multidegrees_eq_of_topHilbertPolynomial_eq d
  rw [← hδ, ← hε, h]

end HilbertPolynomials

end Sheshadri.FlatGradedHilbert
