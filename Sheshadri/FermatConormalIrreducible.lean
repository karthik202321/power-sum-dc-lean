/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.FermatIrreducible
import Sheshadri.ProjectiveConormal

/-! Irreducibility of the actual conormal closure used by the original proof.
The source has two free scaling coordinates together with the hypersurface
coordinates.  Its topology is the algebraic topology on the combined affine
space, not a product of Zariski topologies. -/

noncomputable section
namespace Sheshadri.FermatConormalIrreducible
open MvPolynomial Set
open ConormalPersistence ConormalZariski ConormalTopology FermatIrreducible

variable {Z : Type*} [Fintype Z]

abbrev SourceCoordinates (Z : Type*) := Option (Option Z)

def embedCoordinate (i : Z) : SourceCoordinates Z := some (some i)

def extend (f : MvPolynomial Z ℂ) : MvPolynomial (SourceCoordinates Z) ℂ :=
  rename (some : Option Z → Option (Option Z)) (rename (some : Z → Option Z) f)

@[simp] theorem eval_extend (f : MvPolynomial Z ℂ) (q : SourceCoordinates Z → ℂ) :
    eval q (extend f) = eval (fun i => q (embedCoordinate i)) f := by
  simp only [extend, eval_rename, Function.comp_def, embedCoordinate]

theorem extend_prime (f : MvPolynomial Z ℂ) (hf : Prime f) : Prime (extend f) :=
  prime_rename_some (prime_rename_some hf)

def sourceOpen (f : MvPolynomial Z ℂ) : Set (SourceCoordinates Z → ℂ) :=
  {q | q none ≠ 0 ∧ q (some none) ≠ 0 ∧
    ∃ i, eval q (extend (pderiv i f)) ≠ 0}

theorem sourceOpen_isOpen (f : MvPolynomial Z ℂ) :
    @IsOpen (SourceCoordinates Z → ℂ) (algebraicTopology (SourceCoordinates Z))
      (sourceOpen f) := by
  letI := algebraicTopology (SourceCoordinates Z)
  have hcoord (i : SourceCoordinates Z) : IsOpen {q : SourceCoordinates Z → ℂ | q i ≠ 0} := by
    simpa only [eval_X] using (polynomial_zeroLocus_isClosed (X i)).isOpen_compl
  have hg : IsOpen {q : SourceCoordinates Z → ℂ |
      ∃ i, eval q (extend (pderiv i f)) ≠ 0} := by
    simp only [setOf_exists]
    apply isOpen_iUnion
    intro i
    exact (polynomial_zeroLocus_isClosed _).isOpen_compl
  exact (hcoord none).inter ((hcoord (some none)).inter hg)

def source (f : MvPolynomial Z ℂ) : Set (SourceCoordinates Z → ℂ) :=
  {q | eval q (extend f) = 0} ∩ sourceOpen f

theorem source_isIrreducible (f : MvPolynomial Z ℂ) (hf : Prime f)
    (hne : ∃ z : Z → ℂ, eval z f = 0 ∧ ∃ i, eval z (pderiv i f) ≠ 0) :
    @IsIrreducible (SourceCoordinates Z → ℂ) (algebraicTopology (SourceCoordinates Z))
      (source f) := by
  letI := algebraicTopology (SourceCoordinates Z)
  have hext := extend_prime f hf
  have hI := (Ideal.span_singleton_prime hext.ne_zero).mpr hext
  have hirr : IsIrreducible {q : SourceCoordinates Z → ℂ | eval q (extend f) = 0} := by
    simpa [MvPolynomial.zeroLocus_span] using
      zeroLocus_isIrreducible (Ideal.span {extend f}) hI
  have hnonempty : (source f).Nonempty := by
    obtain ⟨z, hz, i, hi⟩ := hne
    refine ⟨fun j => Option.elim j 1 (fun k => Option.elim k 1 z), ?_⟩
    refine ⟨?_, ?_, ?_, i, ?_⟩
    · simpa [eval_extend, embedCoordinate] using hz
    · exact one_ne_zero
    · exact one_ne_zero
    · simpa [eval_extend, embedCoordinate] using hi
  refine ⟨hnonempty, ?_⟩
  intro U V hU hV hSU hSV
  obtain ⟨x, hx, hxU, hxV⟩ := hirr.2
    (sourceOpen f ∩ U) (sourceOpen f ∩ V)
    ((sourceOpen_isOpen f).inter hU) ((sourceOpen_isOpen f).inter hV)
    (by simpa only [source, Set.inter_assoc] using hSU)
    (by simpa only [source, Set.inter_assoc] using hSV)
  exact ⟨x, ⟨hx, hxU.1⟩, hxU.2, hxV.2⟩

def gaussPolynomials (f : MvPolynomial Z ℂ) :
    (Option Z ⊕ Option Z) → MvPolynomial (SourceCoordinates Z) ℂ :=
  Sum.elim
    (fun j => X none * Option.elim j 1 (fun i => X (embedCoordinate i)))
    (fun j => X (some none) * extend
      (Option.elim j (-∑ i, X i * pderiv i f) (fun i => pderiv i f)))

def gaussMap (f : MvPolynomial Z ℂ) (q : SourceCoordinates Z → ℂ) : Ambient Z :=
  fun j => eval q (gaussPolynomials f j)

theorem gaussMap_algebraic_continuous (f : MvPolynomial Z ℂ) :
    @Continuous (SourceCoordinates Z → ℂ) (Ambient Z)
      (algebraicTopology (SourceCoordinates Z))
      (algebraicTopology (Option Z ⊕ Option Z)) (gaussMap f) :=
  ProjectiveConormal.polynomialMap_algebraic_continuous (gaussPolynomials f)

variable {A : Type*} [Fintype A]

theorem gaussMap_eq (F : MvPolynomial (A ⊕ Z) ℂ) (a : A → ℂ)
    (q : SourceCoordinates Z → ℂ) :
    gaussMap (specialize a F) q =
      gaussPoint F a (fun i => q (embedCoordinate i)) (q none) (q (some none)) := by
  have hg (i : Z) : eval (fun i => q (embedCoordinate i)) (pderiv i (specialize a F)) =
      gradient F a (fun i => q (embedCoordinate i)) i := by
    rw [← specialize_pderiv, eval_specialize]
    rfl
  funext j
  cases j with
  | inl j => cases j <;> simp [gaussMap, gaussPolynomials, gaussPoint, embedCoordinate]
  | inr j =>
    cases j <;>
      simp [gaussMap, gaussPolynomials, gaussPoint, gaussCovector, eval_extend, hg]

theorem image_source_eq_smoothGaussRepresentatives
    (F : MvPolynomial (A ⊕ Z) ℂ) (a : A → ℂ) :
    gaussMap (specialize a F) '' source (specialize a F) = smoothGaussRepresentatives F a := by
  ext p
  constructor
  · rintro ⟨q, ⟨hq, hmu, hnu, i, hi⟩, rfl⟩
    refine ⟨(fun i => q (embedCoordinate i)), q none, q (some none), ?_, ?_, hmu, hnu, ?_⟩
    · simpa [eval_extend, eval_specialize, value] using hq
    · refine ⟨i, ?_⟩
      simpa [eval_extend, ← specialize_pderiv, eval_specialize, gradient, value] using hi
    · exact gaussMap_eq F a q
  · rintro ⟨z, mu, nu, hz, hgrad, hmu, hnu, rfl⟩
    let q : SourceCoordinates Z → ℂ := fun i => Option.elim i mu (fun j => Option.elim j nu z)
    refine ⟨q, ?_, ?_⟩
    · refine ⟨?_, hmu, hnu, ?_⟩
      · simpa [eval_extend, embedCoordinate, q, eval_specialize, value] using hz
      · obtain ⟨i, hi⟩ := hgrad
        refine ⟨i, ?_⟩
        simpa [eval_extend, embedCoordinate, q, ← specialize_pderiv, eval_specialize, gradient,
          value] using hi
    · simpa [q, embedCoordinate] using gaussMap_eq F a q

/-- For a prime hypersurface with at least one smooth complex point, the
literal rescaled Gauss-graph closure is irreducible. -/
theorem conormalClosure_isIrreducible
    (F : MvPolynomial (A ⊕ Z) ℂ) (a : A → ℂ)
    (hf : Prime (specialize a F))
    (hne : ∃ z : Z → ℂ, eval z (specialize a F) = 0 ∧
      ∃ i, eval z (pderiv i (specialize a F)) ≠ 0) :
    @IsIrreducible (Ambient Z) (algebraicTopology (Option Z ⊕ Option Z))
      (conormalClosure F a) := by
  letI := algebraicTopology (SourceCoordinates Z)
  letI := algebraicTopology (Option Z ⊕ Option Z)
  have himg := (source_isIrreducible (specialize a F) hf hne).image
    (gaussMap (specialize a F)) (gaussMap_algebraic_continuous (specialize a F)).continuousOn
  rw [image_source_eq_smoothGaussRepresentatives] at himg
  have hc := himg.closure
  simpa only [closure_algebraicTopology_eq, conormalClosure] using hc

/-- A concrete smooth zero is used only to witness nonemptiness; no finite
polar fibre, flag choice, or point-counting slice is used. -/
theorem exists_smooth_fermat_zero {n : ℕ} (hn : 2 ≤ n) :
    ∃ z : Fin n → ℂ, eval z (PolynomialModel.fermat n : MvPolynomial (Fin n) ℂ) = 0 ∧
      ∃ i, eval z (pderiv i (PolynomialModel.fermat n)) ≠ 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have hn' : n = k + 2 := by omega
  subst hn'
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : ℂ) (by omega : 0 < k + 2)
  let z : Fin (k + 2) → ℂ := Fin.cons 1 (Fin.cons w (fun _ => 0))
  refine ⟨z, ?_, (0 : Fin (k + 2)), ?_⟩
  · simp [PolynomialModel.fermat, Fin.sum_univ_succ, z, hw]
  · change eval z (pderiv 0 (powerSum (k + 2) (k + 2) : MvPolynomial (Fin (k + 2)) ℂ)) ≠ 0
    rw [pderiv_powerSum]
    have hd : ((k + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa [z] using hd

/-- The target-irreducibility premise of the original border proof is
discharged for the actual Fermat specialization. -/
theorem fermat_conormalClosure_isIrreducible {n : ℕ} (hn : 3 ≤ n)
    (F : MvPolynomial (A ⊕ Fin n) ℂ) (a : A → ℂ)
    (hF : specialize a F = PolynomialModel.fermat n) :
    @IsIrreducible (Ambient (Fin n))
      (algebraicTopology (Option (Fin n) ⊕ Option (Fin n))) (conormalClosure F a) := by
  apply conormalClosure_isIrreducible F a
  · rw [hF]
    exact (fermat_irreducible hn).prime
  · rw [hF]
    exact exists_smooth_fermat_zero (by omega)

end Sheshadri.FermatConormalIrreducible
