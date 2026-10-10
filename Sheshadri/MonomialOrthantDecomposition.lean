/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.HilbertStandardMonomials
import Sheshadri.BiMonomialHilbert

/-!
# A finite disjoint orthant decomposition for monomial conditions

Truncate each exponent at one common bound for the finite divisibility tests.
The resulting finite cells are actual disjoint translates of coordinate
orthants. Membership in each monomial ideal is constant on a cell. Thus the
difference of two standard-monomial sets is a union of whole cells, rather
than a signed inclusion-exclusion expression. This is the positivity input
for mixed Hilbert coefficients; no coefficient inequality is assumed here.
-/
noncomputable section
namespace Sheshadri.MonomialOrthantDecomposition
open MvPolynomial
attribute [local instance] Classical.propDecidable

variable {σ : Type*} [Fintype σ]

abbrev Cell (σ : Type*) (B : ℕ) := σ → Fin (B + 1)

/-- Coordinates at the truncation bound are the free directions of a cell. -/
def Free {B : ℕ} (c : Cell σ B) := {i : σ // (c i : ℕ) = B}

instance {B : ℕ} (c : Cell σ B) : Fintype (Free c) := by
  classical
  unfold Free
  infer_instance

/-- The literal initial exponent of the translated orthant. -/
def base {B : ℕ} (c : Cell σ B) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (c i : ℕ))

@[simp] theorem base_apply {B : ℕ} (c : Cell σ B) (i : σ) :
    base c i = (c i : ℕ) := by simp [base]

/-- Canonical finite cell of an exponent, with no choice of a partition. -/
def cell (B : ℕ) (e : σ →₀ ℕ) : Cell σ B :=
  fun i => ⟨min (e i) B, Nat.lt_succ_of_le (min_le_right _ _)⟩

@[simp] theorem cell_apply (B : ℕ) (e : σ →₀ ℕ) (i : σ) :
    (cell B e i : ℕ) = min (e i) B := rfl

/-- Add arbitrary nonnegative exponents precisely in the free directions. -/
def extend {B : ℕ} (c : Cell σ B) (q : Free c →₀ ℕ) : σ →₀ ℕ := by
  classical
  exact Finsupp.equivFunOnFinite.symm
    (fun i => (c i : ℕ) + if h : (c i : ℕ) = B then q ⟨i,h⟩ else 0)

@[simp] theorem extend_apply {B : ℕ} (c : Cell σ B) (q : Free c →₀ ℕ) (i : σ) :
    extend c q i = (c i : ℕ) + if h : (c i : ℕ) = B then q ⟨i,h⟩ else 0 := by
  classical
  simp [extend]

/-- Recover the free part by subtracting the fixed initial exponent. -/
def excess {B : ℕ} (c : Cell σ B) (e : σ →₀ ℕ) : Free c →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => e i.val - B)

@[simp] theorem excess_apply {B : ℕ} (c : Cell σ B) (e : σ →₀ ℕ) (i : Free c) :
    excess c e i = e i.val - B := by simp [excess]

theorem cell_extend {B : ℕ} (c : Cell σ B) (q : Free c →₀ ℕ) :
    cell B (extend c q) = c := by
  classical
  funext i
  apply Fin.ext
  simp only [cell_apply, extend_apply]
  split_ifs with h
  · rw [h, min_eq_right (Nat.le_add_right _ _)]
  · simp only [add_zero]
    exact min_eq_left (Nat.le_of_lt_succ (c i).isLt)

theorem excess_extend {B : ℕ} (c : Cell σ B) (q : Free c →₀ ℕ) :
    excess c (extend c q) = q := by
  classical
  ext i
  simp [i.property]

theorem extend_excess {B : ℕ} (c : Cell σ B) (e : σ →₀ ℕ)
    (he : cell B e = c) : extend c (excess c e) = e := by
  classical
  ext i
  have hi : min (e i) B = (c i : ℕ) := congrArg (fun c => (c i : ℕ)) he
  simp only [extend_apply]
  split_ifs with h
  · simp only [excess_apply]
    omega
  · omega

/-- A cell is exactly one translated coordinate orthant, including cells
with no free directions. This equivalence retains each exponent once. -/
def cellFiberEquiv {B : ℕ} (c : Cell σ B) :
    {e : σ →₀ ℕ // cell B e = c} ≃ (Free c →₀ ℕ) where
  toFun e := excess c e.val
  invFun q := ⟨extend c q, cell_extend c q⟩
  left_inv e := Subtype.ext (extend_excess c e.val e.property)
  right_inv q := excess_extend c q

/-- Every exponent belongs to its unique finite cell. -/
def exponentEquivCells (B : ℕ) :
    (σ →₀ ℕ) ≃ Σ c : Cell σ B, (Free c →₀ ℕ) :=
  (Equiv.sigmaFiberEquiv (cell B)).symm.trans
    (Equiv.sigmaCongrRight fun c => cellFiberEquiv c)

/-- The orthant parameterization is a literal translation by its base. -/
theorem extend_eq_base_add {B : ℕ} (c : Cell σ B) (q : Free c →₀ ℕ) :
    extend c q = base c + Finsupp.embDomain (Function.Embedding.subtype _) q := by
  classical
  ext i
  simp only [extend_apply, Finsupp.add_apply, base_apply]
  by_cases h : (c i : ℕ) = B
  · rw [dif_pos h]
    exact congrArg ((c i : ℕ) + ·)
      (Finsupp.embDomain_apply (Function.Embedding.subtype _) q ⟨i,h⟩).symm
  · rw [dif_neg h, Finsupp.embDomain_notin_range]
    rintro ⟨⟨j,hj⟩, hji⟩
    change j = i at hji
    subst j
    exact h hj

/-- Translation adds the fixed base degree and preserves all free degree. -/
theorem degree_extend {B : ℕ} (c : Cell σ B) (q : Free c →₀ ℕ) :
    (extend c q).degree = (base c).degree + q.degree := by
  rw [extend_eq_base_add, Finsupp.degree_add]
  congr 1
  change (Finsupp.embDomain (Function.Embedding.subtype _) q).sum (fun _ n => n) =
    q.sum (fun _ n => n)
  exact Finsupp.sum_embDomain

/-- The degree slice of each cell is the actual set of monomials in its
free variables, shifted by the degree of its fixed base. -/
def cellDegreeEquiv {B : ℕ} (c : Cell σ B) (d : ℕ) (hd : (base c).degree ≤ d) :
    {e : MonomialHilbert.DegreeMonomials σ d // cell B e.val = c} ≃
      MonomialHilbert.DegreeMonomials (Free c) (d - (base c).degree) where
  toFun e := ⟨excess c e.val.val, by
    have hh := degree_extend c (excess c e.val.val)
    rw [extend_excess c e.val.val e.property, e.val.property] at hh
    omega⟩
  invFun q := ⟨⟨extend c q.val, by rw [degree_extend, q.property]; omega⟩,
    cell_extend c q.val⟩
  left_inv e := Subtype.ext (Subtype.ext (extend_excess c e.val.val e.property))
  right_inv q := Subtype.ext (excess_extend c q.val)

/-- Finite-cell partition of a degree slice selected by any cell condition.
The condition can describe one monomial quotient or the difference of two. -/
def degreeCellsEquiv (B : ℕ) (P : Cell σ B → Prop) (d : ℕ)
    (hd : ∀ c : Cell σ B, (base c).degree ≤ d) :
    {e : MonomialHilbert.DegreeMonomials σ d // P (cell B e.val)} ≃
      Σ c : {c : Cell σ B // P c},
        MonomialHilbert.DegreeMonomials (Free c.val) (d - (base c.val).degree) :=
  (Equiv.sigmaSubtypeFiberEquivSubtype (fun e : MonomialHilbert.DegreeMonomials σ d =>
    cell B e.val) (fun _ => Iff.rfl)).symm.trans
      (Equiv.sigmaCongrRight fun c => cellDegreeEquiv c.val d (hd c.val))

/-- Positive, disjoint counting formula: there are no alternating signs. -/
theorem card_degree_cells (B : ℕ) (P : Cell σ B → Prop) (d : ℕ)
    (hd : ∀ c : Cell σ B, (base c).degree ≤ d) :
    Nat.card {e : MonomialHilbert.DegreeMonomials σ d // P (cell B e.val)} =
      ∑ c : {c : Cell σ B // P c},
        Fintype.card (MonomialHilbert.DegreeMonomials (Free c.val)
          (d - (base c.val).degree)) := by
  classical
  rw [Nat.card_congr (degreeCellsEquiv B P d hd), Nat.card_eq_fintype_card,
    Fintype.card_sigma]

/-- A bounded divisibility test only sees the finite cell. -/
theorem le_iff_le_cell_base (B : ℕ) (g e : σ →₀ ℕ)
    (hg : ∀ i, g i ≤ B) : g ≤ e ↔ g ≤ base (cell B e) := by
  simp only [Finsupp.le_def, base_apply, cell_apply, le_min_iff]
  exact ⟨fun h i => ⟨h i, hg i⟩, fun h i => (h i).1⟩

/-- One literal bound for an arbitrary finite collection of generators. -/
def generatorBound (G : Finset (σ →₀ ℕ)) : ℕ :=
  G.sup (fun g => Finset.univ.sup (fun i => g i))

theorem generator_le_bound (G : Finset (σ →₀ ℕ)) (g : σ →₀ ℕ)
    (hg : g ∈ G) (i : σ) : g i ≤ generatorBound G := by
  classical
  exact (Finset.le_sup (f := fun i => g i) (Finset.mem_univ i)).trans
    (Finset.le_sup (f := fun g : σ →₀ ℕ => Finset.univ.sup (fun i => g i)) hg)

/-- Standard-monomial membership is constant on every constructed cell. -/
theorem avoids_iff_cell_avoids (G : Finset (σ →₀ ℕ)) (B : ℕ)
    (hB : generatorBound G ≤ B) (e : σ →₀ ℕ) :
    (∀ g ∈ G, ¬g ≤ e) ↔ ∀ g ∈ G, ¬g ≤ base (cell B e) := by
  constructor <;> intro h g hg
  · simpa only [← le_iff_le_cell_base B g e
      (fun i => (generator_le_bound G g hg i).trans hB)] using h g hg
  · simpa only [le_iff_le_cell_base B g e
      (fun i => (generator_le_bound G g hg i).trans hB)] using h g hg

/-- Eventual polynomial of one cell; cells with no free coordinates vanish
in sufficiently large degree. -/
def cellPolynomial {B : ℕ} (c : Cell σ B) : Polynomial ℚ :=
  if 0 < Fintype.card (Free c) then
    Polynomial.preHilbertPoly ℚ (Fintype.card (Free c) - 1) (base c).degree else 0

/-- Stars and bars for the actual free directions of a cell. -/
theorem cellPolynomial_eval {B : ℕ} (c : Cell σ B) (d : ℕ)
    (hd : (base c).degree < d) :
    (cellPolynomial c).eval (d : ℚ) =
      Fintype.card (MonomialHilbert.DegreeMonomials (Free c) (d - (base c).degree)) := by
  classical
  unfold cellPolynomial
  split_ifs with hc
  · rw [Polynomial.preHilbertPoly_eq_choose_sub_add ℚ _ (Nat.le_of_lt hd),
      MonomialHilbert.card_degreeMonomials_of_pos _ hc]
  · have hz : Fintype.card (Free c) = 0 := by omega
    rw [Polynomial.eval_zero, MonomialHilbert.card_degreeMonomials, hz]
    simp only [zero_add]
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

/-- Its sole top coefficient is positive whenever the cell survives at
arbitrarily large degree. Lower coefficients need not be positive. -/
theorem cellPolynomial_top_coefficient {B : ℕ} (c : Cell σ B)
    (hc : 0 < Fintype.card (Free c)) :
    (cellPolynomial c).coeff (Fintype.card (Free c) - 1) =
      ((Nat.factorial (Fintype.card (Free c) - 1) : ℚ))⁻¹ := by
  rw [cellPolynomial, if_pos hc, Polynomial.coeff_preHilbertPoly_self]

section TwoBlocks
variable {τ : Type*} [Fintype τ]

abbrev BiCell (σ τ : Type*) (B : ℕ) := Cell σ B × Cell τ B

/-- The two blocks have independent degrees and independent free variables. -/
def biCellPolynomial {B : ℕ} (c : BiCell σ τ B) : Polynomial (Polynomial ℚ) :=
  (cellPolynomial c.1).map Polynomial.C * Polynomial.C (cellPolynomial c.2)

@[simp] theorem biCellPolynomial_coeff {B : ℕ} (c : BiCell σ τ B) (i j : ℕ) :
    ((biCellPolynomial c).coeff i).coeff j =
      (cellPolynomial c.1).coeff i * (cellPolynomial c.2).coeff j := by
  simp only [biCellPolynomial, Polynomial.coeff_mul_C, Polynomial.coeff_map,
    Polynomial.coeff_C_mul]

/-- Actual bijection on the two independently constrained degree slices. -/
def biCellDegreeEquiv {B : ℕ} (c : BiCell σ τ B) (a b : ℕ)
    (ha : (base c.1).degree ≤ a) (hb : (base c.2).degree ≤ b) :
    {e : MonomialHilbert.DegreeMonomials σ a × MonomialHilbert.DegreeMonomials τ b //
      (cell B e.1.val, cell B e.2.val) = c} ≃
      MonomialHilbert.DegreeMonomials (Free c.1) (a - (base c.1).degree) ×
      MonomialHilbert.DegreeMonomials (Free c.2) (b - (base c.2).degree) :=
  (Equiv.subtypeEquivRight fun e => Prod.ext_iff).trans
    (Equiv.subtypeProdEquivProd.trans
      (Equiv.prodCongr (cellDegreeEquiv c.1 a ha) (cellDegreeEquiv c.2 b hb)))

/-- The finite, disjoint partition for arbitrary monomial conditions on
both blocks. It also applies to a difference of nested monomial quotients. -/
def biDegreeCellsEquiv (B : ℕ) (P : BiCell σ τ B → Prop) (a b : ℕ)
    (ha : ∀ c : Cell σ B, (base c).degree ≤ a)
    (hb : ∀ c : Cell τ B, (base c).degree ≤ b) :
    {e : MonomialHilbert.DegreeMonomials σ a × MonomialHilbert.DegreeMonomials τ b //
      P (cell B e.1.val, cell B e.2.val)} ≃
      Σ c : {c : BiCell σ τ B // P c},
        MonomialHilbert.DegreeMonomials (Free c.val.1) (a - (base c.val.1).degree) ×
        MonomialHilbert.DegreeMonomials (Free c.val.2) (b - (base c.val.2).degree) :=
  (Equiv.sigmaSubtypeFiberEquivSubtype (fun e :
    MonomialHilbert.DegreeMonomials σ a × MonomialHilbert.DegreeMonomials τ b =>
      (cell B e.1.val, cell B e.2.val)) (fun _ => Iff.rfl)).symm.trans
        (Equiv.sigmaCongrRight fun c => biCellDegreeEquiv c.val a b (ha _) (hb _))

/-- Positive orthant formula for the bivariate eventual Hilbert polynomial. -/
def orthantPolynomial (B : ℕ) (P : BiCell σ τ B → Prop) : Polynomial (Polynomial ℚ) :=
  ∑ c : {c : BiCell σ τ B // P c}, biCellPolynomial c.val

/-- The polynomial is tied to the literal set of exponents, not a supplied
numerical polynomial or an intersection certificate. -/
theorem orthantPolynomial_eval (B : ℕ) (P : BiCell σ τ B → Prop) (a b : ℕ)
    (ha : ∀ c : Cell σ B, (base c).degree < a)
    (hb : ∀ c : Cell τ B, (base c).degree < b) :
    BiMonomialHilbert.biEval (orthantPolynomial B P) a b =
      Nat.card {e : MonomialHilbert.DegreeMonomials σ a × MonomialHilbert.DegreeMonomials τ b //
        P (cell B e.1.val, cell B e.2.val)} := by
  classical
  rw [Nat.card_congr (biDegreeCellsEquiv B P a b (fun c => (ha c).le)
    (fun c => (hb c).le)), Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [orthantPolynomial, BiMonomialHilbert.biEval, Polynomial.eval_finset_sum,
    biCellPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_map,
    Polynomial.eval₂_at_apply, Fintype.card_prod, Nat.cast_sum, Nat.cast_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [cellPolynomial_eval c.val.1 a (ha _), cellPolynomial_eval c.val.2 b (hb _)]

/-- Degree of the top term of a surviving cell in each block. -/
def leftDegree {B : ℕ} (c : BiCell σ τ B) : ℕ := Fintype.card (Free c.1) - 1

def rightDegree {B : ℕ} (c : BiCell σ τ B) : ℕ := Fintype.card (Free c.2) - 1

def Active {B : ℕ} (c : BiCell σ τ B) : Prop :=
  0 < Fintype.card (Free c.1) ∧ 0 < Fintype.card (Free c.2)

/-- Empty blocks contribute no eventual polynomial, even when they carry
finitely many low-degree monomials. -/
theorem biCellPolynomial_eq_zero_of_not_active {B : ℕ} (c : BiCell σ τ B)
    (hc : ¬ Active c) : biCellPolynomial c = 0 := by
  unfold Active at hc
  by_cases hl : 0 < Fintype.card (Free c.1)
  · have hr : ¬ 0 < Fintype.card (Free c.2) := fun hr => hc ⟨hl,hr⟩
    simp [biCellPolynomial, cellPolynomial, hr]
  · simp [biCellPolynomial, cellPolynomial, hl]

/-- The unique top bidegree of a surviving cell has positive coefficient. -/
theorem biCellPolynomial_top_pos {B : ℕ} (c : BiCell σ τ B) (hc : Active c) :
    0 < ((biCellPolynomial c).coeff (leftDegree c)).coeff (rightDegree c) := by
  rw [biCellPolynomial_coeff]
  change 0 < (cellPolynomial c.1).coeff (Fintype.card (Free c.1) - 1) *
    (cellPolynomial c.2).coeff (Fintype.card (Free c.2) - 1)
  rw [cellPolynomial_top_coefficient c.1 hc.1, cellPolynomial_top_coefficient c.2 hc.2]
  positivity

/-- At or above the total degree of one cell, all mixed coefficients are
nonnegative. The statement deliberately makes no claim about lower terms. -/
theorem biCellPolynomial_coeff_nonneg {B : ℕ} (c : BiCell σ τ B)
    (i j : ℕ) (hdegree : leftDegree c + rightDegree c ≤ i + j) :
    0 ≤ ((biCellPolynomial c).coeff i).coeff j := by
  by_cases hc : Active c
  · rw [biCellPolynomial_coeff]
    by_cases hi : leftDegree c < i
    · have hz : (cellPolynomial c.1).coeff i = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        simpa only [cellPolynomial, if_pos hc.1, Polynomial.natDegree_preHilbertPoly,
          leftDegree] using hi
      rw [hz, zero_mul]
    · by_cases hj : rightDegree c < j
      · have hz : (cellPolynomial c.2).coeff j = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          simpa only [cellPolynomial, if_pos hc.2, Polynomial.natDegree_preHilbertPoly,
            rightDegree] using hj
        rw [hz, mul_zero]
      · have hi' : i = leftDegree c := by omega
        have hj' : j = rightDegree c := by omega
        rw [hi',hj']
        simpa only [biCellPolynomial_coeff] using
          (biCellPolynomial_top_pos c hc).le
  · rw [biCellPolynomial_eq_zero_of_not_active c hc]
    simp

/-- Literal total-degree bound for the bivariate polynomial. -/
def TotalDegreeLE (H : Polynomial (Polynomial ℚ)) (d : ℕ) : Prop :=
  ∀ i j, d < i + j → (H.coeff i).coeff j = 0

/-- No surviving cell can hide above the polynomial's total degree:
its top coefficient and every possible contribution there are positive or
zero. This is the step which makes the comparison valid; pointwise Hilbert
inequalities alone would not imply it. -/
theorem active_cell_degree_le (B : ℕ) (P : BiCell σ τ B → Prop) (d : ℕ)
    (hd : TotalDegreeLE (orthantPolynomial B P) d)
    (c : {c : BiCell σ τ B // P c}) (hc : Active c.val) :
    leftDegree c.val + rightDegree c.val ≤ d := by
  classical
  let S : Finset {c : BiCell σ τ B // P c} := Finset.univ.filter fun c => Active c.val
  have hcS : c ∈ S := by simp [S,hc]
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image S
    (fun c => leftDegree c.val + rightDegree c.val) ⟨c,hcS⟩
  have heA : Active e.val := (Finset.mem_filter.mp he).2
  have hsum : 0 < ((orthantPolynomial B P).coeff (leftDegree e.val)).coeff
      (rightDegree e.val) := by
    simp only [orthantPolynomial, Polynomial.finset_sum_coeff]
    apply Finset.sum_pos'
    · intro z _
      by_cases hz : Active z.val
      · apply biCellPolynomial_coeff_nonneg
        exact hmax z (by simp [S,hz])
      · rw [biCellPolynomial_eq_zero_of_not_active z.val hz]
        simp
    · exact ⟨e, Finset.mem_univ _, biCellPolynomial_top_pos e.val heA⟩
  have hedeg : leftDegree e.val + rightDegree e.val ≤ d := by
    by_contra h
    rw [hd _ _ (by omega)] at hsum
    exact (lt_irrefl _ hsum)
  exact (hmax c hcS).trans hedeg

/-- True nonnegativity of every coefficient on a top total-degree face of
an actual orthant counting polynomial, including a difference of nested
standard-monomial sets. -/
theorem orthantPolynomial_top_coeff_nonneg (B : ℕ) (P : BiCell σ τ B → Prop)
    (d : ℕ) (hd : TotalDegreeLE (orthantPolynomial B P) d)
    (i j : ℕ) (hij : d ≤ i + j) :
    0 ≤ ((orthantPolynomial B P).coeff i).coeff j := by
  classical
  simp only [orthantPolynomial, Polynomial.finset_sum_coeff]
  apply Finset.sum_nonneg
  intro c _
  by_cases hc : Active c.val
  · exact biCellPolynomial_coeff_nonneg c.val i j
      ((active_cell_degree_le B P d hd c hc).trans hij)
  · rw [biCellPolynomial_eq_zero_of_not_active c.val hc]
    simp

end TwoBlocks
end Sheshadri.MonomialOrthantDecomposition
