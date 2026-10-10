/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Exact decomposition of split product systems

For a finite list of factors in each equation, a branch selects one factor
from every equation. If different branch ideals are comaximal, the ideal of
the product equations is exactly the intersection of the branch ideals.
This is an equality of ideals over an arbitrary commutative ring, not merely
an equality of zero sets. Impossible branches may have ideal `⊤`.

The intended application is the affine chart of a multiprojective split
start system. Its linear algebra must separately establish comaximality;
no Bezout count or regular-sequence assertion is assumed here.
-/

noncomputable section
namespace Sheshadri.BezoutExcessProducts
open scoped Classical

variable {R E : Type*} [CommRing R] {D : E → Type*} [∀ e, Fintype (D e)]

def productIdeal (f : ∀ e, D e → R) : Ideal R :=
  Ideal.span (Set.range (fun e => ∏ j, f e j))

def branchIdeal (f : ∀ e, D e → R) (c : ∀ e, D e) : Ideal R :=
  Ideal.span (Set.range (fun e => f e (c e)))

theorem product_mem (f : ∀ e, D e → R) (e : E) :
    (∏ j, f e j) ∈ productIdeal f := Ideal.subset_span ⟨e, rfl⟩

theorem factor_mem (f : ∀ e, D e → R) (c : ∀ e, D e) (e : E) :
    f e (c e) ∈ branchIdeal f c := Ideal.subset_span ⟨e, rfl⟩

theorem branchIdeal_le_iff (f : ∀ e, D e → R) (c : ∀ e, D e) (I : Ideal R) :
    branchIdeal f c ≤ I ↔ ∀ e, f e (c e) ∈ I := by
  simp [branchIdeal, Ideal.span_le, Set.range_subset_iff]

theorem productIdeal_le_branchIdeal (f : ∀ e, D e → R) (c : ∀ e, D e) :
    productIdeal f ≤ branchIdeal f c := by
  classical
  apply Ideal.span_le.mpr
  rintro _ ⟨e, rfl⟩
  change (∏ j, f e j) ∈ branchIdeal f c
  rw [← Finset.prod_erase_mul _ (f e) (Finset.mem_univ (c e))]
  exact (branchIdeal f c).mul_mem_left _ (factor_mem f c e)

/-- A prime containing the product equations contains one branch. This
also handles rows with no factors, since their product equation is `1`. -/
theorem exists_branch_le_prime (f : ∀ e, D e → R) (P : Ideal R) [P.IsPrime]
    (hP : productIdeal f ≤ P) : ∃ c : ∀ e, D e, branchIdeal f c ≤ P := by
  classical
  have hex (e : E) : ∃ j, f e j ∈ P := by
    have h := Ideal.IsPrime.prod_mem_iff.mp (hP (product_mem f e))
    simpa only [Finset.mem_univ, true_and] using h
  choose c hc using hex
  exact ⟨c, (branchIdeal_le_iff f c P).mpr hc⟩

/-- Different comaximal branches cannot lie in the same prime. -/
theorem branch_unique (f : ∀ e, D e → R)
    (hcop : Pairwise (fun c c' => IsCoprime (branchIdeal f c) (branchIdeal f c')))
    (P : Ideal R) (hP : P ≠ ⊤) {c c' : ∀ e, D e}
    (hc : branchIdeal f c ≤ P) (hc' : branchIdeal f c' ≤ P) : c = c' := by
  by_contra hne
  apply hP
  apply top_unique
  rw [← (hcop hne).sup_eq]
  exact sup_le hc hc'

/-- At a branch lying in a prime, every unselected factor is invertible
after localization at that prime. -/
theorem unselected_not_mem (f : ∀ e, D e → R)
    (hcop : Pairwise (fun c c' => IsCoprime (branchIdeal f c) (branchIdeal f c')))
    (P : Ideal R) (hP : P ≠ ⊤) (c : ∀ e, D e)
    (hc : branchIdeal f c ≤ P) (e : E) (j : D e) (hj : j ≠ c e) :
    f e j ∉ P := by
  classical
  intro hf
  let c' : ∀ e, D e := Function.update c e j
  have hc' : branchIdeal f c' ≤ P := by
    apply (branchIdeal_le_iff f c' P).mpr
    intro e'
    by_cases he : e' = e
    · subst e'
      simpa [c'] using hf
    · simpa [c', Function.update_of_ne he] using hc (factor_mem f c e')
  have heq := branch_unique f hcop P hP hc' hc
  exact hj (by simpa [c'] using congrFun heq e)

/-- Equality of the localized product ideal and the unique branch ideal. -/
theorem localized_productIdeal_eq_branchIdeal (f : ∀ e, D e → R)
    (hcop : Pairwise (fun c c' => IsCoprime (branchIdeal f c) (branchIdeal f c')))
    (P : Ideal R) [P.IsPrime] (c : ∀ e, D e) (hc : branchIdeal f c ≤ P) :
    Ideal.map (algebraMap R (Localization.AtPrime P)) (productIdeal f) =
      Ideal.map (algebraMap R (Localization.AtPrime P)) (branchIdeal f c) := by
  classical
  let φ := algebraMap R (Localization.AtPrime P)
  apply le_antisymm (Ideal.map_mono (productIdeal_le_branchIdeal f c))
  apply Ideal.map_le_iff_le_comap.mpr
  apply (branchIdeal_le_iff f c _).mpr
  intro e
  change φ (f e (c e)) ∈ Ideal.map φ (productIdeal f)
  have hunit : IsUnit (φ (∏ j ∈ Finset.univ.erase (c e), f e j)) := by
    apply IsLocalization.map_units (M := P.primeCompl) (Localization.AtPrime P)
      ⟨_, show (∏ j ∈ Finset.univ.erase (c e), f e j) ∉ P from ?_⟩
    intro hprod
    obtain ⟨j, hj, hjP⟩ := Ideal.IsPrime.prod_mem_iff.mp hprod
    exact unselected_not_mem f hcop P ‹P.IsPrime›.ne_top c hc e j
      (Finset.mem_erase.mp hj).1 hjP
  apply (Ideal.unit_mul_mem_iff_mem _ hunit).mp
  rw [← map_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ (c e))]
  exact Ideal.mem_map_of_mem φ (product_mem f e)

/-- The exact algebraic decomposition used by a split start system.
No finiteness or reducedness of the zero set is postulated. -/
theorem productIdeal_eq_iInf_branchIdeal (f : ∀ e, D e → R)
    (hcop : Pairwise (fun c c' => IsCoprime (branchIdeal f c) (branchIdeal f c'))) :
    productIdeal f = ⨅ c : ∀ e, D e, branchIdeal f c := by
  classical
  apply le_antisymm
  · exact le_iInf (productIdeal_le_branchIdeal f)
  · intro x hx
    apply Ideal.mem_of_localization_maximal
    intro P hP
    letI : P.IsMaximal := hP
    let φ := algebraMap R (Localization.AtPrime P)
    by_cases hIP : productIdeal f ≤ P
    · obtain ⟨c, hc⟩ := exists_branch_le_prime f P hIP
      rw [localized_productIdeal_eq_branchIdeal f hcop P c hc]
      exact Ideal.mem_map_of_mem _ ((iInf_le (fun c => branchIdeal f c) c) hx)
    · have hex : ∃ y ∈ productIdeal f, y ∉ P := by
        by_contra hn
        apply hIP
        intro y hy
        by_contra hnP
        exact hn ⟨y, hy, hnP⟩
      obtain ⟨y, hy, hyP⟩ := hex
      have htop : Ideal.map φ (productIdeal f) = ⊤ :=
        (Ideal.map φ (productIdeal f)).eq_top_of_isUnit_mem
          (Ideal.mem_map_of_mem φ hy)
          (IsLocalization.map_units (M := P.primeCompl) _ ⟨y, hyP⟩)
      change φ x ∈ Ideal.map φ (productIdeal f)
      rw [htop]
      trivial

/-- CRT for the actual quotient by the product equations. -/
def productQuotientEquiv [Fintype E] (f : ∀ e, D e → R)
    (hcop : Pairwise (fun c c' => IsCoprime (branchIdeal f c) (branchIdeal f c'))) :
    (R ⧸ productIdeal f) ≃+* ∀ c : ∀ e, D e, R ⧸ branchIdeal f c :=
  (Ideal.quotEquivOfEq (productIdeal_eq_iInf_branchIdeal f hcop)).trans
    (Ideal.quotientInfRingEquivPiQuotient (branchIdeal f) hcop)

@[simp]
theorem productQuotientEquiv_mk [Fintype E] (f : ∀ e, D e → R)
    (hcop : Pairwise (fun c c' => IsCoprime (branchIdeal f c) (branchIdeal f c')))
    (x : R) (c : ∀ e, D e) :
    productQuotientEquiv f hcop (Ideal.Quotient.mk _ x) c =
      Ideal.Quotient.mk (branchIdeal f c) x := rfl

/-- The decomposition respects all scalars acting on the original ring. -/
def productQuotientAlgEquiv (K : Type*) [CommSemiring K] [Algebra K R]
    [Fintype E] (f : ∀ e, D e → R)
    (hcop : Pairwise (fun c c' => IsCoprime (branchIdeal f c) (branchIdeal f c'))) :
    (R ⧸ productIdeal f) ≃ₐ[K] ∀ c : ∀ e, D e, R ⧸ branchIdeal f c :=
  { productQuotientEquiv f hcop with commutes' := fun _ => rfl }

/-- The dimension of the actual product-system quotient is the sum of
the dimensions of its actual branch quotients. -/
theorem finrank_productQuotient (K : Type*) [Field K] [Algebra K R]
    [Fintype E] (f : ∀ e, D e → R)
    (hcop : Pairwise (fun c c' => IsCoprime (branchIdeal f c) (branchIdeal f c')))
    [∀ c : ∀ e, D e, Module.Finite K (R ⧸ branchIdeal f c)] :
    Module.finrank K (R ⧸ productIdeal f) =
      ∑ c : ∀ e, D e, Module.finrank K (R ⧸ branchIdeal f c) := by
  rw [(productQuotientAlgEquiv K f hcop).toLinearEquiv.finrank_eq,
    Module.finrank_pi_fintype]

theorem finite_productQuotient (K : Type*) [CommSemiring K] [Algebra K R]
    [Fintype E] (f : ∀ e, D e → R)
    (hcop : Pairwise (fun c c' => IsCoprime (branchIdeal f c) (branchIdeal f c')))
    [∀ c : ∀ e, D e, Module.Finite K (R ⧸ branchIdeal f c)] :
    Module.Finite K (R ⧸ productIdeal f) :=
  Module.Finite.equiv (productQuotientAlgEquiv K f hcop).toLinearEquiv.symm

end Sheshadri.BezoutExcessProducts
