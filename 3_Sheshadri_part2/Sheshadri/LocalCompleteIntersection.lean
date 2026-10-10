/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.LocalRing.Quotient
import Sheshadri.RegularPrimeAvoidance

/-!
# Elementary exchange of local regular sequences

These lemmas support the local complete-intersection step for isolated
square systems. They manipulate actual ideals, quotient modules and regular
sequences; regularity is not inferred from a label for isolatedness.
-/

noncomputable section
namespace Sheshadri.LocalCompleteIntersection
open RingTheory.Sequence Submodule
open scoped Pointwise

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem ideal_le_annihilator_quotient (I : Ideal R) :
    I ≤ Module.annihilator R (M ⧸ (I • (⊤ : Submodule R M))) := by
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R M)) x
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Submodule.smul_mem_smul hr Submodule.mem_top

theorem isSMulRegular_congr_mod_annihilator {a b : R}
    (hab : a-b ∈ Module.annihilator R M) :
    IsSMulRegular M a ↔ IsSMulRegular M b := by
  have heq : (fun x : M => a • x) = (fun x : M => b • x) := by
    funext x
    exact sub_eq_zero.mp (by simpa only [sub_smul] using
      Module.mem_annihilator.mp hab x)
  change Function.Injective (fun x : M => a • x) ↔
    Function.Injective (fun x : M => b • x)
  rw [heq]

theorem sup_span_eq_of_sub_mem (I : Ideal R) {a b : R} (hab : a-b ∈ I) :
    I ⊔ Ideal.span {a} = I ⊔ Ideal.span {b} := by
  have one_way {a b : R} (hab : a-b ∈ I) :
      I ⊔ Ideal.span {a} ≤ I ⊔ Ideal.span {b} := by
    apply sup_le le_sup_left
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    have h1 : a-b ∈ I ⊔ Ideal.span {b} := (show I ≤ I ⊔ Ideal.span {b} from le_sup_left) hab
    have h2 : b ∈ I ⊔ Ideal.span {b} :=
      (show Ideal.span {b} ≤ I ⊔ Ideal.span {b} from le_sup_right) (Ideal.subset_span rfl)
    simpa only [sub_add_cancel] using (I ⊔ Ideal.span {b}).add_mem h1 h2
  exact le_antisymm (one_way hab) (one_way (by simpa using I.neg_mem hab))

theorem isWeaklyRegular_append_singleton_congr {rs : List R} {a b : R}
    (hab : a-b ∈ Ideal.ofList rs) :
    IsWeaklyRegular M (rs ++ [a]) ↔ IsWeaklyRegular M (rs ++ [b]) := by
  rw [isWeaklyRegular_append_iff, isWeaklyRegular_append_iff,
    isWeaklyRegular_singleton_iff, isWeaklyRegular_singleton_iff]
  exact and_congr_right' (isSMulRegular_congr_mod_annihilator
    (ideal_le_annihilator_quotient (M := M) (Ideal.ofList rs) hab))

variable [IsLocalRing R] [IsNoetherian R M]

/-- Elementary row operations on a local regular sequence, justified by
permutation and equality of the resulting quotient ideals. -/
theorem regular_cons_congr_mod_tail {rs : List R} {a b : R}
    (hreg : IsRegular M (a::rs)) (hba : b-a ∈ Ideal.ofList rs) :
    IsRegular M (b::rs) := by
  have hperm : IsRegular M (rs ++ [a]) :=
    IsLocalRing.isRegular_of_perm hreg (by
      exact List.perm_append_comm (l₁ := [a]) (l₂ := rs))
  have hideal : Ideal.ofList (rs ++ [b]) = Ideal.ofList (rs ++ [a]) := by
    simp only [Ideal.ofList_append, Ideal.ofList_singleton]
    exact sup_span_eq_of_sub_mem (Ideal.ofList rs) hba
  have hnew : IsRegular M (rs ++ [b]) :=
    ⟨(isWeaklyRegular_append_singleton_congr hba).mpr hperm.toIsWeaklyRegular,
      by simpa only [hideal] using hperm.top_ne_smul⟩
  exact IsLocalRing.isRegular_of_perm hnew List.perm_append_comm

theorem regular_mem_maximal {rs : List R} (hreg : IsRegular M rs)
    {r : R} (hr : r ∈ rs) : r ∈ IsLocalRing.maximalIdeal R := by
  apply IsLocalRing.le_maximalIdeal _ (Ideal.subset_span (show r ∈ {x | x ∈ rs} from hr))
  intro htop
  change Ideal.ofList rs = ⊤ at htop
  exact hreg.top_ne_smul (by rw [htop, top_smul])

/-- The annihilator correction makes ideal containment stable under
passing to the quotient by the newly chosen first regular element. -/
theorem containment_after_quotient (gs fs : List R) (a h : R)
    (hinc : Ideal.ofList gs ≤ Ideal.ofList (a::fs) ⊔ Module.annihilator R M)
    (hha : h-a ∈ Ideal.ofList fs) :
    Ideal.ofList gs ≤ Ideal.ofList fs ⊔ Module.annihilator R (QuotSMulTop h M) := by
  have hAnn : Module.annihilator R M ≤ Module.annihilator R (QuotSMulTop h M) :=
    LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _)
  have hh : h ∈ Module.annihilator R (QuotSMulTop h M) := by
    apply Module.mem_annihilator.mpr
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (h • (⊤ : Submodule R M)) x
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨x, Submodule.mem_top, rfl⟩
  apply hinc.trans
  apply sup_le _ (hAnn.trans le_sup_right)
  rw [Ideal.ofList_cons, sup_comm, ← sup_span_eq_of_sub_mem (Ideal.ofList fs) hha]
  exact sup_le le_sup_left
    ((Ideal.span_singleton_le_iff_mem _).mpr
      ((show Module.annihilator R (QuotSMulTop h M) ≤
        Ideal.ofList fs ⊔ Module.annihilator R (QuotSMulTop h M) from le_sup_right) hh))

variable (K : Type*) [Field K] [Infinite K] [Algebra K R] [IsNoetherianRing R]
include K

/-- A same-length list of generators of an ideal containing a regular
sequence is itself regular in a Noetherian local algebra over an infinite
field. The annihilator term permits induction on quotient modules.

The proof is elementary: choose a regular linear combination whose first
coefficient is one, permute the known regular sequence, pass to the quotient,
and finally undo that elementary row operation. No depth or Cohen-Macaulay
certificate is assumed. -/
theorem regular_of_contains_regular_sequence
    (fs gs : List R) (hfs : ∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R)
    (hgs : IsRegular M gs) (hlen : gs.length = fs.length)
    (hinc : Ideal.ofList gs ≤ Ideal.ofList fs ⊔ Module.annihilator R M) :
    IsRegular M fs := by
  induction fs generalizing M gs with
  | nil =>
    letI := hgs.nontrivial
    exact IsRegular.nil R M
  | cons f fs ih =>
    cases gs with
    | nil => simp at hlen
    | cons g gs =>
      letI : Nontrivial M := hgs.nontrivial
      let N := M ⧸ (Ideal.ofList gs • (⊤ : Submodule R M))
      have hperm : IsRegular M (gs ++ [g]) :=
        IsLocalRing.isRegular_of_perm hgs
          (List.perm_append_comm (l₁ := [g]) (l₂ := gs))
      have hweak := (isWeaklyRegular_append_iff M gs [g]).mp hperm.toIsWeaklyRegular
      have hg : IsSMulRegular N g := (isWeaklyRegular_singleton_iff N g).mp hweak.2
      have hann : Module.annihilator R M ≤ Module.annihilator R N :=
        LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _)
      have hgin : g ∈ Ideal.ofList (f::fs) ⊔ Module.annihilator R N :=
        (sup_le_sup_left hann _) (hinc (Ideal.subset_span List.mem_cons_self))
      obtain ⟨h, hdiff, hregular⟩ :=
        RegularPrimeAvoidance.exists_regular_head_mod_tail_of_regular_mem
          K (M := N) f fs g hg hgin
      have hhmax : h ∈ IsLocalRing.maximalIdeal R := by
        have htail : Ideal.ofList fs ≤ IsLocalRing.maximalIdeal R :=
          Ideal.span_le.mpr (fun x hx => hfs x (List.mem_cons_of_mem f hx))
        simpa only [sub_add_cancel] using
          (IsLocalRing.maximalIdeal R).add_mem (htail hdiff) (hfs f List.mem_cons_self)
      have hnew : IsRegular M (gs ++ [h]) := by
        apply IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
          (M := M) (rs := gs ++ [h]) ?_ |>.mpr
        · exact (isWeaklyRegular_append_iff M gs [h]).mpr
            ⟨hweak.1, (isWeaklyRegular_singleton_iff N h).mpr hregular⟩
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact regular_mem_maximal hgs (List.mem_cons_of_mem g hx)
          · simpa only [List.mem_singleton.mp hx] using hhmax
      have hfirst : IsRegular M (h::gs) :=
        IsLocalRing.isRegular_of_perm hnew List.perm_append_comm
      have hfirst' := (isRegular_cons_iff M h gs).mp hfirst
      have htailinc : Ideal.ofList gs ≤
          Ideal.ofList fs ⊔ Module.annihilator R (QuotSMulTop h M) := by
        apply containment_after_quotient gs fs f h _ hdiff
        apply le_trans _ hinc
        rw [Ideal.ofList_cons]
        exact le_sup_right
      have hquot : IsRegular (QuotSMulTop h M) fs :=
        ih gs (fun x hx => hfs x (List.mem_cons_of_mem f hx)) hfirst'.2
          (by simpa using hlen) htailinc
      have hreg : IsRegular M (h::fs) := hquot.cons hfirst'.1
      exact regular_cons_congr_mod_tail hreg (by
        simpa only [neg_sub] using (Ideal.ofList fs).neg_mem hdiff)

/-- Ring version with ordinary ideal containment and no annihilator term. -/
theorem ring_regular_of_contains_regular_sequence
    (fs gs : List R) (hfs : ∀ f ∈ fs, f ∈ IsLocalRing.maximalIdeal R)
    (hgs : IsRegular R gs) (hlen : gs.length = fs.length)
    (hinc : Ideal.ofList gs ≤ Ideal.ofList fs) : IsRegular R fs :=
  regular_of_contains_regular_sequence K fs gs hfs hgs hlen (hinc.trans le_sup_left)

omit K [Field K] [Infinite K] [Algebra K R] [IsNoetherian R M] in
/-- Artinian local quotients contain a power of the actual ambient maximal
ideal. This generalizes the finite-set version to complex local algebras. -/
theorem exists_maximalIdeal_pow_le_of_artinian_quotient (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] :
    ∃ n : ℕ, IsLocalRing.maximalIdeal R ^ n ≤ I := by
  by_cases hI : I = ⊤
  · exact ⟨0, by simp [hI]⟩
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial hI
  letI := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
  have hmap : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I) =
      IsLocalRing.maximalIdeal (R ⧸ I) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sup_eq_left.mpr (IsLocalRing.le_maximalIdeal hI)]
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, ← hmap,
    ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker,
    Ideal.mk_ker] at hn
  exact ⟨n, hn⟩

omit K [Field K] [Infinite K] [Algebra K R] [IsNoetherian R M] in
/-- In particular, a single positive exponent sends every coordinate
vanishing at the point into its actual equation ideal. -/
theorem exists_positive_power_mem_of_artinian_quotient (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ IsLocalRing.maximalIdeal R, x^n ∈ I := by
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_artinian_quotient I
  refine ⟨n+1, Nat.succ_pos n, ?_⟩
  intro x hx
  rw [pow_succ]
  exact I.mul_mem_right x (hn (Ideal.pow_mem_pow hx n))

end Sheshadri.LocalCompleteIntersection
