/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.IdealReduction
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Reduced isolated cuts

The geometric transversality input is expressed as a precise cotangent-space
spanning condition: `m ≤ J ⊔ m • m`. Here `J` is the normal-form ideal together
with the flag equations, and `m` is the maximal ideal of the ambient local ring.
Nakayama upgrades this condition to `J = m`. We prove the resulting quotient is
a field. This is stronger than a set-theoretic isolated-zero assertion.

Identifying the paper's geometric stalk with this algebraic data, and obtaining
the cotangent spanning condition from generic flags, remain external inputs.
There are no custom axioms in this file.
-/

namespace Sheshadri

open Matrix

section Ring
variable {R : Type*} [CommRing R]

/-- Functions that agree modulo the kernel ideal give the same full ideal.
This is the correct interpretation of identities restricted to the graph. -/
theorem adjoin_equations_congr {τ : Type*} (I : Ideal R) (f h : τ → R)
    (hcong : ∀ i, f i - h i ∈ I) :
    I ⊔ equationIdeal f = I ⊔ equationIdeal h := by
  have forward (f h : τ → R) (hc : ∀ i, f i - h i ∈ I) :
      I ⊔ equationIdeal f ≤ I ⊔ equationIdeal h := by
    apply sup_le le_sup_left
    rw [equationIdeal_le_iff]
    intro i
    have hdiff : f i - h i ∈ I ⊔ equationIdeal h := (show I ≤ I ⊔ equationIdeal h from le_sup_left) (hc i)
    have hh : h i ∈ I ⊔ equationIdeal h :=
      (show equationIdeal h ≤ I ⊔ equationIdeal h from le_sup_right)
        (Ideal.subset_span ⟨i, rfl⟩)
    simpa only [sub_add_cancel] using (I ⊔ equationIdeal h).add_mem hdiff hh
  apply le_antisymm (forward f h hcong)
  apply forward h f
  intro i
  simpa only [neg_sub] using I.neg_mem (hcong i)

/-- Multiplying equations by units preserves their generated ideal. -/
theorem equationIdeal_unit_mul {τ : Type*} (f a : τ → R)
    (ha : ∀ i, IsUnit (a i)) :
    equationIdeal (fun i => a i * f i) = equationIdeal f := by
  apply le_antisymm
  · rw [equationIdeal_le_iff]
    intro i
    exact (equationIdeal f).mul_mem_left (a i)
      (Ideal.subset_span ⟨i, rfl⟩)
  · rw [equationIdeal_le_iff]
    intro i
    apply (Ideal.span_singleton_le_iff_mem _).mp
    rw [← Ideal.span_singleton_mul_left_unit (ha i) (f i)]
    exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span ⟨i, rfl⟩)

/-- Algebraic form of the local transverse-cut criterion, proved by Nakayama. -/
theorem transverse_cut_eq_maximal (J m : Ideal R)
    (hmFG : m.FG) (hmrad : m ≤ Ideal.jacobson (⊥ : Ideal R))
    (hvanish : J ≤ m) (hspan : m ≤ J ⊔ m • m) : J = m := by
  apply le_antisymm hvanish
  exact Submodule.le_of_le_smul_of_le_jacobson_bot hmFG hmrad hspan

/-- A transverse local cut has a field as its quotient ring. -/
theorem transverse_cut_quotient_isField (J m : Ideal R)
    (hm : m.IsMaximal) (hmFG : m.FG)
    (hmrad : m ≤ Ideal.jacobson (⊥ : Ideal R))
    (hvanish : J ≤ m) (hspan : m ≤ J ⊔ m • m) :
    IsField (R ⧸ J) := by
  rw [transverse_cut_eq_maximal J m hmFG hmrad hvanish hspan]
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp hm

end Ring

section Ordinary
variable {R ι τ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- Section 4.3 Step 5: full ordinary incidence and unit-rescaled flags cut out
the residue field, given the explicit geometric cotangent-spanning input. -/
theorem ordinary_isolated_reduced
    (B Binv M Minv : Matrix ι ι R) (p c z lam : ι → R) (g : R)
    (hB : B * Binv = 1) (hM : Minv * M = 1)
    (flag a : τ → R) (ha : ∀ i, IsUnit (a i))
    (m : Ideal R) (hm : m.IsMaximal) (hmFG : m.FG)
    (hmrad : m ≤ Ideal.jacobson (⊥ : Ideal R))
    (hvanish : tripleIdeal p g z ⊔ equationIdeal flag ≤ m)
    (hspan : m ≤ (tripleIdeal p g z ⊔ equationIdeal flag) ⊔ m • m) :
    IsField (R ⧸ (tripleIdeal (p ᵥ* B) (p ⬝ᵥ c + g)
      (fun i => (M *ᵥ z) i + g * lam i) ⊔
      equationIdeal (fun i => a i * flag i))) := by
  rw [ordinary_kernel_ideal B Binv M Minv p c z lam g hB hM,
    equationIdeal_unit_mul flag a ha]
  exact transverse_cut_quotient_isField _ m hm hmFG hmrad hvanish hspan

/-- Section 4.4 Step 5: the one-kernel analogue of the ordinary theorem. -/
theorem symmetric_isolated_reduced
    (B Binv : Matrix ι ι R) (z c : ι → R) (g : R)
    (hB : Binv * B = 1)
    (flag a : τ → R) (ha : ∀ i, IsUnit (a i))
    (m : Ideal R) (hm : m.IsMaximal) (hmFG : m.FG)
    (hmrad : m ≤ Ideal.jacobson (⊥ : Ideal R))
    (hvanish : (equationIdeal z ⊔ Ideal.span {g}) ⊔ equationIdeal flag ≤ m)
    (hspan : m ≤ ((equationIdeal z ⊔ Ideal.span {g}) ⊔ equationIdeal flag) ⊔ m • m) :
    IsField (R ⧸ ((equationIdeal (B *ᵥ z) ⊔ Ideal.span {c ⬝ᵥ z + g}) ⊔
      equationIdeal (fun i => a i * flag i))) := by
  rw [symmetric_kernel_ideal B Binv z c g hB, equationIdeal_unit_mul flag a ha]
  exact transverse_cut_quotient_isField _ m hm hmFG hmrad hvanish hspan

/-- The actual polar equations need agree with rescaled flags only modulo
the kernel ideal, exactly as in the paper's conormal identity along the graph. -/
theorem ordinary_isolated_reduced_mod_kernel
    (B Binv M Minv : Matrix ι ι R) (p c z lam : ι → R) (g : R)
    (hB : B * Binv = 1) (hM : Minv * M = 1)
    (flag a polar : τ → R) (ha : ∀ i, IsUnit (a i))
    (hpolar : ∀ i, polar i - a i * flag i ∈
      tripleIdeal (p ᵥ* B) (p ⬝ᵥ c + g)
        (fun j => (M *ᵥ z) j + g * lam j))
    (m : Ideal R) (hm : m.IsMaximal) (hmFG : m.FG)
    (hmrad : m ≤ Ideal.jacobson (⊥ : Ideal R))
    (hvanish : tripleIdeal p g z ⊔ equationIdeal flag ≤ m)
    (hspan : m ≤ (tripleIdeal p g z ⊔ equationIdeal flag) ⊔ m • m) :
    IsField (R ⧸ (tripleIdeal (p ᵥ* B) (p ⬝ᵥ c + g)
      (fun i => (M *ᵥ z) i + g * lam i) ⊔ equationIdeal polar)) := by
  rw [adjoin_equations_congr _ polar (fun i => a i * flag i) hpolar]
  exact ordinary_isolated_reduced B Binv M Minv p c z lam g hB hM flag a ha
    m hm hmFG hmrad hvanish hspan

theorem symmetric_isolated_reduced_mod_kernel
    (B Binv : Matrix ι ι R) (z c : ι → R) (g : R)
    (hB : Binv * B = 1)
    (flag a polar : τ → R) (ha : ∀ i, IsUnit (a i))
    (hpolar : ∀ i, polar i - a i * flag i ∈
      equationIdeal (B *ᵥ z) ⊔ Ideal.span {c ⬝ᵥ z + g})
    (m : Ideal R) (hm : m.IsMaximal) (hmFG : m.FG)
    (hmrad : m ≤ Ideal.jacobson (⊥ : Ideal R))
    (hvanish : (equationIdeal z ⊔ Ideal.span {g}) ⊔ equationIdeal flag ≤ m)
    (hspan : m ≤ ((equationIdeal z ⊔ Ideal.span {g}) ⊔ equationIdeal flag) ⊔ m • m) :
    IsField (R ⧸ ((equationIdeal (B *ᵥ z) ⊔ Ideal.span {c ⬝ᵥ z + g}) ⊔
      equationIdeal polar)) := by
  rw [adjoin_equations_congr _ polar (fun i => a i * flag i) hpolar]
  exact symmetric_isolated_reduced B Binv z c g hB flag a ha
    m hm hmFG hmrad hvanish hspan

end Ordinary
end Sheshadri
