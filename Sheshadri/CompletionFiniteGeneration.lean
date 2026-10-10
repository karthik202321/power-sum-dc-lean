/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Finite generation of a completion from its special fiber

The source module need not be finite over the base ring. A finite family
which generates modulo an ideal generates after completion. This is the
constructive, surjective form of topological Nakayama, proved by successive
corrections in the actual ideal powers.
-/

noncomputable section
namespace Sheshadri.CompletionFiniteGeneration

open AdicCompletion LinearMap

variable {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N)

private theorem power_generation
    (h : LinearMap.range f ⊔ I • (⊤ : Submodule R N) = ⊤) (n : ℕ) :
    Submodule.map f (I ^ n • (⊤ : Submodule R M)) ⊔
      I ^ (n + 1) • (⊤ : Submodule R N) = I ^ n • (⊤ : Submodule R N) := by
  rw [Submodule.map_smul'', Submodule.map_top, pow_succ, mul_smul, ← Submodule.smul_sup, h]

private theorem approximation_step
    (h : LinearMap.range f ⊔ I • (⊤ : Submodule R N) = ⊤)
    (b : AdicCauchySequence I N) (n : ℕ) (a : M)
    (ha : b n - f a ∈ I ^ n • (⊤ : Submodule R N)) :
    ∃ a' : M, b (n + 1) - f a' ∈ I ^ (n + 1) • (⊤ : Submodule R N) ∧
      a' - a ∈ I ^ n • (⊤ : Submodule R M) := by
  have hb : b (n + 1) - b n ∈ I ^ n • (⊤ : Submodule R N) := by
    exact SModEq.sub_mem.mp (b.property (Nat.le_succ n)).symm
  have hd : b (n + 1) - f a ∈ I ^ n • (⊤ : Submodule R N) := by
    convert (I ^ n • (⊤ : Submodule R N)).add_mem hb ha using 1
    abel
  rw [← power_generation I f h n, Submodule.mem_sup] at hd
  obtain ⟨u, hu, v, hv, huv⟩ := hd
  obtain ⟨d, hd, rfl⟩ := hu
  refine ⟨a + d, ?_, ?_⟩
  · convert hv using 1
    rw [map_add]
    calc
      b (n + 1) - (f a + f d) = (b (n + 1) - f a) - f d := by abel
      _ = (f d + v) - f d := by rw [← huv]
      _ = v := by abel
  · simpa using hd

private def approximation
    (h : LinearMap.range f ⊔ I • (⊤ : Submodule R N) = ⊤)
    (b : AdicCauchySequence I N) :
    (n : ℕ) → {a : M // b n - f a ∈ I ^ n • (⊤ : Submodule R N)}
  | 0 => ⟨0, by simp⟩
  | n + 1 =>
    ⟨(approximation_step I f h b n (approximation h b n).val
      (approximation h b n).property).choose,
     (approximation_step I f h b n (approximation h b n).val
      (approximation h b n).property).choose_spec.1⟩

/-- Surjectivity modulo an ideal implies surjectivity after adic completion.
No finite-generation assumption on either original module is needed. -/
theorem map_surjective_of_range_sup
    (h : LinearMap.range f ⊔ I • (⊤ : Submodule R N) = ⊤) :
    Function.Surjective (AdicCompletion.map I f) := by
  intro y
  induction y using AdicCompletion.induction_on I N with
  | h b =>
    let a := approximation I f h b
    let c : AdicCauchySequence I M := AdicCauchySequence.mk I M
      (fun n => (a n).val) (fun n => by
        apply SModEq.sub_mem.mpr
        have ht := (approximation_step I f h b n (a n).val (a n).property).choose_spec.2
        simpa only [neg_sub] using (I ^ n • (⊤ : Submodule R M)).neg_mem ht)
    refine ⟨AdicCompletion.mk I M c, ?_⟩
    apply AdicCompletion.ext
    intro n
    change Submodule.Quotient.mk (f (a n).val) = Submodule.Quotient.mk (b n)
    exact (SModEq.sub_mem.mpr (a n).property).symm

/-- The usual quotient-map formulation of generation modulo an ideal. -/
theorem range_sup_of_reduce_surjective
    (h : Function.Surjective (f.reduceModIdeal I)) :
    LinearMap.range f ⊔ I • (⊤ : Submodule R N) = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, hx⟩ := h (Submodule.Quotient.mk y)
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hy : y - f a ∈ I • (⊤ : Submodule R N) :=
    SModEq.sub_mem.mp hx.symm
  exact Submodule.mem_sup.mpr ⟨f a, ⟨a, rfl⟩, y - f a, hy, by abel⟩

/-- Topological Nakayama for the literal map on quotient modules. -/
theorem map_surjective_of_reduce_surjective
    (h : Function.Surjective (f.reduceModIdeal I)) :
    Function.Surjective (AdicCompletion.map I f) :=
  map_surjective_of_range_sup I f (range_sup_of_reduce_surjective I f h)

/-- A map which reflects membership in every ideal power induces an
injection on completions, without a finiteness assumption. -/
theorem map_injective_of_power_strict
    (h : ∀ (n : ℕ) (x : M), f x ∈ I ^ n • (⊤ : Submodule R N) →
      x ∈ I ^ n • (⊤ : Submodule R M)) :
    Function.Injective (AdicCompletion.map I f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  induction x using AdicCompletion.induction_on I M with
  | h b =>
    apply AdicCompletion.ext
    intro n
    have hn := congrArg (fun z : AdicCompletion I N => z.val n) hx
    change Submodule.Quotient.mk (f (b n)) = 0 at hn
    change Submodule.Quotient.mk (b n) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h n (b n)
      ((Submodule.Quotient.mk_eq_zero _).mp hn))

section Principal

open scoped Pointwise

private theorem mem_parameter_power_iff (π : R) (n : ℕ) (x : M) :
    x ∈ (Ideal.span {π}) ^ n • (⊤ : Submodule R M) ↔ ∃ y : M, π ^ n • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

/-- Regularity of the parameter makes independence modulo the parameter
persist modulo every power. -/
theorem power_strict_of_reduce_injective (π : R)
    (hπ : IsSMulRegular N π)
    (hf : Function.Injective (f.reduceModIdeal (Ideal.span {π})))
    (n : ℕ) (x : M)
    (hx : f x ∈ (Ideal.span {π}) ^ n • (⊤ : Submodule R N)) :
    x ∈ (Ideal.span {π}) ^ n • (⊤ : Submodule R M) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hxone : f x ∈ (Ideal.span {π}) • (⊤ : Submodule R N) := by
      exact (Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero n))) hx
    have hxone' : x ∈ (Ideal.span {π}) • (⊤ : Submodule R M) := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      apply hf
      simpa only [LinearMap.reduceModIdeal_apply, _root_.map_zero] using
        ((Submodule.Quotient.mk_eq_zero _).mpr hxone)
    obtain ⟨y, hy⟩ := (mem_parameter_power_iff (M := M) π 1 x).mp (by simpa using hxone')
    simp only [pow_one] at hy
    obtain ⟨z, hz⟩ := (mem_parameter_power_iff (M := N) π (n + 1) (f x)).mp hx
    have hfy : π ^ n • z = f y := by
      apply hπ
      change π • (π ^ n • z) = π • f y
      rw [← mul_smul, ← pow_succ', hz, ← hy, map_smul]
    obtain ⟨w, hw⟩ := (mem_parameter_power_iff (M := M) π n y).mp
      (ih y ((mem_parameter_power_iff (M := N) π n (f y)).mpr ⟨z, hfy⟩))
    apply (mem_parameter_power_iff (M := M) π (n + 1) x).mpr
    exact ⟨w, by rw [pow_succ', mul_smul, hw, hy]⟩

/-- A map giving a basis modulo a regular parameter becomes an isomorphism
on completion. In particular, this does not assume that its target was
finite over the original base ring. -/
def completionEquivOfReduction (π : R)
    (hπ : IsSMulRegular N π)
    (hf : Function.Bijective (f.reduceModIdeal (Ideal.span {π}))) :
    AdicCompletion (Ideal.span {π}) M ≃ₗ[AdicCompletion (Ideal.span {π}) R]
      AdicCompletion (Ideal.span {π}) N :=
  LinearEquiv.ofBijective (AdicCompletion.map (Ideal.span {π}) f)
    ⟨map_injective_of_power_strict (Ideal.span {π}) f
      (power_strict_of_reduce_injective f π hπ hf.1),
     map_surjective_of_reduce_surjective (Ideal.span {π}) f hf.2⟩

end Principal

/-- A finite module mapping onto the special fiber gives a finite completed
module over the completed base ring. -/
theorem finite_of_range_sup [Module.Finite R M]
    (h : LinearMap.range f ⊔ I • (⊤ : Submodule R N) = ⊤) :
    Module.Finite (AdicCompletion I R) (AdicCompletion I N) := by
  letI : Module.Finite (AdicCompletion I R) (AdicCompletion I M) := by
    exact Module.Finite.of_surjective
      (AdicCompletion.ofTensorProduct I M)
      (AdicCompletion.ofTensorProduct_surjective_of_finite I M)
  exact Module.Finite.of_surjective (AdicCompletion.map I f)
    (map_surjective_of_range_sup I f h)

/-- Finiteness of the actual special-fiber module is sufficient for
finiteness of the completion over the completed coefficient ring. -/
theorem finite_of_quotient_finite
    [Module.Finite R (N ⧸ I • (⊤ : Submodule R N))] :
    Module.Finite (AdicCompletion I R) (AdicCompletion I N) := by
  let Q := N ⧸ I • (⊤ : Submodule R N)
  obtain ⟨d, g, hg⟩ := Module.Finite.exists_fin' R Q
  obtain ⟨f, hf⟩ := Module.projective_lifting_property
    (I • (⊤ : Submodule R N)).mkQ g (Submodule.mkQ_surjective _)
  apply finite_of_range_sup I f
  apply top_unique
  intro y _
  obtain ⟨x, hx⟩ := hg (Submodule.Quotient.mk y)
  have hq : Submodule.Quotient.mk (p := I • (⊤ : Submodule R N)) (f x) =
      Submodule.Quotient.mk y := by
    exact (LinearMap.congr_fun hf x).trans hx
  have hy : y - f x ∈ I • (⊤ : Submodule R N) := SModEq.sub_mem.mp hq.symm
  exact Submodule.mem_sup.mpr ⟨f x, ⟨x, rfl⟩, y - f x, hy, by abel⟩

/-- Lifting a basis modulo a regular parameter yields an actual completed
basis with the same index set. -/
def basisOfReduction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (π : R) (g : (ι → R) →ₗ[R] N) (hπ : IsSMulRegular N π)
    (hg : Function.Bijective (g.reduceModIdeal (Ideal.span {π}))) :
    Basis ι (AdicCompletion (Ideal.span {π}) R)
      (AdicCompletion (Ideal.span {π}) N) :=
  (Pi.basisFun (AdicCompletion (Ideal.span {π}) R) ι).map
    ((AdicCompletion.piEquivOfFintype (Ideal.span {π}) (fun _ : ι => R)).symm.trans
      (completionEquivOfReduction g π hπ hg))

end Sheshadri.CompletionFiniteGeneration
