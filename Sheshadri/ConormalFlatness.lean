/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# The local algebra in Section 7.2

A reduced algebra embeds in its product of minimal-prime quotients. A scalar
which remains nonzero on every such component is a non-zero-divisor. Thus
componentwise dominance (injectivity of the base in each component quotient)
makes the algebra torsion-free over the base.

We also prove, for arbitrary modules, that torsion-free modules over a PID are
flat: each finite relation lies in a finitely generated torsion-free submodule,
which is free, and the equational criterion for flatness finishes the proof.
This includes the DVR local rings of the paper. No finite-module hypothesis
is imposed on the algebra itself.
-/

namespace Sheshadri.ConormalFlatness

open scoped BigOperators

section Reduced

variable {S : Type*} [CommRing S] [IsReduced S]

/-- A reduced-ring element vanishing on every minimal component is zero. -/
theorem eq_zero_of_mem_all_minimalPrimes (x : S)
    (hx : ∀ p : Ideal S, p ∈ minimalPrimes S → x ∈ p) : x = 0 := by
  have hnil : IsNilpotent x := by
    change x ∈ (⊥ : Ideal S).radical
    rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    exact hx
  exact hnil.eq_zero

/-- The actual map to the product of component quotients is injective. -/
theorem component_quotient_map_injective :
    Function.Injective (fun x : S =>
      fun p : {p : Ideal S // p ∈ minimalPrimes S} => Ideal.Quotient.mk p.val x) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply eq_zero_of_mem_all_minimalPrimes
  intro p hp
  apply Ideal.Quotient.eq.mp
  exact congrFun hxy ⟨p, hp⟩

/-- A function nonzero on every reduced component is a non-zero-divisor. -/
theorem mul_eq_zero_of_avoids_minimalPrimes (a x : S)
    (ha : ∀ p : Ideal S, p ∈ minimalPrimes S → a ∉ p)
    (hax : a * x = 0) : x = 0 := by
  apply eq_zero_of_mem_all_minimalPrimes
  intro p hp
  have hprime : p.IsPrime := Ideal.minimalPrimes_isPrime hp
  exact (hprime.mem_or_mem_of_mul_eq_zero hax).resolve_left (ha p hp)

end Reduced

section Dominance

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsReduced S]

/-- The local form of dominance on each component: the base ring injects
into every minimal-prime quotient of the total-space ring. -/
def ComponentwiseDominant : Prop :=
  ∀ p : Ideal S, p ∈ minimalPrimes S →
    Function.Injective ((Ideal.Quotient.mk p).comp (algebraMap R S))

theorem torsionfree_of_reduced_componentwise_dominant
    (hdom : ComponentwiseDominant (R := R) (S := S)) : NoZeroSMulDivisors R S := by
  constructor
  intro r x hrx
  by_cases hr : r = 0
  · exact Or.inl hr
  · right
    apply mul_eq_zero_of_avoids_minimalPrimes (algebraMap R S r) x
    · intro p hp hmem
      apply hr
      apply hdom p hp
      change Ideal.Quotient.mk p (algebraMap R S r) =
        Ideal.Quotient.mk p (algebraMap R S 0)
      rw [map_zero, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    · simpa only [Algebra.smul_def] using hrx

end Dominance

section Flat

variable (R M : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M]

/-- Torsion-free modules over a PID are flat, with no finite-generation
assumption on the module. -/
theorem flat_of_torsionfree_pid : Module.Flat R M := by
  apply Module.Flat.of_forall_isTrivialRelation
  intro l f x hrelation
  let N : Submodule R M := Submodule.span R (Set.range x)
  have hN : N.FG := Submodule.fg_span (Set.finite_range x)
  letI : Module.Finite R N := Module.Finite.iff_fg.mpr hN
  letI : Module.Free R N := Module.free_of_finite_type_torsion_free'
  letI : Module.Flat R N := Module.Flat.of_free
  let y : Fin l → N := fun i => ⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hy : ∑ i, f i • y i = 0 := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, y] using hrelation
  obtain ⟨k, a, z, hyz, hfa⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hy
  refine ⟨k, a, (fun j => (z j : M)), ?_, hfa⟩
  intro i
  have h := congrArg (fun q : N => (q : M)) (hyz i)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, y] using h

end Flat

/-- The complete ring-theoretic flatness step of Section 7.2. A reduced
total-space ring whose components dominate a PID base is flat over that base. -/
theorem flat_of_reduced_componentwise_dominant
    (R S : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing S] [Algebra R S] [IsReduced S]
    (hdom : ComponentwiseDominant (R := R) (S := S)) : Module.Flat R S := by
  letI : NoZeroSMulDivisors R S := torsionfree_of_reduced_componentwise_dominant hdom
  exact flat_of_torsionfree_pid R S

end Sheshadri.ConormalFlatness
