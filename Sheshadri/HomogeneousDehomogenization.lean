/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.HomogeneousPolynomialLift
import Sheshadri.OrdinaryProjectiveHilbert

/-!
# Actual quotient isomorphism for the standard homogeneous chart

The quotient by `x₀-1` is identified with the literal dehomogenized ideal.
This transfers the previously proved homogeneous-chart finiteness theorem
to the actual affine polynomial quotient, preserving nilpotents.
-/

noncomputable section
namespace Sheshadri.HomogeneousDehomogenization

open MvPolynomial HomogeneousDeterminant HomogeneousPolynomialLift

variable {K : Type*} [CommRing K] {n : ℕ}

def rehom : MvPolynomial (Fin n) K →ₐ[K] MvPolynomial (Fin (n+1)) K :=
  aeval (fun i => X i.succ)

@[simp] theorem rehom_C (c : K) : rehom (n := n) (C c) = C c := by simp [rehom]

@[simp] theorem rehom_X (i : Fin n) : rehom (X i : MvPolynomial _ K) = X i.succ := by
  simp [rehom]

@[simp] theorem dehom_rehom (p : MvPolynomial (Fin n) K) : dehom (rehom p) = p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem quotient_rehom_dehom (I : Ideal (MvPolynomial (Fin (n+1)) K))
    (hI : X 0 - 1 ∈ I) (p : MvPolynomial (Fin (n+1)) K) :
    Ideal.Quotient.mk I (rehom (dehom p)) = Ideal.Quotient.mk I p := by
  have hzero : Ideal.Quotient.mk I (X 0) = 1 := by
    have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hI
    simpa only [map_sub, map_one, sub_eq_zero] using hh
  have he : ((Ideal.Quotient.mkₐ K I).comp rehom).comp dehom = Ideal.Quotient.mkₐ K I := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hzero.symm
    · simp
  exact DFunLike.congr_fun he p

def quotientEquiv (I : Ideal (MvPolynomial (Fin (n+1)) K)) (hI : X 0 - 1 ∈ I) :
    (MvPolynomial (Fin (n+1)) K ⧸ I) ≃ₐ[K]
      (MvPolynomial (Fin n) K ⧸ I.map dehom.toRingHom) := by
  let J := I.map dehom.toRingHom
  let a := Ideal.quotientMapₐ J dehom Ideal.le_comap_map
  let ψ := (Ideal.Quotient.mkₐ K I).comp rehom
  have hk : J ≤ RingHom.ker ψ := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change Ideal.Quotient.mk I (rehom (dehom p)) = 0
    rw [quotient_rehom_dehom I hI]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
  let b := Ideal.Quotient.liftₐ J ψ (fun p hp => hk hp)
  apply AlgEquiv.ofAlgHom a b
  · apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro p
    change Ideal.Quotient.mk J (dehom (rehom p)) = Ideal.Quotient.mk J p
    rw [dehom_rehom]
  · apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro p
    exact quotient_rehom_dehom I hI p

theorem chartIdeal_map (I : Ideal (MvPolynomial (Fin (n+1)) K)) :
    (I ⊔ Ideal.span {X 0 - 1}).map dehom.toRingHom =
      I.map dehom.toRingHom := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  change I.map dehom.toRingHom ⊔ Ideal.span {dehom (X 0 - 1)} = _
  rw [map_sub, dehom_X_zero, map_one, sub_self]
  have hz : Ideal.span ({0} : Set (MvPolynomial (Fin n) K)) = ⊥ := by
    apply le_antisymm _ bot_le
    apply Ideal.span_le.mpr
    intro p hp
    simpa only [Set.mem_singleton_iff.mp hp] using
      (Ideal.zero_mem (⊥ : Ideal (MvPolynomial (Fin n) K)))
  rw [hz]
  exact sup_bot_eq _

def chartEquiv (I : Ideal (MvPolynomial (Fin (n+1)) K)) :
    (MvPolynomial (Fin (n+1)) K ⧸ (I ⊔ Ideal.span {X 0 - 1})) ≃ₐ[K]
      (MvPolynomial (Fin n) K ⧸ I.map dehom.toRingHom) :=
  (quotientEquiv (I ⊔ Ideal.span {X 0 - 1}) (show X 0 - 1 ∈ I ⊔ Ideal.span {X 0 - 1} from
    (show Ideal.span {X 0 - 1} ≤ I ⊔ Ideal.span {X 0 - 1} from le_sup_right)
      (Ideal.subset_span (Set.mem_singleton _)))).trans
    (Ideal.quotientEquivAlgOfEq K (chartIdeal_map I))

section Field
variable {L : Type*} [Field L]
open FlatGradedHilbert GenericHomogeneousSections

theorem affineQuotient_finite (I : Ideal (MvPolynomial (Fin (n+1)) L))
    (hI : ∀ d f, f ∈ I → homogeneousComponent d f ∈ I)
    (D : ℕ) (hconst : ∃ N : ℕ, ∀ k > N,
      Module.finrank L (coordinatePiece (Fin (n+1)) L I k) = D)
    (hreg : FilterRegular I (X 0) (isHomogeneous_X L 0)) :
    Module.Finite L (MvPolynomial (Fin n) L ⧸ I.map dehom.toRingHom) := by
  letI : Module.Finite L (MvPolynomial (Fin (n+1)) L ⧸ (I ⊔ Ideal.span {X 0 - 1})) :=
    OrdinaryProjectiveHilbert.chartAlgebra_finite I (X 0) hI
      (isHomogeneous_X L 0) D hconst hreg
  exact Module.Finite.of_surjective (chartEquiv I).toLinearMap (chartEquiv I).surjective

theorem affineQuotient_finrank (I : Ideal (MvPolynomial (Fin (n+1)) L))
    (hI : ∀ d f, f ∈ I → homogeneousComponent d f ∈ I)
    (D : ℕ) (hconst : ∃ N : ℕ, ∀ k > N,
      Module.finrank L (coordinatePiece (Fin (n+1)) L I k) = D)
    (hreg : FilterRegular I (X 0) (isHomogeneous_X L 0)) :
    Module.finrank L (MvPolynomial (Fin n) L ⧸ I.map dehom.toRingHom) = D := by
  rw [← (chartEquiv I).toLinearEquiv.finrank_eq]
  exact OrdinaryProjectiveHilbert.chartAlgebra_finrank I (X 0) hI
    (isHomogeneous_X L 0) D hconst hreg

end Field
end Sheshadri.HomogeneousDehomogenization
