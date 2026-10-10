/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SingularSpecialFiber
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# The actual affine primal chart of an incidence polynomial quotient

Setting the first primal coordinate to one and regrouping the other primal
variables into the coefficient ring gives an explicit quotient isomorphism.
The equation ideal is transported by its literal polynomial map, with no
radicalization. This applies to full or reduced kernel incidence systems.
-/

noncomputable section
namespace Sheshadri.AffineIncidenceCharts
open MvPolynomial
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

variable {K T : Type*} [CommRing K] {n : ℕ}

abbrev HomogeneousRing (n : ℕ) (T K : Type*) [CommRing K] :=
  MvPolynomial (Fin (n+1) ⊕ T) K
abbrev AffineRing (n : ℕ) (T K : Type*) [CommRing K] :=
  MvPolynomial T (MvPolynomial (Fin n) K)

def dehom : HomogeneousRing n T K →ₐ[K] AffineRing n T K :=
  aeval (Sum.elim (Fin.cases 1 (fun i => C (MvPolynomial.X i))) MvPolynomial.X)

def rehom : AffineRing n T K →ₐ[K] HomogeneousRing n T K :=
  { eval₂Hom (rename (fun i : Fin n => (Sum.inl i.succ : Fin (n+1) ⊕ T))).toRingHom
      (fun t => MvPolynomial.X (Sum.inr t)) with
    commutes' := fun r => by simp [algebraMap_eq, IsScalarTower.algebraMap_apply K
      (MvPolynomial (Fin n) K) (AffineRing n T K)] }

@[simp] theorem dehom_C (r : K) : dehom (n := n) (T := T) (C r) = C (C r) := by
  simp [dehom, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K), algebraMap_eq]
@[simp] theorem dehom_X_zero : dehom (n := n) (T := T) (K := K) (MvPolynomial.X (.inl 0)) = 1 := by
  simp [dehom]
@[simp] theorem dehom_X_succ (i : Fin n) :
    dehom (T := T) (K := K) (MvPolynomial.X (.inl i.succ)) = C (MvPolynomial.X i) := by
  simp [dehom]
@[simp] theorem dehom_X_extra (t : T) :
    dehom (n := n) (K := K) (MvPolynomial.X (.inr t)) = MvPolynomial.X t := by
  simp [dehom]

@[simp] theorem rehom_C (q : MvPolynomial (Fin n) K) :
    rehom (T := T) (C q) = rename (fun i => (Sum.inl i.succ : Fin (n+1) ⊕ T)) q := by
  simp [rehom]
@[simp] theorem rehom_X (t : T) :
    rehom (n := n) (K := K) (MvPolynomial.X t) = MvPolynomial.X (.inr t) := by
  simp [rehom]

theorem dehom_rename (q : MvPolynomial (Fin n) K) :
    dehom (rename (fun i => (Sum.inl i.succ : Fin (n+1) ⊕ T)) q) = C q := by
  induction q using MvPolynomial.induction_on with
  | C r => simp
  | add q r hq hr => simp [hq,hr]
  | mul_X q i hq => simp [hq]

@[simp] theorem dehom_rehom (q : AffineRing n T K) : dehom (rehom q) = q := by
  induction q using MvPolynomial.induction_on with
  | C r => simp [dehom_rename]
  | add q r hq hr => simp [hq,hr]
  | mul_X q i hq => simp [hq]

theorem dehom_surjective : Function.Surjective (dehom (n := n) (T := T) (K := K)) :=
  fun q => ⟨rehom q, dehom_rehom q⟩

theorem quotient_rehom_dehom (I : Ideal (HomogeneousRing n T K))
    (hI : MvPolynomial.X (.inl 0) - 1 ∈ I) (q : HomogeneousRing n T K) :
    Ideal.Quotient.mk I (rehom (dehom q)) = Ideal.Quotient.mk I q := by
  have hzero : Ideal.Quotient.mk I (MvPolynomial.X (.inl 0)) = 1 := by
    have hh := Ideal.Quotient.eq_zero_iff_mem.mpr hI
    simpa only [map_sub, map_one, sub_eq_zero] using hh
  have he : ((Ideal.Quotient.mkₐ K I).comp rehom).comp dehom = Ideal.Quotient.mkₐ K I := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with i | t
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hzero.symm
      · simp
    · simp
  exact DFunLike.congr_fun he q

def quotientEquiv (I : Ideal (HomogeneousRing n T K))
    (hI : MvPolynomial.X (.inl 0) - 1 ∈ I) :
    (HomogeneousRing n T K ⧸ I) ≃ₐ[K]
      (AffineRing n T K ⧸ I.map dehom.toRingHom) := by
  let J := I.map dehom.toRingHom
  let a := Ideal.quotientMapₐ J dehom Ideal.le_comap_map
  let ψ := (Ideal.Quotient.mkₐ K I).comp rehom
  have hk : J ≤ RingHom.ker ψ := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro q hq
    change Ideal.Quotient.mk I (rehom (dehom q)) = 0
    rw [quotient_rehom_dehom I hI]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hq
  let b := Ideal.Quotient.liftₐ J ψ (fun q hq => hk hq)
  apply AlgEquiv.ofAlgHom a b
  · apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro q
    change Ideal.Quotient.mk J (dehom (rehom q)) = Ideal.Quotient.mk J q
    rw [dehom_rehom]
  · apply Ideal.Quotient.algHom_ext
    apply AlgHom.ext
    intro q
    exact quotient_rehom_dehom I hI q

@[simp] theorem quotientEquiv_mk (I : Ideal (HomogeneousRing n T K))
    (hI : MvPolynomial.X (.inl 0) - 1 ∈ I) (q : HomogeneousRing n T K) :
    quotientEquiv I hI (Ideal.Quotient.mk I q) =
      Ideal.Quotient.mk (I.map dehom.toRingHom) (dehom q) := rfl

end Sheshadri.AffineIncidenceCharts
