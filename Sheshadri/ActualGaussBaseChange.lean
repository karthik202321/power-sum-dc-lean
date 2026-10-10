/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ActualGaussFlatness
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The specialized quotient is the actual affine-line base-change fibre

This identifies `FibreCoordinateRing` with the tensor product of the actual
total coordinate ring and the residue field of the base point. The residue
ring `ℂ[t]/(t-a)` is explicitly equivalent to `ℂ`. Thus the previously
constructed specialized equations and cycles refer to a genuine algebraic
base-change fibre, not an unrelated quotient with the same set of zeros.
-/

noncomputable section
namespace Sheshadri.ActualGaussBaseChange

open MvPolynomial ActualGaussFamily ActualGaussFlatness
open scoped TensorProduct

variable {Z : Type*} [Fintype Z]

def parameterIdeal (t : ℂ) : Ideal (MvPolynomial (TotalCoordinates Unit Z) ℂ) :=
  Ideal.span {X (Sum.inl ()) - C t}

def basePointIdeal (t : ℂ) : Ideal (Polynomial ℂ) :=
  Ideal.span {Polynomial.X - Polynomial.C t}

abbrev Residue (t : ℂ) := Polynomial ℂ ⧸ basePointIdeal t

def residueEquivComplex (t : ℂ) : Residue t ≃+* ℂ :=
  (Polynomial.quotientSpanXSubCAlgEquiv t).toRingEquiv

theorem specialize_surjective (a : Unit → ℂ) :
    Function.Surjective (specialize (Z := Z) a) := by
  have hc : (specialize (Z := Z) a).comp
      (rename (Sum.inr : (Option Z ⊕ Option Z) → TotalCoordinates Unit Z)).toRingHom =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [specialize]
    · intro i
      simp [specialize]
  intro p
  refine ⟨rename Sum.inr p, ?_⟩
  exact RingHom.congr_fun hc p

theorem ker_specialize (t : ℂ) :
    RingHom.ker (specialize (Z := Z) (fun _ : Unit => t)) = parameterIdeal t := by
  let J : Ideal (MvPolynomial (TotalCoordinates Unit Z) ℂ) := parameterIdeal t
  have hgenerator : X (Sum.inl ()) - C t ∈ J := Ideal.subset_span (by simp)
  have hparam : Ideal.Quotient.mk J (X (Sum.inl ())) = Ideal.Quotient.mk J (C t) :=
    Ideal.Quotient.eq.mpr hgenerator
  let back : MvPolynomial (Option Z ⊕ Option Z) ℂ →+*
      (MvPolynomial (TotalCoordinates Unit Z) ℂ ⧸ J) :=
    (Ideal.Quotient.mk J).comp (rename Sum.inr).toRingHom
  have hcomp : back.comp (specialize (fun _ : Unit => t)) = Ideal.Quotient.mk J := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [back, specialize]
    · rintro (⟨⟩ | i)
      · simpa [back, specialize] using hparam.symm
      · simp [back, specialize]
  apply le_antisymm
  · intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← RingHom.congr_fun hcomp p]
    change back (specialize (fun _ : Unit => t) p) = 0
    rw [RingHom.mem_ker.mp hp, map_zero]
  · apply Ideal.span_le.mpr
    intro p hp
    have : p = X (Sum.inl ()) - C t := Set.mem_singleton_iff.mp hp
    rw [this]
    change specialize (fun _ : Unit => t) (X (Sum.inl ()) - C t) = 0
    simp [specialize]

theorem basePointIdeal_map (t : ℂ) :
    Ideal.map (baseMap (Z := Z)) (basePointIdeal t) = parameterIdeal t := by
  simp [basePointIdeal, parameterIdeal, Ideal.map_span, Set.image_singleton,
    baseMap, Polynomial.eval₂_sub]

/-- Quotient by the total equations and the actual parameter equation is
equivalent to quotient by their literal coordinate specializations. -/
def specializedQuotientEquiv
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (t : ℂ) :
    (MvPolynomial (TotalCoordinates Unit Z) ℂ ⧸
      (totalIdeal F U ⊔ parameterIdeal t)) ≃+*
        FibreCoordinateRing F U (fun _ => t) := by
  let f := specialize (Z := Z) (fun _ : Unit => t)
  have hf := specialize_surjective (Z := Z) (fun _ : Unit => t)
  have he : Ideal.comap f (fibreIdeal F U (fun _ => t)) =
      totalIdeal F U ⊔ parameterIdeal t := by
    rw [fibreIdeal, Ideal.comap_map_of_surjective _ hf]
    change totalIdeal F U ⊔ RingHom.ker f = _
    rw [ker_specialize]
  exact RingEquiv.ofBijective
    (Ideal.quotientMap (fibreIdeal F U (fun _ => t)) f he.ge)
    ⟨Ideal.quotientMap_injective' he.le, Ideal.quotientMap_surjective hf⟩

theorem basePointIdeal_map_quotient
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (t : ℂ) :
    Ideal.map (algebraMap (Polynomial ℂ) (CoordinateRing F U)) (basePointIdeal t) =
      Ideal.map (Ideal.Quotient.mk (totalIdeal F U)) (parameterIdeal (Z := Z) t) := by
  change Ideal.map ((Ideal.Quotient.mk (totalIdeal F U)).comp baseMap) _ = _
  rw [← Ideal.map_map, basePointIdeal_map]

/-- The genuine scheme-fibre coordinate ring: tensor base change by the
residue ring of the affine-line parameter equals the specialized quotient. -/
def fibreTensorEquiv
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (t : ℂ) :
    (CoordinateRing F U ⊗[Polynomial ℂ] Residue t) ≃+*
      FibreCoordinateRing F U (fun _ => t) :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    (CoordinateRing F U) (basePointIdeal t)).symm.toRingEquiv |>.trans
      (Ideal.quotEquivOfEq (basePointIdeal_map_quotient F U t)) |>.trans
        (DoubleQuot.quotQuotEquivQuotSup (totalIdeal F U) (parameterIdeal t)) |>.trans
          (specializedQuotientEquiv F U t)

end Sheshadri.ActualGaussBaseChange
