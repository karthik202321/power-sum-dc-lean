/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.SingularRootPersistence
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Isolated local multiplicities survive contraction over an actual DVR

The residue map, uniformizer, equations and fraction field are literal data.
The only geometric assumption is that the selected zero of the square special
system has an Artinian local intersection algebra. Regularity, cancellation
of every generic denominator, and preservation of the full local algebra are
proved; no reducedness or persistence certificate is assumed.
-/

noncomputable section
namespace Sheshadri.DVRRootPersistence
open MvPolynomial BezoutHorizontalFamily GeneralGradedBaseChange
open CoordinatePowerRegular IsolatedCompleteIntersection RingTheory.Sequence
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

section SpecialFiber
variable {D k σ : Type*} [CommRing D] [Field k]
    (ε : D →+* k) (hε : Function.Surjective ε) (π : D)
    (hker : RingHom.ker ε = Ideal.span {π})

def specialize : MvPolynomial σ D →+* MvPolynomial σ k := MvPolynomial.map ε

include hε in
theorem specialize_surjective : Function.Surjective (specialize (σ := σ) ε) :=
  MvPolynomial.map_surjective ε hε

include hker in
theorem specialize_ker : RingHom.ker (specialize (σ := σ) ε) = Ideal.span {C π} := by
  ext F
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact (MvPolynomial.C_dvd_iff_map_hom_eq_zero ε π (fun q => by
    change q ∈ RingHom.ker ε ↔ _
    rw [hker, Ideal.mem_span_singleton]) F).symm

def totalPointIdeal (p : σ → k) : Ideal (MvPolynomial σ D) :=
  (pointIdeal p).comap (specialize ε)

instance totalPointIdeal_isPrime (p : σ → k) : (totalPointIdeal ε p).IsPrime :=
  Ideal.comap_isPrime _ _

abbrev TotalLocalRing (p : σ → k) := Localization.AtPrime (totalPointIdeal ε p)

def localParameter (p : σ → k) : TotalLocalRing ε p :=
  algebraMap (MvPolynomial σ D) (TotalLocalRing ε p) (C π)

include hker in
theorem specialize_ker_map (p : σ → k) :
    (RingHom.ker (specialize (σ := σ) ε)).map
      (algebraMap _ (TotalLocalRing ε p)) = Ideal.span {localParameter ε π p} := by
  rw [specialize_ker ε π hker, Ideal.map_span]
  simp only [Set.image_singleton, localParameter]

def specialFiberEquiv (p : σ → k) :
    (TotalLocalRing ε p ⧸ Ideal.span {localParameter ε π p}) ≃+* PointLocalRing p :=
  (Ideal.quotEquivOfEq (specialize_ker_map ε π hker p).symm).trans
    (SingularSpecialFiber.localizationQuotientEquiv (totalPointIdeal ε p)
      (pointIdeal p) (specialize ε) (specialize_surjective ε hε) rfl)

@[simp] theorem specialFiberEquiv_mk (p : σ → k) (F : MvPolynomial σ D) :
    specialFiberEquiv ε hε π hker p
      (Ideal.Quotient.mk _ (algebraMap _ (TotalLocalRing ε p) F)) =
      algebraMap _ (PointLocalRing p) (specialize ε F) := by
  change Localization.localRingHom (totalPointIdeal ε p) (pointIdeal p)
    (specialize ε) rfl (algebraMap _ (TotalLocalRing ε p) F) = _
  exact Localization.localRingHom_to_map _ _ _ _ F

end SpecialFiber

section Contraction
variable {D L σ A : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Field L] [Algebra D L] [IsFractionRing D L]
    [CommRing A] [IsLocalRing A]

/-- All nonzero DVR scalars act injectively if the actual uniformizer does. -/
theorem mapped_scalar_regular (g : D →+* A) (π : D) (hπ : Irreducible π)
    (hreg : IsLeftRegular (g π)) (r : D) (hr : r ≠ 0) : IsLeftRegular (g r) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hπ
  rw [map_mul, map_pow]
  exact ((u.isUnit.map g).isRegular.left).mul (hreg.pow n)

/-- Generic contraction kills no additional element in a local quotient
where the uniformizer is regular, including its nilpotent elements. -/
theorem contractedIdeal_le_ker (I : Ideal (MvPolynomial σ D))
    (g : MvPolynomial σ D →+* A) (hI : I ≤ RingHom.ker g)
    (π : D) (hπ : Irreducible π) (hreg : IsLeftRegular (g (C π))) :
    contractedIdeal (R := D) (extendedIdeal (K := L) I) ≤ RingHom.ker g := by
  intro p hp
  obtain ⟨r, hr, hrp⟩ := (mem_contracted_extension_iff (K := L) I p).mp hp
  have he : g (C r) * g p = 0 := by
    simpa only [RingHom.mem_ker, map_mul] using hI hrp
  exact (mapped_scalar_regular (g.comp C) π hπ hreg r hr).mul_left_eq_zero_iff.mp he

theorem map_contractedIdeal_eq (I : Ideal (MvPolynomial σ D))
    (φ : MvPolynomial σ D →+* A) (hproper : I.map φ ≠ ⊤)
    (π : D) (hπ : Irreducible π)
    (hreg : IsSMulRegular (A ⧸ I.map φ) (φ (C π))) :
    (contractedIdeal (R := D) (extendedIdeal (K := L) I)).map φ = I.map φ := by
  let Q := A ⧸ I.map φ
  letI : Nontrivial Q := Ideal.Quotient.nontrivial hproper
  letI : IsLocalRing Q := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk (I.map φ)) Ideal.Quotient.mk_surjective
  let g : MvPolynomial σ D →+* Q := (Ideal.Quotient.mk (I.map φ)).comp φ
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    have hkernel : I ≤ RingHom.ker g := by
      intro p hp
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ hp)
    have hrq : IsLeftRegular (g (C π)) := hreg
    intro p hp
    change φ p ∈ I.map φ
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact contractedIdeal_le_ker (L := L) I g hkernel π hπ hrq hp
  · exact Ideal.map_mono (originalIdeal_le_contraction I)

theorem localization_parameter_regular (P : Ideal (MvPolynomial σ D)) [P.IsPrime]
    (π : D) (hπ : π ≠ 0) :
    IsSMulRegular (Localization.AtPrime P)
      ((algebraMap (MvPolynomial σ D) (Localization.AtPrime P)) (C π)) := by
  apply IsLeftRegular.isSMulRegular
  apply (isRegular_of_ne_zero ?_).left
  apply fun h => (C_ne_zero.mpr hπ : (C π : MvPolynomial σ D) ≠ 0)
    ((IsLocalization.injective (Localization.AtPrime P)
      P.primeCompl_le_nonZeroDivisors) (h.trans (map_zero _).symm))

theorem localization_contractedIdeal_eq_of_special_regular [Finite σ]
    (fs : List (MvPolynomial σ D)) (P : Ideal (MvPolynomial σ D)) [P.IsPrime]
    (hIP : Ideal.ofList fs ≤ P) (π : D) (hπ : Irreducible π)
    (hf : IsRegular ((Localization.AtPrime P) ⧸ Ideal.span {
        (algebraMap (MvPolynomial σ D) (Localization.AtPrime P)) (C π)})
      (fs.map (algebraMap (MvPolynomial σ D) (Localization.AtPrime P)))) :
    (contractedIdeal (R := D) (extendedIdeal (K := L) (Ideal.ofList fs))).map
        (algebraMap _ (Localization.AtPrime P)) =
      (Ideal.ofList fs).map (algebraMap _ (Localization.AtPrime P)) := by
  letI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  apply map_contractedIdeal_eq (Ideal.ofList fs) (algebraMap _ (Localization.AtPrime P))
  · have hle := Ideal.map_mono (f := algebraMap _ (Localization.AtPrime P)) hIP
    rw [Localization.AtPrime.map_eq_maximalIdeal] at hle
    exact ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) hle
  · exact hπ
  · rw [Ideal.map_ofList]
    exact SingularDeformation.parameter_regular_on_equation_quotient _ _
      (localization_parameter_regular P π hπ.ne_zero) hf

end Contraction

section General
variable {σ k D L : Type*} [Fintype σ] [Field k] [Infinite k]
    [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Field L] [Algebra D L] [IsFractionRing D L]
    (ε : D →+* k) (hε : Function.Surjective ε) (π : D)
    (hπ : Irreducible π) (hker : RingHom.ker ε = Ideal.span {π})

def specialIdeal (fs : List (MvPolynomial σ D)) :
    Ideal (MvPolynomial σ k) := Ideal.ofList (fs.map (specialize ε))

omit [Fintype σ] [Infinite k] in
theorem specialIdeal_le_pointIdeal (fs : List (MvPolynomial σ D))
    (p : σ → k) (hz : ∀ r ∈ fs, eval p ((specialize ε) r) = 0) :
    specialIdeal ε fs ≤ IsolatedLocalMultiplicity.pointIdeal p := by
  apply Ideal.span_le.mpr
  rintro r hr
  change r ∈ fs.map (specialize ε) at hr
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
  exact hz a ha

include hε hker in
/-- The original special equations form a regular sequence in the actual
localized special fibre, derived from isolated square-system Artinianity. -/
theorem special_equations_regular
    (fs : List (MvPolynomial σ D)) (p : σ → k)
    (hsquare : fs.length = Fintype.card σ)
    (hz : ∀ r ∈ fs, eval p (specialize ε r) = 0)
    [IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing
      (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz))] :
    IsRegular (TotalLocalRing ε p ⧸ Ideal.span {localParameter ε π p})
      (fs.map (algebraMap _ (TotalLocalRing ε p))) := by
  let S := MvPolynomial σ D
  let T := TotalLocalRing ε p
  letI : IsArtinianRing (PointLocalRing p ⧸ localEquationIdeal p (fs.map (specialize ε))) := by
    change IsArtinianRing (PointLocalRing p ⧸
      Ideal.ofList ((fs.map (specialize ε)).map (algebraMap _ (PointLocalRing p))))
    rw [← Ideal.map_ofList]
    exact SingularSpecialFiber.local_equation_quotient_artinian (specialIdeal ε fs) p
      (specialIdeal_le_pointIdeal ε fs p hz)
  have hreg := isolated_square_regular p (fs.map (specialize ε))
    (by simpa using hsquare) (by
      intro r hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact hz a ha)
  let e := specialFiberEquiv ε hε π hker p
  have hrelation : List.Forall₂
      (fun (r : T) (s : PointLocalRing p) => ∀ x, e (r • x) = s • e x)
      (fs.map (algebraMap S T))
      (fs.map (fun r => algebraMap (MvPolynomial σ k) (PointLocalRing p) ((specialize ε) r))) := by
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r hr x
    change e (Ideal.Quotient.mk _ (algebraMap S T r) * x) = _ * e x
    rw [map_mul, specialFiberEquiv_mk]
  have hf : IsRegular (T ⧸ Ideal.span {localParameter ε π p}) (fs.map (algebraMap S T)) :=
    e.toAddEquiv.isRegular_congr hrelation |>.mpr (by
      simpa only [localEquations, List.map_map, Function.comp_def] using hreg)
  exact hf


include hε hπ hker in
/-- The actual uniformizer is regular in the actual total local equation
quotient. All its special-fibre regularity is derived from isolatedness. -/
theorem local_equations_parameter_regular
    (fs : List (MvPolynomial σ D)) (p : σ → k)
    (hsquare : fs.length = Fintype.card σ)
    (hz : ∀ r ∈ fs, eval p (specialize ε r) = 0)
    [IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing
      (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz))] :
    IsSMulRegular (TotalLocalRing ε p ⧸
      (Ideal.ofList fs).map (algebraMap _ (TotalLocalRing ε p))) (localParameter ε π p) := by
  letI : IsNoetherianRing (TotalLocalRing ε p) :=
    IsLocalization.isNoetherianRing (totalPointIdeal ε p).primeCompl _ inferInstance
  rw [Ideal.map_ofList]
  exact SingularDeformation.parameter_regular_on_equation_quotient _ _
    (localization_parameter_regular (totalPointIdeal ε p) π hπ.ne_zero)
    (special_equations_regular ε hε π hker fs p hsquare hz)

include hε hπ hker in
/-- Every generic-contracted equation annihilates the original complete
local intersection algebra, rather than only its residue field. -/
theorem family_contraction_annihilates_local
    (fs : List (MvPolynomial σ D)) (p : σ → k)
    (hsquare : fs.length = Fintype.card σ)
    (hz : ∀ r ∈ fs, eval p ((specialize ε) r) = 0)
    [IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing
      (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz))]
    (q : MvPolynomial σ D)
    (hq : q ∈ contractedIdeal (extendedIdeal (K := L) (Ideal.ofList fs))) :
    IsolatedLocalMultiplicity.localPolynomialMap
      (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz) ((specialize ε) q) = 0 := by
  let S := MvPolynomial σ D
  let T := TotalLocalRing ε p
  let B := IsolatedLocalMultiplicity.LocalIntersectionRing
    (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz)
  letI : IsArtinianRing (PointLocalRing p ⧸ localEquationIdeal p (fs.map (specialize ε))) := by
    change IsArtinianRing (PointLocalRing p ⧸
      Ideal.ofList ((fs.map (specialize ε)).map (algebraMap _ (PointLocalRing p))))
    rw [← Ideal.map_ofList]
    exact SingularSpecialFiber.local_equation_quotient_artinian (specialIdeal ε fs) p
      (specialIdeal_le_pointIdeal ε fs p hz)
  have hreg := isolated_square_regular p (fs.map (specialize ε))
    (by simpa using hsquare) (by
      intro r hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact hz a ha)
  let e := specialFiberEquiv ε hε π hker p
  have hrelation : List.Forall₂
      (fun (r : T) (s : PointLocalRing p) => ∀ x, e (r • x) = s • e x)
      (fs.map (algebraMap S T))
      (fs.map (fun r => algebraMap (MvPolynomial σ k) (PointLocalRing p) ((specialize ε) r))) := by
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r hr x
    change e (Ideal.Quotient.mk _ (algebraMap S T r) * x) = _ * e x
    rw [map_mul, specialFiberEquiv_mk]
  have hf : IsRegular (T ⧸ Ideal.span {localParameter ε π p}) (fs.map (algebraMap S T)) :=
    e.toAddEquiv.isRegular_congr hrelation |>.mpr (by
      simpa only [localEquations, List.map_map, Function.comp_def] using hreg)
  have hIP : Ideal.ofList fs ≤ totalPointIdeal ε p := by
    apply Ideal.span_le.mpr
    intro r hr
    exact hz r hr
  have heq := localization_contractedIdeal_eq_of_special_regular
    (L := L) fs (totalPointIdeal ε p) hIP π hπ hf
  let P := IsolatedLocalMultiplicity.quotientPointIdeal
    (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz)
  let g : S →+* (MvPolynomial σ k ⧸ specialIdeal ε fs) :=
    (Ideal.Quotient.mk (specialIdeal ε fs)).comp (specialize ε)
  have hP : totalPointIdeal ε p = P.comap g := by ext r; rfl
  let ψ : T →+* B := Localization.localRingHom (totalPointIdeal ε p) P g hP
  have hψ (r : S) : ψ (algebraMap S T r) =
      IsolatedLocalMultiplicity.localPolynomialMap
        (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz) ((specialize ε) r) :=
    Localization.localRingHom_to_map _ _ _ _ r
  have hkill : (Ideal.ofList fs).map (algebraMap S T) ≤ RingHom.ker ψ := by
    apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    intro r hr
    change ψ (algebraMap S T r) = 0
    rw [hψ]
    change algebraMap _ _ (Ideal.Quotient.mk (specialIdeal ε fs) ((specialize ε) r)) = 0
    have hm : (specialize ε) r ∈ specialIdeal ε fs :=
      Ideal.subset_span (show (specialize ε) r ∈ {x | x ∈ fs.map (specialize ε)} from
        List.mem_map.mpr ⟨r,hr,rfl⟩)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]
  have hloc : algebraMap S T q ∈ (Ideal.ofList fs).map (algebraMap S T) := by
    rw [← heq]
    exact Ideal.mem_map_of_mem _ hq
  have hv : ψ (algebraMap S T q) = 0 := hkill hloc
  rwa [hψ] at hv


include hε hπ hker in
/-- Generic contraction has exactly the same specialized ideal in the
original polynomial local ring. This is scheme-theoretic equality, including
all singular and nonreduced multiplicity information. -/
theorem specialized_contractedIdeal_localization_eq
    (fs : List (MvPolynomial σ D)) (p : σ → k)
    (hsquare : fs.length = Fintype.card σ)
    (hz : ∀ r ∈ fs, eval p (specialize ε r) = 0)
    [IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing
      (specialIdeal ε fs) p (specialIdeal_le_pointIdeal ε fs p hz))] :
    ((contractedIdeal (R := D) (extendedIdeal (K := L) (Ideal.ofList fs))).map
      (specialize ε)).map (algebraMap _ (PointLocalRing p)) =
    (specialIdeal ε fs).map (algebraMap _ (PointLocalRing p)) := by
  apply le_antisymm
  · rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro q hq
    change algebraMap _ (PointLocalRing p) (specialize ε q) ∈
      (specialIdeal ε fs).map (algebraMap _ (PointLocalRing p))
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (SingularSpecialFiber.localEquationQuotientEquiv (specialIdeal ε fs) p
      (specialIdeal_le_pointIdeal ε fs p hz)).injective
    rw [map_zero, SingularSpecialFiber.localEquationQuotientEquiv_mk]
    exact family_contraction_annihilates_local ε hε π hπ hker fs p hsquare hz q hq
  · apply Ideal.map_mono
    have h : (Ideal.ofList fs).map (specialize ε) ≤
        (contractedIdeal (R := D) (extendedIdeal (K := L) (Ideal.ofList fs))).map
          (specialize ε) := Ideal.map_mono (originalIdeal_le_contraction _)
    simpa only [Ideal.map_ofList, specialIdeal] using h


end General

end Sheshadri.DVRRootPersistence
