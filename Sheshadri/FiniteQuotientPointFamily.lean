/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ArtinianLocalDecomposition
import Sheshadri.IsolatedLocalMultiplicity

/-!
# The complete actual rational-point family of a finite equation quotient

For a finite quotient of a polynomial algebra over an algebraically closed
field, its maximal ideals construct actual coordinate points. This gives all
zeros, distinguishes them, identifies their literal localized equation rings,
and sums their scheme-theoretic lengths. No chosen-root or completeness
certificate is assumed.
-/

noncomputable section
namespace Sheshadri.FiniteQuotientPointFamily
open MvPolynomial IsolatedLocalMultiplicity ArtinianLocalDecomposition

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000

variable {σ K : Type*} [Field K] [IsAlgClosed K]
variable (I : Ideal (MvPolynomial σ K)) [Module.Finite K (EquationQuotient I)]

def residue (P : MaximalSpectrum (EquationQuotient I)) : EquationQuotient I →ₐ[K] K :=
  (finiteLocalResidue K (Localization.AtPrime P.asIdeal)).comp
    (IsScalarTower.toAlgHom K (EquationQuotient I) (Localization.AtPrime P.asIdeal))

theorem residue_kernel (P : MaximalSpectrum (EquationQuotient I)) :
    RingHom.ker (residue I P) = P.asIdeal := by
  change RingHom.ker ((finiteLocalResidue K (Localization.AtPrime P.asIdeal)).toRingHom.comp
    (algebraMap (EquationQuotient I) (Localization.AtPrime P.asIdeal))) = P.asIdeal
  change (RingHom.ker (finiteLocalResidue K (Localization.AtPrime P.asIdeal))).comap
    (algebraMap (EquationQuotient I) (Localization.AtPrime P.asIdeal)) = P.asIdeal
  have hker : RingHom.ker (finiteLocalResidue K (Localization.AtPrime P.asIdeal)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P.asIdeal) :=
    IsLocalRing.ker_eq_maximalIdeal (finiteLocalResidue K (Localization.AtPrime P.asIdeal)).toRingHom
      (LocalLengthDimension.residue_surjective (finiteLocalResidue K (Localization.AtPrime P.asIdeal)))
  rw [hker]
  exact Localization.AtPrime.comap_maximalIdeal

def point (P : MaximalSpectrum (EquationQuotient I)) : σ → K :=
  fun i => residue I P (Ideal.Quotient.mk I (X i))

theorem residue_comp_quotient (P : MaximalSpectrum (EquationQuotient I)) :
    (residue I P).comp (Ideal.Quotient.mkₐ K I) = aeval (point I P) := by
  ext i
  simp [point]

@[simp] theorem residue_mk (P : MaximalSpectrum (EquationQuotient I)) (f : MvPolynomial σ K) :
    residue I P (Ideal.Quotient.mk I f) = eval (point I P) f :=
  DFunLike.congr_fun (residue_comp_quotient I P) f

theorem point_vanishes (P : MaximalSpectrum (EquationQuotient I)) : I ≤ pointIdeal (point I P) := by
  intro f hf
  change eval (point I P) f = 0
  rw [← residue_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]

theorem pointIdeal_eq_comap (P : MaximalSpectrum (EquationQuotient I)) :
    pointIdeal (point I P) = P.asIdeal.comap (Ideal.Quotient.mk I) := by
  rw [← residue_kernel I P]
  ext f
  change eval (point I P) f = 0 ↔ residue I P (Ideal.Quotient.mk I f) = 0
  rw [residue_mk]

theorem quotientEvaluation_eq_residue (P : MaximalSpectrum (EquationQuotient I)) :
    quotientEvaluation I (point I P) (point_vanishes I P) = residue I P := by
  ext x
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact (residue_mk I P f).symm

theorem quotientPointIdeal_eq (P : MaximalSpectrum (EquationQuotient I)) :
    quotientPointIdeal I (point I P) (point_vanishes I P) = P.asIdeal := by
  rw [quotientPointIdeal, quotientEvaluation_eq_residue, residue_kernel]

theorem point_injective : Function.Injective (point I) := by
  intro P Q hpq
  apply MaximalSpectrum.ext
  apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) (Ideal.Quotient.mk_surjective)
  rw [← pointIdeal_eq_comap I P, ← pointIdeal_eq_comap I Q, hpq]

/-- Every actual zero is among the constructed maximal-spectrum points. -/
theorem point_complete (p : σ → K) (hp : I ≤ pointIdeal p) :
    ∃ P : MaximalSpectrum (EquationQuotient I), point I P = p := by
  let P : MaximalSpectrum (EquationQuotient I) :=
    ⟨quotientPointIdeal I p hp, inferInstance⟩
  refine ⟨P, pointIdeal_injective ?_⟩
  rw [pointIdeal_eq_comap]
  ext f
  rfl

def pointEquiv : MaximalSpectrum (EquationQuotient I) ≃ {p : σ → K // I ≤ pointIdeal p} :=
  Equiv.ofBijective (fun P => ⟨point I P, point_vanishes I P⟩) ⟨
    fun _ _ h => point_injective I (congrArg Subtype.val h), by
      rintro ⟨p, hp⟩
      obtain ⟨P, hP⟩ := point_complete I p hp
      exact ⟨P, Subtype.ext hP⟩⟩

theorem zero_set_finite : Finite {p : σ → K // I ≤ pointIdeal p} := by
  letI : IsArtinianRing (EquationQuotient I) := IsArtinianRing.of_finite K _
  exact Finite.of_equiv (MaximalSpectrum (EquationQuotient I)) (pointEquiv I)

def localPointEquiv (P : MaximalSpectrum (EquationQuotient I)) :
    Localization.AtPrime P.asIdeal ≃ₐ[K]
      LocalIntersectionRing I (point I P) (point_vanishes I P) := by
  let A := LocalIntersectionRing I (point I P) (point_vanishes I P)
  have hcomp : (quotientPointIdeal I (point I P) (point_vanishes I P)).primeCompl =
      P.asIdeal.primeCompl := by
    ext x
    change x ∉ quotientPointIdeal I (point I P) (point_vanishes I P) ↔ x ∉ P.asIdeal
    rw [quotientPointIdeal_eq]
  letI : IsLocalization P.asIdeal.primeCompl A := by
    rw [← hcomp]
    infer_instance
  exact (IsLocalization.algEquiv P.asIdeal.primeCompl
    (Localization.AtPrime P.asIdeal) A).restrictScalars K

instance point_local_artinian (P : MaximalSpectrum (EquationQuotient I)) :
    IsArtinianRing (LocalIntersectionRing I (point I P) (point_vanishes I P)) := by
  letI : IsArtinianRing (EquationQuotient I) := IsArtinianRing.of_finite K _
  infer_instance

theorem point_local_length (P : MaximalSpectrum (EquationQuotient I)) :
    Module.length (Localization.AtPrime P.asIdeal) (Localization.AtPrime P.asIdeal) =
      multiplicity I (point I P) (point_vanishes I P) := by
  rw [finiteLocal_length_eq_finrank K]
  change (Module.finrank K (Localization.AtPrime P.asIdeal) : ℕ∞) =
    Module.length (LocalIntersectionRing I (point I P) (point_vanishes I P))
      (LocalIntersectionRing I (point I P) (point_vanishes I P))
  letI : Module.Finite K (LocalIntersectionRing I (point I P) (point_vanishes I P)) :=
    Module.Finite.of_surjective (localPointEquiv I P).toLinearMap (localPointEquiv I P).surjective
  rw [finiteLocal_length_eq_finrank K, (localPointEquiv I P).toLinearEquiv.finrank_eq]

theorem finrank_eq_sum_point_multiplicity [Fintype (MaximalSpectrum (EquationQuotient I))] :
    (Module.finrank K (EquationQuotient I) : ℕ∞) =
      ∑ P : MaximalSpectrum (EquationQuotient I), multiplicity I (point I P) (point_vanishes I P) := by
  rw [finrank_eq_sum_local_length K (EquationQuotient I)]
  exact Finset.sum_congr rfl (fun P _ => point_local_length I P)

/-- Dimension is the sum of multiplicities over the entire actual affine
zero set. Both completeness of the point family and finiteness are proved. -/
theorem finrank_eq_finsum_zero_multiplicity :
    (Module.finrank K (EquationQuotient I) : ℕ∞) =
      ∑ᶠ p : {p : σ → K // I ≤ pointIdeal p}, multiplicity I p.val p.property := by
  letI : IsArtinianRing (EquationQuotient I) := IsArtinianRing.of_finite K _
  letI := Fintype.ofFinite (MaximalSpectrum (EquationQuotient I))
  rw [finrank_eq_sum_point_multiplicity I]
  rw [← finsum_comp_equiv (pointEquiv I), finsum_eq_sum_of_fintype]
  rfl

end Sheshadri.FiniteQuotientPointFamily
