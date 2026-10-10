/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.DVRRootPersistence
import Sheshadri.DeterminantDvrFamily
import Sheshadri.ConormalGaussSection

/-!
# The actual Gauss-polar section over the constructed border DVR

The special equations are literally the already constructed finite Fermat
section. Their generic equations are the derivative-polar equations of the
actual determinant polynomial. No family, length or persistence certificate
is introduced.
-/
noncomputable section
namespace Sheshadri.DVRGaussSection
open MvPolynomial PolynomialModel ConormalGaussSection
open SmoothGaussPolars SmoothGaussDegree SmoothGaussSectionLength
open HomogeneousQuotientExact
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section Equations
variable {σ R S : Type*} [Fintype σ] [CommRing R] [CommRing S]

def relativePolar (f : MvPolynomial σ R) (ell : σ → R) : MvPolynomial σ R :=
  ∑ i, C (ell i) * pderiv i f

def relativeLinear (a : σ → R) : MvPolynomial σ R := ∑ i, C (a i) * X i

def equations (f : MvPolynomial σ R) (ell : ℕ → σ → R) (r : ℕ) (a : σ → R) :
    List (MvPolynomial σ R) :=
  (f :: (List.range r).map (fun j => relativePolar f (ell j))) ++ [relativeLinear a - 1]

@[simp] theorem equations_length (f : MvPolynomial σ R) (ell : ℕ → σ → R)
    (r : ℕ) (a : σ → R) : (equations f ell r a).length = r+2 := by
  simp [equations]

@[simp] theorem map_relativePolar (φ : R →+* S) (f : MvPolynomial σ R)
    (ell : σ → R) :
    MvPolynomial.map φ (relativePolar f ell) =
      relativePolar (MvPolynomial.map φ f) (fun i => φ (ell i)) := by
  simp only [relativePolar, map_sum, map_mul, MvPolynomial.map_C, ← pderiv_map]

@[simp] theorem map_relativeLinear (φ : R →+* S) (a : σ → R) :
    MvPolynomial.map φ (relativeLinear a) = relativeLinear (fun i => φ (a i)) := by
  simp [relativeLinear]

@[simp] theorem map_equations (φ : R →+* S) (f : MvPolynomial σ R)
    (ell : ℕ → σ → R) (r : ℕ) (a : σ → R) :
    (equations f ell r a).map (MvPolynomial.map φ) =
      equations (MvPolynomial.map φ f) (fun j i => φ (ell j i)) r (fun i => φ (a i)) := by
  simp [equations, List.map_map, Function.comp_def]

end Equations

section Field
variable {σ K : Type*} [Fintype σ] [Field K]

@[simp] theorem relativePolar_eq (f : MvPolynomial σ K) (ell : σ → K) :
    relativePolar f ell = polar f ell := rfl

@[simp] theorem relativeLinear_eq (a : σ → K) :
    relativeLinear a = SmoothGaussSection.linearPolynomial a := rfl

 theorem polarList_ideal (f : MvPolynomial σ K) (ell : ℕ → σ → K) (r : ℕ) :
    Ideal.ofList (f :: (List.range r).map (fun j => relativePolar f (ell j))) =
      polarIdeal f ell r := by
  induction r with
  | zero => simp [polarIdeal, idealSequence]
  | succ r ih =>
    rw [List.range_succ, List.map_append]
    change Ideal.ofList ((f :: (List.range r).map (fun j => relativePolar f (ell j))) ++
      [relativePolar f (ell r)]) = _
    rw [Ideal.ofList_append, ih, Ideal.ofList_singleton]
    rfl

 theorem equations_ideal (f : MvPolynomial σ K) (ell : ℕ → σ → K)
    (r : ℕ) (a : σ → K) :
    Ideal.ofList (equations f ell r a) = polarChartIdeal f ell r a := by
  rw [equations, Ideal.ofList_append, polarList_ideal, Ideal.ofList_singleton]
  rfl

end Field

section Family
variable {n m : ℕ} {D L : Type*} [CommRing D] [IsDomain D]
  [Algebra ℂ D] [Field L] [Algebra ℂ L]

def familyEquations (family : DeterminantDvrFamily.Family n m D L)
    (s : Section (fermat n) n) : List (MvPolynomial (Fin n) D) :=
  equations family.polynomial (fun j i => algebraMap ℂ D (s.ell j i))
    (n-2) (fun i => algebraMap ℂ D (s.a i))

 theorem familyEquations_length (family : DeterminantDvrFamily.Family n m D L)
    (s : Section (fermat n) n) (hn : 2 ≤ n) : (familyEquations family s).length = n := by
  rw [familyEquations, equations_length]
  omega

 theorem familyEquations_special (family : DeterminantDvrFamily.Family n m D L)
    (s : Section (fermat n) n) :
    (familyEquations family s).map (MvPolynomial.map family.residue.toRingHom) =
      equations (fermat n) s.ell (n-2) s.a := by
  have hc (c : ℂ) : family.residue.toRingHom (algebraMap ℂ D c) = c :=
    family.residue.commutes c
  simp only [familyEquations, map_equations, family.special_eq, hc]

 theorem familyEquations_generic (family : DeterminantDvrFamily.Family n m D L)
    (s : Section (fermat n) n) :
    (familyEquations family s).map (MvPolynomial.map family.generic.toRingHom) =
      equations (determinant family.pencil) (fun j i => algebraMap ℂ L (s.ell j i))
        (n-2) (fun i => algebraMap ℂ L (s.a i)) := by
  have hc (c : ℂ) : family.generic.toRingHom (algebraMap ℂ D c) = algebraMap ℂ L c :=
    family.generic.commutes c
  simp only [familyEquations, map_equations, family.generic_eq, hc]

 theorem familyEquations_specialIdeal (family : DeterminantDvrFamily.Family n m D L)
    (s : Section (fermat n) n) :
    DVRRootPersistence.specialIdeal family.residue.toRingHom (familyEquations family s) =
      polarChartIdeal (fermat n) s.ell (n-2) s.a := by
  change Ideal.ofList ((familyEquations family s).map
    (MvPolynomial.map family.residue.toRingHom)) = _
  rw [familyEquations_special, equations_ideal]

end Family

section Persistence
variable {n d : ℕ} {D L : Type*} [CommRing D] [IsDomain D]
  [Algebra ℂ D] [IsDiscreteValuationRing D]
  [Field L] [Algebra D L] [IsFractionRing D L]

private def localEquivOfIdealEq {σ : Type*}
    (I J : Ideal (MvPolynomial σ ℂ)) (he : I = J) (p : σ → ℂ)
    (hI : I ≤ IsolatedLocalMultiplicity.pointIdeal p)
    (hJ : J ≤ IsolatedLocalMultiplicity.pointIdeal p) :
    IsolatedLocalMultiplicity.LocalIntersectionRing I p hI ≃+*
      IsolatedLocalMultiplicity.LocalIntersectionRing J p hJ := by
  subst J
  exact RingEquiv.refl _

/-- Flags may move by arbitrary elements of the maximal ideal. Their special
section remains the literal constructed Gauss section, with its full length. -/
theorem equations_specialIdeal {f : MvPolynomial (Fin n) ℂ}
    (ε : D →ₐ[ℂ] ℂ) (F : MvPolynomial (Fin n) D) (hF : map ε.toRingHom F = f)
    (s : Section f d) (ell : ℕ → Fin n → D) (a : Fin n → D)
    (hell : ∀ j i, ε (ell j i) = s.ell j i) (ha : ∀ i, ε (a i) = s.a i) :
    DVRRootPersistence.specialIdeal ε.toRingHom (equations F ell (n-2) a) =
      polarChartIdeal f s.ell (n-2) s.a := by
  change Ideal.ofList ((equations F ell (n-2) a).map (map ε.toRingHom)) = _
  rw [map_equations, hF]
  have he : (fun j i => ε.toRingHom (ell j i)) = s.ell := by
    funext j i
    exact hell j i
  have hae : (fun i => ε.toRingHom (a i)) = s.a := by
    funext i
    exact ha i
  rw [he, hae, equations_ideal]

/-- Applied local specialization: every selected Gauss-section local ideal
is exactly preserved by generic contraction over the actual DVR. This allows
residue-preserving generic choices of both sets of flags. -/
theorem section_contraction_local_eq {f : MvPolynomial (Fin n) ℂ}
    (ε : D →ₐ[ℂ] ℂ) (π : D) (hπ : Irreducible π)
    (hker : RingHom.ker ε = Ideal.span {π})
    (F : MvPolynomial (Fin n) D) (hF : map ε.toRingHom F = f)
    (s : Section f d) (ell : ℕ → Fin n → D) (a : Fin n → D)
    (hell : ∀ j i, ε (ell j i) = s.ell j i) (ha : ∀ i, ε (a i) = s.a i)
    (hn : 2 ≤ n) (p : Fin s.count) :
    ((BezoutHorizontalFamily.contractedIdeal (R := D)
      (GeneralGradedBaseChange.extendedIdeal (K := L)
        (Ideal.ofList (equations F ell (n-2) a)))).map (map ε.toRingHom)).map
      (algebraMap _ (CoordinatePowerRegular.PointLocalRing (s.point p))) =
    (polarChartIdeal f s.ell (n-2) s.a).map
      (algebraMap _ (CoordinatePowerRegular.PointLocalRing (s.point p))) := by
  have hε : Function.Surjective ε.toRingHom := fun c =>
    ⟨algebraMap ℂ D c, ε.commutes c⟩
  have hsp := equations_specialIdeal ε F hF s ell a hell ha
  have hz : ∀ q ∈ equations F ell (n-2) a,
      eval (s.point p) (DVRRootPersistence.specialize ε.toRingHom q) = 0 := by
    intro q hq
    apply s.vanishes p
    rw [← hsp]
    exact Ideal.subset_span (List.mem_map.mpr ⟨q, hq, rfl⟩)
  letI : IsArtinianRing (IsolatedLocalMultiplicity.LocalIntersectionRing
      (DVRRootPersistence.specialIdeal ε.toRingHom (equations F ell (n-2) a))
      (s.point p) (DVRRootPersistence.specialIdeal_le_pointIdeal ε.toRingHom _ _ hz)) := by
    letI := s.artinian p
    exact (localEquivOfIdealEq _ _ hsp (s.point p) _ (s.vanishes p)).symm.isArtinianRing
  have h := DVRRootPersistence.specialized_contractedIdeal_localization_eq
    (L := L) ε.toRingHom hε π hπ hker (equations F ell (n-2) a) (s.point p)
    (by simp only [equations_length, Fintype.card_fin]; omega) hz
  simpa only [hsp] using h

end Persistence
end Sheshadri.DVRGaussSection
