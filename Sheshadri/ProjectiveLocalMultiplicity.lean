/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.MultiProjectiveBezout
import Sheshadri.IsolatedLocalMultiplicity
import Mathlib.Data.Fintype.Sum

/-!
# Local intersection multiplicity in an actual projective coordinate chart

A chart fixes one nonzero coordinate in each projective block to its value at
the selected point. Its equation ideal includes the original homogeneous
equations and these three chart equations. The local ring is the localization
of that literal quotient, and multiplicity is its module length. In particular,
singularities and nilpotents are retained. Isolatedness means that this actual
local ring is Artinian; the global equation scheme may have excess components.
-/

noncomputable section
namespace Sheshadri.ProjectiveLocalMultiplicity
set_option synthInstance.maxHeartbeats 200000
open MvPolynomial MultiProjective

variable {X U V E : Type*}

structure Chart (p : Variables X U V → ℂ) where
  ix : X
  iu : U
  iv : V
  hx : p (.inl ix) ≠ 0
  hu : p (.inr (.inl iu)) ≠ 0
  hv : p (.inr (.inr iv)) ≠ 0

def Chart.coordinate {p : Variables X U V → ℂ} (c : Chart p) :
    Fin 3 → Variables X U V
  | 0 => .inl c.ix
  | 1 => .inr (.inl c.iu)
  | 2 => .inr (.inr c.iv)

theorem Chart.coordinate_ne_zero {p : Variables X U V → ℂ} (c : Chart p)
    (i : Fin 3) : p (c.coordinate i) ≠ 0 := by
  fin_cases i
  · exact c.hx
  · exact c.hu
  · exact c.hv

def chartEquations (f : E → MvPolynomial (Variables X U V) ℂ)
    (p : Variables X U V → ℂ) (c : Chart p) :
    E ⊕ Fin 3 → MvPolynomial (Variables X U V) ℂ
  | .inl e => f e
  | .inr i => MvPolynomial.X (c.coordinate i) - C (p (c.coordinate i))

def chartIdeal (f : E → MvPolynomial (Variables X U V) ℂ)
    (p : Variables X U V → ℂ) (c : Chart p) :
    Ideal (MvPolynomial (Variables X U V) ℂ) :=
  Ideal.span (Set.range (chartEquations f p c))

theorem chartEquations_zero (f : E → MvPolynomial (Variables X U V) ℂ)
    (p : Variables X U V → ℂ) (c : Chart p)
    (hz : ∀ e, eval p (f e) = 0) (e : E ⊕ Fin 3) :
    eval p (chartEquations f p c e) = 0 := by
  cases e with
  | inl e => exact hz e
  | inr i => simp [chartEquations]

theorem chartIdeal_le_pointIdeal (f : E → MvPolynomial (Variables X U V) ℂ)
    (p : Variables X U V → ℂ) (c : Chart p)
    (hz : ∀ e, eval p (f e) = 0) :
    chartIdeal f p c ≤ IsolatedLocalMultiplicity.pointIdeal p := by
  apply Ideal.span_le.mpr
  rintro _ ⟨e,rfl⟩
  exact chartEquations_zero f p c hz e

/-- The actual local ring in the chosen valid projective chart. -/
abbrev LocalRing (f : E → MvPolynomial (Variables X U V) ℂ)
    (p : Variables X U V → ℂ) (c : Chart p) (hz : ∀ e, eval p (f e) = 0) :=
  IsolatedLocalMultiplicity.LocalIntersectionRing (chartIdeal f p c) p
    (chartIdeal_le_pointIdeal f p c hz)

/-- Scheme-theoretic local intersection multiplicity, not reduced-point count. -/
def multiplicity (f : E → MvPolynomial (Variables X U V) ℂ)
    (p : Variables X U V → ℂ) (c : Chart p) (hz : ∀ e, eval p (f e) = 0) : ℕ∞ :=
  Module.length (LocalRing f p c hz) (LocalRing f p c hz)

theorem multiplicity_eq_finrank [Finite X] [Finite U] [Finite V]
    (f : E → MvPolynomial (Variables X U V) ℂ)
    (p : Variables X U V → ℂ) (c : Chart p) (hz : ∀ e, eval p (f e) = 0)
    [IsArtinianRing (LocalRing f p c hz)] :
    multiplicity f p c hz = (Module.finrank ℂ (LocalRing f p c hz) : ℕ∞) :=
  IsolatedLocalMultiplicity.multiplicity_eq_finrank (chartIdeal f p c) p
    (chartIdeal_le_pointIdeal f p c hz)

def polynomialMap (f : E → MvPolynomial (Variables X U V) ℂ)
    (p : Variables X U V → ℂ) (c : Chart p) (hz : ∀ e, eval p (f e) = 0) :
    MvPolynomial (Variables X U V) ℂ →ₐ[ℂ] LocalRing f p c hz :=
  IsolatedLocalMultiplicity.localPolynomialMap (chartIdeal f p c) p
    (chartIdeal_le_pointIdeal f p c hz)

theorem polynomialMap_equations (f : E → MvPolynomial (Variables X U V) ℂ)
    (p : Variables X U V → ℂ) (c : Chart p) (hz : ∀ e, eval p (f e) = 0)
    (e : E ⊕ Fin 3) : polynomialMap f p c hz (chartEquations f p c e) = 0 := by
  change algebraMap _ _ (Ideal.Quotient.mk (chartIdeal f p c)
    (chartEquations f p c e)) = 0
  have he : Ideal.Quotient.mk (chartIdeal f p c) (chartEquations f p c e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_range_self e))
  rw [he, map_zero]

theorem polynomialMap_chart_coordinate (f : E → MvPolynomial (Variables X U V) ℂ)
    (p : Variables X U V → ℂ) (c : Chart p) (hz : ∀ e, eval p (f e) = 0)
    (i : Fin 3) : polynomialMap f p c hz (MvPolynomial.X (c.coordinate i)) =
      algebraMap ℂ (LocalRing f p c hz) (p (c.coordinate i)) := by
  have h := polynomialMap_equations f p c hz (.inr i)
  change polynomialMap f p c hz (MvPolynomial.X (c.coordinate i) - C _) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  exact h.trans ((polynomialMap f p c hz).commutes _)

theorem chart_system_square [Fintype X] [Fintype U] [Fintype V] [Fintype E]
    [Nonempty X] [Nonempty U] [Nonempty V]
    (hcard : Fintype.card E = (Fintype.card X-1)+(Fintype.card U-1)+(Fintype.card V-1)) :
    Fintype.card (E ⊕ Fin 3) = Fintype.card (Variables X U V) := by
  have hx := Fintype.card_pos (α := X)
  have hu := Fintype.card_pos (α := U)
  have hv := Fintype.card_pos (α := V)
  simp only [Variables, Fintype.card_sum, Fintype.card_fin]
  omega

end Sheshadri.ProjectiveLocalMultiplicity
