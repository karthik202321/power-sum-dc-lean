/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ActualGaussFamily
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Saturation of the actual Gauss-family ideal over an affine line

For a polynomial family over the affine complex line and an open set of good
parameters, the actual total Gauss-closure ideal is saturated with respect to
every nonzero base polynomial. This is proved using nearby smooth zeros, not
assumed componentwise dominance. Consequently the actual reduced closure has
no base torsion. The subsequent PID flatness argument applies to this ideal.

This does not replace the separate construction of a general algebraic
curve through a coefficient-space border point by a rational curve.
-/

noncomputable section
namespace Sheshadri.ActualGaussFlatness

open MvPolynomial Set Filter
open ActualGaussFamily ConormalZariski ConormalPersistence
open scoped Topology

variable {Z : Type*} [Fintype Z]

/-- Embed the univariate base coordinate into the parameter block. -/
def baseMap : Polynomial ℂ →+* MvPolynomial (TotalCoordinates Unit Z) ℂ :=
  Polynomial.eval₂RingHom C (X (Sum.inl ()))

instance totalBaseAlgebra :
    Algebra (Polynomial ℂ) (MvPolynomial (TotalCoordinates Unit Z) ℂ) :=
  (baseMap (Z := Z)).toAlgebra

@[simp] theorem eval_baseMap (r : Polynomial ℂ) (q : TotalAmbient Unit Z) :
    eval q (baseMap r) = r.eval (q (Sum.inl ())) := by
  induction r using Polynomial.induction_on' with
  | add r s hr hs => simp only [map_add, hr, hs, Polynomial.eval_add]
  | monomial k c => simp [baseMap, Polynomial.eval₂_monomial, Polynomial.eval_monomial]

theorem dense_nonzero_evaluations (r : Polynomial ℂ) (hr : r ≠ 0) :
    Dense {t : ℂ | r.eval t ≠ 0} := by
  exact (Polynomial.finite_setOf_isRoot hr).countable.dense_compl ℂ

/-- Cancellation of a nonzero base polynomial in the concrete total ideal.
Smooth-root persistence proves vanishing also over the finitely many roots
of the base multiplier. -/
theorem totalIdeal_saturated
    (F : MvPolynomial (Unit ⊕ Z) ℂ) (U : Set (Unit → ℂ)) (hU : IsOpen U)
    (r : Polynomial ℂ) (hr : r ≠ 0)
    (f : MvPolynomial (TotalCoordinates Unit Z) ℂ)
    (hf : r • f ∈ totalIdeal F U) : f ∈ totalIdeal F U := by
  rintro q ⟨a, ha, p, hp, rfl⟩
  obtain ⟨z, mu, nu, hz, ⟨j, hj⟩, hmu, hnu, rfl⟩ := hp
  obtain ⟨b, hb0, hbc, hg, hG, hbranch⟩ :=
    smooth_zero_gauss_persistence F a z j hz hj
  let par : ℂ → Unit → ℂ := fun t _ => t
  have hpar0 : par (a ()) = a := by funext i; cases i; rfl
  have hpar : Continuous par := continuous_pi (fun _ => continuous_id)
  have hpa : Tendsto par (𝓝 (a ())) (𝓝 a) := by
    simpa only [hpar0] using hpar.continuousAt.tendsto (x := a ())
  let g : ℂ → TotalAmbient Unit Z := fun t =>
    Sum.elim (par t) (gaussPoint F (par t) (b (par t)) mu nu)
  have hpair : ContinuousAt (fun t => (par t, b (par t))) (a ()) :=
    hpar.continuousAt.prodMk (hbc.comp_of_eq hpar.continuousAt hpar0)
  have hgcont : ContinuousAt g (a ()) :=
    continuous_join.continuousAt.comp
      (hpar.continuousAt.prodMk ((continuous_gaussPoint F mu nu).continuousAt.comp hpair))
  have hecont : ContinuousAt (fun t => eval (g t) f) (a ()) :=
    (PolynomialAnalytic.hasStrictFDerivAt_eval f (g (a ()))).continuousAt.comp hgcont
  have hden := dense_nonzero_evaluations r hr
  letI : NeBot (𝓝[{t : ℂ | r.eval t ≠ 0}] (a ())) :=
    mem_closure_iff_nhdsWithin_neBot.mp (hden (a ()))
  have he : ∀ᶠ t in 𝓝[{t : ℂ | r.eval t ≠ 0}] (a ()), eval (g t) f = 0 := by
    filter_upwards [self_mem_nhdsWithin,
      (hpa.eventually (hU.mem_nhds ha)).filter_mono nhdsWithin_le_nhds,
      (hpa.eventually hbranch).filter_mono nhdsWithin_le_nhds] with t hrt htU htroot
    have hmem : g t ∈ totalGraph F U :=
      ⟨par t, htU, gaussPoint F (par t) (b (par t)) mu nu,
        ⟨b (par t), mu, nu, htroot.1, ⟨j, htroot.2.1⟩, hmu, hnu, rfl⟩, rfl⟩
    have hm := hf (g t) hmem
    change eval (g t) ((baseMap r) * f) = 0 at hm
    rw [map_mul, eval_baseMap] at hm
    exact (mul_eq_zero.mp hm).resolve_left hrt
  have hzlim : eval (g (a ())) f = 0 :=
    isClosed_singleton.mem_of_tendsto
      (hecont.tendsto.mono_left nhdsWithin_le_nhds) he
  simpa only [g, hpar0, hb0] using hzlim

end Sheshadri.ActualGaussFlatness
