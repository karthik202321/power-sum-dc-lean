/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.IncidenceDifferential
import Mathlib.Algebra.DualNumber

/-! First-order polynomial evaluation as an actual ring homomorphism.
The two coordinates are the polynomial value and its formal directional
derivative. This allows matrix identities over a ring to be differentiated
without introducing an analytic or geometric axiom. -/

noncomputable section
namespace Sheshadri.TangentEvaluation

open MvPolynomial MultiProjective IncidenceDifferential

variable {σ : Type*} [Fintype σ]

def tangentEval (p v : σ → ℂ) : MvPolynomial σ ℂ →+* DualNumber ℂ where
  toFun f := ⟨eval p f, directional f p v⟩
  map_one' := by
    apply TrivSqZeroExt.ext
    · simp
    · change directional 1 p v = 0
      simpa only [map_one] using directional_C p v 1
  map_mul' f g := by
    apply TrivSqZeroExt.ext
    · exact map_mul (eval p) f g
    · change directional (f * g) p v =
        eval p f * directional g p v + directional f p v * eval p g
      rw [directional_mul, add_comm]
  map_zero' := by
    apply TrivSqZeroExt.ext
    · simp
    · change directional 0 p v = 0
      simpa only [map_zero] using directional_C p v 0
  map_add' f g := by
    apply TrivSqZeroExt.ext
    · exact map_add (eval p) f g
    · exact directional_add p v f g

@[simp] theorem tangentEval_fst (p v : σ → ℂ) (f : MvPolynomial σ ℂ) :
    (tangentEval p v f).fst = eval p f := rfl

@[simp] theorem tangentEval_snd (p v : σ → ℂ) (f : MvPolynomial σ ℂ) :
    (tangentEval p v f).snd = directional f p v := rfl

@[simp] theorem tangentEval_C (p v : σ → ℂ) (c : ℂ) :
    tangentEval p v (C c) = TrivSqZeroExt.inl c := by
  apply TrivSqZeroExt.ext <;> simp

@[simp] theorem tangentEval_X (p v : σ → ℂ) (i : σ) :
    tangentEval p v (X i) = (⟨p i, v i⟩ : DualNumber ℂ) := by
  apply TrivSqZeroExt.ext <;> simp

end Sheshadri.TangentEvaluation
