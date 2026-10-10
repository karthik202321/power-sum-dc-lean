/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalHilbert

/-!
# From constant Euler characteristics to constant multidegrees

An iterated rational polynomial has outer variable `q` and inner variable
`t`, modeling the Euler-characteristic polynomial of `O(q, q*t)`.
Agreement on the natural-number grid determines this polynomial. Its
coefficient at `q^d` then determines all multidegrees.

The Euler characteristics and the polynomial are independent supplied data:
neither is defined from the multidegrees. Their geometric interpretation,
the evaluation identity, the relation to intersection numbers, and constancy
of Euler characteristics in a proper flat family remain external geometric
inputs. This file does not claim to construct schemes or prove flat-family
cohomological invariance. It proves the full intervening polynomial argument
with no custom axioms.
-/

noncomputable section

namespace Sheshadri.ConormalEulerHilbert

open Polynomial

/-- Evaluate the outer `q` variable and then the inner `t` variable. -/
def gridEval (H : Polynomial (Polynomial ℚ)) (q t : ℕ) : ℚ :=
  (H.eval (Polynomial.C (q : ℚ))).eval (t : ℚ)

/-- A rational polynomial is determined by its values at all natural numbers. -/
theorem polynomial_eq_of_nat_eval_eq (p r : Polynomial ℚ)
    (h : ∀ n : ℕ, p.eval (n : ℚ) = r.eval (n : ℚ)) : p = r := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : Set.Infinite (Set.range (fun n : ℕ => (n : ℚ))) :=
    Set.infinite_range_of_injective Nat.cast_injective
  apply hinf.mono
  rintro x ⟨n, rfl⟩
  exact h n

/-- The actual two-variable interpolation step: agreement of all values on
the natural-number grid implies equality of the iterated polynomials. -/
theorem polynomial_eq_of_nat_grid_eval_eq (H J : Polynomial (Polynomial ℚ))
    (h : ∀ q t : ℕ, gridEval H q t = gridEval J q t) : H = J := by
  have hrows : ∀ q : ℕ, H.eval (Polynomial.C (q : ℚ)) =
      J.eval (Polynomial.C (q : ℚ)) := by
    intro q
    exact polynomial_eq_of_nat_eval_eq _ _ (h q)
  apply Polynomial.eq_of_infinite_eval_eq
  have hinj : Function.Injective (fun n : ℕ => Polynomial.C (n : ℚ)) :=
    Polynomial.C_injective.comp Nat.cast_injective
  have hinf := Set.infinite_range_of_injective hinj
  apply hinf.mono
  rintro x ⟨n, rfl⟩
  exact hrows n

/-- Independent numerical input representing the Euler-characteristic
polynomial of a geometric family. The polynomial is not defined by `delta`.

`evaluates` corresponds to `χ(O(q,q*t))`. `topCoefficient` is the geometric
Hilbert/intersection-number formula. Those interpretations are not proved
by this numerical structure and must be established in an application. -/
structure EulerHilbertData (Parameter : Type*) (d : ℕ)
    (delta : Parameter → Fin (d + 1) → ℚ) where
  eulerCharacteristic : Parameter → ℕ → ℕ → ℤ
  hilbertPolynomial : Parameter → Polynomial (Polynomial ℚ)
  evaluates : ∀ c q t, gridEval (hilbertPolynomial c) q t =
    (eulerCharacteristic c q t : ℚ)
  topCoefficient : ∀ c, (hilbertPolynomial c).coeff d =
    ConormalHilbert.topHilbertPolynomial d (delta c)

variable {Parameter : Type*} {d : ℕ} {delta : Parameter → Fin (d + 1) → ℚ}

/-- Constancy of independently supplied integer Euler characteristics gives
equality of the full polynomials, not just their prescribed top terms. -/
theorem hilbert_polynomials_constant_of_euler_characteristics_constant
    (data : EulerHilbertData Parameter d delta) (base : Parameter)
    (hχ : ∀ c q t, data.eulerCharacteristic c q t =
      data.eulerCharacteristic base q t) :
    ∀ c, data.hilbertPolynomial c = data.hilbertPolynomial base := by
  intro c
  apply polynomial_eq_of_nat_grid_eval_eq
  intro q t
  rw [data.evaluates, data.evaluates, hχ c q t]

/-- The complete numerical part of the proper-flat conservation argument:
constant Euler characteristics imply equal Hilbert polynomials, hence equal
`q^d` coefficients, hence equality of every multidegree. The proper-flat
Euler-characteristic theorem itself remains the explicit hypothesis `hχ`. -/
theorem multidegrees_constant_of_euler_characteristics_constant
    (data : EulerHilbertData Parameter d delta) (base : Parameter)
    (hχ : ∀ c q t, data.eulerCharacteristic c q t =
      data.eulerCharacteristic base q t) :
    ∀ c k, delta c k = delta base k := by
  intro c k
  have hH := hilbert_polynomials_constant_of_euler_characteristics_constant data base hχ c
  have htop : ConormalHilbert.topHilbertPolynomial d (delta c) =
      ConormalHilbert.topHilbertPolynomial d (delta base) := by
    rw [← data.topCoefficient c, ← data.topCoefficient base, hH]
  exact congrFun (ConormalHilbert.multidegrees_eq_of_topHilbertPolynomial_eq d htop) k

/-- Pairwise form, without a chosen distinguished fibre. -/
theorem multidegrees_eq_of_euler_characteristics_eq
    (data : EulerHilbertData Parameter d delta) (c c' : Parameter)
    (hχ : ∀ q t, data.eulerCharacteristic c q t = data.eulerCharacteristic c' q t) :
    delta c = delta c' := by
  have hH : data.hilbertPolynomial c = data.hilbertPolynomial c' := by
    apply polynomial_eq_of_nat_grid_eval_eq
    intro q t
    rw [data.evaluates, data.evaluates, hχ q t]
  apply ConormalHilbert.multidegrees_eq_of_topHilbertPolynomial_eq d
  rw [← data.topCoefficient c, ← data.topCoefficient c', hH]

end Sheshadri.ConormalEulerHilbert
