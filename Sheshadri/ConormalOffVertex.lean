/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ProjectiveConormal

/-!
# The Fermat cone conormal away from its vertex

Polynomial equations are propagated through the actual affine algebraic
closure. Nonzero-gradient linear algebra then recovers the exact Gauss graph
at every point whose primal tail is nonzero. Hence closing the Gauss graph
introduces no new conormal pairs off the cone vertex. This is the missing
local qualification in the manuscript's cone-section argument.
-/

noncomputable section
namespace Sheshadri.ConormalOffVertex

open MvPolynomial Set
open scoped LinearAlgebra.Projectivization BigOperators
open ProjectiveConormal ConormalCone ConormalPersistence ZariskiBridge

abbrev Coordinates (n : ℕ) := Option (Fin n) ⊕ Option (Fin n)

def primalTail {n : ℕ} (p : Coordinates n → ℂ) : Fin n → ℂ :=
  fun i => p (Sum.inl (some i))

def dualTail {n : ℕ} (p : Coordinates n → ℂ) : Fin n → ℂ :=
  fun i => p (Sum.inr (some i))

def coneEquation (n d : ℕ) : MvPolynomial (Coordinates n) ℂ :=
  rename (fun i => Sum.inl (some i)) (powerSum n d)

def minorEquation (n d : ℕ) (i j : Fin n) : MvPolynomial (Coordinates n) ℂ :=
  X (Sum.inr (some i)) * X (Sum.inl (some j)) ^ (d - 1) -
    X (Sum.inr (some j)) * X (Sum.inl (some i)) ^ (d - 1)

@[simp] theorem eval_coneEquation (n d : ℕ) (p : Coordinates n → ℂ) :
    eval p (coneEquation n d) = eval (primalTail p) (powerSum n d) := by
  simp only [coneEquation, eval_rename]
  rfl

@[simp] theorem eval_minorEquation (n d : ℕ) (p : Coordinates n → ℂ) (i j : Fin n) :
    eval p (minorEquation n d i j) =
      dualTail p i * primalTail p j ^ (d - 1) -
        dualTail p j * primalTail p i ^ (d - 1) := by
  simp [minorEquation, primalTail, dualTail]

/-- All three kinds of equations are actual polynomial consequences of
membership in the affine smooth Gauss representative locus. -/
theorem gauss_equations (n d : ℕ) (hd : 0 < d) (p : Coordinates n → ℂ)
    (hp : p ∈ ConormalZariski.smoothGaussRepresentatives (powerSumFamily n d) noParameters) :
    eval p (coneEquation n d) = 0 ∧ p (Sum.inr none) = 0 ∧
      ∀ i j, eval p (minorEquation n d i j) = 0 := by
  obtain ⟨z, mu, nu, hzero, hgrad, hmu, hnu, rfl⟩ := hp
  have hzero' : eval z (powerSum n d) = 0 := by rwa [value_powerSumFamily] at hzero
  have htail : primalTail (ConormalZariski.gaussPoint (powerSumFamily n d)
      noParameters z mu nu) = mu • z := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [eval_coneEquation, htail, powerSum_eval_smul, hzero', mul_zero]
  · change nu * gaussCovector (powerSumFamily n d) noParameters z none = 0
    rw [gaussCovector_powerSumFamily n d hd z hzero']
    exact mul_zero nu
  · intro i j
    simp only [eval_minorEquation, dualTail, primalTail,
      ConormalZariski.gaussPoint, Sum.elim_inl, Sum.elim_inr,
      Option.elim_some, gaussCovector, gradient_powerSumFamily, mul_pow]
    ring

/-- The defining cone equation, zero dual vertex coordinate and all Gauss
rank minors persist in the polynomial closure, with no flatness assumption. -/
theorem conormalClosure_equations (n d : ℕ) (hd : 0 < d) (p : Coordinates n → ℂ)
    (hp : p ∈ ConormalZariski.conormalClosure (powerSumFamily n d) noParameters) :
    eval (primalTail p) (powerSum n d) = 0 ∧ p (Sum.inr none) = 0 ∧
      ∀ i j, dualTail p i * primalTail p j ^ (d - 1) =
        dualTail p j * primalTail p i ^ (d - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := hp (coneEquation n d) (fun q hq => (gauss_equations n d hd q hq).1)
    simpa only [eval_coneEquation] using h
  · have h := hp (X (Sum.inr none)) (fun q hq => by
      simpa only [eval_X] using (gauss_equations n d hd q hq).2.1)
    simpa only [eval_X] using h
  · intro i j
    have h := hp (minorEquation n d i j) (fun q hq => (gauss_equations n d hd q hq).2.2 i j)
    exact sub_eq_zero.mp (by simpa only [eval_minorEquation] using h)

/-- A nonzero rank-one pair of vectors is genuinely proportional. -/
theorem proportional_of_minors {K : Type*} [Field K] {V : Type*}
    (v g : V → K) (hv : v ≠ 0) (hg : g ≠ 0)
    (hminor : ∀ i j, v i * g j = v j * g i) :
    ∃ c : K, c ≠ 0 ∧ v = c • g := by
  obtain ⟨j, hj⟩ : ∃ j, g j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hg (funext h)
  have heq : v = (v j / g j) • g := by
    funext i
    change v i = (v j / g j) * g i
    rw [div_mul_eq_mul_div]
    exact (eq_div_iff hj).2 (hminor i j)
  refine ⟨v j / g j, ?_, heq⟩
  intro h
  apply hv
  rw [heq, h, zero_smul]

/-- No additional conormal points appear away from the cone vertex:
a genuine nonzero representative in the closure has the exact homogeneous
Gauss covector, up to its allowed nonzero scale. -/
theorem conormalClosure_off_vertex_is_gauss (n d : ℕ) (hd : 0 < d)
    (p : Representatives (Option (Fin n)) (Option (Fin n)))
    (hp : p.val ∈ ConormalZariski.conormalClosure (powerSumFamily n d) noParameters)
    (hvertex : primalTail p.val ≠ 0) :
    projectivize p ∈ coneGaussGraph n d hd := by
  obtain ⟨hzero, hdualzero, hminor⟩ := conormalClosure_equations n d hd p.val hp
  have hdual : dualTail p.val ≠ 0 := by
    intro h
    apply p.property.2
    funext i
    cases i with
    | none => exact hdualzero
    | some i => exact congrFun h i
  have hg : powerGradient n d (primalTail p.val) ≠ 0 :=
    powerGradient_ne_zero n d hd _ hvertex
  have hminor' : ∀ i j,
      dualTail p.val i * powerGradient n d (primalTail p.val) j =
        dualTail p.val j * powerGradient n d (primalTail p.val) i := by
    intro i j
    dsimp only [powerGradient]
    linear_combination (d : ℂ) * hminor i j
  obtain ⟨nu, hnu, hproportional⟩ := proportional_of_minors _ _ hdual hg hminor'
  refine ⟨p.val (Sum.inl none), nu, primalTail p.val, hvertex, hnu, hzero, ?_⟩
  apply congrArg projectivize
  apply Subtype.ext
  funext i
  cases i with
  | inl i => cases i <;> rfl
  | inr i =>
    cases i with
    | none => simpa [coneGaussPoint] using hdualzero
    | some i => exact congrFun hproportional i

/-- A projective point avoids the cone vertex exactly when one nonzero
representative has nonzero primal tail. The existential form is invariant
under independent projective scalings by construction. -/
def AwayFromVertex (n : ℕ)
    (p : BiProjective (Option (Fin n)) (Option (Fin n))) : Prop :=
  ∃ (r : Representatives (Option (Fin n)) (Option (Fin n))),
    projectivize r = p ∧ primalTail r.val ≠ 0

/-- The closure and the smooth cone Gauss graph agree on the open complement
of the primal vertex. This is the exact restriction used by a primal
hyperplane avoiding the vertex in the original proof. -/
theorem conormal_off_vertex_eq_gauss (n d : ℕ) (hd : 0 < d) :
    conormal (powerSumFamily n d) noParameters ∩ {p | AwayFromVertex n p} =
      coneGaussGraph n d hd := by
  ext p
  constructor
  · rintro ⟨hp, r, hr, hvertex⟩
    rw [conormal_eq_projectivized_affineClosure] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    have hqvertex : primalTail q.val ≠ 0 := by
      obtain ⟨mu, nu, hmu, hnu, heq⟩ :=
        (projectivize_eq_iff r q).mp (hr.trans hqp.symm)
      intro hzero
      apply hvertex
      funext i
      have h := congrFun heq (Sum.inl (some i))
      change primalTail r.val i = mu * primalTail q.val i at h
      rw [hzero] at h
      simpa using h
    rw [← hqp]
    exact conormalClosure_off_vertex_is_gauss n d hd q hq hqvertex
  · intro hp
    refine ⟨coneGaussGraph_subset_conormal n d hd hp, ?_⟩
    obtain ⟨t, nu, z, hz, hnu, hzero, hp⟩ := hp
    exact ⟨⟨coneGaussPoint n d t z nu, coneGaussPoint_nonzero n d hd t nu z hz hnu⟩,
      hp.symm, hz⟩



/-- The primal hyperplane section inside the actual biprojective ambient. -/
def PrimalHyperplaneSection (n : ℕ) (a : ℂ) (ell : Fin n → ℂ) :
    Set (BiProjective (Option (Fin n)) (Option (Fin n))) :=
  {p | ∃ r : Representatives (Option (Fin n)) (Option (Fin n)),
    projectivize r = p ∧ a * r.val (Sum.inl none) + linearForm ell (primalTail r.val) = 0}

theorem primalHyperplaneSection_awayFromVertex (n : ℕ) (a : ℂ) (ha : a ≠ 0)
    (ell : Fin n → ℂ) :
    PrimalHyperplaneSection n a ell ⊆ {p | AwayFromVertex n p} := by
  rintro p ⟨r, hr, heq⟩
  refine ⟨r, hr, ?_⟩
  intro hz
  have hfirst : r.val (Sum.inl none) = 0 := by
    have hlin : linearForm ell (primalTail r.val) = 0 := by simp [hz, linearForm]
    rw [hlin, add_zero] at heq
    exact (mul_eq_zero.mp heq).resolve_left ha
  apply r.property.1
  funext i
  cases i with
  | none => exact hfirst
  | some i => exact congrFun hz i

/-- The corrected cone-section statement: intersecting the whole conormal
closure with any primal hyperplane avoiding the vertex selects only the
ordinary smooth Gauss graph. No global projection across the vertex is used. -/
theorem conormal_hyperplaneSection_eq_gauss (n d : ℕ) (hd : 0 < d)
    (a : ℂ) (ha : a ≠ 0) (ell : Fin n → ℂ) :
    conormal (powerSumFamily n d) noParameters ∩ PrimalHyperplaneSection n a ell =
      coneGaussGraph n d hd ∩ PrimalHyperplaneSection n a ell := by
  ext p
  constructor
  · rintro ⟨hp, hsection⟩
    refine ⟨?_, hsection⟩
    rw [← conormal_off_vertex_eq_gauss n d hd]
    exact ⟨hp, primalHyperplaneSection_awayFromVertex n a ha ell hsection⟩
  · rintro ⟨hp, hsection⟩
    exact ⟨coneGaussGraph_subset_conormal n d hd hp, hsection⟩

end Sheshadri.ConormalOffVertex
