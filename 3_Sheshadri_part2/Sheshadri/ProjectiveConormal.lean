/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ConormalZariski
import Sheshadri.ConormalTopology
import Sheshadri.ConormalCone
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Maps.Basic

/-!
# The actual biprojective conormal and the cone section

The points in this file are mathlib `Projectivization` points, not a surrogate
certificate. The biprojective algebraic topology is the quotient topology of
the polynomial Zariski topology on pairs of nonzero vectors. We prove that the
closure of the affine smooth Gauss graph in that topology is exactly the
projectivization of the polynomial closure of its independently rescaled
representatives. This removes zero representatives and proves the previously
missing set/topological projectivization bridge.
-/

noncomputable section
set_option maxHeartbeats 300000
namespace Sheshadri.ProjectiveConormal

open MvPolynomial Set
open scoped LinearAlgebra.Projectivization Topology
open ZariskiBridge ConormalPersistence

variable {I J : Type*}

abbrev PairAmbient (I J : Type*) := I ⊕ J → ℂ
abbrev BiProjective (I J : Type*) := ℙ ℂ (I → ℂ) × ℙ ℂ (J → ℂ)

def NonzeroBlocks (p : PairAmbient I J) : Prop :=
  (fun i => p (Sum.inl i)) ≠ 0 ∧ (fun j => p (Sum.inr j)) ≠ 0

abbrev Representatives (I J : Type*) := {p : PairAmbient I J // NonzeroBlocks p}

def projectivize (p : Representatives I J) : BiProjective I J :=
  (Projectivization.mk ℂ (fun i => p.val (Sum.inl i)) p.property.1,
   Projectivization.mk ℂ (fun j => p.val (Sum.inr j)) p.property.2)

theorem projectivize_surjective : Function.Surjective (projectivize (I := I) (J := J)) := by
  intro q
  refine ⟨⟨Sum.elim q.1.rep q.2.rep, q.1.rep_nonzero, q.2.rep_nonzero⟩, ?_⟩
  simp [projectivize]

def blockScale (mu nu : ℂ) (p : PairAmbient I J) : PairAmbient I J :=
  Sum.elim (fun i => mu * p (Sum.inl i)) (fun j => nu * p (Sum.inr j))

def ScaleInvariant (s : Set (PairAmbient I J)) : Prop :=
  ∀ p ∈ s, ∀ mu nu : ℂ, mu ≠ 0 → nu ≠ 0 → blockScale mu nu p ∈ s

/-- Polynomial substitution proves that algebraic closure preserves the
actual independent scaling action; this is not a closure-comparison axiom. -/
theorem zariskiClosure_scaleInvariant {s : Set (PairAmbient I J)}
    (hs : ScaleInvariant s) : ScaleInvariant (zariskiClosure s) := by
  intro p hp mu nu hmu hnu q hq
  let subst : I ⊕ J → MvPolynomial (I ⊕ J) ℂ :=
    Sum.elim (fun i => C mu * X (Sum.inl i)) (fun j => C nu * X (Sum.inr j))
  have heval (x : PairAmbient I J) :
      eval x (eval₂ C subst q) = eval (blockScale mu nu x) q := by
    rw [eval_eval₂]
    have hc : (eval x).comp C = RingHom.id ℂ := by ext; simp
    rw [hc, eval₂_id]
    apply congrArg (fun z => eval z q)
    funext i
    cases i <;> simp [subst, blockScale]
  rw [← heval]
  apply hp (eval₂ C subst q)
  intro x hx
  rw [heval]
  exact hq _ (hs x hx mu nu hmu hnu)

/-- Equality of projective pairs means independent nonzero rescaling. -/
theorem projectivize_eq_iff (p q : Representatives I J) :
    projectivize p = projectivize q ↔
      ∃ mu nu : ℂ, mu ≠ 0 ∧ nu ≠ 0 ∧ p.val = blockScale mu nu q.val := by
  constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    obtain ⟨mu, hmu⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp h₁
    obtain ⟨nu, hnu⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mp h₂
    refine ⟨mu, nu, mu.ne_zero, nu.ne_zero, ?_⟩
    funext i
    cases i with
    | inl i => exact (congrFun hmu i).symm
    | inr j => exact (congrFun hnu j).symm
  · rintro ⟨mu, nu, hmu, hnu, h⟩
    apply Prod.ext
    · apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      refine ⟨mu, ?_⟩
      funext i
      exact (congrFun h (Sum.inl i)).symm
    · apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      refine ⟨nu, ?_⟩
      funext j
      exact (congrFun h (Sum.inr j)).symm

theorem preimage_image_of_scaleInvariant {s : Set (PairAmbient I J)}
    (hs : ScaleInvariant s) :
    projectivize ⁻¹' (projectivize '' {p : Representatives I J | p.val ∈ s}) =
      {p : Representatives I J | p.val ∈ s} := by
  ext p
  constructor
  · rintro ⟨q, hq, heq⟩
    obtain ⟨mu, nu, hmu, hnu, h⟩ := (projectivize_eq_iff p q).mp heq.symm
    change p.val ∈ s
    rw [h]
    exact hs q.val hq mu nu hmu hnu
  · intro hp
    exact ⟨p, hp, rfl⟩

/-- The algebraic topology on the nonzero representative locus. -/
def representativeTopology (I J : Type*) : TopologicalSpace (Representatives I J) :=
  TopologicalSpace.induced Subtype.val (ConormalTopology.algebraicTopology (I ⊕ J))

/-- The Zariski quotient topology on the actual product of projective spaces.
This definition keeps the algebraic topology distinct from Euclidean topology. -/
def biprojectiveTopology (I J : Type*) : TopologicalSpace (BiProjective I J) :=
  TopologicalSpace.coinduced projectivize (representativeTopology I J)

theorem projectivize_isQuotientMap :
    @Topology.IsQuotientMap (Representatives I J) (BiProjective I J)
      (representativeTopology I J) (biprojectiveTopology I J) projectivize := by
  letI := representativeTopology I J
  letI := biprojectiveTopology I J
  exact ⟨projectivize_surjective, rfl⟩

/-- Removing zero blocks after affine algebraic closure gives exactly the
closure of the image in biprojective space, for any rescaling-invariant set
of genuine nonzero representatives. -/
theorem projectivization_zariskiClosure_eq_closure
    (s : Set (PairAmbient I J)) (hs : ScaleInvariant s)
    (hne : ∀ p ∈ s, NonzeroBlocks p) :
    projectivize '' {p : Representatives I J | p.val ∈ zariskiClosure s} =
      @closure (BiProjective I J) (biprojectiveTopology I J)
        (projectivize '' {p : Representatives I J | p.val ∈ s}) := by
  letI : TopologicalSpace (PairAmbient I J) := ConormalTopology.algebraicTopology _
  letI : TopologicalSpace (Representatives I J) := representativeTopology I J
  letI : TopologicalSpace (BiProjective I J) := biprojectiveTopology I J
  let t : Set (Representatives I J) := {p | p.val ∈ s}
  have himage : Subtype.val '' t = s := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hp
      exact ⟨⟨p, hne p hp⟩, hp, rfl⟩
  have hclosure : closure t = {p : Representatives I J | p.val ∈ zariskiClosure s} := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, himage]
    rw [ConormalTopology.closure_algebraicTopology_eq]
    rfl
  have hclosed : IsClosed (projectivize '' {p : Representatives I J |
      p.val ∈ zariskiClosure s}) := by
    apply projectivize_isQuotientMap.isClosed_preimage.mp
    rw [preimage_image_of_scaleInvariant (zariskiClosure_scaleInvariant hs), ← hclosure]
    exact isClosed_closure
  apply Set.Subset.antisymm
  · rw [← hclosure]
    exact image_closure_subset_closure_image projectivize_isQuotientMap.continuous
  · exact closure_minimal (Set.image_mono (fun p hp =>
      ConormalTopology.subset_zariskiClosure s hp)) hclosed

section Gauss
variable {A Z : Type*} [Fintype A] [Fintype Z]

/-- The actual affine-chart Gauss graph in the biprojective ambient space. -/
def affineGaussGraph (F : MvPolynomial (A ⊕ Z) ℂ) (a : A → ℂ) :
    Set (BiProjective (Option Z) (Option Z)) :=
  projectivize '' {p : Representatives (Option Z) (Option Z) |
    p.val ∈ ConormalZariski.smoothGaussRepresentatives F a}

/-- The projective conormal closure of this affine smooth chart. -/
def conormal (F : MvPolynomial (A ⊕ Z) ℂ) (a : A → ℂ) :
    Set (BiProjective (Option Z) (Option Z)) :=
  @closure _ (biprojectiveTopology _ _) (affineGaussGraph F a)

theorem smoothGaussRepresentatives_nonzero (F : MvPolynomial (A ⊕ Z) ℂ)
    (a : A → ℂ) :
    ∀ p ∈ ConormalZariski.smoothGaussRepresentatives F a, NonzeroBlocks p := by
  rintro p ⟨z, mu, nu, hz, ⟨j, hj⟩, hmu, hnu, rfl⟩
  constructor
  · intro h
    have hh := congrFun h none
    exact hmu (by simpa [ConormalZariski.gaussPoint] using hh)
  · intro h
    have hh := congrFun h (some j)
    have : nu * gradient F a z j = 0 := hh
    exact mul_ne_zero hnu hj this

theorem smoothGaussRepresentatives_scaleInvariant
    (F : MvPolynomial (A ⊕ Z) ℂ) (a : A → ℂ) :
    ScaleInvariant (ConormalZariski.smoothGaussRepresentatives F a) := by
  rintro p ⟨z, mu, nu, hz, hj, hmu, hnu, rfl⟩ c d hc hd
  refine ⟨z, c * mu, d * nu, hz, hj, mul_ne_zero hc hmu, mul_ne_zero hd hnu, ?_⟩
  funext i
  cases i <;> simp [blockScale, ConormalZariski.gaussPoint, mul_assoc]

/-- This is the formerly missing identification with actual projective
points and their closed conormal set. It assumes no projective-containment
certificate and proves the quotient/closure compatibility. -/
theorem conormal_eq_projectivized_affineClosure
    (F : MvPolynomial (A ⊕ Z) ℂ) (a : A → ℂ) :
    conormal F a = projectivize '' {p : Representatives (Option Z) (Option Z) |
      p.val ∈ ConormalZariski.conormalClosure F a} := by
  symm
  exact projectivization_zariskiClosure_eq_closure _
    (smoothGaussRepresentatives_scaleInvariant F a)
    (smoothGaussRepresentatives_nonzero F a)

/-- Any algebraically closed special fibre containing the affine closure
therefore contains the actual biprojective conormal. -/
theorem conormal_subset_projectivization {F : MvPolynomial (A ⊕ Z) ℂ}
    {a : A → ℂ} {s : Set (ConormalZariski.Ambient Z)}
    (h : ConormalZariski.conormalClosure F a ⊆ s) :
    conormal F a ⊆ projectivize '' {p : Representatives (Option Z) (Option Z) | p.val ∈ s} := by
  rw [conormal_eq_projectivized_affineClosure]
  exact Set.image_mono (fun _ hp => h hp)

end Gauss


section PowerSumCone
open ConormalCone
open scoped BigOperators

/-- The actual constant power-sum polynomial, in the same parameter/point
polynomial type used by the persistence theorem. -/
def powerSumFamily (n d : ℕ) : MvPolynomial (Empty ⊕ Fin n) ℂ :=
  rename Sum.inr (powerSum n d)

def noParameters : Empty → ℂ := Empty.elim

theorem value_powerSumFamily (n d : ℕ) (z : Fin n → ℂ) :
    value (powerSumFamily n d) noParameters z = eval z (powerSum n d) := by
  simp [value, powerSumFamily, eval_rename, Function.comp_def]

theorem gradient_powerSumFamily (n d : ℕ) (z : Fin n → ℂ) (i : Fin n) :
    gradient (powerSumFamily n d) noParameters z i = (d : ℂ) * z i ^ (d - 1) := by
  change eval _ (pderiv (Sum.inr i) (rename Sum.inr (powerSum n d))) = _
  rw [pderiv_rename Sum.inr_injective]
  simp [eval_rename, Function.comp_def, pderiv_powerSum]

def powerGradient (n d : ℕ) (z : Fin n → ℂ) : Fin n → ℂ :=
  fun i => (d : ℂ) * z i ^ (d - 1)

theorem powerGradient_ne_zero (n d : ℕ) (hd : 0 < d) (z : Fin n → ℂ)
    (hz : z ≠ 0) : powerGradient n d z ≠ 0 := by
  obtain ⟨i, hi⟩ := powerSum_smooth_away_from_vertex n d hd z hz
  intro h
  apply hi
  simpa [powerGradient, eval_pderiv_powerSum] using congrFun h i

theorem powerSum_eval_smul (n d : ℕ) (c : ℂ) (z : Fin n → ℂ) :
    eval (c • z) (powerSum n d) = c ^ d * eval z (powerSum n d) := by
  simp only [powerSum, map_sum, map_pow, eval_X, Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.mul_sum]

theorem powerGradient_smul (n d : ℕ) (c : ℂ) (z : Fin n → ℂ) :
    powerGradient n d (c • z) = c ^ (d - 1) • powerGradient n d z := by
  funext i
  simp only [powerGradient, Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

/-- A genuine homogeneous Gauss representative on the smooth cone:
primal point `(t,z)`, tangent covector proportional to `(0,grad(z))`. -/
def coneGaussPoint (n d : ℕ) (t : ℂ) (z : Fin n → ℂ) (nu : ℂ) :
    PairAmbient (Option (Fin n)) (Option (Fin n)) :=
  Sum.elim (fun i => Option.elim i t z)
    (fun i => nu * Option.elim i 0 (powerGradient n d z))

theorem coneGaussPoint_nonzero (n d : ℕ) (hd : 0 < d) (t nu : ℂ)
    (z : Fin n → ℂ) (hz : z ≠ 0) (hnu : nu ≠ 0) :
    NonzeroBlocks (coneGaussPoint n d t z nu) := by
  constructor
  · intro h
    apply hz
    funext i
    exact congrFun h (some i)
  · intro h
    apply powerGradient_ne_zero n d hd z hz
    funext i
    have hh : nu * powerGradient n d z i = 0 := congrFun h (some i)
    exact (mul_eq_zero.mp hh).resolve_left hnu

theorem gaussCovector_powerSumFamily (n d : ℕ) (hd : 0 < d)
    (z : Fin n → ℂ) (hz : eval z (powerSum n d) = 0) :
    gaussCovector (powerSumFamily n d) noParameters z =
      fun i => Option.elim i 0 (powerGradient n d z) := by
  funext i
  cases i with
  | none =>
    change -(∑ j, z j * gradient (powerSumFamily n d) noParameters z j) = 0
    simp_rw [gradient_powerSumFamily]
    simpa only [eval_pderiv_powerSum] using powerSum_gauss_zero_coordinate n d hd z hz
  | some i => exact gradient_powerSumFamily n d z i

/-- Every nonzero homogenizing-coordinate cone point lies in the actual
smooth affine Gauss representative set, after the dictated rescalings. -/
theorem coneGaussPoint_mem_smoothGauss_of_ne_zero
    (n d : ℕ) (hd : 0 < d) (t nu : ℂ) (ht : t ≠ 0) (hnu : nu ≠ 0)
    (z : Fin n → ℂ) (hz : z ≠ 0) (hzero : eval z (powerSum n d) = 0) :
    coneGaussPoint n d t z nu ∈
      ConormalZariski.smoothGaussRepresentatives (powerSumFamily n d) noParameters := by
  have hscaled : eval (t⁻¹ • z) (powerSum n d) = 0 := by
    rw [powerSum_eval_smul, hzero, mul_zero]
  have hscaledne : t⁻¹ • z ≠ 0 := smul_ne_zero (inv_ne_zero ht) hz
  obtain ⟨i, hi⟩ := powerSum_smooth_away_from_vertex n d hd (t⁻¹ • z) hscaledne
  refine ⟨t⁻¹ • z, t, nu * t ^ (d - 1), ?_, ⟨i, ?_⟩, ht,
    mul_ne_zero hnu (pow_ne_zero _ ht), ?_⟩
  · rwa [value_powerSumFamily]
  · simpa only [gradient_powerSumFamily, eval_pderiv_powerSum] using hi
  · rw [show ConormalZariski.gaussPoint (powerSumFamily n d) noParameters (t⁻¹ • z)
        t (nu * t ^ (d - 1)) =
        Sum.elim (fun j => t * Option.elim j 1 (t⁻¹ • z))
          (fun j => nu * t ^ (d - 1) * gaussCovector (powerSumFamily n d) noParameters
            (t⁻¹ • z) j) from rfl]
    rw [gaussCovector_powerSumFamily n d hd _ hscaled, powerGradient_smul]
    funext j
    cases j with
    | inl j => cases j <;> simp [coneGaussPoint, ht]
    | inr j =>
      cases j with
      | none => simp [coneGaussPoint]
      | some i =>
        simp only [coneGaussPoint, Sum.elim_inr, Option.elim_some, Pi.smul_apply,
          smul_eq_mul]
        have htprod : t ^ (d - 1) * t⁻¹ ^ (d - 1) = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ ht, one_pow]
        calc
          _ = nu * 1 * powerGradient n d z i := by ring
          _ = _ := by rw [← htprod]; ring

/-- The chart `x₀≠0` is dense in the full smooth cone Gauss graph. This
proves the geometric chart identification, including points at infinity,
by continuity in the ruling coordinate. No explicit polar slice is used. -/
theorem coneGaussPoint_mem_affine_conormalClosure
    (n d : ℕ) (hd : 0 < d) (t nu : ℂ) (hnu : nu ≠ 0)
    (z : Fin n → ℂ) (hz : z ≠ 0) (hzero : eval z (powerSum n d) = 0) :
    coneGaussPoint n d t z nu ∈
      ConormalZariski.conormalClosure (powerSumFamily n d) noParameters := by
  let s := ConormalZariski.conormalClosure (powerSumFamily n d) noParameters
  have hcontinuous : Continuous (fun t : ℂ => coneGaussPoint n d t z nu) := by
    apply continuous_pi
    intro j
    cases j with
    | inl j =>
      cases j with
      | none => exact continuous_id
      | some j => exact continuous_const
    | inr j => exact continuous_const
  have hclosed : IsClosed {t : ℂ | coneGaussPoint n d t z nu ∈ s} :=
    (ConormalZariski.isClosed_zariskiClosure _).preimage hcontinuous
  have hdense : Dense {t : ℂ | coneGaussPoint n d t z nu ∈ s} := by
    apply (dense_compl_singleton (0 : ℂ)).mono
    intro t ht
    exact ConormalZariski.subset_zariskiClosure _
      (coneGaussPoint_mem_smoothGauss_of_ne_zero n d hd t nu ht hnu z hz hzero)
  have huniv := hclosed.closure_eq.symm.trans hdense.closure_eq
  have htmem : t ∈ {t : ℂ | coneGaussPoint n d t z nu ∈ s} := by
    rw [huniv]
    exact Set.mem_univ t
  exact htmem

/-- The full smooth cone Gauss graph on actual projective points. -/
def coneGaussGraph (n d : ℕ) (hd : 0 < d) :
    Set (BiProjective (Option (Fin n)) (Option (Fin n))) :=
  {p | ∃ (t nu : ℂ) (z : Fin n → ℂ) (hz : z ≠ 0) (hnu : nu ≠ 0),
    eval z (powerSum n d) = 0 ∧
      p = projectivize ⟨coneGaussPoint n d t z nu,
        coneGaussPoint_nonzero n d hd t nu z hz hnu⟩}

/-- Every smooth projective cone Gauss point, even in `x₀=0`, belongs to
the projective closure obtained from the affine chart. -/
theorem coneGaussGraph_subset_conormal (n d : ℕ) (hd : 0 < d) :
    coneGaussGraph n d hd ⊆ conormal (powerSumFamily n d) noParameters := by
  rintro p ⟨t, nu, z, hz, hnu, hzero, rfl⟩
  rw [conormal_eq_projectivized_affineClosure]
  refine ⟨⟨coneGaussPoint n d t z nu,
    coneGaussPoint_nonzero n d hd t nu z hz hnu⟩, ?_, rfl⟩
  exact coneGaussPoint_mem_affine_conormalClosure n d hd t nu hnu z hz hzero



/-- The affine smooth graph is a subgraph of the full projective cone graph.
For degree at least two, nonvanishing of the gradient excludes the vertex. -/
theorem affineGaussGraph_subset_coneGaussGraph (n d : ℕ) (hd : 2 ≤ d) :
    affineGaussGraph (powerSumFamily n d) noParameters ⊆
      coneGaussGraph n d (by omega) := by
  rintro p ⟨q, hq, rfl⟩
  obtain ⟨z, mu, nu, hzero, ⟨i, hi⟩, hmu, hnu, hq⟩ := hq
  have hzero' : eval z (powerSum n d) = 0 := by rwa [value_powerSumFamily] at hzero
  have hz : z ≠ 0 := by
    intro h
    apply hi
    rw [gradient_powerSumFamily, h]
    simp [show d - 1 ≠ 0 by omega]
  refine ⟨1, 1, z, hz, one_ne_zero, hzero', ?_⟩
  apply (projectivize_eq_iff _ _).mpr
  refine ⟨mu, nu, hmu, hnu, ?_⟩
  rw [hq]
  have hc := gaussCovector_powerSumFamily n d (by omega) z hzero'
  funext j
  cases j with
  | inl j => cases j <;> rfl
  | inr j =>
    change nu * gaussCovector (powerSumFamily n d) noParameters z j = _
    rw [hc]
    simp [blockScale, coneGaussPoint]

/-- Equality with the closure of the entire smooth projective cone Gauss
graph. Thus `conormal` is the actual cone conormal, not merely a chart subset. -/
theorem conormal_eq_closure_full_coneGaussGraph (n d : ℕ) (hd : 2 ≤ d) :
    conormal (powerSumFamily n d) noParameters =
      @closure _ (biprojectiveTopology _ _) (coneGaussGraph n d (by omega)) := by
  letI := biprojectiveTopology (Option (Fin n)) (Option (Fin n))
  apply Set.Subset.antisymm
  · exact closure_mono (affineGaussGraph_subset_coneGaussGraph n d hd)
  · exact closure_minimal (coneGaussGraph_subset_conormal n d (by omega)) isClosed_closure

/-- The homogeneous cone polynomial in genuine projective coordinates. -/
def conePolynomial (n d : ℕ) : MvPolynomial (Option (Fin n)) ℂ :=
  ∑ i, X (some i) ^ d

theorem conePolynomial_value (n d : ℕ) (t : ℂ) (z : Fin n → ℂ) :
    eval (fun i => Option.elim i t z) (conePolynomial n d) =
      eval z (powerSum n d) := by
  simp [conePolynomial, powerSum]

theorem conePolynomial_pderiv_none (n d : ℕ) :
    pderiv none (conePolynomial n d) = 0 := by
  simp [conePolynomial, pderiv_pow]

theorem conePolynomial_pderiv_some (n d : ℕ) (i : Fin n) :
    pderiv (some i) (conePolynomial n d) = C (d : ℂ) * X (some i) ^ (d - 1) := by
  classical
  simp [conePolynomial, pderiv_pow, Pi.single_apply]

/-- The covector in `coneGaussPoint` is the actual differential of the
homogeneous cone polynomial, including its zero first coordinate. -/
theorem conePolynomial_gradient (n d : ℕ) (t : ℂ) (z : Fin n → ℂ) :
    (fun i => eval (fun j => Option.elim j t z) (pderiv i (conePolynomial n d))) =
      fun i => Option.elim i 0 (powerGradient n d z) := by
  funext i
  cases i with
  | none => simp [conePolynomial_pderiv_none]
  | some i => simp [conePolynomial_pderiv_some, powerGradient]

end PowerSumCone

section ProjectiveSection
open ConormalCone
variable {n : ℕ}

/-- The linear section of the cone by any hyperplane avoiding its vertex. -/
def sectionLinearMap (a : ℂ) (ell : Fin n → ℂ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun := sectionPoint a ell
  map_add' z w := by
    have h : linearForm ell (z + w) = linearForm ell z + linearForm ell w := by
      simp [linearForm, mul_add, Finset.sum_add_distrib]
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    simp only [sectionPoint_zero, Pi.add_apply, h]
    ring
  map_smul' c z := sectionPoint_smul a ell z c

/-- The cone section descends to actual projective points. -/
def projectiveSection (a : ℂ) (ell : Fin n → ℂ) :
    ℙ ℂ (Fin n → ℂ) → ℙ ℂ (Fin (n + 1) → ℂ) :=
  Projectivization.map (sectionLinearMap a ell) (sectionPoint_injective a ell)

theorem projectiveSection_injective (a : ℂ) (ell : Fin n → ℂ) :
    Function.Injective (projectiveSection a ell) :=
  Projectivization.map_injective _ _

/-- A projective point lies in the stated primal hyperplane when one (and
hence every) nonzero representative satisfies its linear equation. -/
def InHyperplane (a : ℂ) (ell : Fin n → ℂ)
    (p : ℙ ℂ (Fin (n + 1) → ℂ)) : Prop :=
  ∃ (x : Fin (n + 1) → ℂ) (hx : x ≠ 0),
    p = Projectivization.mk ℂ x hx ∧
      a * x 0 + linearForm ell (fun i => x i.succ) = 0

/-- Exact image identification: radial projection is inverse to the
projective section on a hyperplane avoiding the cone vertex. -/
theorem range_projectiveSection (a : ℂ) (ha : a ≠ 0) (ell : Fin n → ℂ) :
    Set.range (projectiveSection a ell) = {p | InHyperplane a ell p} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨sectionPoint a ell q.rep, sectionPoint_ne_zero a ell q.rep q.rep_nonzero, ?_,
      sectionPoint_mem_hyperplane a ha ell q.rep⟩
    conv_lhs => rw [← Projectivization.mk_rep q]
    rfl
  · rintro ⟨x, hx, rfl, heq⟩
    let z : Fin n → ℂ := fun i => x i.succ
    have hz : z ≠ 0 := by
      intro hz
      apply hx
      have hfirst : x 0 = 0 := by
        have hlin : linearForm ell z = 0 := by simp [hz, linearForm]
        change a * x 0 + linearForm ell z = 0 at heq
        rw [hlin, add_zero] at heq
        exact (mul_eq_zero.mp heq).resolve_left ha
      funext i
      exact Fin.cases hfirst (fun j => congrFun hz j) i
    refine ⟨Projectivization.mk ℂ z hz, ?_⟩
    have hsection : sectionPoint a ell z = x := by
      have he := sectionPoint_unique a ha ell z (x 0) heq
      rw [← he]
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    change Projectivization.mk ℂ (sectionPoint a ell z) _ = _
    congr 1

/-- A genuine equivalence, rather than the invalid global cone-conormal
bundle projection across the vertex. -/
def projectiveHyperplaneSectionEquiv (a : ℂ) (ha : a ≠ 0) (ell : Fin n → ℂ) :
    ℙ ℂ (Fin n → ℂ) ≃ {p : ℙ ℂ (Fin (n + 1) → ℂ) // InHyperplane a ell p} :=
  Equiv.ofBijective
    (fun q => ⟨projectiveSection a ell q, by
      change projectiveSection a ell q ∈ {p | InHyperplane a ell p}
      rw [← range_projectiveSection a ha ell]
      exact ⟨q, rfl⟩⟩)
    ⟨fun q r h => projectiveSection_injective a ell (congrArg Subtype.val h), by
      intro p
      have hp : p.val ∈ Set.range (projectiveSection a ell) := by
        rw [range_projectiveSection a ha ell]
        exact p.property
      obtain ⟨q, hq⟩ := hp
      exact ⟨q, Subtype.ext hq⟩⟩

end ProjectiveSection


section PolynomialMaps
variable {X Y : Type*}

/-- Coordinatewise polynomial maps are continuous for the actual polynomial
Zariski topologies on the combined affine coordinates. -/
theorem polynomialMap_algebraic_continuous (P : Y → MvPolynomial X ℂ) :
    @Continuous (X → ℂ) (Y → ℂ)
      (ConormalTopology.algebraicTopology X) (ConormalTopology.algebraicTopology Y)
      (fun x y => eval x (P y)) := by
  letI := ConormalTopology.algebraicTopology X
  letI := ConormalTopology.algebraicTopology Y
  apply continuous_iff_isClosed.mpr
  intro s hs
  apply ConormalTopology.isClosed_of_zariskiClosure_eq
  apply Set.Subset.antisymm
  · intro x hx
    change (fun y => eval x (P y)) ∈ s
    rw [← (ConormalTopology.isClosed_algebraicTopology_iff s).mp hs]
    intro q hq
    have heval (z : X → ℂ) :
        eval z (eval₂ C P q) = eval (fun y => eval z (P y)) q := by
      rw [eval_eval₂]
      have hc : (eval z).comp C = RingHom.id ℂ := by ext; simp
      rw [hc, eval₂_id]
    rw [← heval]
    apply hx (eval₂ C P q)
    intro z hz
    rw [heval]
    exact hq _ hz
  · exact ConormalTopology.subset_zariskiClosure _

end PolynomialMaps


section HomogeneousGaussIdentification
open ConormalCone

/-- The literal homogeneous differential at a representative. -/
def homogeneousGradient {V : Type*} (H : MvPolynomial V ℂ) (x : V → ℂ) : V → ℂ :=
  fun i => eval x (pderiv i H)

/-- The usual Gauss graph of a homogeneous hypersurface: its points are
actual projective primal points paired with the projective differential,
on the zero locus where that differential is nonzero. -/
def homogeneousGaussGraph {V : Type*} (H : MvPolynomial V ℂ) : Set (BiProjective V V) :=
  {p | ∃ (x : V → ℂ) (hx : x ≠ 0) (hg : homogeneousGradient H x ≠ 0),
    eval x H = 0 ∧ p = projectivize ⟨Sum.elim x (homogeneousGradient H x), hx, hg⟩}

/-- The graph used above is exactly the usual homogeneous-gradient graph,
with smoothness at the cone vertex checked from the degree assumption. -/
theorem coneGaussGraph_eq_homogeneousGaussGraph (n d : ℕ) (hd : 2 ≤ d) :
    coneGaussGraph n d (by omega) = homogeneousGaussGraph (conePolynomial n d) := by
  ext p
  constructor
  · rintro ⟨t, nu, z, hz, hnu, hzero, hp⟩
    let x : Option (Fin n) → ℂ := fun i => Option.elim i t z
    have hx : x ≠ 0 := by
      intro hx
      apply hz
      funext i
      exact congrFun hx (some i)
    have hg : homogeneousGradient (conePolynomial n d) x ≠ 0 := by
      intro h
      apply powerGradient_ne_zero n d (by omega) z hz
      funext i
      have hh := congrFun h (some i)
      simpa [homogeneousGradient, x, conePolynomial_pderiv_some, powerGradient] using hh
    refine ⟨x, hx, hg, ?_, ?_⟩
    · exact (conePolynomial_value n d t z).trans hzero
    · rw [hp]
      apply (projectivize_eq_iff _ _).mpr
      refine ⟨1, nu, one_ne_zero, hnu, ?_⟩
      funext j
      cases j with
      | inl j => simp [coneGaussPoint, blockScale, x]
      | inr j =>
        change nu * Option.elim j 0 (powerGradient n d z) =
          nu * homogeneousGradient (conePolynomial n d) x j
        congr 1
        exact (congrFun (conePolynomial_gradient n d t z) j).symm
  · rintro ⟨x, hx, hg, hzero, hp⟩
    let t := x none
    let z : Fin n → ℂ := fun i => x (some i)
    have hxeq : x = fun i => Option.elim i t z := by
      funext i
      cases i <;> rfl
    have hgrad : homogeneousGradient (conePolynomial n d) x =
        fun i => Option.elim i 0 (powerGradient n d z) := by
      change (fun i => eval x (pderiv i (conePolynomial n d))) = _
      rw [hxeq]
      exact conePolynomial_gradient n d t z
    have hz : z ≠ 0 := by
      intro hz
      apply hg
      rw [hgrad]
      funext i
      cases i with
      | none => rfl
      | some i => simp [powerGradient, hz, show d - 1 ≠ 0 by omega]
    have hzroot : eval z (powerSum n d) = 0 := by
      rw [hxeq, conePolynomial_value] at hzero
      exact hzero
    refine ⟨t, 1, z, hz, one_ne_zero, hzroot, ?_⟩
    rw [hp]
    apply congrArg projectivize
    apply Subtype.ext
    funext j
    cases j with
    | inl j => exact congrFun hxeq j
    | inr j =>
      change homogeneousGradient (conePolynomial n d) x j =
        1 * Option.elim j 0 (powerGradient n d z)
      rw [one_mul]
      exact congrFun hgrad j

/-- The affine construction is the conormal of the actual homogeneous cone
hypersurface under the standard definition as closure of its smooth Gauss
graph. All of the chart and projectivization identifications are proved. -/
theorem conormal_eq_homogeneousGaussClosure (n d : ℕ) (hd : 2 ≤ d) :
    conormal (powerSumFamily n d) noParameters =
      @closure _ (biprojectiveTopology _ _) (homogeneousGaussGraph (conePolynomial n d)) := by
  rw [conormal_eq_closure_full_coneGaussGraph n d hd,
    coneGaussGraph_eq_homogeneousGaussGraph n d hd]

end HomogeneousGaussIdentification
end Sheshadri.ProjectiveConormal
