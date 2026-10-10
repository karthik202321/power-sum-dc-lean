/-
Release attribution (managed; proof body unchanged).
Copyright (c) 2026 Karthik Sheshadri.
SPDX-License-Identifier: Apache-2.0
Author: Karthik Sheshadri
Repository URL: https://github.com/karthik202321/power-sum-dc-lean
Paper: https://arxiv.org/abs/2606.13628
Archive DOI: 10.5281/zenodo.23274251
-/
import Sheshadri.ProjectivePointInterpolation

/-! # Monotonicity for actual weighted coordinate pieces

Inclusion of equation ideals gives a surjective map on every weighted piece.
This elementary step fixes the direction of the comparison-fibre inequality.
-/

noncomputable section
namespace Sheshadri.BezoutPieceComparison
open MvPolynomial ProjectivePointInterpolation
variable {σ K D : Type*} [Field K] [AddCommMonoid D]

def quotientMap {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J) :
    (MvPolynomial σ K ⧸ I) →ₐ[K] (MvPolynomial σ K ⧸ J) :=
  Ideal.Quotient.liftₐ I (Ideal.Quotient.mkₐ K J)
    (fun _ hp => Ideal.Quotient.eq_zero_iff_mem.mpr (h hp))

def pieceMap (w : σ → D) {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J) (d : D) :
    coordinatePiece w I d →ₗ[K] coordinatePiece w J d :=
  ((quotientMap h).toLinearMap.comp (coordinatePiece w I d).subtype).codRestrict _ (by
    rintro ⟨x,p,hp,rfl⟩
    exact ⟨p,hp,rfl⟩)

theorem pieceMap_surjective (w : σ → D) {I J : Ideal (MvPolynomial σ K)}
    (h : I ≤ J) (d : D) : Function.Surjective (pieceMap w h d) := by
  rintro ⟨x,p,hp,rfl⟩
  exact ⟨⟨Ideal.Quotient.mk I p,p,hp,rfl⟩,rfl⟩

theorem piece_finrank_antitone (w : σ → D) {I J : Ideal (MvPolynomial σ K)}
    (h : I ≤ J) (d : D) [Module.Finite K (coordinatePiece w I d)] :
    Module.finrank K (coordinatePiece w J d) ≤
      Module.finrank K (coordinatePiece w I d) := by
  have hb := (pieceMap w h d).finrank_range_le
  rwa [LinearMap.range_eq_top.mpr (pieceMap_surjective w h d), finrank_top] at hb

end Sheshadri.BezoutPieceComparison
