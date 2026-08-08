/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Exponential.Variation

/-!
# The differential of the Lie-group exponential

This file computes the differential of the tangent-space Lie-group exponential after translating
its value back to the identity. The result is the integral of the adjoint orbit.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main definitions

* `TauCeti.Lie.tangentLieExpLeftTrivializedFDeriv`: the differential of the tangent-space
  exponential followed by left translation back to the identity.

## Main results

* `TauCeti.Lie.tangentLieExpLeftTrivializedFDeriv_apply_eq_integral`: the pointwise integral
  formula for the left-trivialized differential.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The conjugation formulas".
-/

public section

noncomputable section

namespace TauCeti.Lie

open Manifold MeasureTheory
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

local instance lieGroupBoundarylessManifoldExponentialDerivative : BoundarylessManifold I G where
  isInteriorPoint' g :=
    ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) g

attribute [local instance] LieGroup.minSmoothnessThree

/-- The differential of the tangent-space exponential at `X`, followed by the differential of
left multiplication by `exp (-X)` so that its value lies back at the identity. -/
def tangentLieExpLeftTrivializedFDeriv (X : GroupLieAlgebra I G) : E →L[ℝ] E :=
  (mfderiv I I
    (fun g : G => mulInvariantExp (I := I) (G := G) (-X) * g)
    (mulInvariantExp (I := I) (G := G) X)).comp
  (mfderiv 𝓘(ℝ, E) I
    (fun v : E => mulInvariantExp (I := I) (G := G)
      (show GroupLieAlgebra I G from v)) (@id E X))

private theorem timeFDeriv_exponentialVariation_one_eq
    (f : C^∞⟮I, G; ℝ⟯) (X Y : GroupLieAlgebra I G) :
    let F : ℝ × ℝ → ℝ := fun p =>
      f (mulInvariantExp (I := I) (G := G) ((-p.2) • X) *
        mulInvariantExp (I := I) (G := G) (p.2 • (X + p.1 • Y)))
    timeFDeriv F 0 1 = mvfderiv I f 1
      (tangentLieExpLeftTrivializedFDeriv (I := I) (G := G) X (@id E Y)) := by
  dsimp only
  let F : ℝ × ℝ → ℝ := fun p =>
    f (mulInvariantExp (I := I) (G := G) ((-p.2) • X) *
      mulInvariantExp (I := I) (G := G) (p.2 • (X + p.1 • Y)))
  have hF : ContDiff ℝ ∞ F := by
    simpa only [F] using ContMDiffMap.contDiff_exponentialVariation
      (I := I) (G := G) f X Y
  have hemb : HasDerivAt (fun t : ℝ => (t, (1 : ℝ))) (1, 0) 0 :=
    (hasDerivAt_id (𝕜 := ℝ) 0).prodMk (hasDerivAt_const (x := 0) 1)
  have hpartialRaw := (hF.differentiable (by norm_num) (0, 1)).hasFDerivAt
    |>.comp_hasDerivAt (f := fun t : ℝ => (t, (1 : ℝ))) 0 hemb
  have hpartial : HasDerivAt (fun t => F (t, 1)) (timeFDeriv F 0 1) 0 := by
    simpa only [timeFDeriv_apply, Function.comp_def] using hpartialRaw
  let z : ℝ → E := fun t => @id E X + t • (@id E Y)
  have hz : HasDerivAt z (@id E Y) 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℝ)) (@id E X)).add
        ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const (@id E Y)) using 1
    · ext t
      rfl
    · simp only [zero_add, one_smul]
  let Exp : E → G := fun v => mulInvariantExp (I := I) (G := G)
    (show GroupLieAlgebra I G from v)
  have hExp : HasMFDerivAt 𝓘(ℝ, E) I Exp (@id E X)
      (mfderiv 𝓘(ℝ, E) I Exp (@id E X)) :=
    (contMDiff_mulInvariantExp (I := I) (G := G)).mdifferentiable
      (by simp) (@id E X) |>.hasMFDerivAt
  have hExpAt : HasMFDerivAt 𝓘(ℝ, E) I Exp
      (z 0)
      (mfderiv 𝓘(ℝ, E) I Exp (@id E X)) := by
    have hz0 : z 0 = @id E X := by simp only [z, zero_smul, add_zero]
    rw [hz0]
    exact hExp
  have hExpLine := hExpAt.comp 0 hz.hasFDerivAt.hasMFDerivAt
  let L : G → G := fun g => mulInvariantExp (I := I) (G := G) (-X) * g
  have hL : HasMFDerivAt I I L (mulInvariantExp (I := I) (G := G) X)
      (mfderiv I I L (mulInvariantExp (I := I) (G := G) X)) := by
    exact (contMDiffAt_mul_left (I := I) (n := ∞)
      (a := mulInvariantExp (I := I) (G := G) (-X))
      (b := mulInvariantExp (I := I) (G := G) X)).mdifferentiableAt
        (by simp) |>.hasMFDerivAt
  have hExpLineZero : (Exp ∘ z) 0 =
      mulInvariantExp (I := I) (G := G) X := by
    have hz0 : z 0 = @id E X := by simp only [z, zero_smul, add_zero]
    rw [Function.comp_apply, hz0]
    with_unfolding_all rfl
  have hLAt : HasMFDerivAt I I L
      ((Exp ∘ z) 0)
      (mfderiv I I L (mulInvariantExp (I := I) (G := G) X)) := by
    rw [hExpLineZero]
    exact hL
  have hLLine := hLAt.comp 0 hExpLine
  have hbase : L (mulInvariantExp (I := I) (G := G) X) = 1 := by
    simp only [L]
    rw [mulInvariantExp_neg, inv_mul_cancel]
  have hcurveZero : (L ∘ Exp ∘ z) 0 = 1 := by
    change L ((Exp ∘ z) 0) = 1
    rw [hExpLineZero]
    exact hbase
  have hfOne := f.contMDiff.mdifferentiable (by simp) (1 : G) |>.hasMFDerivAt
  have hfAt : HasMFDerivAt I 𝓘(ℝ, ℝ) f ((L ∘ Exp ∘ z) 0) (mvfderiv I f 1) := by
    rw [hcurveZero]
    exact hfOne
  have hcomp := hfAt.comp 0 hLLine
  have hcompF : HasFDerivAt
      (f ∘ L ∘ Exp ∘ z)
      (((mvfderiv I f 1).comp
        ((mfderiv I I L (mulInvariantExp (I := I) (G := G) X)).comp
          (mfderiv 𝓘(ℝ, E) I Exp (@id E X)))).comp
        (ContinuousLinearMap.toSpanSingleton ℝ (@id E Y))) 0 := by
    with_unfolding_all exact hcomp.hasFDerivAt
  have hspan :
      (ContinuousLinearMap.toSpanSingleton ℝ (@id E Y)) 1 = @id E Y := by
    rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  have hline : HasDerivAt (f ∘ L ∘ Exp ∘ z)
      (mvfderiv I f 1
        (tangentLieExpLeftTrivializedFDeriv (I := I) (G := G) X (@id E Y))) 0 := by
    apply hcompF.hasDerivAt.congr_deriv
    with_unfolding_all
      rw [ContinuousLinearMap.comp_apply]
    calc
      _ = ((mvfderiv I f 1).comp
          ((mfderiv I I L (mulInvariantExp (I := I) (G := G) X)).comp
            (mfderiv 𝓘(ℝ, E) I Exp (@id E X)))) (@id E Y) :=
        congrArg _ hspan
      _ = _ := by
        with_unfolding_all rfl
  have hpartial' : HasDerivAt (f ∘ L ∘ Exp ∘ z) (timeFDeriv F 0 1) 0 := by
    apply hpartial.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun t => by
      simp only [F, Function.comp_apply, L, Exp, z, one_smul]
      congr 3
      rw [neg_one_smul]
  exact hpartial'.unique hline

/-- The left-trivialized differential of the tangent-space exponential is the integral of the
adjoint orbit. -/
theorem tangentLieExpLeftTrivializedFDeriv_apply_eq_integral
    (X Y : GroupLieAlgebra I G) :
    tangentLieExpLeftTrivializedFDeriv (I := I) (G := G) X (@id E Y) =
      ∫ s in (0 : ℝ)..1, @id E (tangentAd (I := I)
        (mulInvariantExp (I := I) (G := G) ((-s) • X)) Y) := by
  with_unfolding_all apply tangentToPointDerivation_injective (I := I) (1 : G)
  ext f
  let q : E →L[ℝ] ℝ := by
    with_unfolding_all exact mvfderiv I f 1
  let fsmooth : C^∞⟮I, G; ℝ⟯ := f
  have hscalar := ContMDiffMap.timeFDeriv_exponentialVariation_one
    (I := I) (G := G) fsmooth X Y
  dsimp only at hscalar
  rw [timeFDeriv_exponentialVariation_one_eq (I := I) (G := G) fsmooth X Y] at hscalar
  have hscalar' :
      q (tangentLieExpLeftTrivializedFDeriv (I := I) (G := G) X (@id E Y)) =
        ∫ s in (0 : ℝ)..1, q (@id E (tangentAd (I := I)
          (mulInvariantExp (I := I) (G := G) ((-s) • X)) Y)) := by
    with_unfolding_all change q _ =
      (∫ s in (0 : ℝ)..1, q (@id E (mulInvariantVectorField
        (tangentAd (I := I)
          (mulInvariantExp (I := I) (G := G) ((-s) • X)) Y) 1))) at hscalar
    simpa only [mulInvariantVectorField_one] using hscalar
  have hint : IntervalIntegrable
      (fun s : ℝ => @id E (tangentAd (I := I)
        (mulInvariantExp (I := I) (G := G) ((-s) • X)) Y)) volume 0 1 := by
    have harg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun s : ℝ => @id E ((-s) • X)) := by
      exact (show ContDiff ℝ ∞ (fun s : ℝ => @id E ((-s) • X)) by
        fun_prop).contMDiff
    have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞
        (fun s : ℝ => mulInvariantExp (I := I) (G := G) ((-s) • X)) :=
      (contMDiff_mulInvariantExp (I := I) (G := G)).comp harg
    have hV : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun s : ℝ => @id E (tangentAd (I := I)
          (mulInvariantExp (I := I) (G := G) ((-s) • X)) Y)) := by
      exact (contMDiff_tangentAd_apply (I := I) (G := G)).comp
        (hγ.prodMk contMDiff_const)
    exact hV.continuous.intervalIntegrable 0 1
  change q (tangentLieExpLeftTrivializedFDeriv (I := I) (G := G) X (@id E Y)) =
    q (∫ s in (0 : ℝ)..1, @id E (tangentAd (I := I)
      (mulInvariantExp (I := I) (G := G) ((-s) • X)) Y))
  rw [← q.intervalIntegral_comp_comm hint]
  exact hscalar'

end TauCeti.Lie

