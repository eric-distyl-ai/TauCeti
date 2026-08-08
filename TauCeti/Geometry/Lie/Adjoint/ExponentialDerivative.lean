/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Exponential.Variation
public import TauCeti.Analysis.Normed.Algebra.OneSubExpNegDivSelf.Integral

/-!
# The differential of the Lie-group exponential

This file computes the differential of the tangent-space Lie-group exponential after translating
its value back to the identity. The result is first expressed as the integral of the adjoint orbit,
then as the everywhere-defined filled quotient `(1 - exp (-ad X)) / ad X`.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main definitions

* `TauCeti.Lie.tangentLieExpLeftTrivializedFDeriv`: the differential of the tangent-space
  exponential followed by left translation back to the identity.

## Main results

* `TauCeti.Lie.tangentLieExpLeftTrivializedFDeriv_apply_eq_integral`: the pointwise integral
  formula for the left-trivialized differential.
* `TauCeti.Lie.mfderiv_mulInvariantExp_eq_left_comp_oneSubExpNegDivSelf`: the arbitrary-point
  derivative formula for the tangent-space exponential.
* `TauCeti.Lie.mfderiv_lieExp_eq_left_comp_oneSubExpNegDivSelf`: the roadmap-facing derivative
  formula for the derivation-based Lie-group exponential.

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

/-- The left-trivialized differential of the tangent-space exponential is the filled
exponential quotient of the tangent adjoint operator. -/
theorem tangentLieExpLeftTrivializedFDeriv_apply_eq_oneSubExpNegDivSelf
    (X Y : GroupLieAlgebra I G) :
    tangentLieExpLeftTrivializedFDeriv (I := I) (G := G) X (@id E Y) =
      oneSubExpNegDivSelf ℝ (tangentAdContinuousLinearMap (I := I) X) (@id E Y) := by
  rw [tangentLieExpLeftTrivializedFDeriv_apply_eq_integral,
    oneSubExpNegDivSelf_eq_integral_exp]
  let _ : NormedAlgebra ℚ (E →L[ℝ] E) :=
    NormedAlgebra.restrictScalars ℚ ℝ _
  let A := tangentAdContinuousLinearMap (I := I) X
  have hint : IntervalIntegrable
      (fun s : ℝ => NormedSpace.exp (s • (-A))) volume 0 1 :=
    Continuous.intervalIntegrable (μ := volume) (by fun_prop) 0 1
  rw [ContinuousLinearMap.intervalIntegral_apply (μ := volume) hint (@id E Y)]
  apply intervalIntegral.integral_congr
  intro s _hs
  have hscale :
      tangentAdContinuousLinearMap (I := I) ((-s) • X) = s • (-A) := by
    rw [tangentAdContinuousLinearMap_smul]
    dsimp only [A]
    simp only [neg_smul, smul_neg]
  have htangent := tangentAd_mulInvariantExp_apply
    (I := I) (G := G) ((-s) • X) Y
  have hexp := congrArg (fun B : E →L[ℝ] E => B (@id E Y))
    (congrArg NormedSpace.exp hscale)
  with_unfolding_all exact htangent.trans hexp

/-- The differential of the tangent-space exponential at an arbitrary point is left translation
of the filled tangent-adjoint quotient. -/
theorem mfderiv_mulInvariantExp_eq_left_comp_oneSubExpNegDivSelf
    (X : GroupLieAlgebra I G) :
    mfderiv 𝓘(ℝ, E) I
        (fun v : E => mulInvariantExp (I := I) (G := G)
          (show GroupLieAlgebra I G from v)) (@id E X) =
      (show E →L[ℝ] E from mfderiv I I
        (fun g : G => mulInvariantExp (I := I) (G := G) X * g) 1).comp
        (oneSubExpNegDivSelf ℝ (tangentAdContinuousLinearMap (I := I) X)) := by
  let Exp : E → G := fun v => mulInvariantExp (I := I) (G := G)
    (show GroupLieAlgebra I G from v)
  let Lneg : G → G := fun g => mulInvariantExp (I := I) (G := G) (-X) * g
  let Lpos : G → G := fun g => mulInvariantExp (I := I) (G := G) X * g
  have hExp : MDiffAt Exp (@id E X) :=
    (contMDiff_mulInvariantExp (I := I) (G := G)).mdifferentiable
      (by simp) (@id E X)
  have hLneg : MDifferentiable I I Lneg := by
    simpa only [Lneg] using
      (contMDiff_mul_left (I := I) (n := ∞)
        (a := mulInvariantExp (I := I) (G := G) (-X))).mdifferentiable (by simp)
  have hLpos : MDifferentiable I I Lpos := by
    simpa only [Lpos] using
      (contMDiff_mul_left (I := I) (n := ∞)
        (a := mulInvariantExp (I := I) (G := G) X)).mdifferentiable (by simp)
  have hExpAt : Exp (@id E X) = mulInvariantExp (I := I) (G := G) X := by
    with_unfolding_all rfl
  have hbase : (Lneg ∘ Exp) (@id E X) = 1 := by
    rw [Function.comp_apply, hExpAt]
    simp only [Lneg]
    rw [mulInvariantExp_neg, inv_mul_cancel]
  have hfun : Lpos ∘ Lneg ∘ Exp = Exp := by
    funext v
    simp only [Function.comp_apply, Lpos, Lneg]
    rw [mulInvariantExp_neg, ← mul_assoc, mul_inv_cancel, one_mul]
  let dExp : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I Exp (@id E X)
  let dNegExp : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I (Lneg ∘ Exp) (@id E X)
  let dComp : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I (Lpos ∘ Lneg ∘ Exp) (@id E X)
  let dLpos : E →L[ℝ] E := mfderiv I I Lpos 1
  let dLneg : E →L[ℝ] E :=
    mfderiv I I Lneg (mulInvariantExp (I := I) (G := G) X)
  have hdComp : dExp = dComp := by
    dsimp only [dExp, dComp]
    exact (mfderiv_congr (I := 𝓘(ℝ, E)) (I' := I) hfun).symm
  have hdLpos : dComp = dLpos.comp dNegExp := by
    dsimp only [dComp, dLpos, dNegExp]
    rw [← hbase]
    exact mfderiv_comp (@id E X)
      (hLpos ((Lneg ∘ Exp) (@id E X)))
      ((hLneg (Exp (@id E X))).comp (@id E X) hExp)
  have hdLneg : dNegExp = dLneg.comp dExp := by
    dsimp only [dNegExp, dLneg, dExp]
    rw [mfderiv_comp (@id E X) (hLneg (Exp (@id E X))) hExp, hExpAt]
    rfl
  have hdTrivialized :
      dLneg.comp dExp =
        tangentLieExpLeftTrivializedFDeriv (I := I) (G := G) X := by
    rfl
  change dExp = dLpos.comp
    (oneSubExpNegDivSelf ℝ (tangentAdContinuousLinearMap (I := I) X))
  calc
    dExp = dComp := hdComp
    _ = dLpos.comp dNegExp := hdLpos
    _ = dLpos.comp (dLneg.comp dExp) := by rw [hdLneg]
    _ = dLpos.comp
        (tangentLieExpLeftTrivializedFDeriv (I := I) (G := G) X) := by
      rw [hdTrivialized]
    _ = dLpos.comp
        (oneSubExpNegDivSelf ℝ (tangentAdContinuousLinearMap (I := I) X)) := by
      congr 1
      apply ContinuousLinearMap.ext
      intro Y
      exact tangentLieExpLeftTrivializedFDeriv_apply_eq_oneSubExpNegDivSelf
        (I := I) (G := G) X (@id (GroupLieAlgebra I G) Y)

/-- The canonical derivation–tangent equivalence intertwines the filled quotients of the two
continuous realizations of the infinitesimal adjoint. -/
theorem oneSubExpNegDivSelf_adContinuousLinearMap_intertwine
    (X : LeftInvariantDerivation I G) :
    let eIso := leftInvariantDerivationLinearIsometryEquivModelVectorSpace
      (I := I) (G := G)
    let eLie := leftInvariantDerivationLieEquivGroupLieAlgebra
      (I := I) (G := G) BoundarylessManifold.isInteriorPoint
    (oneSubExpNegDivSelf ℝ (tangentAdContinuousLinearMap (I := I) (eLie X))).comp
        eIso.toContinuousLinearEquiv.toContinuousLinearMap =
      eIso.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (oneSubExpNegDivSelf ℝ (adContinuousLinearMap (I := I) X)) := by
  dsimp only
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation
      (I := I) (G := G) BoundarylessManifold.isInteriorPoint
  let _ : CompleteSpace (LeftInvariantDerivation I G) :=
    FiniteDimensional.complete ℝ (LeftInvariantDerivation I G)
  let eIso := leftInvariantDerivationLinearIsometryEquivModelVectorSpace
    (I := I) (G := G)
  let eLie := leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := I) (G := G) BoundarylessManifold.isInteriorPoint
  let c := eIso.toContinuousLinearEquiv.conjContinuousAlgEquiv
  have hc : c (adContinuousLinearMap (I := I) X) =
      tangentAdContinuousLinearMap (I := I) (eLie X) := by
    simpa only [c, eIso, eLie] using
      conjContinuousAlgEquiv_adContinuousLinearMap (I := I) (G := G) X
  have hmap := c.toContinuousAlgHom.map_oneSubExpNegDivSelf
    (adContinuousLinearMap (I := I) X)
  change c (oneSubExpNegDivSelf ℝ (adContinuousLinearMap (I := I) X)) =
    oneSubExpNegDivSelf ℝ (c (adContinuousLinearMap (I := I) X)) at hmap
  rw [hc] at hmap
  apply ContinuousLinearMap.ext
  intro Y
  change oneSubExpNegDivSelf ℝ (tangentAdContinuousLinearMap (I := I) (eLie X))
      (eIso Y) =
    eIso (oneSubExpNegDivSelf ℝ (adContinuousLinearMap (I := I) X) Y)
  have happ := congrArg (fun A : E →L[ℝ] E => A (eIso Y)) hmap
  have hinv : eIso.toContinuousLinearEquiv.symm (eIso Y) = Y :=
    eIso.toContinuousLinearEquiv.symm_apply_apply Y
  simpa only [ContinuousLinearMap.comp_apply, c,
    ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, hinv] using happ.symm

/-- At an arbitrary Lie-algebra element, the differential of the Lie-group exponential is left
translation of the everywhere-defined filled quotient of the infinitesimal adjoint. -/
theorem mfderiv_lieExp_eq_left_comp_oneSubExpNegDivSelf
    (X : LeftInvariantDerivation I G) :
    let eIso := leftInvariantDerivationLinearIsometryEquivModelVectorSpace
      (I := I) (G := G)
    (show LeftInvariantDerivation I G →L[ℝ] E from
      mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) I lieExp X) =
      (show E →L[ℝ] E from
        mfderiv I I (fun g : G => lieExp X * g) 1).comp
        (eIso.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (oneSubExpNegDivSelf ℝ (adContinuousLinearMap (I := I) X))) := by
  dsimp only
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation
      (I := I) (G := G) BoundarylessManifold.isInteriorPoint
  let _ : CompleteSpace (LeftInvariantDerivation I G) :=
    FiniteDimensional.complete ℝ (LeftInvariantDerivation I G)
  let eIso := leftInvariantDerivationLinearIsometryEquivModelVectorSpace
    (I := I) (G := G)
  let eLie := leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := I) (G := G) BoundarylessManifold.isInteriorPoint
  let Exp : E → G := fun v => mulInvariantExp (I := I) (G := G)
    (show GroupLieAlgebra I G from v)
  have hfun : lieExp (I := I) (G := G) = Exp ∘ eIso := by
    funext Y
    rw [lieExp_eq_mulInvariantExp]
    simp only [Exp, Function.comp_apply, eIso,
      leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply]
  have heIsoApply (Y : LeftInvariantDerivation I G) :
      eIso Y = @id E (eLie Y) := by
    simp only [eIso, eLie,
      leftInvariantDerivationLinearIsometryEquivModelVectorSpace_apply,
      leftInvariantDerivationLieEquivGroupLieAlgebra_apply]
    rfl
  have hExp : MDiffAt Exp (eIso X) :=
    (contMDiff_mulInvariantExp (I := I) (G := G)).mdifferentiable
      (by simp) (eIso X)
  have heIso : MDifferentiableAt
      𝓘(ℝ, LeftInvariantDerivation I G) 𝓘(ℝ, E) eIso X :=
    eIso.toContinuousLinearEquiv.hasFDerivAt.differentiableAt.mdifferentiableAt
  let eCLM : LeftInvariantDerivation I G →L[ℝ] E :=
    eIso.toContinuousLinearEquiv.toContinuousLinearMap
  let deIso : LeftInvariantDerivation I G →L[ℝ] E :=
    mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) 𝓘(ℝ, E) eIso X
  have heIsoDeriv : deIso = eCLM := by
    dsimp only [deIso, eCLM]
    rw [mfderiv_eq_fderiv]
    exact eIso.toContinuousLinearEquiv.hasFDerivAt.fderiv
  let dLie : LeftInvariantDerivation I G →L[ℝ] E :=
    mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) I lieExp X
  let dComp : LeftInvariantDerivation I G →L[ℝ] E :=
    mfderiv 𝓘(ℝ, LeftInvariantDerivation I G) I (Exp ∘ eIso) X
  let dExp : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) I Exp (eIso X)
  let dL : E →L[ℝ] E := mfderiv I I (fun g : G => lieExp X * g) 1
  let Rtan : E →L[ℝ] E :=
    oneSubExpNegDivSelf ℝ (tangentAdContinuousLinearMap (I := I) (eLie X))
  let Rad : LeftInvariantDerivation I G →L[ℝ] LeftInvariantDerivation I G :=
    oneSubExpNegDivSelf ℝ (adContinuousLinearMap (I := I) X)
  have hfunDeriv : dLie = dComp := by
    dsimp only [dLie, dComp]
    exact mfderiv_congr
      (I := 𝓘(ℝ, LeftInvariantDerivation I G)) (I' := I) hfun
  have hcompDeriv : dComp = dExp.comp deIso := by
    dsimp only [dComp, dExp, deIso]
    exact mfderiv_comp X hExp heIso
  have hchain : dLie = dExp.comp eCLM := by
    calc
      dLie = dComp := hfunDeriv
      _ = dExp.comp deIso := hcompDeriv
      _ = dExp.comp eCLM := by rw [heIsoDeriv]
  have hgroup : lieExp X = mulInvariantExp (I := I) (G := G) (eLie X) := by
    rw [lieExp_eq_mulInvariantExp]
    simp only [eLie, leftInvariantDerivationLieEquivGroupLieAlgebra_apply]
  have htangent : dExp = dL.comp Rtan := by
    dsimp only [dExp, dL, Rtan]
    rw [heIsoApply, hgroup]
    exact mfderiv_mulInvariantExp_eq_left_comp_oneSubExpNegDivSelf
      (I := I) (G := G) (eLie X)
  have hintertwine : Rtan.comp eCLM = eCLM.comp Rad := by
    simpa only [Rtan, eCLM, Rad, eIso, eLie] using
      oneSubExpNegDivSelf_adContinuousLinearMap_intertwine (I := I) (G := G) X
  change dLie = dL.comp (eCLM.comp Rad)
  calc
    dLie = dExp.comp eCLM := hchain
    _ = (dL.comp Rtan).comp eCLM := by rw [htangent]
    _ = dL.comp (Rtan.comp eCLM) := rfl
    _ = dL.comp (eCLM.comp Rad) := by rw [hintertwine]

end TauCeti.Lie

