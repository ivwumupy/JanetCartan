module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCoreResidual
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingAssembly
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingLeading
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import Lean

/-!
# Complete-source cancellation on the unchanged original core

The consumer is `new:eq:qT-identity`: combine the actual initialized core
identity with the actual full source and the original PROJECTED affine
cancellation. The unmeasured tensor equation is neither used nor asserted.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Frobenius
open JanetCartan

@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalCanonicalCompletedResidual
open CurrentMean
open Set Metric ContinuumRow AmplitudeBound ProjectedStressFrame

private theorem measurement_one_on_core {n : ℕ} {μ : ℝ} (hμ : 0 < μ)
    {x : Euclidean n} (hx : x ∈ closedBall 0 μ) :
    FixedCutoffs.physical hμ 1 x = 1 := by
  have hx2 : x ∈ closedBall (0 : Euclidean n) (2 * μ) :=
    closedBall_subset_closedBall (by linarith only [hμ]) hx
  have hp := FixedCutoffs.physical_plateau (n := n) hμ 1
  have hx' : x ∈ closedBall (0 : Euclidean n) (((1 : Fin 3) + 1 : ℝ) * μ) := by
    convert hx2 using 1
    norm_num
  exact (show x ∈ {y | FixedCutoffs.physical hμ 1 y = 1} from interior_subset (hp hx'))

private theorem representative_on_core {n : ℕ} {μ : ℝ}
    (hμ : 0 < μ) (hcell : 4 * μ < 1 / 2)
    {x : Euclidean n} (hx : x ∈ closedBall 0 μ) :
    centeredTorusRepresentative (torusQuotient x) = x :=
  PeriodicLocalL2.centeredTorusRepresentative_quotient
    (FixedCutoffs.closedBall_four_subset_cell hcell
      (closedBall_subset_closedBall (by linarith only [hμ]) hx))

private theorem leading_component_on_core {n N : ℕ} {μ : ℝ}
    (hμ : 0 < μ) (hcell : 4 * μ < 1 / 2) (F : Euclidean n → Euclidean N)
    (leading : SmoothResidual n) (H : MetricField n) {x : Euclidean n}
    (hx : x ∈ closedBall 0 μ)
    (hval : leading.val (torusQuotient x) () =
      Sampling.canonicalSamplingMeasurement (projectedStress F) hμ
        (centeredTorusRepresentative (torusQuotient x))
        (H (centeredTorusRepresentative (torusQuotient x)))) (i : Fin n) :
    leading.val (torusQuotient x) () i = tensorPairing (projectedStress F x i) (H x) := by
  rw [hval, representative_on_core hμ hcell hx, Sampling.canonicalSamplingMeasurement_apply,
    measurement_one_on_core hμ hx, one_mul]

private theorem self_component_on_core {n N : ℕ} {μ : ℝ}
    (hμ : 0 < μ) (hcell : 4 * μ < 1 / 2) (F : Euclidean n → Euclidean N)
    (self : SmoothResidual n) {x : Euclidean n} (hx : x ∈ closedBall 0 μ) (S : MetricTensor n)
    (hval : self.val (torusQuotient x) () = OriginalCanonicalMeasurement.nativeMeasurement
      (Sampling.canonicalSamplingMeasurement (projectedStress F) hμ) (torusQuotient x) S)
    (i : Fin n) :
    self.val (torusQuotient x) () i = tensorPairing (projectedStress F x i) S := by
  rw [hval, OriginalCanonicalMeasurement.nativeMeasurement_apply, representative_on_core hμ hcell hx,
    Sampling.canonicalSamplingMeasurement_apply, measurement_one_on_core hμ hx, one_mul]

private theorem complete_source_component {n : ℕ}
    (leading target self : SmoothResidual n) (z : Torus n) (i : Fin n)
    (P H S : MetricTensor n)
    (hleading : leading.val z () i = tensorPairing P H)
    (hself : self.val z () i = tensorPairing P S) :
    (OriginalCompleteForcing.completeSource leading target self).val z () i =
      tensorPairing P H + target.val z () i - tensorPairing P S := by
  change leading.val z () i + target.val z () i - self.val z () i = _
  rw [hleading,hself]

private theorem cancel_initialized_pairing {n : ℕ}
    (P B H S J : MetricTensor n) (residual forcing target : ℝ)
    (hres : residual = forcing + tensorPairing P (B + S) - tensorPairing P J)
    (hg : forcing = tensorPairing P H + target - tensorPairing P S)
    (hcancel : tensorPairing P (B + H) = 0) :
    residual = target - tensorPairing P J := by
  have hadd (A D : MetricTensor n) : tensorPairing P (A + D) =
      tensorPairing P A + tensorPairing P D := by
    simp only [tensorPairing, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hadd] at hres hcancel
  linarith only [hres,hg,hcancel]

end JanetCartan.PhysicalMean.OriginalCanonicalCompletedResidual
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalCompletedResidual
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate

private def app (name : Name) (args : Array Expr) : Expr := mkAppN (mkConst name) args

private def localTerm (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)

private def save (params : Array Expr) (proof : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params (← inferType proof))
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  let env ← getEnv
  for term in #[type,value] do
    let missing := term.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual completed residual: missing producers {missing.toList}"
    if term.hasFVar || term.hasMVar || term.hasLevelMVar || term.hasLooseBVars || term.hasSorry then
      throwError "actual completed residual: unresolved or extra input"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := `JanetCartan.PhysicalMean.OriginalCanonicalCompletedResidual.residual_eq_projected_core_defect
  addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
  addDocStringCore name "The full source with the ACTUAL original leading50 and selected sampled self50 yields the exact projected initialized physical defect on the unchanged original closed core. The target and source are DATA; every background, projected cancellation and E/Q identity is supplied by its original producer. No second forcing, cutoff, inverse or successful-source premise is introduced (new:eq:qT-identity)."

elab "construct_original_completed_core_residual" : command => liftTermElabM do
  OriginalCanonicalSourceApplication.withActualQuadratic fun trial _ native _ _ => do
    let p := trial[:50].toArray
    let L := trial[51]!
    let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift p
    let selected := p ++ #[shift,L]
    let rawE ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear selected
    unless rawE.isAppOfArity `JanetCartan.PhysicalMean.fixedSourceLinear 28 do
      throwError "actual completed residual: exact selected linear28 changed"
    let .forallE _ Y _ _ := (← inferType rawE.getAppArgs[21]!).consumeMData
      | throwError "actual completed residual: original coerced source type missing"
    let rawCancel ← bodyAt `JanetCartan.PhysicalBackground.NativeMeasuredCancellation.on_exterior_plateau native
    unless rawCancel.isAppOfArity `JanetCartan.PhysicalBackground.retained_measured_physical_core_cancellation 64 do
      throwError "actual completed residual: native projected cancellation64 changed"
    let c := rawCancel.getAppArgs
    let n := c[0]!
    let N := c[1]!
    let mu := c[21]!
    let hr := c[22]!
    let hcell := c[23]!
    let F := c[34]!
    let core := app `JanetCartan.PhysicalBackground.NativeMeasuredCancellation.core native[:21].toArray
    let hooks := app `JanetCartan.PhysicalBackground.NativeMeasuredCancellation.core_plateau native[:21].toArray
    let leading := app `JanetCartan.PhysicalMean.OriginalCompleteForcing.leadingMean p
    let self := app `JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedSampleSelf p
    let Hfield := app `JanetCartan.PhysicalBackground.NativeAdmission.physicalMean native
    withLocalDeclNoLocalInstanceUpdate `target .default Y fun target => do
      withLocalDeclNoLocalInstanceUpdate `source .default Y fun source => do
        let forcing := app `JanetCartan.PhysicalMean.OriginalCompleteForcing.completeSource #[n,leading,target,self]
        withLocalDeclNoLocalInstanceUpdate `x .default (app `JanetCartan.Euclidean #[n]) fun x => do
          let hxType ← localTerm [(`K,core),(`x,x)] "x ∈ K"
          withLocalDeclNoLocalInstanceUpdate `hx .default hxType fun hx => do
            withLocalDeclNoLocalInstanceUpdate `component .default (app ``Fin #[n]) fun i => do
              let z := app `JanetCartan.torusQuotient #[n,x]
              let hxMeasured := Expr.proj ``And 0 (mkAppN hooks #[x,hx])
              let hres := app `JanetCartan.PhysicalMean.OriginalCanonicalCoreResidual.residual_eq_initialized_core_defect
                (selected ++ #[forcing,source,x,hx,i])
              let resType ← inferType hres
              unless resType.isAppOfArity ``Eq 3 do throwError "actual initialized residual is not an equality"
              let rhs := resType.getAppArgs[2]!
              unless rhs.isAppOfArity ``HSub.hSub 6 do throwError "actual initialized residual lost its final minus sign"
              let initialSum := rhs.getAppArgs[4]!
              let lastPair := rhs.getAppArgs[5]!
              unless initialSum.isAppOfArity ``HAdd.hAdd 6 &&
                  lastPair.isAppOfArity `JanetCartan.tensorPairing 3 do
                throwError "actual initialized residual lost its two original terms"
              let initialPair := initialSum.getAppArgs[5]!
              unless initialPair.isAppOfArity `JanetCartan.tensorPairing 3 do
                throwError "actual initialized residual lost its projected initial term"
              let P := initialPair.getAppArgs[1]!
              let initialTensor := initialPair.getAppArgs[2]!
              unless initialTensor.isAppOfArity ``HAdd.hAdd 6 do
                throwError "actual initialized residual lost the original base/self sum"
              let B := initialTensor.getAppArgs[4]!
              let S := initialTensor.getAppArgs[5]!
              let J := lastPair.getAppArgs[2]!
              let H := mkApp Hfield x
              let hLeadingValue := mkApp (app `JanetCartan.PhysicalMean.OriginalCompleteForcing.leading_mean_value p) z
              let hSelfValue := mkApp (app `JanetCartan.PhysicalMean.OriginalCompleteForcing.selected_sample_self_value p) z
              let hLeading := app ``leading_component_on_core
                #[n,N,mu,hr,hcell,F,leading,Hfield,x,hxMeasured,hLeadingValue,i]
              let hSelf := app ``self_component_on_core
                #[n,N,mu,hr,hcell,F,self,x,hxMeasured,S,hSelfValue,i]
              let hg := app ``complete_source_component #[n,leading,target,self,z,i,P,H,S,hLeading,hSelf]
              let hcancel := app `JanetCartan.PhysicalBackground.NativeMeasuredCancellation.cancellation
                (native ++ #[x,hx,i])
              let targetValue ← localTerm [(`t,target),(`z,z),(`i,i)] "t.val z () i"
              let proof := app ``cancel_initialized_pairing
                #[n,P,B,H,S,J,resType.getAppArgs[1]!,initialSum.getAppArgs[4]!,targetValue,hres,hg,hcancel]
              let params := p ++ #[L,target,source,x,hx,i]
              unless params.size == 56 do throwError "actual completed residual changed native56"
              save params proof
              logInfo "actual completed physical core residual56: same selected full source, original projected affine cancellation; target/source DATA"

end JanetCartan.PhysicalMean.OriginalCanonicalCompletedResidual
end

construct_original_completed_core_residual
