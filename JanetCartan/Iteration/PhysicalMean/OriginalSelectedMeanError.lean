module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularity
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanErrorTransfer
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Actual completed mean error equals the same full-source Picard error

All W/target/full-self smoothness and symmetry fields are supplied by their
original producers. Only the INITIAL geometric threshold and finite-moment
order reach are numeric inputs. The RHS is the SAME full selected forcing
Picard residual, with its original E/Q/shift/prefix and unweighted source.
Consumer: its genuine finite-precision estimate and physical cutoff/core join
(`new:eq:mean-error-formula`, `main:prop:mean`). No successful source profile,
mean estimate or normal completion premise is added.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
@[expose] noncomputable section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanError
private theorem error_of_same_residual {n : ℕ} (T : MetricTensor n) (C : ℝ)
    (a b : Euclidean n) (hab : a = b) (h : ‖T‖ ≤ C*‖b‖) : ‖T‖ ≤ C*‖a‖ := by
  rw [hab]
  exact h
end JanetCartan.PhysicalMean.OriginalSelectedMeanError
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanError
open Lean Meta Elab Command
open OriginalSelectedMeanDataTemplate (withActualSelectedFields)
private def root := `JanetCartan.PhysicalMean.OriginalSelectedMeanData
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "actual selected mean error: unavailable {key}"
  return (value.beta p).headBeta
private def termWith (bindings : List (Name × Expr)) (text : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings text)

run_elab withActualSelectedFields fun p f native native39 _ => do
  withTransparency .default do
    let selected := p[:52].toArray
    let stage := p[:54].toArray
    let W := app (root ++ `initializedField) stage
    let T := app (root ++ `normalizedTarget) selected
    let H := app (root ++ `fullSampledSelf) stage
    let hW := app (root ++ `initializedField_smooth) stage
    let U := (← inferType hW).getAppArgs.back!
    let hT := app (root ++ `normalizedTarget_smooth) selected
    let hH := app (root ++ `fullSampledSelf_smooth) stage
    let hTon ← termWith [(`h,hT),(`T,T),(`U,U)] "(h.contDiffOn : ContDiffOn ℝ ∞ T U)"
    let hHon ← termWith [(`h,hH),(`H,H),(`U,U)] "(h.contDiffOn : ContDiffOn ℝ ∞ H U)"
    let S := app `JanetCartan.PhysicalMean.OriginalMeanErrorTransfer.Serror native[:44].toArray
    let gate ← termWith [(`S,S),(`R0,native[44]!)] "S ≤ R0"
    let targetArgs := f[4]!.getAppArgs
    let momentGate ← termWith [(`m,targetArgs[5]!),(`R,targetArgs[4]!)] "(2 : ℝ)*(m : ℝ) ≤ R"
    withLocalDeclNoLocalInstanceUpdate `hErrorReached .default gate fun hS => do
      withLocalDeclNoLocalInstanceUpdate `hMomentFrequency .default momentGate fun hR => do
        let x := p[54]!
        let hx := p[55]!
        let c ← bodyAt `JanetCartan.PhysicalBackground.NativeMeasuredCancellation.on_exterior_plateau native39
        unless c.isAppOfArity `JanetCartan.PhysicalBackground.retained_measured_physical_core_cancellation 64 do
          throwError "actual selected mean error: changed original core geometry"
        let ca := c.getAppArgs
        let plateau := app `JanetCartan.PhysicalBackground.NativeMeasuredCancellation.core_plateau
          (native39[:21].toArray ++ #[x,hx])
        let small := Expr.proj ``And 0 plateau
        let buffer := app `JanetCartan.PhysicalBackground.NativeSourceGeometry.measurement_buffer native39[:21].toArray
        let b := app `JanetCartan.PhysicalSeed.OriginalBoundary.b native39[:2].toArray
        let hxWide ← termWith [(`n,f[0]!),(`x,x),(`b,b),(`mu,ca[21]!),(`hm,ca[22]!),(`hx,small),(`buffer,buffer)]
          ("(by have hm' : 0 < mu := hm; exact Metric.ball_subset_closedBall " ++
           "(buffer (Metric.closedBall_subset_closedBall (show mu ≤ 6*mu by linarith only [hm']) hx)) " ++
           ": x ∈ Metric.closedBall (0 : JanetCartan.Euclidean n) b)")
        let transfer := app `JanetCartan.PhysicalMean.OriginalMeanErrorTransfer.smooth_and_error
          (native ++ #[hS,W,T,H,hW,hTon,hHon])
        let htSymm := app (root ++ `normalizedTarget_isSymm) (selected ++ #[hR,x])
        let hHSymm := app (root ++ `fullSampledSelf_isSymm) p[:55].toArray
        let bound := mkAppN (Expr.proj ``And 1 transfer) #[x,hxWide,htSymm,hHSymm]
        let boundType ← inferType bound
        unless boundType.isAppOfArity ``LE.le 4 do throwError "actual selected mean error: changed error inequality"
        let normError := boundType.getAppArgs[2]!
        let rhs := boundType.getAppArgs[3]!
        unless normError.isAppOfArity ``Norm.norm 3 && rhs.isAppOfArity ``HMul.hMul 6 do
          throwError "actual selected mean error: changed physical Frobenius norm or coefficient"
        let residual := app (root ++ `residual_eq_reduced_physical_residual) p
        let equality ← inferType residual
        let proof := app ``error_of_same_residual
          #[f[0]!,normError.getAppArgs[2]!,rhs.getAppArgs[4]!,equality.getAppArgs[1]!,
            equality.getAppArgs[2]!,residual,bound]
        let proofType ← inferType proof
        let some rawCompleted := proofType.find? (·.isAppOfArity `JanetCartan.CurrentMean.completedMeanField 6)
          | throwError "actual selected mean error: genuine transfer lost its single completedMeanField"
        let completed := app (root ++ `completedMean) stage
        let target := proofType.replace fun e => if e == rawCompleted then some completed else none
        unless (target.find? (· == completed)).isSome do
          throwError "actual selected mean error: lost the SAME single completion"
        let params := stage ++ #[hS,hR,x,hx]
        let type ← instantiateMVars (← mkForallFVars params target)
        let value ← instantiateMVars (← mkLambdaFVars params proof)
        let env ← getEnv
        for e in #[type,value] do
          let missing := e.getUsedConstants.filter (fun key => (env.find? key).isNone)
          unless missing.isEmpty do throwError "actual selected mean error: missing {missing.toList}"
          if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
            throwError "actual selected mean error: extra or unresolved input"
        let (type,value) := Lean.ShareCommon.shareCommon (type,value)
        let name := root ++ `completedMean_error_le_picard_residual
        addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
        addDocStringCore name "Actual completed mean error on the original core bounded by the SAME selected full-source Picard residual. All W/target/full-self regularity and tensor symmetry proved from original data; only numeric INITIAL Serror≤R0 and finite-moment2m≤R gates. No source, current-frame or mean success premise (new:eq:mean-error-formula)."
        logInfo "actual completed mean error58: SAME full-source Picard residual, all field regularity/symmetry supplied, only two numeric gates"
end JanetCartan.PhysicalMean.OriginalSelectedMeanError
end
