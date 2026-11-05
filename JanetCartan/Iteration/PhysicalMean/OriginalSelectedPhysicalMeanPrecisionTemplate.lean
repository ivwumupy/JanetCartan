module
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanErrorPrecisionTransfer
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularityTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularityTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean
/-!
# Apply genuine original Picard precision to the same physical mean

This application metadata is checkable independently of the pending actual
physical58/precision55 exports. Its execution leaf must supply both actual
producers. No analytic field is ever added to a theorem telescope: only INITIAL
auxiliary/error reaches and CURRENT moment/precision/frame reaches remain
(`main:eq:mean-equation`, `main:prop:mean`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedPhysicalMeanPrecision
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalSelectedMeanData
private def precisionRoot := `JanetCartan.PhysicalMean.OriginalFullSourcePicard
private def source := `JanetCartan.PhysicalMean.OriginalCanonicalSource
private def transfer := `JanetCartan.PhysicalMean.OriginalMeanErrorPrecisionTransfer
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def termWith (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)
private def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual physical precision: missing {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual physical precision: extra or unresolved analytic/numeric field"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  liftM <| IO.eprintln s!"actual physical precision: kernel checking {name}/{p.size}"
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual SAME full-source Picard/Schwartz mean error from genuine115 C1 precision and physical59 germ/error specialized by the existing fixed44 final-core containment; accuracy precedes history. Initial Serror, initial Saux and CURRENT finite-moment/precision/frame reaches are only numerical. No analytic success premise (main:eq:mean-equation)."
  liftM <| IO.eprintln s!"actual physical precision: kernel passed {name}/{p.size}"
elab "prove_original_physical_mean_precision " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "actual physical precision: unknown mode"
  OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f native native39 _ => do
    withTransparency .default do
      let selected := p[:52].toArray
      let fixed := native[:44].toArray
      let n := f[0]!
      let hn := native39[1]!
      let R := app `JanetCartan.historyScale #[native[44]!,mkConst `JanetCartan.growthExponent,native[46]!]
      withLocalDeclNoLocalInstanceUpdate `accuracy .default (mkConst ``Real) fun accuracy => do
        let a ← if mode.getNat == 0 then pure accuracy else
          termWith [(`a,accuracy)] "a + 1"
        let beforeHistory := selected[:33].toArray.push accuracy
        let precisionArgs := (selected[:33].toArray.push a) ++ selected[33:].toArray
        let precision := app (precisionRoot ++ `residual_cNorm) precisionArgs
        forallBoundedTelescope (← inferType precision) (some 2) fun numeric precisionType => do
          unless numeric.size == 2 && precisionType.isAppOfArity ``LE.le 4 do
            throwError "actual physical precision: changed original115 numerical gates"
          let some residual := precisionType.find? (·.isAppOfArity (source ++ `selected_residualWithForcing) 53)
            | throwError "actual physical precision: lost SAME original residual53"
          let J := residual.getAppArgs[50]!
          let count := residual.getAppArgs[52]!
          unless !J.hasLooseBVars && J.isAppOfArity `JanetCartan.RawInputPartition.cutoffCount 1 do
            throwError "actual physical precision: J changed after Picard count"
          let hPrecision := mkAppN precision numeric
          let eps := precisionType.getAppArgs[3]!
          let error := app (root ++ `physicalMean_error_on_common_core) (selected ++ #[J,count])
          forallBoundedTelescope (← inferType error) (some 4) fun ep errorType => do
            unless ep.size == 4 && errorType.isAppOfArity ``LE.le 4 do
              throwError "actual physical precision: changed fixed-core58 error boundary"
            let E := errorType.getAppArgs[2]!.getAppArgs.back!
            let x := ep[2]!
            let proof := app (transfer ++ `physical_error_of_residual_cNorm)
              #[n,hn,residual,E,x,eps,mkAppN error ep,hPrecision]
            let params := beforeHistory ++ selected[33:].toArray ++ numeric ++ ep
            if mode.getNat == 0 then
              save `physicalMean_error_le_precision_on_common_core params proof (← inferType proof)
            else
              let C := app `JanetCartan.UniformStep.projectedStressResidualConstant #[n,hn]
              let frameGate ← termWith [(`C,C),(`R,R)] "C ≤ R"
              withLocalDeclNoLocalInstanceUpdate `hCurrentFrameReach .default frameGate fun hFrame => do
                let hInitial ← mkAppM ``le_trans
                  #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed,native[45]!]
                let facts ← mkAppM `JanetCartan.PhysicalMean.fixedPicard_history_scale_facts #[hInitial,native[46]!]
                let hR := Expr.proj ``And 0 facts
                let e := (← inferType proof).getAppArgs[2]!
                let final := app (transfer ++ `frame_error_le_requested_precision)
                  #[e,C,R,accuracy,hR,hFrame,proof]
                save `physicalMean_error_le_requested_precision_on_common_core (params.push hFrame) final (← inferType final)
end JanetCartan.PhysicalMean.OriginalSelectedPhysicalMeanPrecision
end
