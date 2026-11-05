module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalSourceTemplate
public import JanetCartan.Iteration.PhysicalPairs.CombinedNode
/-! # Exact source-data identification of the original angular amplitude

The actual unweighted component adjoint, global inverse, fixed prefix, and ONE
selected shift are retained. The derivative is the complete full-angular
whole-source derivative, including its zero-safe carrier factor. This identity
has no source-profile premise and introduces no Fourier-support estimate.
Consumer: the R-scale source-tame amplitude in `main:eq:mean-final-amplitude`
and the SAME amplitude in `main:prop:pairs`.
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSourceAmplitudeTemplate
open Lean Meta Elab Command
open PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSourceAmplitude
private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args
private def termWith (vars : List (Name × Expr)) (code : String)
    (goal : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code goal)
private def save (key : Name) (params : Array Expr) (value : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "original source amplitude: unresolved declaration {key}"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "original source amplitude: missing {missing.toList}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  liftM <| IO.eprintln s!"original source amplitude: kernel checking {name}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  liftM <| IO.eprintln s!"original source amplitude: kernel passed {name}"

/-- Identify the actual canonical source derivative with the observed amplitude
of the SAME whole physical angular field. The observation cutoff is still
visible; its original plateau is a separate geometric specialization. -/
elab "identify_original_source_angular_amplitude " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "original source amplitude: unknown publication mode"
  withActualSelectedSourceWave fun params source input field _ native64 _ => do
    unless params.size == 53 && native64.size == 64 do
      throwError "original source amplitude: changed selected source53/native64 boundary"
    unless input.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalInput.wideInput 8 &&
        field.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalLocalWaves.Combined.field 69 do
      throwError "original source amplitude: changed unweighted input or actual full field"
    let ia := input.getAppArgs
    let sample := field.getAppArgs[64:68].toArray
    let node := app `JanetCartan.SeparatedSampling.node sample[1:4].toArray
    let native := app `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.G_native
      (native64 ++ #[node,input])
    let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift params[:50].toArray
    let G := app `JanetCartan.PhysicalMean.OriginalCanonicalSampled.Gprefix
      (params[:50].toArray ++ #[shift,params[50]!])
    forallBoundedTelescope (← inferType native) (some 1) fun z _ => do
      unless z.size == 1 do throwError "original source amplitude: missing original torus point"
      let hnative := mkAppN native z
      let equality ← inferType hnative
      unless equality.isAppOfArity ``Eq 3 do throwError "original source amplitude: changed native equality"
      let rhs := equality.getAppArgs[2]!
      unless rhs.isAppOfArity ``HSMul.hSMul 6 do
        throwError "original source amplitude: original observation factor missing"
      let derivative := rhs.getAppArgs[5]!
      let original := `JanetCartan.CanonicalAtomRealization.wholeSourceCorrectedDerivative
      unless derivative.isAppOf original do
        throwError "original source amplitude: not the complete demodulated whole-source derivative"
      let args := derivative.getAppArgs
      let point := args.back!
      let identity := app `JanetCartan.CurrentMean.sampledDerivativeAmplitude_wholeSourceCorrectedWave_eq args.pop
      let pointwise ← mkAppM ``congrFun #[identity,point]
      let reversed ← mkAppM ``Eq.symm #[pointwise]
      let transport ← mkAppM ``congrArg #[rhs.appFn!,reversed]
      let proof ← mkAppM ``Eq.trans #[hnative,transport]
      let proved ← inferType proof
      unless proved.isAppOfArity ``Eq 3 do throwError "original source amplitude: lost exact matrix identity"
      let canonical ← termWith [(`A,ia[3]!),(`G,G),(`Q0,ia[4]!),(`r,source),(`z,z[0]!),(`i,params[52]!)]
        "(JanetCartan.PhysicalMean.fixedSourceDerivative A G Q0 r).val z i"
      let target ← mkEq canonical proved.getAppArgs[2]!
      let all := params ++ z
      if mode.getNat == 0 then
        save `observed_angular_statement all target true (some (mkSort .zero))
      else
        save `observed_angular_amplitude all proof false
          (some (app (ns ++ `observed_angular_statement) all))
end JanetCartan.PhysicalPairs.OriginalSourceAmplitudeTemplate
end
