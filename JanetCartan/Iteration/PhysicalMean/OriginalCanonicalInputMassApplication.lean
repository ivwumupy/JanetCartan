module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputMassBudget
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalSourceTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import Lean

/-!
# Consumer of the sole original sampled tuple for Fourier mass

This module does not build a sampled tuple. It consumes task89's already checked
native53 dictionary and the unchanged task86 supplied-source input/detector
reader. All source-inverse fields are instantiated from task100. The genuine
full-source Picard profile is a subsequent obligation of task14
(`main:eq:primary-fixed-scales`, `app:ch_mean_pairs:eq:raw-adjoint-moments`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalInputMassApplication
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalMean.OriginalCanonicalInputMass
private def app (name : Name) (args : Array Expr) : Expr := mkAppN (mkConst name) args

private def get (fields : Array (Name × Expr)) (key : Name) : MetaM Expr := do
  let hits := fields.filter (fun p => p.1 == key)
  unless hits.size == 1 do throwError "actual unweighted mass: expected one {key}, found {hits.size}"
  return hits[0]!.2

private def binderKey (key : Name) (domain : Expr) (bi : BinderInfo) : Name :=
  if bi == .instImplicit && domain.isAppOf ``MetricSpace then `instMetricSpace
  else key.eraseMacroScopes

/-- Read, but do not reconstruct, the original physical source's exact unweighted
input and detector5. The result is closed over its original native53 data ABI. -/
def sourcePayloads : MetaM (Array (Name × Expr)) := do
  let result ← IO.mkRef (#[] : Array (Name × Expr))
  JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate.withActualSelectedSourceWave
    fun p _ input _ _ _ detector => do
      unless p.size == 53 do throwError "actual unweighted mass: source-wave ABI changed"
      let payload ← (detector.push (`input,input)).mapM fun (key,value) => do
        let closed ← instantiateMVars (← mkLambdaFVars p value)
        if closed.hasFVar || closed.hasMVar || closed.hasLevelMVar || closed.hasLooseBVars || closed.hasSorry then
          throwError "actual unweighted mass: source detector/input has an extra input"
        return (key,closed)
      result.set payload
  let payload ← result.get
  unless payload.size == 6 do throwError "actual unweighted mass: missing exact detector5 and input"
  return payload

private def sourceTail (p : Array Expr) (fields : Array (Name × Expr)) (key : Name)
    (domain : Expr) : MetaM Expr := withTransparency .default do
  let n ← get fields `n
  let e ← get fields `e
  let w ← mkAppM ``DFunLike.coe #[app `JanetCartan.CurrentMean.smoothResidualToL2 #[n],e]
  let regular := key == `hreg
  forallBoundedTelescope domain (some (if regular then 1 else 2)) fun args _ => do
    let q := args[0]!
    let hw := app `JanetCartan.CurrentMean.smoothResidualToL2_mem #[n,e,q]
    let producer ← if regular then get fields `Q0_regular else
      pure (app `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles.inverse_profile p[:50].toArray)
    mkLambdaFVars args (mkAppN producer #[q,w,hw])

private def save (mode : Nat) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  unless p.size == 55 do throwError "actual unweighted mass: expected native53 plus source/sample DATA"
  let statement := root ++ `fourierMass_statement
  let resultType := if mode == 0 then mkSort .zero else app statement p
  let resultValue := if mode == 0 then target else proof
  let type ← instantiateMVars (← mkForallFVars p resultType)
  let value ← instantiateMVars (← mkLambdaFVars p resultValue)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual unweighted mass: missing producers {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual unweighted mass: unresolved or extra input"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := if mode == 0 then statement else root ++ `fourierMass_le
  if mode == 0 then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The literal task86 supplied-source physical wide input has Fourier mass at most Cmass44 times its H^(n+1) source norm. The SAME task89 sampled tuple, task100 global inverse and original detector bound ONE prove every analytic field; no successful mass/source, inverse weight, new cutoff or altered Fourier normalization (main:eq:primary-fixed-scales)."

/-- Apply only the supplied canonical primitive dictionary. The extra two
arguments are the arbitrary smooth source and its original sampled index. -/
partial def publish (mode : Nat) (payload : Array (Name × Expr)) (p : Array Expr)
    (original : Array (Name × Expr)) : MetaM Unit := do
  unless mode < 2 do throwError "actual unweighted mass: unknown publication mode"
  unless p.size == 53 do throwError "actual unweighted mass: expected the sole native50+moment guards+prefix tuple"
  let inv := `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles
  let common := original ++ #[(`Cinv,app (inv ++ `Cinv) p[:44].toArray),
    (`hCinv,app (inv ++ `Cinv_nonneg) p[:44].toArray),
    (`hn,mkApp (mkConst ``Nat.succ_pos) p[0]!),(`cutoff,p[52]!)]
  let name := `JanetCartan.PhysicalMean.OriginalCanonicalInput.sampled_wideInput_fourierMass_le
  let info ← getConstInfo name
  let levels := info.levelParams.map (fun _ => Level.zero)
  let rec go (type : Expr) (args : Array Expr) (fields : Array (Name × Expr))
      (sources : Array Expr) : MetaM Unit := do
    match type with
    | .forallE binder domain body bi =>
      let key := binderKey binder domain bi
      if key == `e || key == `i then
        withLocalDeclNoLocalInstanceUpdate binder bi domain fun value =>
          go (body.instantiate1 value) (args.push value) (fields.push (key,value)) (sources.push value)
      else if key == `hreg || key == `hinverse then
        let value ← sourceTail p fields key domain
        go (body.instantiate1 value) (args.push value) (fields.push (key,value)) sources
      else if key == `d then
        unless sources.size == 2 do throwError "actual unweighted mass: source/sample DATA order changed"
        let data := p[:50].toArray ++ #[p[52]!,sources[0]!,sources[1]!]
        let actualPayload := payload.map (fun (key,value) => (key,(value.beta data).headBeta))
        let M ← get actualPayload `M
        let one ← withTransparency .default <| Term.TermElabM.run'
          (JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate.termWith [] "(1 : ℝ)")
        unless ← withTransparency .default (isDefEq M one) do
          throwError "actual unweighted mass: original detector no longer has bound ONE"
        let fields := fields ++ actualPayload
        let value ← get fields key
        go (body.instantiate1 value) (args.push value) fields sources
      else
        let value ← get fields key
        go (body.instantiate1 value) (args.push value) fields sources
    | target =>
      unless sources.size == 2 do throwError "actual unweighted mass: expected precisely source/sample DATA"
      let some cost := target.find? (·.isAppOf `JanetCartan.PhysicalMean.OriginalCanonicalInput.sourceMassConstant)
        | throwError "actual unweighted mass: lost static original cost"
      let some input := target.find? (·.isAppOf `JanetCartan.PhysicalMean.OriginalCanonicalInput.wideInput)
        | throwError "actual unweighted mass: lost unweighted original input"
      unless input.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalInput.wideInput 8 do
        throwError "actual unweighted mass: original input8 changed"
      let physicalInput ← get fields `input
      let namedCost := app (root ++ `Cmass) p[:44].toArray
      let target := target.replace fun e =>
        if e == cost then some namedCost else if e == input then some physicalInput else none
      let proof := mkAppN (mkConst name levels) args
      save mode (p ++ sources) proof target
      if mode == 0 then
        logInfo "actual unweighted Fourier mass statement55: literal original physical input/detector, proof separate"
      else
        logInfo "actual unweighted Fourier mass55: SAME original physical input/detector, sole sampled tuple/global inverse, Cmass44*H^(n+1) source"
  go (info.type.instantiateLevelParams info.levelParams levels) #[] common #[]

end JanetCartan.PhysicalMean.OriginalCanonicalInputMassApplication
end
