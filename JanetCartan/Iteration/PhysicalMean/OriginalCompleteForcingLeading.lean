module
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingLeadingTemplate
import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCurrentApplication
import all JanetCartan.Iteration.PhysicalBackground.RetainedMeasuredCancellation
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMeasurementApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivative
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Lean Meta Elab Command
open JanetCartan.PhysicalMean.OriginalBackgroundHermitianTemplate (bodyAt withActualRow)
open JanetCartan.PhysicalMean.OriginalCanonicalCurrentApplication (nativeCurrentArguments)
meta section
private def ns := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def bg := `JanetCartan.PhysicalMean.OriginalBackgroundHermitian
private def adm := `JanetCartan.PhysicalBackground.NativeAdmission
private def app (c : Name) (as : Array Expr) := mkAppN (mkConst c) as
private partial def dropLets (e : Expr) : Expr :=
  match e.consumeMData.headBeta with
  | .letE _ _ v b _ => dropLets (b.instantiate1 v)
  | z => z
private def labeled (c : Name) (args : Array Expr) : MetaM (Array (Name × Expr)) := do
  let mut t := (← getConstInfo c).type
  let mut out := #[]
  for arg in args do
    t := dropLets t
    let .forallE n _ b _ := t | throwError "missing named native geometry binder {out.size}"
    out := out.push (n.eraseMacroScopes,arg)
    t := b.instantiate1 arg
  return out
private def save (key : Name) (p : Array Expr) (v t : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p t)
  let value ← instantiateMVars (← mkLambdaFVars p v)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "leading source {key}: missing {missing.toList}"
    if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasSorry then throwError "leading source {key}: introduced an unclosed hypothesis"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  if data then addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The actual original native50 measured affine leading field on the same global admission39, with unchanged chi squared, density and measurement. No added cutoff or transported-comparison bound (new:eq:mean-source)."
  logInfo m!"actual original leading source {key}/{p.size}"
private def withLeading (next : Array Expr → Array Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit :=
  withTransparency .reducible <| withActualRow fun d => do
    let p := d.parameters[:50].toArray
    let native ← nativeCurrentArguments d
    let outer ← bodyAt `JanetCartan.PhysicalBackground.NativeMeasuredCancellation.on_exterior_plateau native
    unless outer.isAppOfArity `JanetCartan.PhysicalBackground.retained_measured_physical_core_cancellation 64 do throwError "not the literal native cancellation producer"
    let raw := dropLets (← bodyAt outer.getAppFn.constName! outer.getAppArgs)
    let consumer := `JanetCartan.PhysicalBackground.physicalDensityMean_core_cancellation
    unless raw.isAppOf consumer do throwError "not actual original physical geometry {raw.getAppFn.constName?}/{raw.getAppNumArgs}"
    let names ← labeled consumer raw.getAppArgs
    let get := JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate.lookup names
    let C := d.mean70[37]!
    unless C.isAppOfArity `JanetCartan.Sampling.canonicalSamplingMeasurement 4 do throwError "different common measurement"
    let ca := C.getAppArgs
    let hcell := app `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.observation_cell d.native64[:22].toArray
    let hC := app (bg ++ `commonC_smooth) p
    let n ← get `n
    let args := #[n,← get `N,← get `ι,← get `inst,← get `d,← get `χ,← get `hχ,← get `hχc,
      ca[2]!,ca[3]!,hcell,ca[1]!,hC,← get `V,← get `hV,← get `hχV,
      ← get `hYphysical,← get `hνphysical,← get `hξphysical,← get `v,raw.getAppArgs[raw.getAppNumArgs-2]!]
    let construct := mkAppN (mkConst (ns ++ `nativeAffineLeading) [.zero]) args
    let H := mkAppN (mkConst `JanetCartan.PositiveBackground.physicalDensityMean [.zero])
      #[args[0]!,args[1]!,args[2]!,args[3]!,args[4]!,args[5]!,args[19]!]
    let namedH := app (adm ++ `physicalMean) native
    let ht ← inferType construct
    next p native construct H namedH
    unless ht.isAppOf `Subtype do logInfo m!"leading result sort head {ht.getAppFn.constName?}"

run_elab withLeading fun p _ construct H _ => do
  save `physicalAffineMean p H (← inferType H) true
  save `leadingMean p construct (← inferType construct) true

run_elab withLeading fun p _ _ H namedH => do
  let v ← mkEqRefl H
  save `physicalAffineMean_eq_original p v (← mkEq (app (ns ++ `physicalAffineMean) p) namedH)

run_elab withLeading fun p native construct H namedH => do
  let info ← getConstInfo construct.getAppFn.constName!
  let some body := info.value? (allowOpaque := true) | throwError "missing actual leading constructor"
  let raw := ((body.instantiateLevelParams info.levelParams construct.getAppFn.constLevels!).beta construct.getAppArgs).headBeta
  unless raw.isAppOf (ns ++ `measuredLeadingResidual) do throwError "changed actual leading constructor"
  let C := raw.getAppArgs[1]!
  let pair ← bodyAt (ns ++ `measuredLeadingResidual) raw.getAppArgs
  unless pair.isAppOfArity ``Subtype.mk 4 do throwError "not the actual smooth residual constructor"
  let n := mkApp (mkConst ``Nat.succ) p[0]!
  let ztype := mkApp (mkConst `JanetCartan.Torus) n
  withLocalDeclNoLocalInstanceUpdate `z .default ztype fun z => do
    let f := app (ns ++ `leadingMean) p
    let val := mkAppN (.proj ``Subtype 0 f) #[z,mkConst ``Unit.unit]
    let literal := pair.getAppArgs[2]!.beta #[z,mkConst ``Unit.unit]
    let rhs := literal.replace fun e => if e == C then some (app (bg ++ `commonC) p)
      else if e == H then some namedH else none
    unless (rhs.find? (· == namedH)).isSome && (rhs.find? (· == app (bg ++ `commonC) p)).isSome do
      throwError "lost exact affine mean or original common measurement in value"
    let ty := mkApp3 (mkConst ``Eq [.one]) (mkApp (mkConst `JanetCartan.Euclidean) n) val rhs
    let pr := mkApp2 (mkConst ``Eq.refl [.one]) (mkApp (mkConst `JanetCartan.Euclidean) n) literal
    save `leading_mean_value p (← mkLambdaFVars #[z] pr) (← mkForallFVars #[z] ty)
  unless native.size == 39 do throwError "lost exact native39"
end
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.leadingMean
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.physicalAffineMean_eq_original
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.leading_mean_value
