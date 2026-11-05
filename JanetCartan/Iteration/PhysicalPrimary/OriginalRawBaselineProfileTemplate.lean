module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryAmplitude
public import JanetCartan.Iteration.PhysicalPairs.OriginalBaselineAmplitudeProfiles
import all JanetCartan.Iteration.PhysicalPairs.OriginalBaselineAmplitudeProfiles
import all JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryAmplitude
public meta import Lean
/-!
# The same outer-node slice of the before-response raw derivative matrix

Consumer: the baseline plus full-source raw derivative factorization in
`main:eq:primary-strain`. Reuse the original outer-admission compact membership
and the existing physical-slice calculus, but apply the independently proved
BEFORE-B amplitude and its raw coefficient jets. Neither corrected amplitude
bounds nor an inner angular nonzero condition is used. The fixed-row budget
precedes every initial scale, history, source, sample, and derivative order.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalPrimary.OriginalRawBaselineProfileTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPrimary.OriginalRawBaselineProfiles
private def raw := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryAmplitude
private def parent := `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.Native
private def baseline := `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "raw baseline: missing original metadata {key}"
  return (value.beta p).headBeta
private def save (key : Name) (p : Array Expr) (value target : Expr)
    (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "raw baseline: extra or unresolved input in {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "raw baseline: missing original witness {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual raw baseline {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The genuine unscaled BEFORE-B baseline derivative matrix at the SAME original outer node. Actual raw52 smoothness/jets and original outer-only compact admission give all physical T^q jets on the unchanged whole chart, with static original-row C44 before history/target/source/sample. No inner angular nonzero condition, corrected-G bound, sample weight, or analytic profile premise (main:eq:primary-strain)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "raw baseline: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS actual raw baseline {key}/{p.size}: {axioms}"

/-- Sum only original fixed rows, never sampled labels. -/
def withBudget (next : Array Expr → Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (raw ++ `C)).type (some 44) fun p rest => do
    unless p.size == 44 && rest.isForall do throwError "raw baseline: static44/row changed"
    let rows := app (raw ++ `C) p
    let rowType := rest.bindingDomain!
    let concrete ← bodyAt rowType.getAppFn.constName! rowType.getAppArgs
    let inst ← synthInstance (mkApp (mkConst ``Fintype [.zero]) concrete)
    let args := #[rowType,inst,rows]
    let total := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalPdoProfiles.finite_profile_majorant [.zero]) args
    next p total args

/-- Retain the original outer nonzero-weight admission; no inner angular guard. -/
def withActual (next : Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  let pointKey := baseline ++ `original_chart_point
  forallBoundedTelescope (← getConstInfo pointKey).type (some 57) fun p rest => do
    unless p.size == 57 do throwError "raw baseline: native52/outer5 changed"
    forallBoundedTelescope rest (some 2) fun xy membership => do
      unless xy.size == 2 && membership.isAppOfArity ``Membership.mem 5 do
        throwError "raw baseline: original chart membership changed"
      let point := membership.getAppArgs[4]!
      unless point.isAppOfArity ``Prod.mk 4 do throwError "raw baseline: joint outer point changed"
      let c := point.getAppArgs[3]!
      let fixed := p[:44].toArray
      let row := fixed.push p[50]!
      let native := p[:52].toArray
      let A := app (raw ++ `amplitude) native
      let rawBody ← bodyAt (raw ++ `amplitude) native
      unless rawBody.isAppOfArity `JanetCartan.RawPrimary.fullDerivativeAmplitude 14 do
        throwError "raw baseline: not the BEFORE-B full derivative amplitude"
      let a := rawBody.getAppArgs
      -- Read ONLY the existing profile's domain: no corrected profile proof is used.
      let parentType ← inferType (app (baseline ++ `parent_slice_profile) p)
      let X := parentType.getAppArgs[0]!.getAppArgs[10]!
      unless X.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart 23 do
        throwError "raw baseline: not the unchanged whole original chart"
      let J := app (parent ++ `J) row
      let O := app (parent ++ `Ω) row
      let B ← mkLambdaFVars #[xy[0]!] (mkApp A point)
      let heq ← mkLambdaFVars xy (← mkEqRefl (mkApp A point))
      let hjet := app (raw ++ `jets) native
      let T := app `JanetCartan.currentCoefficientScale #[p[44]!,p[46]!]
      let rpar ← forallBoundedTelescope (← inferType hjet) (some 3) fun qp inequality => do
        unless inequality.isAppOfArity ``LE.le 4 do throwError "raw baseline: raw jet inequality changed"
        let power := inequality.appArg!.appArg!
        let exponent := power.appArg!
        unless exponent.appFn!.appArg! == qp[0]! do throwError "raw baseline: original reserve changed"
        unless ← isDefEq power.appFn!.appArg! T do throwError "raw baseline: not coefficient scale"
        return exponent.appArg!
      let hR ← mkAppM ``le_trans #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed,p[45]!]
      let hT := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
        #[p[44]!,hR,p[46]!]
      let proof := app (baseline ++ `Calculus.baseline_profile_of_parent)
        #[a[0]!,a[1]!,X,app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_open X.getAppArgs,
          J,O,app (parent ++ `Ω_open) row,app (parent ++ `J_in_Ω) row,A,app (raw ++ `smooth) native,
          B,c,heq,app pointKey p,app (raw ++ `C) row,app (root ++ `Cbaseline) fixed,
          app (raw ++ `C_nonneg) row,app (root ++ `row_le_Cbaseline) row,T,hT,rpar,hjet]
      next p B proof

elab "publish_actual_raw_baseline " which:num : command => liftTermElabM do
  let mode := which.getNat
  unless mode < 5 do throwError "raw baseline: unknown publication mode"
  if mode < 3 then
    withBudget fun p total args => do
      if mode == 0 then save `Cbaseline p total (← inferType total) true
      else
        let key := if mode == 1 then `finite_profile_majorant_nonneg else `le_finite_profile_majorant
        let proof := mkAppN (mkConst (`JanetCartan.PhysicalPrimary.OriginalPdoProfiles ++ key) [.zero]) args
        let target := (← inferType proof).replace fun e =>
          if e == total then some (app (root ++ `Cbaseline) p) else none
        save (if mode == 1 then `Cbaseline_nonneg else `row_le_Cbaseline) p proof target
  else
    withActual fun p B proof => do
      let fieldArgs := p[:56].toArray
      if mode == 3 then save `baseline fieldArgs B (← inferType B) true
      else
        let named := app (root ++ `baseline) fieldArgs
        let target := (← inferType proof).replace fun e => if e == B then some named else none
        unless (target.find? (· == named)).isSome do throwError "raw baseline: actual field disappeared"
        save `baseline_profile p proof target
end JanetCartan.PhysicalPrimary.OriginalRawBaselineProfileTemplate
end
