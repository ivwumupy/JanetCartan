module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.DataTemplate
public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledPolynomial
public meta import Lean

/-! # The existing low-reserve graph gate on primary source labels

The graph's coefficient threshold is its own fixed original choice. It is
not compared to the separately chosen higher-reserve phase threshold. The
existing signed initial threshold covers it at the actual construction.
Only that numerical reach restricts the original labels here; their history,
source, node, phase and inverse are unchanged (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.ObservedLabelsTemplate

open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def body (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let some value := ci.value? (allowOpaque := true) |
    throwError "primary graph admission: unavailable original body {ci.name}"
  return ((value.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta

/-- Read the exact low-reserve threshold from the existing graph itself. -/
def lowThreshold (d : RawProfilesTemplate.Data) : MetaM Expr := do
  let p := d.native.push d.baselineArgs[50]!
  let phase ← body (app (root ++ `PhaseProfiles.Native.phase) p)
  unless phase.isAppOfArity `JanetCartan.PhysicalPairs.SampledQuadrature.group_phase 42 do
    throwError "primary graph admission: original phase graph changed"
  let reached ← inferType phase.getAppArgs[37]!
  unless reached.isAppOfArity ``LE.le 4 && reached.getAppArgs[2]!.isAppOfArity
      `JanetCartan.PhysicalInitialization.OriginalRegular.Graph.S 34 do
    throwError "primary graph admission: original graph reach changed"
  let graph ← body (app `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial.GraphFamily
    reached.getAppArgs[2]!.getAppArgs)
  unless graph.isAppOfArity ``JanetCartan.PhysicalInitialization.OriginalSampledPolynomial.Histories 5 do
    throwError "primary graph admission: original measured graph family changed"
  pure graph.getAppArgs[4]!

private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "primary graph admission: later source/history operand escaped {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual primary low-graph admission {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The literal original GraphFamily low-reserve coefficient threshold is fixed before N, accuracy or history. Its numerical reach restricts the existing primary labels without changing any source, sample, phase, inverse or physical field. At actual canonical data the existing signed Tpair gate supplies this reach; no monotonicity of independently chosen thresholds or analytic success premise is assumed (main:eq:primary-strain)."
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "primary graph admission: nonstandard axioms {name}: {ax}"
  logInfo m!"PASS actual primary low-graph admission {key}/{p.size}: {ax}"

elab "publish_actual_primary_graph_admission " mode:num : command => liftTermElabM do
  unless mode.getNat ≤ 3 do throwError "primary graph admission: unknown mode"
  if mode.getNat ≤ 1 then
    DataTemplate.withData fun d => do
      let fixed := d.selected[:33].toArray
      let low ← lowThreshold d
      if mode.getNat == 0 then
        save `Sop fixed low (mkConst ``Real) true
      else
        unless low.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles.S 33 do
          throwError "primary graph admission: low operator threshold changed"
        let proof := app `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles.fact0 low.getAppArgs
        let target := (← inferType proof).replace fun e => if e == low then some (app (root ++ `Sop) fixed) else none
        save `Sop_ge_two fixed proof target
    return
  if mode.getNat == 2 then
    DataTemplate.withLabels fun fixed _ t d _ => do
      let guard ← mkAppM ``LE.le #[app (root ++ `Sop) fixed[:33].toArray,d.native[44]!]
      let predicate ← mkLambdaFVars #[t] guard
      let labels ← mkAppM ``Subtype #[predicate]
      save `ObservedLabels fixed labels (mkSort .one) true
    return
  DataTemplate.withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `imaginary .default (mkConst ``Bool) fun imaginary => do
      let guard ← mkAppM ``LE.le #[app (root ++ `Sop) d.selected[:33].toArray,d.native[44]!]
      withLocalDeclNoLocalInstanceUpdate `hOp .default guard fun hOp => do
        let labels := app (root ++ `ObservedLabels) d.fixed
        let subtype ← whnf labels
        unless subtype.isAppOfArity ``Subtype 2 do
          throwError "primary graph admission: observed labels are not the numeric subtype"
        let original := app (root ++ `label) (d.profileArgs.push imaginary)
        let value := mkAppN (mkConst ``Subtype.mk subtype.getAppFn.constLevels!)
          (subtype.getAppArgs ++ #[original,hOp])
        save `observedLabel (d.profileArgs ++ #[imaginary,hOp]) value labels true

/-- Read exactly the old label through its numerical-admission subtype. -/
def withLabels
    (next : Array Expr → Expr → Expr → RawProfilesTemplate.Data → Expr → Expr → MetaM Unit) : MetaM Unit :=
  DataTemplate.withLabels fun fixed _ old d imaginary => do
    let labels := app (root ++ `ObservedLabels) fixed
    withLocalDeclNoLocalInstanceUpdate `sourceLabel .default labels fun t => do
      let value := Expr.proj ``Subtype 0 t
      let replace (e : Expr) : MetaM Expr := do
        return (← mkLambdaFVars #[old] e).beta #[value]
      let actual : RawProfilesTemplate.Data := {
        native := ← d.native.mapM replace
        selected := ← d.selected.mapM replace
        hAux := ← replace d.hAux
        steps := d.steps
        sample := ← replace d.sample
        sourceArgs := ← d.sourceArgs.mapM replace
        baselineArgs := ← d.baselineArgs.mapM replace
        baseline := ← replace d.baseline
        source := ← replace d.source
        hBaseline := ← replace d.hBaseline }
      next fixed labels t actual (← replace imaginary) (.proj ``Subtype 1 t)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.ObservedLabelsTemplate
end
