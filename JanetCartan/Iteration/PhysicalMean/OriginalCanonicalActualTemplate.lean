module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivative
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
public meta import Lean

/-!
# The checked canonical derivative on the actual saved50 source

Retain the exact graph42, source53, color rate and finite-band margin already
inside the one native sampling event. No inverse, scalar, source budget, cutoff,
shift or history is selected here. Consumers are the actual raw-row comparison
and fixed-source mean (`app:ch_mean_pairs:defn:mean-canonical`).
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.PhysicalMean.OriginalCanonicalActualTemplate
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate

private def root := `JanetCartan.PhysicalMean.OriginalCanonicalActual
private def progress (message : String) : MetaM Unit := do
  logInfo message
  if let some path ← IO.getEnv "JANET_ACTUAL_G_TRACE" then
    IO.FS.withFile path .append fun h => do
      h.putStrLn message
      h.flush
private def tail (h : Expr) (j : Nat) := Nat.repeat (fun e => Expr.proj ``And 1 e) j h
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (tail h j)

private def save (name : Name) (params : Array Expr) (value : Expr)
    (data : Bool) (expected : Option Expr := none) : MetaM Expr := do
  let env ← getEnv
  let missingValue := value.getUsedConstants.filter (fun n => (env.find? n).isNone)
  unless missingValue.isEmpty do
    throwError "actual canonical G: missing value producers {missingValue.toList}"
  let target ← match expected with | some t => pure t | none => inferType value
  let missingType := target.getUsedConstants.filter (fun n => (env.find? n).isNone)
  unless missingType.isEmpty do
    throwError "actual canonical G: missing type producers {missingType.toList}"
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  for closed in #[type,value] do
    let missing := closed.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "actual canonical G: missing closed-telescope producers {missing.toList}"
  if type.hasFVar || type.hasMVar || type.hasLevelMVar || type.hasLooseBVars || type.hasSorry ||
      value.hasFVar || value.hasMVar || value.hasLevelMVar || value.hasLooseBVars || value.hasSorry then
    throwError "actual canonical G: open or assumed field {name}"
  let name := root ++ name
  progress s!"actual canonical G: closed original telescope ready, kernel checking {name}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The canonical full-angular derivative on the SAME saved native50 original source53/graph42 and literal color rate; no new source, sample or analytic premise (app:ch_mean_pairs:defn:mean-canonical)."
  return mkAppN (mkConst name) params

/-- Read actual producer spines rather than adding graph, source or rate success
hypotheses. The returned53 parameters are native50, row, color, and outer node. -/
def withActualG
    (next : Array Expr → Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  withTransparency .reducible <| withActualRow fun d => do
    let graph := d.mean70[53]!
    unless graph.isAppOfArity `JanetCartan.PhysicalSampling.OriginalGraphResponse.B 42 do
      throwError "actual canonical G: missing literal graph42"
    let measured ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalRow.D d.parameters[:50].toArray
    unless measured.isAppOfArity `JanetCartan.PhysicalSampling.OriginalJointEvent.measured_kernel 60 do
      throwError "actual canonical G: changed saved measured60"
    let m := measured.getAppArgs
    let rates := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalCommonStage.stage_rates)
      (m[:46].toArray ++ #[m[47]!,m[48]!,m[49]!])
    let hΛ := part rates 1
    let hΛType ← inferType hΛ
    unless hΛType.isAppOfArity ``LE.le 4 do
      throwError "actual canonical G: original Lambda lower bound changed"
    let Λ := hΛType.getAppArgs[3]!
    let n := d.raw13[0]!
    let J := mkApp (mkConst `JanetCartan.RawInputPartition.cutoffCount) Λ
    let input := mkAppN (mkConst `JanetCartan.RawInputPartition.WideInput) #[n,J]
    let torus := mkApp (mkConst `JanetCartan.Torus) n
    let .forallE label colorType _ bi ← inferType d.native64[61]!
      | throwError "actual canonical G: missing original color rate domain"
    withLocalDeclNoLocalInstanceUpdate label bi colorType fun color => do
      let actual ← savedResponse d color
      let s := actual.source53
      let extra := #[24,25,30,32,33,34,35,36,37,38,40,45,46,47,48,49,50,51,52].map (s[·]!)
      let family := graph.getAppArgs ++ extra
      unless family.size == 61 do throwError "actual canonical G: changed joined family61"
      let hmargin := tail (mkAppN (tail rates 6) #[d.row,color]) 3
      withLocalDeclNoLocalInstanceUpdate `node .default
          (mkConst `JanetCartan.SeparatedSampling.Point) fun node => do
        let params := d.parameters ++ #[color,node]
        let native := family ++ #[Λ,hΛ,hmargin,node]
        unless params.size == 53 && native.size == 65 do
          throwError "actual canonical G: native53/full65 mismatch"
        progress "actual canonical G: native53/source53/graph42/rate3 joined"
        next params native input torus

elab "construct_actual_canonical_derivative " mode:num : command => liftTermElabM do
  withActualG fun params native input torus => do
    let oldG := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.G) native
    match mode.getNat with
    | 0 =>
      discard <| save `G params oldG true
      logInfo "actual native53 G: SAME saved50 event, graph42/source53, original color rate and ALL finite-band margins; no added source/profile/rate/shift premise"
    | 1 =>
      withLocalDeclNoLocalInstanceUpdate `v .default input fun v => do
        withLocalDeclNoLocalInstanceUpdate `z .default torus fun z => do
          let proof := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.G_native)
            (native ++ #[v,z])
          discard <| save `G_native (params ++ #[v,z]) proof false
          logInfo "actual native55 G_native: exact inferred generic physical target on SAME source53; actual G53 is its literal definition, without expanding the entire physical RHS"
    | _ => throwError "actual canonical G: unknown publication stage"

end JanetCartan.PhysicalMean.OriginalCanonicalActualTemplate
end
