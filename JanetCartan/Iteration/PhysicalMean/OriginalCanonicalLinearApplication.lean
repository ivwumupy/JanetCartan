module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourceApplication
public meta import Lean

/-!
# The actual uncut-auxiliary plus sampled-wave linear source

Use the identical quadratic-source packing, global admission39 inverse and
uncut continuum carriers. The baseline is the unscaled full-parent field on
the original outer sample, including inner-factor zero. Consumer: the actual
finite Picard run (`new:eq:mean-operators`).
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.PhysicalMean.OriginalCanonicalLinearApplication
open Lean Meta Elab Command
open OriginalCanonicalSourceApplication

private def sampleFintype (μ quadratic : Expr) : MetaM Expr := do
  let .forallE _ sampleType _ _ := (← inferType μ).consumeMData
    | throwError "actual source linear: original sample domain missing"
  for argument in quadratic.getAppArgs do
    let type ← inferType argument
    if type.isAppOfArity ``Fintype 1 then
      if ← isDefEq type.appArg! sampleType then return argument
  throwError "actual source linear: literal quadratic sample Fintype missing"

private def save (params : Array Expr) (term : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params (← inferType term))
  let value ← instantiateMVars (← mkLambdaFVars params term)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual source linear: missing producer constants {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual source linear: unresolved or extra input"
  let name := `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear
  addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  addDocStringCore name "The actual uncut-auxiliary plus fixed-sampled-wave smooth source action, using the SAME global current Q0, full unscaled positive baseline and original sample as the quadratic action (new:eq:mean-operators)."
  logInfo "actual fixed-source linear52: same quadratic packing/global inverse, uncut auxiliary and full positive baseline"

elab "construct_actual_canonical_source_linear" : command => liftTermElabM do
  withActualQuadratic fun params _ native39 data quadratic => do
    let current (key : Name) := mkAppN (mkConst
      (`JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current ++ key)) native39
    let fixed (key : Name) := mkAppN (mkConst
      (`JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current ++ key)) native39[:21].toArray
    let μ := data[0]!
    let C := data[1]!
    let hC := data[2]!
    let A := data[3]!
    let G := data[4]!
    let Q0 := data[5]!
    let base := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalSampled.base)
      params[:51].toArray
    let fI ← sampleFintype μ quadratic
    let value ← withLetDecl `sameSampleFintype (← inferType fI) fI fun fi => do
      let result ← withLocalInstances [← fi.fvarId!.getDecl] <|
        mkAppM `JanetCartan.PhysicalMean.fixedSourceLinear #[
          current `coefficient,current `coefficient_smooth,
          fixed `measurement,fixed `source,fixed `exterior,
          fixed `measurement_smooth,fixed `source_smooth,fixed `exterior_smooth,
          current `carriers,Q0,current `source_regular,μ,base,C,hC,A,G]
      return (← instantiateMVars result).replaceFVar fi fI
    save params value

end JanetCartan.PhysicalMean.OriginalCanonicalLinearApplication
end
