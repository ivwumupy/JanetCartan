module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceChart
/-! # Original chart representatives before current source data

Extract the identical measured cutoff from the checked original23 plateau.
Its existing SelectedBoundary half-cell bound removes the periodic
representative everywhere on that same chart, before history/sample/source.
Consumer: transport the actual native Cnorm profile to the physical angular
amplitude (`main:eq:mean-final-amplitude`, `main:prop:current-waves`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSourcePlateau
open Lean Meta Elab Command
private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args
run_cmd liftTermElabM do
  let germName := `JanetCartan.PhysicalPairs.OriginalSourcePlateau.germ_on_original_chart
  forallBoundedTelescope (← getConstInfo germName).type (some 23) fun p _ => do
    unless p.size == 23 do throwError "source representative: original static23 changed"
    let hg := app germName p
    let proof ← forallBoundedTelescope (← inferType hg) (some 2) fun xy _ => do
      unless xy.size == 2 do throwError "source representative: changed original chart premise"
      let hone ← mkAppM ``Filter.EventuallyEq.eq_of_nhds #[mkAppN hg xy]
      let eq := (← inferType hone).getAppArgs
      let ψ := eq[1]!.appFn!
      unless ψ.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalRegular.measuredSourceCutoff 3 do
        throwError "source representative: plateau changed its original measured source cutoff"
      let ca := ψ.getAppArgs
      let n := ca[0]!
      let μ := ca[1]!
      let hμ := ca[2]!
      unless μ.isAppOfArity `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure 21 do
        throwError "source representative: radius is not from the same native selected boundary"
      let hcell := app `JanetCartan.PhysicalSeed.SelectedBoundary.hMeasureCell μ.getAppArgs
      let two ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 3)) 2
      let hsupport := app `JanetCartan.ContinuumRow.FixedCutoffs.physical_tsupport_four #[n,μ,hμ,two]
      let result := app `JanetCartan.PhysicalPairs.OriginalSourceChartTemplate.representative_of_observation_one
        #[n,μ,ψ,hsupport,hcell,xy[0]!,hone]
      mkLambdaFVars xy result
    let type ← instantiateMVars (← mkForallFVars p (← inferType proof))
    let value ← instantiateMVars (← mkLambdaFVars p proof)
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
        throwError "source representative: open original data"
    let pair := Lean.ShareCommon.shareCommon (type,value)
    let name := `JanetCartan.PhysicalPairs.OriginalSourcePlateau.representative_on_original_chart
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "source representative: nonstandard axioms {axioms}"
    logInfo m!"same original23 chart has its true centered representative, before source/sample data: {axioms}"
end JanetCartan.PhysicalPairs.OriginalSourcePlateau
end
