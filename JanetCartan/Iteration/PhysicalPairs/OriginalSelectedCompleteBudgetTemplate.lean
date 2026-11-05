module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianProfiles
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteBaselineIdentity
/-! # One static complete-node derivative budget before every source/history

The SAME Cbaseline44 and common-D_N-derived Csource34 are fixed on selected33+N.
This budget is independent of the actual source/profile publication and does
not by itself assert membership of the later physical complete wave
(`main:prop:pairs`, `new:sec:order-of-choices`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSelectedCompleteBudgetTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalSelectedCompleteProfiles
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def namedPrice (type CB CD C : Expr) : Expr := type.replace fun e => do
  if !e.isAppOfArity ``HAdd.hAdd 6 then none else
    let a := e.getAppArgs
    if a[4]!.isApp && a[5]!.isApp && a[4]!.appFn! == CB && a[5]!.appFn! == CD &&
        a[4]!.appArg! == a[5]!.appArg! then
      some (mkApp C a[4]!.appArg!)
    else none
private def save (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "static complete-node budget: later input escaped {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking fixed complete-node budget {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The original complete-amplitude derivative price Cbaseline44+Csource34 is fixed on selected33+N before every history, smoothing, target, source or sample; actual complete-wave membership is supplied separately (main:prop:pairs; new:sec:order-of-choices)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "static complete-node budget: nonstandard axioms {axioms}"
  logInfo m!"fixed complete-node budget {key}/{p.size}: {axioms}"
elab "define_original_selected_complete_budget " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "static complete-node budget: unknown mode"
  PhysicalMean.OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p _ native _ _ => do
    let static := p[:33].toArray.push p[53]!
    let CB := app `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.Cbaseline native[:44].toArray
    let hCB := app `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.Cbaseline_nonneg native[:44].toArray
    let CD := app `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.Csource static
    let hCD := app `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.Csource_nonneg static
    if mode.getNat == 0 then
      let price ← withLocalDeclD `order (mkConst ``Nat) fun q => do
        mkLambdaFVars #[q] (← mkAppM ``HAdd.hAdd #[mkApp CB q,mkApp CD q])
      save `Camplitude static price (← inferType price) true
    else
      let proof ← withLocalDeclD `order (mkConst ``Nat) fun q => do
        mkLambdaFVars #[q] (← mkAppM ``add_nonneg #[mkApp hCB q,mkApp hCD q])
      let target := namedPrice (← inferType proof) CB CD (app (root ++ `Camplitude) static)
      save `Camplitude_nonneg static proof target
end JanetCartan.PhysicalPairs.OriginalSelectedCompleteBudgetTemplate
end
