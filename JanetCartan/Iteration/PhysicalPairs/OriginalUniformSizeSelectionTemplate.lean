module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSizeSelection
public import JanetCartan.Iteration.PhysicalPairs.UniformHistorySize
import all JanetCartan.Iteration.PhysicalPairs.OriginalSizeSelection
/-! # The original physical size threshold before every later amplitude budget

The SAME physical size specialization now consumes the honest reordered
coefficient/reconstruction producer. earlyThreshold and earlyS have prefix
original37+hcap ONLY. D is selected afterward on original37+hcap+C+hC. The
40-parameter threshold aliases discard C/hC definitionally for compatibility
with the already checked actual packet calculus; no new geometry, history cap,
reference or sigma is selected (`main:prop:pairs`, `new:sec:order-of-choices`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalUniformSizeSelectionTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalUniformSizeSelection
private def old := `JanetCartan.PhysicalPairs.OriginalSizeSelection
private def earlyTheorem := `JanetCartan.PhysicalPairs.exists_uniform_threshold_physical_history_localized_product_size_constants
private def oldTheorem := `JanetCartan.PhysicalPairs.exists_physical_history_localized_normalized_product_size_constants
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "early original physical size: later amplitude/history escaped {key}"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "early original physical size: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking original size threshold BEFORE C/N {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The unchanged actual physical-size coefficient/reconstruction threshold is fixed on original37+hcap BEFORE every complete-node price C, Picard accuracy N, source, history, target and smoothing; only D is selected afterward. No cap, reference or sigma is changed (main:prop:pairs; new:sec:order-of-choices)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "early original physical size: nonstandard axioms {axioms}"
  logInfo m!"original size threshold BEFORE C/N {key}/{p.size}: {axioms}"
elab "select_original_uniform_size " mode:num : command => liftTermElabM do
  unless mode.getNat < 18 do throwError "early original physical size: unknown mode"
  let oldInfo ← getConstInfo (old ++ `native_budget)
  forallBoundedTelescope oldInfo.type (some 40) fun p _ => do
    let early := p[:38].toArray
    let fixed := p[:37].toArray
    if mode.getNat == 0 then
      let raw := (oldInfo.value! (allowOpaque := true)).beta p
      unless raw.isAppOf oldTheorem do throwError "early original physical size: actual physical specialization changed"
      let args := raw.getAppArgs
      let selected ← forallTelescope (← getConstInfo oldTheorem).type fun inputs _ => do
        unless inputs.size == args.size do throwError "early original physical size: producer parameter count changed"
        let mut selected := #[]
        for k in [:inputs.size] do
          let nm := (← inputs[k]!.fvarId!.getDecl).userName
          unless nm == `C || nm == `hC do selected := selected.push args[k]!
        pure selected
      let proof := mkAppN (mkConst earlyTheorem raw.getAppFn.constLevels!) selected
      save `native_budget early proof (← inferType proof)
      return
    let budget := app (root ++ `native_budget) early
    if mode.getNat == 1 then
      let price ← mkAppM ``Classical.choose #[budget]
      save `earlyThreshold early price (← inferType price) true
      return
    let threshold := app (root ++ `earlyThreshold) early
    if mode.getNat == 2 then
      let proof ← mkAppM ``Classical.choose_spec #[budget]
      let target := (← inferType budget).appArg!.beta #[threshold]
      save `earlySpec early proof target
      return
    let spec := app (root ++ `earlySpec) early
    if mode.getNat == 3 then
      let proof := Expr.proj ``And 0 spec
      save `earlyThreshold_ge_two early proof (← inferType proof)
      return
    let exD := mkAppN (Expr.proj ``And 1 spec) p[38:40].toArray
    if mode.getNat == 4 then
      let D ← mkAppM ``Classical.choose #[exD]
      save `D p D (← inferType D) true
      return
    if mode.getNat == 5 then
      let proof ← mkAppM ``Classical.choose_spec #[exD]
      let target := (← inferType exD).appArg!.beta #[app (root ++ `D) p]
      save `Dspec p proof target
      return
    if mode.getNat == 6 || mode.getNat == 7 then
      let proof := Expr.proj ``And (if mode.getNat == 6 then 0 else 1) (app (root ++ `Dspec) p)
      save (if mode.getNat == 6 then `D_nonneg else `continuation) p proof (← inferType proof)
      return
    let signed := app `JanetCartan.PhysicalPairs.SampledHistory.S fixed
    if mode.getNat == 8 then
      let S ← mkAppM ``Max.max #[signed,threshold]
      save `earlyS early S (← inferType S) true
      return
    let S := app (root ++ `earlyS) early
    if mode.getNat == 9 || mode.getNat == 10 then
      let isSigned := mode.getNat == 9
      let proof ← mkAppM (if isSigned then ``le_max_left else ``le_max_right) #[signed,threshold]
      let target ← mkAppM ``LE.le #[if isSigned then signed else threshold,S]
      save (if isSigned then `early_reaches_signed else `early_reaches_size) early proof target
      return
    if mode.getNat == 11 then
      let proof ← mkAppM ``le_trans #[app (root ++ `earlyThreshold_ge_two) early,app (root ++ `early_reaches_size) early]
      save `early_hS early proof (← inferType proof)
      return
    if mode.getNat == 12 || mode.getNat == 13 then
      let value := if mode.getNat == 12 then threshold else S
      save (if mode.getNat == 12 then `threshold else `S) p value (← inferType value) true
      return
    let field := match mode.getNat with
      | 14 => `early_reaches_signed
      | 15 => `early_reaches_size
      | 16 => `early_hS
      | _ => `earlyThreshold_ge_two
    let key := match mode.getNat with
      | 14 => `reaches_signed
      | 15 => `reaches_size
      | 16 => `hS
      | _ => `threshold_ge_two
    let proof := app (root ++ field) early
    let target := (← inferType proof).replace fun e =>
      if e == threshold then some (app (root ++ `threshold) p)
      else if e == S then some (app (root ++ `S) p) else none
    save key p proof target
end JanetCartan.PhysicalPairs.OriginalUniformSizeSelectionTemplate
end
