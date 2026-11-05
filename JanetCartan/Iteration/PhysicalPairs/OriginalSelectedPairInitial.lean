module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedPairGates
public import JanetCartan.Iteration.PhysicalPairs.OriginalUniformSizeSelection
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceSignedCorrection
public import JanetCartan.Iteration.RevisedUniform.OriginalFinalReachSelection
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
/-! # Initial reach for the actual signed correction on the frozen prehistory

For the unchanged dimension-only geometry and any fixed pair scale, take the
maximum of the original prehistory threshold and its genuine *pre-accuracy*
signed/size threshold. The latter is read from the literal signed correction's
own gate; its physical size reserve is already covered by the frozen rStar.
Both bounds are reached at R₀, not imposed later on a current stage R. No
accuracy, amplitude budget, history, target or sample enters this choice
(`new:sec:order-of-choices`, `main:prop:pairs`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public section
namespace JanetCartan.PhysicalPairs.OriginalSelectedPairInitial
/-- One initial maximum reaches the old prehistory and its complete signed-size
window; a later stage or accuracy does not participate in this implication. -/
theorem reach_original_and_signed (T S W R : ℝ) (hW : W ≤ S) (h : max T S ≤ R) :
    T ≤ R ∧ S ≤ R ∧ W ≤ R :=
  ⟨(le_max_left T S).trans h, (le_max_right T S).trans h, hW.trans ((le_max_right T S).trans h)⟩
end JanetCartan.PhysicalPairs.OriginalSelectedPairInitial
end
public meta section
namespace JanetCartan.PhysicalPairs.OriginalSelectedPairInitialTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalSelectedPairInitial
private def data := `JanetCartan.RevisedUniform.OriginalFinalReach
private def sizes := `JanetCartan.PhysicalPairs.OriginalUniformSizeSelection
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def save (key : Name) (p : Array Expr) (proof target : Expr) (isData := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "dimension-only signed initial reach: later input escaped {key}"
    let missing := e.getUsedConstants.filter (fun k => (env.find? k).isNone)
    unless missing.isEmpty do throwError "dimension-only signed initial reach: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking SAME dimension-only signed initial threshold {key}/{p.size}"
  (← IO.getStdout).flush
  if isData then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME frozen original prehistory, original signed window and complete physical size threshold are reached at the initial R₀ from one fixed numerical maximum, before all accuracies, amplitude prices, histories, targets and samples. No new geometry, sigma, cap or current-stage gate (main:prop:pairs; new:sec:order-of-choices)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "dimension-only signed initial reach: nonstandard axioms {axioms}"
  logInfo m!"SAME dimension-only signed initial threshold {key}/{p.size}: {axioms}"
run_meta do
  RevisedUniform.OriginalSelectedPrehistoryTemplate.withDimensionStatic fun dh _ _ native => do
    withLocalDeclD `Cscale (mkConst ``Real) fun scale => do
      let keep := dh.push scale
      let correction := `JanetCartan.PhysicalPairs.OriginalSourceSignedCorrection.correction
      let rest ← instantiateForall (← getConstInfo correction).type (native.push scale)
      forallBoundedTelescope rest (some 8) fun tail atSigned => do
        unless tail.size == 8 && atSigned.isForall do throwError "dimension-only signed initial reach: actual S55 interface changed"
        let gate := atSigned.bindingDomain!
        unless gate.isAppOfArity ``LE.le 4 && gate.appArg! == tail[0]! do
          throwError "dimension-only signed initial reach: actual S55 is no longer gated at initial R₀"
        let window := gate.getAppArgs[2]!
        unless window.isAppOfArity `JanetCartan.PhysicalPairs.SampledHistory.S 37 do
          throwError "dimension-only signed initial reach: not the original signed window"
        let b := window.getAppArgs
        let hcap := app ``JanetCartan.PhysicalPairs.OriginalSelectedPairGates.history_covers_size #[dh[0]!]
        let bcap := b.push hcap
        let prehistory := app (data ++ `Tfinal) dh
        let signedSize := app (sizes ++ `earlyS) bcap
        let initial ← mkAppM ``Max.max #[prehistory,signedSize]
        save `Tpair keep initial (mkConst ``Real) true
private def withThreshold (next : Array Expr → Expr → Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let ci ← getConstInfo (root ++ `Tpair)
  forallTelescope ci.type fun keep _ => do
    let raw := (ci.value! (allowOpaque := true)).beta keep
    unless keep.size == 3 && raw.isAppOfArity ``Max.max 4 do
      throwError "dimension-only signed initial reach: actual initial maximum changed"
    let prehistory := raw.getAppArgs[2]!
    let signedSize := raw.getAppArgs[3]!
    unless signedSize.isAppOfArity (sizes ++ `earlyS) 38 do
      throwError "dimension-only signed initial reach: original pre-N threshold changed"
    next keep prehistory signedSize signedSize.getAppArgs
run_meta do
  withThreshold fun keep prehistory signedSize _ => do
    let named := app (root ++ `Tpair) keep
    let left ← mkAppM ``le_max_left #[prehistory,signedSize]
    let htwo ← mkAppM ``le_trans #[app (data ++ `two_le_Tfinal) keep[:2].toArray,left]
    let two ← mkNumeral (mkConst ``Real) 2
    save `two_le_Tpair keep htwo (← mkAppM ``LE.le #[two,named])
run_meta do
  withThreshold fun keep prehistory signedSize bcap => do
    let named := app (root ++ `Tpair) keep
    let window := app `JanetCartan.PhysicalPairs.SampledHistory.S bcap[:37].toArray
    withLocalDeclNoLocalInstanceUpdate `R₀ .default (mkConst ``Real) fun R₀ => do
      withLocalDeclNoLocalInstanceUpdate `hInitial .default (← mkAppM ``LE.le #[named,R₀]) fun hInitial => do
        let proof := app (root ++ `reach_original_and_signed)
          #[prehistory,signedSize,window,R₀,app (sizes ++ `early_reaches_signed) bcap,hInitial]
        save `initial_reaches (keep ++ #[R₀,hInitial]) proof (← inferType proof)
end JanetCartan.PhysicalPairs.OriginalSelectedPairInitialTemplate
end
