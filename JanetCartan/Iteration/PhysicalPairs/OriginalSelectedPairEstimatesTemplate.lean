module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedNodeAdmission
public import JanetCartan.Iteration.PhysicalPairs.OriginalUniformMassRates
public import JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
/-! # Actual full-Picard signed correction estimates on the unchanged history

Instantiate the source-uniform signed estimates with the genuine all-order
complete-node producer, not with a wave/profile hypothesis. The original fixed
gamma already meets the strain-frame bound. The remaining size-cap condition
is numerical and is paid by OriginalSelectedPairGates on the frozen prehistory;
no geometry, sigma, source, sampling event or correction is selected again.
The uncut primary/self form is published first; its exact aggregate/full-self
identification is a separate pointwise algebraic join (`main:prop:pairs`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSelectedPairEstimatesTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalSelectedPairEstimates
private def profiles := `JanetCartan.PhysicalPairs.OriginalSelectedCompleteProfiles
private def lag := `JanetCartan.PhysicalPairs.OriginalUniformStageLag
private def size := `JanetCartan.PhysicalPairs.OriginalUniformStageSize
private def selection := `JanetCartan.PhysicalPairs.OriginalUniformSizeSelection
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual signed correction estimate: added analytic input or misplaced constant {key}"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "actual signed correction estimate: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual complete-source signed estimate {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME actual complete full-Picard source correction obeys the original uniform physical signed estimate after the genuine baseline/native-source node profile is instantiated; constants precede all histories/targets/smoothing, the frozen frame is retained, and only numerical threshold/cap gates remain (main:prop:pairs; main:eq:pair-error; main:eq:pair-high-size)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual signed correction estimate: nonstandard axioms {axioms}"
  logInfo m!"actual complete-source signed estimate {key}/{p.size}: {axioms}"
elab "estimate_original_selected_signed_correction " mode:num : command => liftTermElabM do
  unless mode.getNat < 8 do throwError "actual signed correction estimate: unknown mode"
  forallBoundedTelescope (← getConstInfo (profiles ++ `nodeJets)).type (some 56) fun p ledger => do
    unless ledger.isAppOfArity `JanetCartan.PhysicalPairs.OriginalSelectedWaves.nodeJets 8 do
      throwError "actual signed correction estimate: actual node admission changed"
    let data := ledger.getAppArgs
    let C := data[4]!
    let θ := data[6]!
    let W := data[7]!
    unless θ.isAppOfArity `JanetCartan.PhysicalPairs.OriginalStageMetric.angles 45 && W.isLambda do
      throwError "actual signed correction estimate: not the SAME original common source family"
    let stem := θ.getAppArgs
    let b := stem[:37].toArray
    let wave := W.bindingBody!
    unless wave.isAppOfArity `JanetCartan.PhysicalPairs.OriginalSourceSchwartz.wave 53 do
      throwError "actual signed correction estimate: original complete Schwartz nodes changed"
    let wa := wave.getAppArgs
    let native := wa[:50].toArray
    if (wa[:52].toArray).any Expr.hasLooseBVars then
      throwError "actual signed correction estimate: selected source depends on the node"
    let static := p[:33].toArray ++ #[p[53]!,p[54]!]
    let hC := app (profiles ++ `Camplitude_nonneg) (p[:33].toArray.push p[53]!)
    let hJ := app (profiles ++ `nodeJets) p
    let sourceCorrection := `JanetCartan.PhysicalPairs.OriginalSourceSignedCorrection.correction
    let correctionPrefix := native[:44].toArray ++ #[p[54]!] ++ native[44:].toArray ++ wa[50:52].toArray ++ #[p[55]!]
    let actualCorrection (δ : Expr) := app sourceCorrection (correctionPrefix.push δ)
    let retain (type S : Expr) := type.replace fun e =>
      if e.isAppOfArity `JanetCartan.PhysicalPairs.OriginalSignedSum.correction 47 then some S else none
    if #[0,1,7].contains mode.getNat then
      withLocalDeclD `accuracyOrder (mkConst ``Nat) fun q => do
        let pre := b ++ #[C,hC,q]
        let price := app (lag ++ `constant) pre
        if mode.getNat == 0 then
          save `Clag (static.push q) price (← inferType price) true
          return
        let hFrame := app `JanetCartan.PhysicalSampling.OriginalBareScale.γ_le_ambient native[:24].toArray
        withLocalDeclD `δ (mkConst ``Real) fun δ => do
          let params := pre ++ #[hFrame] ++ stem[37:].toArray ++ #[W,hJ,δ]
          let key := if mode.getNat == 1 then lag ++ `metric_lag else `JanetCartan.PhysicalPairs.OriginalUniformMassRates.metric_lag
          let proof := app key params
          let target := (retain (← inferType proof) (actualCorrection δ)).replace fun e =>
            if e == price then some (app (root ++ `Clag) (static.push q)) else none
          save (if mode.getNat == 1 then `uncut_metric_lag else `uncut_mass_lag) (p ++ #[δ,q]) proof target
      return
    let capType := (← inferType (app (selection ++ `native_budget) b)).bindingDomain!
    withLocalDeclD `originalHistoryCoversSize capType fun hcap => do
      let pre := b ++ #[hcap,C,hC]
      let fixed := static.push hcap
      let early := p[:33].toArray ++ #[p[54]!,hcap]
      let threshold := app (selection ++ `earlyS) (b.push hcap)
      if mode.getNat == 2 then
        save `sizeThreshold early threshold (← inferType threshold) true
        return
      if mode.getNat == 3 then
        withLocalDeclD `physicalOrder (mkConst ``Nat) fun r => do
          let price := app `JanetCartan.PhysicalPairs.OriginalUniformStageSize.constant (pre.push r)
          save `Csize (fixed.push r) price (← inferType price) true
        return
      let gate ← mkAppM ``LE.le #[app (root ++ `sizeThreshold) early,native[44]!]
      withLocalDeclD `reachedActualSignedSize gate fun hSize =>
        withLocalDeclD `δ (mkConst ``Real) fun δ => do
          let later := #[native[44]!,hSize] ++ stem[39:].toArray ++ #[W,hJ,δ]
          let all := p ++ #[hcap,hSize,δ]
          if mode.getNat == 4 then
            withLocalDeclD `physicalOrder (mkConst ``Nat) fun r => do
              let proof := app (size ++ `size) ((pre.push r) ++ later)
              let cost := app `JanetCartan.PhysicalPairs.OriginalUniformStageSize.constant (pre.push r)
              let target := (retain (← inferType proof) (actualCorrection δ)).replace fun e =>
                if e == cost then some (app (root ++ `Csize) (fixed.push r)) else none
              save `size (all.push r) proof target
          else
            let key := if mode.getNat == 5 then size ++ `physicalL2 else `JanetCartan.PhysicalPairs.OriginalUniformMassRates.size
            let proof := app key (pre ++ later)
            save (if mode.getNat == 5 then `physicalL2 else `mass_size) all proof
              (retain (← inferType proof) (actualCorrection δ))
end JanetCartan.PhysicalPairs.OriginalSelectedPairEstimatesTemplate
end
