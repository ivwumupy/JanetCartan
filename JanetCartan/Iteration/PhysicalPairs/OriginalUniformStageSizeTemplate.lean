module
public import JanetCartan.Iteration.PhysicalPairs.OriginalUniformPacketSize
public import JanetCartan.Iteration.PhysicalPairs.OriginalStageSize
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedWaves
/-! # The SAME finite correction size with all source waves after the price

The genuine physical threshold precedes every complete-node price and Picard
accuracy; the all-order size constant is selected afterward, before the waves.
Apply the local pair producer to each original pair of one later complete family,
then use the SAME finite signed mass sum. The coefficient mass is retained
before its original numerical estimate. Actual complete-node profile admission
remains a separate genuine producer (`main:prop:pairs`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalUniformStageSizeTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalUniformStageSize
private def original := `JanetCartan.PhysicalPairs.OriginalStageSize
private def sel := `JanetCartan.PhysicalPairs.OriginalUniformSizeSelection
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def sum := `JanetCartan.PhysicalPairs.OriginalSignedSum
private def mass := `JanetCartan.PhysicalPairs.OriginalSampleMass
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def save (key : Name) (p : Array Expr) (proof : Expr) (expected : Option Expr := none) (data := false) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType proof
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "uniform actual finite size: misplaced source/history in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual finite signed size {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME original finite signed correction has the SAME prehistory all-order size constants and threshold, with all later complete source waves after those constants; original coefficient mass and plus/minus finite summation retained (main:prop:pairs; app:ch_pairs:eq:pairs-lag-sum-size)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "uniform actual finite size: nonstandard axioms {axioms}"
  logInfo m!"actual finite signed size {key}/{p.size}: {axioms}"
elab "define_original_uniform_stage_size_price" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (sel ++ `D)).type (some 40) fun pre _ => do
    let D := app (sel ++ `D) pre
    let M := app (mass ++ `constant) pre[:22].toArray
    withLocalDeclD `physicalOrder (mkConst ``Nat) fun r => do
      let price := app (original ++ `cost) #[mkApp D r,M]
      save `constant (pre.push r) price (some (mkConst ``Real)) true
elab "prove_original_uniform_stage_size " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "uniform actual finite size: unknown mode"
  forallBoundedTelescope (← getConstInfo (sel ++ `D)).type (some 40) fun pre _ => do
    let b := pre[:37].toArray
    let D := app (sel ++ `D) pre
    let M := app (mass ++ `constant) b[:22].toArray
    let n := mkApp (mkConst ``Nat.succ) b[0]!
    let N := app `JanetCartan.embeddingDimension #[n]
    let exponent := app `JanetCartan.RevisedScales.forcingExponent #[n]
    withLocalDeclD `physicalOrder (mkConst ``Nat) fun r => do
      let s := if mode.getNat == 2 then mkNatLit 0 else r
      let cost := app (original ++ `cost) #[mkApp D s,M]
      let named := app (root ++ `constant) (pre.push s)
      withLocalDeclD `R₀ (mkConst ``Real) fun R₀ => do
        withLocalDeclD `reachedSignedAndSize (← mkAppM ``LE.le #[app (sel ++ `S) pre,R₀]) fun h₀ => do
          let ho ← mkAppM ``le_trans #[app (sel ++ `reaches_signed) pre,h₀]
          let ht ← mkAppM ``le_trans #[app (sel ++ `reaches_size) pre,h₀]
          let head := b ++ #[R₀,ho]
          forallBoundedTelescope (← inferType (app (sum ++ `correction) head)) (some 6) fun row _ => do
            let stem := head ++ row
            let hR ← mkAppM (original ++ `stage_one) #[app (sel ++ `hS) pre,h₀,row[0]!]
            let R := (← inferType hR).appArg!
            let wt := (← inferType (app (sum ++ `correction) stem)).bindingDomain!
            withLocalDeclD `completePrimaryWaves wt fun Z => do
              let I := wt.bindingDomain!
              let θ := app `JanetCartan.PhysicalPairs.OriginalStageMetric.angles stem
              let gf := (← inferType (app (hist ++ `historyMap) b)).bindingBody!
              let chart := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart gf.getAppArgs[:23].toArray
              let fine := app `JanetCartan.PhysicalPairs.OriginalWindow.fineScale #[b[36]!,R]
              let nodeProfile := app `JanetCartan.PhysicalPairs.OriginalSelectedWaves.nodeJets #[n,N,I,chart,pre[38]!,fine,θ,Z]
              withLocalDeclD `trueCompleteNodeJets nodeProfile fun hJ =>
                withLocalDeclD `δ (mkConst ``Real) fun δ => do
                  let rest := #[R₀,h₀] ++ row ++ #[Z,hJ,δ]
                  let all := (if mode.getNat == 2 then pre else pre.push s) ++ rest
                  let native := stem ++ #[Z,δ]
                  if mode.getNat == 2 then
                    let bound := app (root ++ `size) ((pre.push s) ++ rest)
                    let proof := app (original ++ `order_zero) #[n,N,app (sum ++ `correction) native,named,R,δ,hR,bound]
                    save `physicalL2 all proof
                    return
                  if mode.getNat == 1 then
                    let bound := app (root ++ `coefficient_mass_size) all
                    let massBound := Expr.proj ``And 0 (.proj ``And 1 (app (mass ++ `coefficient_budgets) stem))
                    let quantity := (← inferType massBound).getAppArgs[2]!
                    let lhs := (← inferType bound).getAppArgs[2]!
                    let hD := mkApp (app (sel ++ `D_nonneg) pre) s
                    let proof := app (original ++ `total) #[mkApp D s,M,exponent,R,δ,lhs,quantity,s,hD,hR,massBound,bound]
                    let target := (← inferType proof).replace fun e => if e == cost then some named else none
                    save `size all proof (some target)
                    return
                  let hD := mkApp (app (sel ++ `D_nonneg) pre) s
                  let hSingle := app (original ++ `packet_nonneg) #[mkApp D s,R,s,hD,hR]
                  let B := (← inferType hSingle).appArg!
                  let sr ← mkAppOptM ``Nat.cast #[some (mkConst ``Real),none,s]
                  let priced := mkAppN (app (sum ++ `exact_coefficient_mass_bound) native) #[sr,B,hSingle]
                  let packets ← forallBoundedTelescope (← inferType priced).bindingDomain! (some 4) fun signs _ => do
                    let pt := stem ++ signs
                    let label := app (hist ++ `label) pt
                    let profileType := app `JanetCartan.PhysicalPairs.OriginalUniformWaveData.DerivativeProfile
                      (b ++ #[pre[38]!,label,Z])
                    let profile ← forallBoundedTelescope (← whnf profileType) (some 4) fun y _ => do
                      mkLambdaFVars y (← mkAppM ``And.intro
                        #[mkAppN hJ (#[signs[1]!] ++ y[1:].toArray),mkAppN hJ (#[signs[2]!] ++ y[1:].toArray)])
                    let proof := app `JanetCartan.PhysicalPairs.OriginalUniformPacketSize.size
                      (pre ++ #[R₀,ho,ht] ++ row ++ signs ++ #[Z,profile,s])
                    mkLambdaFVars signs proof
                  save `coefficient_mass_size all (mkApp priced packets)
end JanetCartan.PhysicalPairs.OriginalUniformStageSizeTemplate
end
