module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedCell
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceChart
/-! # The same original observation gives actual Schwartz source waves

Only the existing ψ is used. Its support buffer and the complete unscaled
baseline-plus-whole-angular smoothness are already proved for the actual tuple.
The resulting representative agrees with the SAME raw wave in a neighborhood
of every point of the original source chart. This is the input to the unchanged
signed-pair ledger, not a redefinition of the final physical cutoff or a wave
profile assumption (`app:ch_pairs:lem:pairs-ledger`).
-/
public meta section
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSourceSchwartzTemplate
open Lean Meta Elab Command
open PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSourceSchwartz
private def ob := `JanetCartan.PhysicalMean.OriginalCanonicalDerivative
private def selected := `JanetCartan.PhysicalPairs.OriginalSelectedCell
private def buffer := `JanetCartan.PhysicalPairs.OriginalObservationBuffer
private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args
private def body (key : Name) (p : Array Expr) : MetaM Expr := do
  return ((← getConstInfo key).value! (allowOpaque := true)).beta p
private def save (key : Name) (p : Array Expr) (value type : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p type)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasMVar || e.hasLevelMVar || e.hasFVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual observed source: unresolved field {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  liftM <| IO.eprintln s!"actual observed source: kernel checking {name}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  liftM <| IO.eprintln s!"actual observed source: kernel passed {name}"

elab "publish_original_source_schwartz " which:num : command => liftTermElabM do
  unless which.getNat < 6 do throwError "actual observed source: unknown publication mode"
  withActualSelectedSourceWave fun p _ input _ _ native64 _ => do
    let n := input.getAppArgs[0]!
    let observed ← body `JanetCartan.PhysicalPairs.OriginalSourceAmplitude.observed_angular_statement p
    let some whole := observed.find? (·.isAppOfArity `JanetCartan.CanonicalAtomRealization.wholeSourceCorrectedWave 20) |
      throwError "actual observed source: lost the same complete native whole source"
    let N := whole.getAppArgs[1]!
    let T := whole.getAppArgs[6]!
    unless T.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalLocalWaves.T 53 do
      throwError "actual observed source: missing original source53"
    let source := T.getAppArgs
    for e in #[n,N,T] do
      if e.hasLooseBVars then throwError "actual observed source: chart DATA depends on the later torus point"
    let fixed := native64[:22].toArray
    let ψ := app (ob ++ `observationFunction) fixed
    let hψ := app (ob ++ `observation_smooth) fixed
    let Z := app ``JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourceCombinedWave p
    let bargs := p[:50].toArray.push p[52]!
    let bt ← body (buffer ++ `statement) bargs
    unless bt.isAppOfArity ``And 2 do throwError "actual observed source: changed existing buffer certificate"
    let bx := app (buffer ++ `buffer) bargs
    let hX := app ``And.left #[bt.getAppArgs[0]!,bt.getAppArgs[1]!,bx]
    let hs := app ``And.right #[bt.getAppArgs[0]!,bt.getAppArgs[1]!,bx]
    let X := bt.getAppArgs[0]!.appArg!
    let st ← body (selected ++ `statement) p
    unless st.isAppOfArity ``ContDiffOn 11 do throwError "actual observed source: changed actual complete-wave smoothness"
    let a := st.getAppArgs
    if which.getNat < 2 then
      let hObserved := mkAppN (mkConst ``JanetCartan.PrimarySourceAdmission.contDiff_cutoff_of_support_subset [.zero])
        #[n,a[5]!,a[6]!,a[7]!,ψ,Z,X,hψ,hX,app (selected ++ `smooth) p,hs]
      if which.getNat == 0 then
        save `smooth_statement p (← inferType hObserved) (mkSort .zero) true
      else
        save `smooth p hObserved (app (ns ++ `smooth_statement) p)
      return
    let compact ← mkAppM ``ContDiffBump.hasCompactSupport #[app (ob ++ `observationCutoff) fixed]
    let compactType ← inferType compact
    let .forallE _ finiteType _ .instImplicit := compactType |
      throwError "actual observed source: changed cutoff finite-dimensional compact-support certificate"
    let compact := mkApp compact (← synthInstance finiteType)
    unless (← inferType compact).isAppOf ``HasCompactSupport do
      throwError "actual observed source: cutoff compact-support instance not fully applied"
    let smooth := app (ns ++ `smooth) p
    let made := app ``JanetCartan.PhysicalPairs.ObservedSchwartz.wave #[n,N,ψ,compact,Z,smooth]
    if which.getNat == 2 then
      save `wave p made (← inferType made) true
      return
    let actual := app (ns ++ `wave) p
    let point := a[2]!
    withLocalDeclD `x point fun x => do
      if which.getNat == 3 then
        let proof := app ``JanetCartan.PhysicalPairs.ObservedSchwartz.wave_apply #[n,N,ψ,compact,Z,smooth,x]
        let target := (← inferType proof).replace fun e => if e == made then some actual else none
        unless (target.find? (· == actual)).isSome do throwError "actual observed source: missed the published Schwartz representative"
        save `wave_apply (p.push x) proof target
      else
        let chart := app ``JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart source[:23].toArray
        withLocalDeclD `hx (← mkAppM ``Membership.mem #[chart,x]) fun hx => do
          let plateau := app ``JanetCartan.PhysicalPairs.OriginalSourcePlateau.germ_on_original_chart
            (source[:23].toArray ++ #[x,hx])
          let proof := app ``JanetCartan.PhysicalPairs.ObservedSchwartz.wave_eventuallyEq
            #[n,N,ψ,compact,Z,smooth,x,plateau]
          let target := (← inferType proof).replace fun e => if e == made then some actual else none
          unless (target.find? (· == actual)).isSome do throwError "actual observed source: missed the actual wave germ"
          let all := p ++ #[x,hx]
          if which.getNat == 4 then save `germ_statement all target (mkSort .zero) true
          else save `germ_on_original_chart all proof (app (ns ++ `germ_statement) all)
end JanetCartan.PhysicalPairs.OriginalSourceSchwartzTemplate
end
