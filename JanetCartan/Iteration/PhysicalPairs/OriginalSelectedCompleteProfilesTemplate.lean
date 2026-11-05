module
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteBaselineProfiles
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedCompleteBudget
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedSourceProfiles
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteAmplitudeProfilesTemplate
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceSignedPhase
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedWaves
public import JanetCartan.Iteration.PhysicalPairs.OriginalStageSize
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedSourceEstimates
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSampling
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSampling
/-! # Actual complete-source single-node profiles before the signed product

The genuine native all-order full-Picard source profile and the actual outer
baseline producer imply the whole original chart profile of the SAME complete
phase-cancelled derivative. Its price is fixed on selected33+N before every
history, smoothing scale, target or source sample. The source is not an analytic
input: it is the original full-forcing Picard iterate at the fixed cutoff L
(`main:prop:pairs`, `main:eq:mean-final-amplitude`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSelectedCompleteProfilesTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalSelectedCompleteProfiles
private def full := `JanetCartan.PhysicalPairs.OriginalCompleteAmplitude
private def split := `JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit
private def source := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def namePrice (type CB CD C : Expr) : Expr := type.replace fun e => do
  if !e.isAppOfArity ``HAdd.hAdd 6 then none else
    let a := e.getAppArgs
    if a[4]!.isApp && a[5]!.isApp && a[4]!.appFn! == CB && a[5]!.appFn! == CD &&
        a[4]!.appArg! == a[5]!.appArg! then
      some (mkApp C a[4]!.appArg!)
    else none
private def termWith (bindings : List (Name × Expr)) (text : String) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings text)
private def part (e : Expr) (k : Nat) : Expr := Expr.proj ``And 0
  (Nat.rec (motive := fun _ => Expr) e (fun _ v => Expr.proj ``And 1 v) k)
private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual complete-node profile: later input or analytic premise escaped {key}"
    let missing := e.getUsedConstants.filter (fun key => (env.find? key).isNone)
    unless missing.isEmpty do throwError "actual complete-node profile: unavailable producer {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual complete-node profile {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME original observed complete full-forcing Picard wave has genuine full-chart phase-cancelled derivative jets bounded by the static selected33+N baseline-plus-Csource price; actual native source and outer-baseline producers are consumed, without source, amplitude or output success hypotheses (main:prop:pairs; main:eq:mean-final-amplitude)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual complete-node profile: nonstandard axioms {axioms}"
  logInfo m!"actual complete-node profile {key}/{p.size}: {axioms}"
elab "prove_original_selected_complete_profile " mode:num : command => liftTermElabM do
  unless mode.getNat == 3 do throwError "actual complete-node profile: unknown mode"
  PhysicalMean.OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f native _ _ => do
    let static := p[:33].toArray.push p[53]!
    let CB := app `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.Cbaseline native[:44].toArray
    let hCB := app `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.Cbaseline_nonneg native[:44].toArray
    let CD := app (source ++ `Csource) static
    let hCD := app (source ++ `Csource_nonneg) static
    let atX := (mkApp f[5]! p[54]!).headBeta
    let a := atX.getAppArgs
    let Z := a[7]!.getAppArgs[2]!
    let originalSource := Z.getAppArgs[5]!.getAppArgs[5]!
    let sample := (← inferType a[6]!).bindingDomain!
    let moment := `JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmission
    let hγ := app (moment ++ `AtPoint.gamma_le_tolerance) p[:21].toArray
    let hR90 := app (moment ++ `moment_reached) p[:35].toArray
    let high := app `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.high_error (native ++ #[hγ,hR90])
    let some linear := (← inferType high).find? (·.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear 52)
      | throwError "actual complete-node profile: missing original full cutoff"
    let L := linear.getAppArgs[51]!
    unless L.isAppOfArity `JanetCartan.RawInputPartition.cutoffCount 1 && !L.containsFVar p[53]!.fvarId! do
      throwError "actual complete-node profile: cutoff is not fixed before Picard iteration"
    let u := originalSource.replace fun e => if e == p[52]! then some L else none
    forallBoundedTelescope (← inferType high) (some 1) fun reach _ => do
      unless reach.size == 1 do throwError "actual complete-node profile: auxiliary numeric reach changed"
      let selected := p[:52].toArray ++ reach ++ #[p[53]!]
      let hInitial ← mkAppM ``le_trans
        #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS native[:44].toArray,native[45]!]
      let facts ← mkAppM ``JanetCartan.PhysicalMean.fixedPicard_history_scale_facts #[hInitial,native[46]!]
      let hR := part facts 0
      let R := (← inferType hR).appArg!
      let hT := part facts 1
      let T := (← inferType hT).appArg!
      let hh := part facts 3
      let h := (← inferType hh).appArg!
      withLocalDeclD `sample sample fun i => do
        let actual := native ++ #[L,u,i]
        let all := selected.push i
        let A := app (full ++ `amplitude) actual
        let B := app (split ++ `baselineAmplitude) actual
        let S := app (split ++ `sourceAmplitude) actual
        let baseline := app `JanetCartan.PhysicalPairs.OriginalCompleteBaselineProfiles.baseline_profile actual
        let btype ← inferType baseline
        let chart := btype.getAppArgs[0]!.getAppArgs[10]!
        unless chart.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart 23 do
          throwError "actual complete-node profile: baseline is not on the whole original chart"
        let hchart := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_open chart.getAppArgs
        let n := mkApp (mkConst ``Nat.succ) native[0]!
        let N := app `JanetCartan.embeddingDimension #[n]
        let sourceZero := app (root ++ `source_profile) (all.push (mkNatLit 0))
        let sourceJets ← withLocalDeclD `order (mkConst ``Nat) fun q =>
          mkLambdaFVars #[q] (.proj ``And 1 (app (root ++ `source_profile) (all.push q)))
        let hTzero ← termWith [(`hT,hT)] "(zero_le_one : (0 : ℝ) ≤ 1).trans hT"
        let proof := app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeProfiles.complete_true_R_profile
          #[n,N,chart,hchart,A,B,S,app (split ++ `amplitude_eq_base_add_source) actual,
            .proj ``And 0 baseline,.proj ``And 0 sourceZero,CB,CD,hCB,hCD,T,R,h,hTzero,
            part facts 2,hR,part facts 4,.proj ``And 1 baseline,sourceJets]
        let target := namePrice (← inferType proof) CB CD (app (root ++ `Camplitude) static)
        save `profile all proof target
elab "admit_original_selected_complete_waves" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (root ++ `profile)).type (some 55) fun p target => do
    unless target.isAppOfArity ``And 2 do throwError "actual node admission: full profile conjunction changed"
    let smooth := target.getAppArgs[0]!.getAppArgs
    let A := smooth[9]!
    let chart := smooth[10]!
    unless A.isAppOfArity (full ++ `amplitude) 53 do throwError "actual node admission: original full amplitude changed"
    let waveArgs := A.getAppArgs
    let native := waveArgs[:50].toArray
    let selected := p[:54].toArray
    let static := p[:33].toArray.push p[53]!
    let C := app (root ++ `Camplitude) static
    let hC := app (root ++ `Camplitude_nonneg) static
    let n := mkApp (mkConst ``Nat.succ) native[0]!
    let N := app `JanetCartan.embeddingDimension #[n]
    let correction := `JanetCartan.PhysicalPairs.OriginalSourceSignedCorrection.correction
    withLocalDeclD `Cscale (mkConst ``Real) fun scale => do
      let pre := native[:44].toArray ++ #[scale] ++ native[44:].toArray ++ waveArgs[50:52].toArray
      unless pre.size == 53 do throwError "actual node admission: SAME correction53 prefix changed"
      let gate := (← inferType (app correction pre)).bindingDomain!
      withLocalDeclD `reachedSignedWindow gate fun hSigned => do
        let parameters := pre ++ #[hSigned,← mkNumeral (mkConst ``Real) 0]
        let actual := ((← getConstInfo correction).value! (allowOpaque := true)).beta parameters
        unless actual.isAppOfArity `JanetCartan.PhysicalPairs.OriginalSignedSum.correction 47 do
          throwError "actual node admission: not the SAME original signed correction"
        let sa := actual.getAppArgs
        let θ := app `JanetCartan.PhysicalPairs.OriginalStageMetric.angles sa[:45].toArray
        let R := app `JanetCartan.historyScale #[native[44]!,mkConst `JanetCartan.growthExponent,native[46]!]
        let hR := app `JanetCartan.PhysicalPairs.OriginalStageSize.stage_one
          #[app `JanetCartan.PhysicalPairs.SampledHistory.S sa[:37].toArray,native[44]!,
            app `JanetCartan.PhysicalPairs.SampledHistory.hS sa[:37].toArray,hSigned,native[46]!]
        let fine := app `JanetCartan.PhysicalPairs.OriginalWindow.fineScale #[scale,R]
        let ledger := app `JanetCartan.PhysicalPairs.OriginalSelectedWaves.nodeJets
          #[n,N,← inferType p[54]!,chart,C,fine,θ,sa[45]!]
        let jets := Expr.proj ``And 1 (app (root ++ `profile) p)
        let proof ← forallBoundedTelescope (← inferType jets) (some 3) fun point _ => do
          let q := point[0]!
          let x := point[1]!
          let hx := point[2]!
          let bound := app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeProfiles.jet_le_original_fine
            #[n,N,A,scale,mkApp C q,R,mkApp hC q,hR,q,x,mkAppN jets point]
          let same := app `JanetCartan.PhysicalPairs.OriginalSourceSignedPhase.amplitude_eq_signed
            (parameters.push p[54]!)
          let pred ← withLocalDeclD `amplitude (← inferType A) fun Z => do
            mkLambdaFVars #[Z] ((← inferType bound).replace fun e => if e == A then some Z else none)
          let trans ← mkAppM ``congrArg #[pred,same]
          let result ← mkAppM ``Eq.mp #[trans,bound]
          mkLambdaFVars #[p[54]!,x,hx,q] result
        save `nodeJets (selected ++ #[scale,hSigned]) proof ledger
end JanetCartan.PhysicalPairs.OriginalSelectedCompleteProfilesTemplate
end
