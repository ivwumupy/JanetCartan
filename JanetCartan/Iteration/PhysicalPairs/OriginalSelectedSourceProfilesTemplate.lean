module
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteSourceProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedSourceEstimates
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSampling
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSampling
/-! # Actual full-Picard physical source jets on the entire original chart

Consume the genuine selected native-source profile and the exact physical/native
amplitude identity. The all-order constant is the SAME Csource_N fixed before
history/target/smoothing. This does not need the baseline producer and introduces
no source-profile or output-bound premise (`main:prop:pairs`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSelectedSourceProfilesTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalSelectedCompleteProfiles
private def source := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
elab "profile_original_selected_physical_source" : command => liftTermElabM do
  PhysicalMean.OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f native _ _ => do
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
      | throwError "actual physical source profile: original fixed cutoff missing"
    let L := linear.getAppArgs[51]!
    unless L.isAppOfArity `JanetCartan.RawInputPartition.cutoffCount 1 && !L.containsFVar p[53]!.fvarId! do
      throwError "actual physical source profile: cutoff must be fixed before Picard iteration"
    let u := originalSource.replace fun e => if e == p[52]! then some L else none
    forallBoundedTelescope (← inferType high) (some 1) fun reach _ => do
      unless reach.size == 1 do throwError "actual physical source profile: numerical auxiliary reach changed"
      let selected := p[:52].toArray ++ reach ++ #[p[53]!]
      withLocalDeclD `sample sample fun i => do
        let nativeArgs := native ++ #[hγ,hR90,L,u,i]
        let same := app `JanetCartan.PhysicalPairs.OriginalCompleteSourceIdentity.source_eq_native nativeArgs
        let chart ← forallBoundedTelescope (← inferType same) (some 2) fun point _ => do
          let chart := (← inferType point[1]!).getAppArgs[3]!
          unless chart.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart 23 do
            throwError "actual physical source profile: not the whole original chart"
          pure chart
        let actual := native ++ #[L,u,i]
        let S := app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit.sourceAmplitude actual
        let D := app `JanetCartan.PhysicalPairs.OriginalCompleteSourceIdentity.nativeAmplitude nativeArgs
        let n := mkApp (mkConst ``Nat.succ) native[0]!
        let N := app `JanetCartan.embeddingDimension #[n]
        withLocalDeclD `order (mkConst ``Nat) fun q => do
          let all := selected ++ #[i,q]
          let nativeProfile := app (source ++ `native_source_profile) all
          let norms := Expr.proj ``And 1 nativeProfile
          let price ← forallBoundedTelescope (← inferType norms) (some 1) fun _ target => pure target.appArg!
          let proof := app `JanetCartan.PhysicalPairs.OriginalCompleteSourceProfiles.physical_jets_of_native
            #[n,N,S,D,chart,app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_open chart.getAppArgs,
              same,Expr.proj ``And 0 nativeProfile,q,price,norms]
          let type ← instantiateMVars (← mkForallFVars all (← inferType proof))
          let value ← instantiateMVars (← mkLambdaFVars all proof)
          for e in #[type,value] do
            if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
              throwError "actual physical source profile: added analytic input or unresolved field"
          let (type,value) := Lean.ShareCommon.shareCommon (type,value)
          let name := root ++ `source_profile
          IO.println "Kernel checking actual full-Picard physical source profile/56"
          (← IO.getStdout).flush
          addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
          addDocStringCore name "The literal physical source summand in the actual complete-wave derivative is smooth on the WHOLE original chart and has Csource_N(q)*h*R^q jets from the SAME genuine native full-Picard producer, with no added source/profile or output-success premise (main:prop:pairs; main:eq:mean-final-amplitude)."
          let axioms ← collectAxioms name
          unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
            throwError "actual physical source profile: nonstandard axioms {axioms}"
          logInfo m!"actual full-Picard physical source profile/56: {axioms}"
end JanetCartan.PhysicalPairs.OriginalSelectedSourceProfilesTemplate
end
