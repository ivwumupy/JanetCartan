module
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteBaselineIdentity
public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteSourceIdentity
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceSignedPhase
public import JanetCartan.Iteration.PhysicalPairs.OriginalBaselineNativeProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedHermitianProfiles
/-! # The SAME observed full self tensor of the signed and mean constructions

The two exact baseline-to-parent identities meet at the SAME outer sample.
The whole source derivative is already the same native D. Combine these before
squaring, and cancel only the actual unit phase of the complete derivative.
The original weight occurs once. No size or self-tensor hypothesis, leading
amplitude or altered observation is used (`main:eq:self-off`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public section
namespace JanetCartan.PhysicalPairs.OriginalSelectedSelfIdentity
/-- The two genuine baseline identifications meet at the same parent value;
add the actual whole source before forming a Hermitian square. -/
theorem full_node_eq_of_original_parent {n N : ℕ}
    (A B D Bnative Bsample Dnative : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (x : Euclidean n) (parent : Matrix (Fin N) (Fin n) ℂ)
    (hsplit : A x = B x + D x) (hB : B = Bnative)
    (hp : Bnative x = parent) (hc : Bsample x = parent) (hD : D x = Dnative x) :
    A x = Bsample x + Dnative x := by
  rw [hsplit,hB,hp,← hc,hD]
end JanetCartan.PhysicalPairs.OriginalSelectedSelfIdentity
end
public meta section
namespace JanetCartan.PhysicalPairs.OriginalSelectedSelfIdentityTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalSelectedSelfIdentity
private def herm := `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
/- This equality only needs the already constructed self field. Opening the
residual's extra core-membership binder also reduces the unrelated, large
target/core construction during local-instance discovery. Read the identical
54-argument field directly, with no residual-domain hypothesis. -/
private def withOriginalSelfData
    (next : Array Expr → Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let self := `JanetCartan.PhysicalMean.OriginalSelectedMeanData.fullSampledSelf
  let forcing := `JanetCartan.PhysicalMean.OriginalCompleteForcing
  let ci ← getConstInfo self
  forallBoundedTelescope ci.type (some 54) fun p fieldType => do
    unless p.size == 54 && fieldType.isForall do
      throwError "actual full-self join: original selected54 field changed"
    let H := ((ci.value! (allowOpaque := true)).beta p).headBeta
    let full := (((← getConstInfo (forcing ++ `selectedFullSource)).value! (allowOpaque := true)).beta p[:52].toArray).headBeta
    unless full.isAppOfArity (forcing ++ `completeSource) 4 do
      throwError "actual full-self join: lost the SAME complete forcing"
    let leading := full.getAppArgs[1]!
    unless leading.isAppOfArity (forcing ++ `leadingMean) 50 do
      throwError "actual full-self join: original native50 changed"
    withLocalDeclNoLocalInstanceUpdate `x .default fieldType.bindingDomain! fun x =>
      next (p.push x) H leading.getAppArgs
private def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual full-self join: unresolved original data or added premise {key}"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "actual full-self join: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking SAME observed/mean full self {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The actual observed complete primary's Hermitian derivative self is the SAME original full sampled mean tensor on the whole source chart: original outer baseline, whole source, phase and one weight retained, without an analytic or tensor-identity premise (main:eq:self-off; main:eq:mean-final-amplitude)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual full-self join: nonstandard axioms {axioms}"
  logInfo m!"SAME observed/mean full self {key}/{p.size}: {axioms}"
elab "identify_original_selected_full_self " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "actual full-self join: unknown mode"
  withOriginalSelfData fun p H native => do
    let atX := (mkApp H p[54]!).headBeta
    unless atX.isAppOfArity `JanetCartan.CurrentMean.weightedHermitianTensor 9 do
      throwError "actual full-self join: original full self changed"
    let a := atX.getAppArgs
    let initialized := a[7]!.getAppArgs[2]!
    let u := initialized.getAppArgs[5]!.getAppArgs[5]!
    let sample := (← inferType a[6]!).bindingDomain!
    let sourceArgs := native ++ #[p[52]!,u]
    let chart := app (herm ++ `sourceChart) p[:33].toArray
    let x := p[54]!
    withLocalDeclNoLocalInstanceUpdate `hxSourceChart .default (← mkAppM ``Membership.mem #[chart,x]) fun hx => do
      if mode.getNat == 0 then
        withLocalDeclNoLocalInstanceUpdate `sample .default sample fun i => do
          let actual := sourceArgs.push i
          let hB := app `JanetCartan.PhysicalPairs.OriginalCompleteBaselineIdentity.baseline_eq_actual_baseline actual
          let Bnative := (← inferType hB).getAppArgs[2]!
          unless Bnative.isAppOfArity `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.baselineAmplitude 56 do
            throwError "actual full-self join: unchanged outer baseline56 disappeared"
          unless sample.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
            throwError "actual full-self join: not the original SampleIndex"
          let hweight := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.original_sample_weight_ne_zero [.zero])
            (sample.getAppArgs.push i)
          let nativeParent := app `JanetCartan.PhysicalPairs.OriginalBaselineNativeProfiles.baseline_eq_parent
            (Bnative.getAppArgs ++ #[hweight,x,hx])
          let canonicalParent := app (herm ++ `sampled_baseline_eq_parent) (p[:39].toArray ++ #[i,x,hx])
          let parent := (← inferType nativeParent).getAppArgs[2]!
          let moment := `JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmission
          let hγ := app (moment ++ `AtPoint.gamma_le_tolerance) p[:21].toArray
          let hR := app (moment ++ `moment_reached) p[:35].toArray
          let sourceEq := app `JanetCartan.PhysicalPairs.OriginalCompleteSourceIdentity.source_eq_native
            (native ++ #[hγ,hR,p[52]!,u,i,x,hx])
          let split := app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit.amplitude_eq_base_add_source (actual ++ #[x,hx])
          let n := mkApp (mkConst ``Nat.succ) native[0]!
          let N := app `JanetCartan.embeddingDimension #[n]
          let A := app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitude.amplitude actual
          let B := app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit.baselineAmplitude actual
          let D := app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitudeSplit.sourceAmplitude actual
          let Bsample := mkApp (app (herm ++ `sampledBaseline) p[:39].toArray) i
          let Dnative := mkApp (app (herm ++ `nativeSourceField) p[:54].toArray) i
          let proof := app (root ++ `full_node_eq_of_original_parent)
            #[n,N,A,B,D,Bnative,Bsample,Dnative,x,parent,split,hB,nativeParent,canonicalParent,sourceEq]
          save `amplitude_eq_full_native (p[:54].toArray ++ #[i,x,hx]) proof (← inferType proof)
        return
      let full := app (herm ++ `full_self_native_on_chart) (p[:55].toArray.push hx)
      let equality ← inferType full
      let nativeTensor := equality.getAppArgs[2]!
      unless nativeTensor.isAppOfArity ``JanetCartan.CurrentMean.weightedHermitianTensor 9 do
        throwError "actual full-self join: same full native tensor changed"
      let ta := nativeTensor.getAppArgs
      let n := mkApp (mkConst ``Nat.succ) native[0]!
      let N := app `JanetCartan.embeddingDimension #[n]
      let μ := ta[6]!
      let waves ← withLocalDeclNoLocalInstanceUpdate `sample .default sample fun i => do
        let Z ← mkAppM ``DFunLike.coe #[app `JanetCartan.PhysicalPairs.OriginalSourceSchwartz.wave (sourceArgs.push i)]
        mkLambdaFVars #[i] Z
      let phases ← withLocalDeclNoLocalInstanceUpdate `sample .default sample fun i =>
        mkLambdaFVars #[i] (app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitude.phase (sourceArgs.push i))
      let amplitudes ← withLocalDeclNoLocalInstanceUpdate `sample .default sample fun i =>
        mkLambdaFVars #[i] (app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitude.amplitude (sourceArgs.push i))
      let sampledAtX ← withLocalDeclNoLocalInstanceUpdate `sample .default sample fun i => mkLambdaFVars #[i] (mkApp (mkApp amplitudes i) x)
      let nativeAtX := mkApp ta[7]! x
      let each ← withLocalDeclNoLocalInstanceUpdate `sample .default sample fun i => do
        let proof := app (root ++ `amplitude_eq_full_native) (p[:54].toArray ++ #[i,x,hx])
        withLocalDeclNoLocalInstanceUpdate `nonzeroWeight .default (← mkAppM ``Ne #[mkApp μ i,← mkNumeral (mkConst ``Real) 0]) fun hi =>
          mkLambdaFVars #[i,hi] proof
      let sumEq := mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.weighted_full_self_eq_on_active [.zero])
        #[n,N,sample,ta[5]!,μ,sampledAtX,nativeAtX,each]
      let phaseEq := mkAppN (mkConst ``JanetCartan.UniformStep.weightedHermitian_sampledDerivativeAmplitude [.zero])
        #[n,N,sample,ta[5]!,μ,waves,phases]
      let atPoint ← mkAppM ``congrFun #[phaseEq,x]
      let proof ← mkAppM ``Eq.trans #[atPoint,← mkAppM ``Eq.trans #[sumEq,← mkAppM ``Eq.symm #[full]]]
      let desired ← mkEq (← inferType atPoint).getAppArgs[1]! equality.getAppArgs[1]!
      save `observed_self_on_chart (p[:55].toArray.push hx) proof desired
end JanetCartan.PhysicalPairs.OriginalSelectedSelfIdentityTemplate
end
