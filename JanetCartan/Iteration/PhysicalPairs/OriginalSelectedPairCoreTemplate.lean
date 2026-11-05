module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedPairEstimatesTemplate
public import JanetCartan.Iteration.PhysicalPairs.OriginalSelectedSelfIdentityTemplate
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourcePrimaryCore
public import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometry
/-! # Pair residual for the literal aggregate primary and complete mean self

On the unchanged original core, use the aggregate primary's existing cutoff germ
and the exact full observed/self identity. This is the SAME correction, current,
original sample and weight; it is not a new primary or a leading self tensor
(`main:eq:self-off`, `main:prop:pairs`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public noncomputable section
open scoped Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs.OriginalSelectedPairCore
/-- Use the original physical smoothing core, not a smaller replacement domain. -/
theorem original_core_in_chart {n : ℕ} (D : LocalDomain) {x : Euclidean n}
    (hx : x ∈ D.core n) : x ∈ D.chart n :=
  Metric.closedBall_subset_ball D.coreRadius_lt_chartRadius hx
/-- The actual residual is unchanged by the two SAME-field pointwise identities. -/
theorem transfer_actual_offself {n N : ℕ} (P Q : Euclidean n → Euclidean N)
    (H J : MetricField n) (v : MetricTensor n) (price : ℝ) (x : Euclidean n)
    (hP : inducedMetric P x = inducedMetric Q x) (hH : H x = J x)
    (h : ‖v + (inducedMetric Q-J) x‖ ≤ price) :
    ‖v + (inducedMetric P-H) x‖ ≤ price := by
  change ‖v + (inducedMetric P x-H x)‖ ≤ price
  rw [hP,hH]
  exact h
end JanetCartan.PhysicalPairs.OriginalSelectedPairCore
end
public meta section
namespace JanetCartan.PhysicalPairs.OriginalSelectedPairCoreTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalSelectedPairCore
private def estimates := `JanetCartan.PhysicalPairs.OriginalSelectedPairEstimates
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
/-- Open only the original point and its core-membership proof. Neither is a
local typeclass instance. Keeping the literal two binder types avoids unfolding
the large original domain while scanning for instances. Consumers are the
actual pointwise join and its C⁰ consequence; no hypothesis is added. -/
def withOriginalCorePoint (type : Expr)
    (next : Array Expr → Expr → MetaM Expr) : MetaM Expr := do
  let .forallE pointName pointType afterPoint pointInfo := type
    | throwError "actual pair core: expected the original point binder"
  withLocalDeclNoLocalInstanceUpdate pointName pointInfo pointType fun x => do
    let .forallE gateName gateType afterGate gateInfo := afterPoint.instantiate1 x
      | throwError "actual pair core: expected the original core-membership binder"
    withLocalDeclNoLocalInstanceUpdate gateName gateInfo gateType fun hx =>
      next #[x,hx] (afterGate.instantiate1 hx)
private def save (key : Name) (p : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual pair core: unresolved original full-self identity {key}"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "actual pair core: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual aggregate/full-self pair residual {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The actual original complete-source signed correction cancels the off-self metric of the SAME final aggregate-cutoff primary relative to the SAME complete sampled mean self, on the unchanged physical core with fixed prehistory constants (main:eq:self-off; main:prop:pairs; main:eq:pair-error)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual pair core: nonstandard axioms {axioms}"
  logInfo m!"actual aggregate/full-self pair residual {key}/{p.size}: {axioms}"
elab "identify_original_selected_pair_core " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "actual pair core: unknown mode"
  let input := estimates ++ (if mode.getNat == 0 then `uncut_metric_lag else `uncut_mass_lag)
  forallBoundedTelescope (← getConstInfo input).type (some 58) fun p target => do
    let some S := target.find? (·.isAppOfArity `JanetCartan.PhysicalPairs.OriginalSourceSignedCorrection.correction 55)
      | throwError "actual pair core: SAME actual signed correction55 missing"
    let c := S.getAppArgs
    let value := ((← getConstInfo `JanetCartan.PhysicalPairs.OriginalSourceSignedCorrection.correction).value! (allowOpaque := true)).beta c
    unless value.isAppOfArity `JanetCartan.PhysicalPairs.OriginalSignedSum.correction 47 do
      throwError "actual pair core: finite original signed sum changed"
    let old := value.getAppArgs
    let native := c[:44].toArray ++ c[45:51].toArray
    let n := mkApp (mkConst ``Nat.succ) native[0]!
    let N := app `JanetCartan.embeddingDimension #[n]
    let proof ← withOriginalCorePoint target fun y _ => do
      let primaryEq := app `JanetCartan.PhysicalPairs.OriginalSourcePrimaryCore.metric (c ++ y)
      let pe := (← inferType primaryEq).getAppArgs
      let P := pe[1]!.getAppArgs[2]!
      let Q := pe[2]!.getAppArgs[2]!
      let selfPrefix := p[:52].toArray ++ #[c[51]!,p[53]!,y[0]!]
      let sourceGate := (← inferType (app `JanetCartan.PhysicalPairs.OriginalSelectedSelfIdentity.observed_self_on_chart selfPrefix)).bindingDomain!
      unless sourceGate.isAppOfArity ``Membership.mem 5 do throwError "actual pair core: missing original source chart gate"
      let namedChart := sourceGate.getAppArgs[3]!
      let chart ← if namedChart.isAppOfArity `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.sourceChart 33 then do
        pure (((← getConstInfo `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.sourceChart).value! (allowOpaque := true)).beta namedChart.getAppArgs)
        else pure namedChart
      unless chart.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart 23 do
        throwError "actual pair core: source chart changed"
      let original := chart.getAppArgs
      let domain := app `JanetCartan.RevisedUniform.OriginalSmoothing.Dsmooth original
      let hxSmooth := app (root ++ `original_core_in_chart) #[n,domain,y[0]!,y[1]!]
      let hxSource := mkAppN (app `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry.smoothing_chart_in_source_chart original)
        #[y[0]!,hxSmooth]
      let selfEq := app `JanetCartan.PhysicalPairs.OriginalSelectedSelfIdentity.observed_self_on_chart (selfPrefix.push hxSource)
      let H := app `JanetCartan.PhysicalMean.OriginalSelectedMeanData.fullSampledSelf (p[:52].toArray ++ #[c[51]!,p[53]!])
      let diag := app `JanetCartan.PhysicalPairs.OriginalStageMetric.self old
      let rawDiag := ((← getConstInfo `JanetCartan.PhysicalPairs.OriginalStageMetric.self).value! (allowOpaque := true)).beta old
      unless rawDiag.isAppOfArity `JanetCartan.PhysicalPairs.OriginalStageMetric.diagonal 8 do
        throwError "actual pair core: original uncut diagonal changed"
      let da := rawDiag.getAppArgs
      let scale ← mkAppM ``HPow.hPow #[← mkAppM ``HMul.hMul #[da[4]!,
        ← mkAppM ``HPow.hPow #[da[5]!,app `JanetCartan.RevisedScales.forcingExponent #[n]]],mkNatLit 2]
      let scaled ← mkAppM ``HSMul.hSMul #[scale,H]
      let scaledEq ← withLocalDeclNoLocalInstanceUpdate `selfValue .default (← inferType selfEq).getAppArgs[0]! fun Z => do
        let f ← mkLambdaFVars #[Z] (← mkAppM ``HSMul.hSMul #[scale,Z])
        mkAppM ``congrArg #[f,selfEq]
      let reversed ← mkAppM ``Eq.symm #[scaledEq]
      let bound := mkAppN (app input p) y
      let bt := (← inferType bound).getAppArgs
      let add := bt[2]!.appArg!.getAppArgs
      let v := add[add.size-2]!
      let result := app (root ++ `transfer_actual_offself)
        #[n,N,P,Q,scaled,diag,v,bt.back!,y[0]!,primaryEq,reversed,bound]
      mkLambdaFVars y result
    save (if mode.getNat == 0 then `metric_lag else `mass_lag) p proof (← inferType proof)
end JanetCartan.PhysicalPairs.OriginalSelectedPairCoreTemplate
end
