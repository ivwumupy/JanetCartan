module

public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgets
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativePhaseMargins
public meta import Lean

/-!
# The one current used by the original comparison

Join the actual graph margin and native inverse/profile thresholds by a numerical
maximum. The original graph parameters precede the source dilation; the native
source/inverse caps and reserve remain numerical inputs. The source map, history,
selected row, common measurement and retained five-field tuple are unchanged.

The returned retained-profile continuation still requires task24's actual initial
profile, and the full finite comparison still requires task13's uncut ambient
response. No norm estimate, successful inverse, phase-smallness conclusion or
comparison bound is introduced as an assumed field
(`app:ch_waves:eq:colored-normal-comparison`, `new:sec:order-of-choices`).
-/

public meta section
set_option Elab.async false
namespace JanetCartan.PhysicalNormalInverse.OriginalComparisonCurrentApplication
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalNormalInverse.OriginalComparisonCurrent
private def originalNS := `JanetCartan.PhysicalInitialization.OriginalCurrent
private def comparisonNS := `JanetCartan.PhysicalNormalInverse.OriginalComparison
private def retainedNS := `JanetCartan.PhysicalNormalInverse.OriginalRetained
private def measurementNS := `JanetCartan.PhysicalNormalInverse.OriginalMeasurement
private def marginSource := `JanetCartan.PhysicalSampling.OriginalPhaseMargins.all_four_phase_margins_native

private def save (short : Name) (params : Array Expr) (proof : Expr)
    (data := false) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars params (← inferType proof))
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  if type.hasMVar || value.hasMVar || type.hasLevelMVar || value.hasLevelMVar ||
      type.hasFVar || value.hasFVar || type.hasSorry || value.hasSorry then
    throwError "original comparison current: open or recovered declaration {short}"
  let name := root ++ short
  if data then
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  logInfo m!"kernel-checked original comparison current {short}: {params.size} inputs"
  return mkAppN (mkConst name) params

private def nativeLeadingArgs (params : Array Expr) : MetaM (Array Expr) := do
  let mut value := mkAppN (mkConst (originalNS ++ `current)) params
  for _ in [:4] do
    if value.getAppFn.isConstOf `JanetCartan.PhysicalPrimary.LeadingCell.current then break
    let some body := (← getConstInfo value.getAppFn.constName!).value?
      | throwError "original comparison current: actual current alias has no body"
    value := body.beta value.getAppArgs
  unless value.isAppOfArity `JanetCartan.PhysicalPrimary.LeadingCell.current 36 do
    throwError "original comparison current: missing exact retained36 current"
  return value.getAppArgs

private def joinOnHistory (params native profiles comparison : Array Expr)
    (graphProof graphThreshold compareThreshold : Expr) : MetaM Unit := do
  let S ← save `S params (← mkAppM ``Max.max #[compareThreshold, graphThreshold]) true
  let hCompare ← save `S_comparison params
    (← mkAppM `le_max_left #[compareThreshold, graphThreshold])
  let hGraph ← save `S_graph params
    (← mkAppM `le_max_right #[compareThreshold, graphThreshold])
  let compare (name : Name) := mkAppN (mkConst (comparisonNS ++ name)) comparison
  discard <| save `hS params (← mkAppM `le_trans #[compare `hS, hCompare])
  let graphType ← whnf (← inferType graphProof)
  withLocalDeclD `R₀ graphType.bindingDomain! fun R₀ => do
    withLocalDeclD `hReached (← mkAppM ``LE.le #[S, R₀]) fun hReached => do
      let reachedCompare ← mkAppM `le_trans #[hCompare, hReached]
      let reachedGraph ← mkAppM `le_trans #[hGraph, hReached]
      let reachedNative ← mkAppM `le_trans #[compare `S_native, reachedCompare]
      let reachedProfiles ← mkAppM `le_trans #[compare `S_profiles, reachedCompare]
      let reachedMeasure ← mkAppM `le_trans #[compare `S_measurement, reachedCompare]
      let graph := mkAppN graphProof #[R₀, reachedGraph]
      forallBoundedTelescope (← inferType graph) (some 4) fun history _ => do
        unless history.size == 4 do throwError "original comparison current: expected actual history4"
        let i := profiles[31]!
        let currentParams := params ++ #[R₀, hReached] ++ history
        let currentArgs := native ++ #[R₀, reachedNative] ++ history ++ #[i]
        let measureArgs := native ++ #[R₀, reachedMeasure] ++ history ++ #[i]
        discard <| save `current currentParams
          (mkAppN (mkConst (originalNS ++ `current)) currentArgs) true
        let retained ← nativeLeadingArgs currentArgs
        discard <| save `ambient_geometry currentParams
          (← mkAppM ``And.intro #[retained[31]!,
            ← mkAppM ``And.intro #[retained[32]!, retained[33]!]])
        discard <| save `phase_margins currentParams (mkAppN graph (history.push i))
        discard <| save `retained_profiles currentParams
          (mkAppN (mkConst (retainedNS ++ `on_original_sampling_radius))
            (profiles ++ #[R₀, reachedProfiles] ++ history))
        discard <| save `measurement currentParams
          (mkAppN (mkConst (measurementNS ++ `on_current)) measureArgs)
        let lower := mkAppN (mkConst (measurementNS ++ `at_reserve)) measureArgs
        forallBoundedTelescope (← inferType lower) (some 2) fun reserves _ => do
          unless reserves.size == 2 do
            throwError "original comparison current: expected shared measurement reserve2"
          discard <| save `measurement_at_reserve (currentParams ++ reserves) (mkAppN lower reserves)

private def joinNativeCaps (graph : Array Expr) : MetaM Unit := do
  let samplingInfo ← getConstInfo `JanetCartan.PhysicalSampling.samplingCappedExtra
  let samplingTail := samplingInfo.type.bindingBody!.instantiate1 graph[0]!
  let n := samplingTail.bindingDomain!.appArg!
  let merged := mkAppN (mkConst `JanetCartan.PhysicalSampling.samplingCappedExtra)
    #[graph[0]!, graph[1]!, graph[2]!, graph[21]!]
  let original := (#[n, graph[1]!] ++ graph[3:22].toArray).set! 20 merged
  let start := mkAppN (mkConst (originalNS ++ `current)) (original.push graph[27]!)
  forallBoundedTelescope (← inferType start) (some 2) fun caps _ => do
    let beforeReserve := original ++ #[graph[27]!] ++ caps ++ graph[29:33].toArray
    let current := mkAppN (mkConst (originalNS ++ `current)) beforeReserve
    forallBoundedTelescope (← inferType current) (some 1) fun canonical _ => do
      let beforeLeading := beforeReserve ++ canonical ++ #[graph[35]!]
      let current := mkAppN (mkConst (originalNS ++ `current)) beforeLeading
      forallBoundedTelescope (← inferType current) (some 1) fun leading _ => do
        let native := beforeLeading ++ leading
        unless native.size == 31 do
          throwError "original comparison current: changed actual native31 prefix"
        let profileStart := mkAppN (mkConst (retainedNS ++ `S)) native
        forallBoundedTelescope (← inferType profileStart) (some 3) fun initial _ => do
          unless initial.size == 3 do
            throwError "original comparison current: expected selected index and fixed initial budget pair"
          let profiles := native ++ initial
          let comparison := graph[:22].toArray ++ native[21:31].toArray ++ initial
          let params := graph ++ caps ++ canonical ++ leading ++ initial
          unless params.size == 43 && comparison.size == 35 do
            throwError "original comparison current: expected actual graph/native43 and comparison35"
          let graphProof := mkAppN (mkConst marginSource) graph
          let graphThreshold ← forallBoundedTelescope (← inferType graphProof) (some 2) fun reached _ => do
            let type ← inferType reached[1]!
            unless type.isAppOfArity ``LE.le 4 do
              throwError "original comparison current: missing original graph threshold inequality"
            return type.getAppArgs[2]!
          let compareThreshold := mkAppN (mkConst (comparisonNS ++ `S)) comparison
          joinOnHistory params native profiles comparison graphProof graphThreshold compareThreshold

/-- The original Graph36 fixed inputs plus four native numerical caps/reserves
and the selected initial budget give one shared current, with no new choice. -/
elab "apply_original_comparison_current_inputs" : command => liftTermElabM do
  let info ← getConstInfo marginSource
  forallBoundedTelescope info.type (some 36) fun graph _ => do
    unless graph.size == 36 do throwError "original comparison current: expected actual graph fixed36"
    joinNativeCaps graph

end JanetCartan.PhysicalNormalInverse.OriginalComparisonCurrentApplication
