module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-!
# Exact original53 local-domain applications

Only the already-selected source/current/leading getters are unfolded. In
particular the original source threshold is projected through its EXISTING max;
there is no new threshold, reference, leading witness, cell or cutoff choice.
-/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def source := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
private def prescribed := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Prescribed
private def current := `JanetCartan.PhysicalInitialization.OriginalCurrent
private def leading := `JanetCartan.PhysicalInitialization.CurrentLeading
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def smoothing := `JanetCartan.RevisedUniform.OriginalSmoothing

/-- Project a fixed conjunction without unfolding any selected witness. -/
def component (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | j+1 => component (.proj ``And 1 e) j

/-- Open just one declared abbreviation at its actual input spine. -/
def bodyAt (name : Name) (xs : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo name).value?
    | throwError "original local geometry: unavailable definition {name}"
  Core.betaReduce (value.beta xs)

/-- Share just the one expensive *existing* source domain: checking the
native reached inequality (position 40) costs over 257,000 heartbeats. Its
body is literally the original inequality; this introduces no new premise. -/
def sourceInputDomain (xs : Array Expr) (domain : Expr) : MetaM Expr := do
  if xs.size != 40 then return domain
  let name := `JanetCartan.PhysicalPrimary.OriginalLocalWaveInputs.sourceReached
  if (← getEnv).contains name then return mkAppN (mkConst name) xs
  store name xs domain true

/-- Open the native source telescope with its costly domains shared by name. -/
partial def withSourcePrefix (limit : Nat) (finish : Array Expr → MetaM Unit) : MetaM Unit := do
  let rec go (type : Expr) (xs : Array Expr) : MetaM Unit := do
    if xs.size == limit then finish xs
    else
      let .forallE name d body bi ← whnf type | throwError "original local wave: incomplete source telescope at {xs.size}"
      let d ← sourceInputDomain xs d
      withLocalDecl name bi d fun u => go (body.instantiate1 u) (xs.push u)
  go (← getConstInfo (source ++ `full_source_profiles)).type #[]

elab "abbreviate_original_local_inputs_through " k:num : command => liftTermElabM do
  withSourcePrefix (k.getNat+1) fun _ => pure ()

/-- Exact source/current expressions. This meta record does not add a
mathematical data structure, witness or hypothesis to any exported theorem. -/
structure SourceCurrent where
  fixed : Array Expr
  selected : Array Expr
  patch : Expr
  cell : Expr
  datum : Expr
  dataArgs : Array Expr
  reached : Expr

/-- Read the existing Actual.S = max(Current.S,native source threshold), then
reuse the same CurrentLeading.AtPatch datum on its same selected cell. -/
def sourceCurrent (s : Array Expr) : MetaM SourceCurrent := do
  unless s.size == 53 do throwError "original local geometry: expected exact source53"
  let reachedHead ← bodyAt (source ++ `S) s[:39].toArray
  unless reachedHead.isAppOfArity (prescribed ++ `S) 53 do
    throwError "original local geometry: Actual.S no longer aliases prescribed53"
  let closed := reachedHead.getAppArgs
  let fixed := closed[:31].toArray
  let expected := #[(← inferType s[1]!).appArg!] ++ s[1:21].toArray ++ s[23:33].toArray
  for j in [:31] do
    unless ← isDefEq fixed[j]! expected[j]! do throwError "original source changed current input {j}"
  -- The original prescribed V already contains the SAME selected patch and
  -- cell, including their dependent sigma types; do not construct them again.
  let originalV := closed[39]!
  unless originalV.isAppOfArity (masks ++ `V) 25 do
    throwError "original local geometry: lost actual selected parameter window"
  let vArgs := originalV.getAppArgs
  let (patch,cell) := (vArgs[23]!,vArgs[24]!)
  let threshold ← bodyAt (prescribed ++ `S) closed
  unless threshold.isAppOfArity ``Max.max 4 do
    throwError "original local geometry: source threshold is not its native max"
  let args := threshold.getAppArgs
  let currentS := mkAppN (mkConst (current ++ `S)) fixed
  unless ← isDefEq args[2]! currentS do
    throwError "original local geometry: source max lost SAME current threshold"
  let reachedName := ns ++ `current_reached
  let isInitial := !(← getEnv).contains reachedName
  let reached ← if isInitial then do
      let h ← mkAppM `le_trans #[← mkAppM `le_max_left #[args[2]!,args[3]!],s[40]!]
      store reachedName s h
    else pure (mkAppN (mkConst reachedName) s)
  let selected := fixed ++ #[s[39]!,reached] ++ s[41:45].toArray ++ #[s[34]!]
  -- Follow only the original getter definitions. This is the same retained36
  -- extraction as in OriginalComparisonCurrent, now also checking Φ and Y.
  let retained (field : Name) : MetaM (Array Expr) := do
    let head := `JanetCartan.PhysicalPrimary.LeadingCell ++ field
    let mut e := mkAppN (mkConst (current ++ field)) selected
    for _ in [:4] do
      if e.getAppFn.isConstOf head then break
      let some body := (← getConstInfo e.getAppFn.constName!).value? |
        throwError "original local geometry: current getter lost its native body"
      e := body.beta e.getAppArgs
    unless e.isAppOfArity head 36 do throwError "original local geometry: expected native retained36 for {field}"
    return e.getAppArgs
  let ca ← retained `current
  let datum := ca[34]!
  let nativeCell := ca[35]!
  unless datum.isAppOf (leading ++ `AtPatch.fact0) && (← isDefEq datum.appArg! patch) && (← isDefEq nativeCell cell) do
    throwError "original local geometry: current is not the source's SAME selected AtPatch/cell"
  let dataType ← inferType datum
  unless dataType.isAppOfArity `JanetCartan.PhysicalPrimary.RetainedLeadingData 34 do
    throwError "original local geometry: SAME retained leading datum changed"
  let dataArgs := ca[:34].toArray
  unless dataType.getAppArgs == dataArgs do throwError "original local geometry: changed primitive datum arguments"
  if isInitial then
    for field in #[`Φ,`Y] do
      unless (← retained field) == ca do throwError "original source/current/flow have different native retained arguments at {field}"
    discard <| store (ns ++ `leading_data) s datum
  return {fixed,selected,patch,cell,datum,dataArgs,reached}

/-- The common smoothing chart is the native χ₂ plateau and is contained in
the SAME source chart. All objects have the unchanged original23 input spine. -/
elab "retain_original_local_cutoff_geometry" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (smoothing ++ `Dsmooth)).type (some 23) fun family _ => do
    unless family.size == 23 do throwError "original local cutoff: expected original23"
    let n := mkApp (mkConst ``Nat.succ) family[0]!
    let D := mkAppN (mkConst (smoothing ++ `Dsmooth)) family
    let X := mkAppN (mkConst `JanetCartan.LocalDomain.chart) #[D,n]
    let χ := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalRegular.χ₂) family
    let hf := mkAppN (mkConst (masks ++ `χ₂_smooth)) family
    let χfun := (← inferType hf).appArg!
    let support ← mkAppM `tsupport #[χfun]
    let hinner ← mkAppM (ns ++ `inner_ball_subset_tsupport) #[χ]
    let target ← mkAppM `Set.Subset #[X,support]
    let hinner ← store (ns ++ `smoothing_chart_in_source_support) family hinner false (some target)
    let hsource := mkAppN (mkConst (masks ++ `χ₂_support_chart)) family
    discard <| store (ns ++ `smoothing_chart_in_source_chart) family
      (← mkAppM `Set.Subset.trans #[hinner,hsource])
    discard <| store (ns ++ `same_core) family
      (mkAppN (mkConst (smoothing ++ `core_eq)) family)

/-- Project one literal clause of the SAME native current. Keep its native
open set, instead of normalizing that large dependent set again. -/
elab "retain_original_local_current_geometry " which:num : command => liftTermElabM do
  withSourcePrefix 53 fun s => do
    let a ← sourceCurrent s
    let j := which.getNat
    if j == 0 then
      logInfo "retained the literal native source/current threshold, AtPatch datum, cell and both actual flow getters"
    else if j ≤ 4 then
      let geometry := mkAppN (mkConst (current ++ `geometry)) a.selected
      let key := #[`current_open,`current_space,`current_phase,`current_cell][j-1]!
      discard <| store (ns ++ key) s (component geometry (j-1))
      logInfo m!"checked native original current clause {key}"
    else
      let cellParams := s[:23].toArray ++ #[a.patch,a.cell]
      if j == 5 then
        let hproduct := mkAppN (mkConst (masks ++ `product_in_comparison_cell)) cellParams
        let cell := mkAppN (mkConst (ns ++ `current_cell)) s
        let through ← forallBoundedTelescope (← inferType hproduct) (some 2) fun v _ => do
          unless v.size == 2 do throwError "original product: missing point and membership"
          mkLambdaFVars v (mkAppN cell #[v[0]!,mkAppN hproduct v])
        discard <| store (ns ++ `source_product_in_current) s through
      else if j == 6 then
        discard <| store (ns ++ `parameter_window) s
          (mkAppN (mkConst (masks ++ `V)) cellParams) true
        discard <| store (ns ++ `parameter_window_open) s
          (mkAppN (mkConst (masks ++ `V_open)) cellParams)
      else throwError "unknown original current clause"

/-- Apply original positive outer support to the very same selected cell. -/
elab "retain_original_local_outer_geometry" : command => liftTermElabM do
  withSourcePrefix 53 fun s => do
    let a ← sourceCurrent s
    let n := a.fixed[0]!
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[n,s[1]!,s[20]!]
    let native := a.fixed[:21].toArray.set! 20 capped
    let outer (field : Name) := mkAppN
      (mkConst (`JanetCartan.PhysicalBackground.OriginalOuterCutoff ++ field)) (native.push s[34]!)
    let χ := outer `χ
    let hOriginal := outer `support_original
    let hParameter ← forallBoundedTelescope (← inferType hOriginal) (some 2) fun p _ => do
      unless p.size == 2 do throwError "original outer geometry: expected supported carrier"
      let h ← mkAppM (ns ++ `outer_carrier_in_parameter_window)
        #[s[1]!,a.patch,a.cell,p[0]!,mkAppN hOriginal p]
      mkLambdaFVars p h
    discard <| store (ns ++ `outer_cutoff) s χ true
    discard <| store (ns ++ `outer_support_signed) s (outer `support_signed)
    discard <| store (ns ++ `outer_parameter_window) s hParameter
    discard <| store (ns ++ `outer_weight_parameter) s
      (← mkAppM (ns ++ `outer_weight_parameter_window) #[a.dataArgs[4]!,χ,hParameter])
    let hClosed ← forallBoundedTelescope (← inferType hOriginal) (some 2) fun pp _ => do
      let h ← mkAppM (ns ++ `outer_carrier_in_closed_cell)
        #[s[1]!,a.patch,a.cell,pp[0]!,mkAppN hOriginal pp]
      mkLambdaFVars pp h
    let closed ← mkAppM (ns ++ `outer_weight_parameter_window) #[a.dataArgs[4]!,χ,hClosed]
    let closed ← store (ns ++ `outer_weight_closed_cell) s closed
    let θspec := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.parameterCutoff_spec)
      #[n,s[1]!,a.patch,a.cell]
    let germ : Expr := .proj ``And 1 (.proj ``And 1 (.proj ``And 1 θspec))
    let value ← forallBoundedTelescope (← inferType closed) (some 5) fun sample _ => do
      let q := mkAppN closed sample
      let mem ← Core.betaReduce (← zetaReduce (← inferType q))
      unless mem.isAppOfArity ``Membership.mem 5 do
        throwError "actual outer baseline lacks small closed carrier cell"
      mkLambdaFVars sample (mkAppN germ #[mem.getAppArgs[4]!,q])
    discard <| store (ns ++ `outer_weight_θ_germ) s value
  logInfo "actual original53 local geometry: native current/AtPatch/cell, existing source max, source chart times SAME doubled window inside current O; original23 Dsmooth chart inside original chi2 support, SAME core D; actual74 outer support gives SAME active-node parameter window, no baseline zero claim"

end JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
end
