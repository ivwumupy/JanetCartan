module

public meta import Lean

/-!
Incremental replacement for the scalar numerical application. Each command
checks only one reference/choice/threshold step at the ORIGINAL per-command
heartbeat budget. Every datum is still extracted from the same earlier proof;
no source, gap, history, or analytic-success input is added.
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalScalarHistoryApplication
open Lean Meta Elab Command

private def target : Name := `JanetCartan.PhysicalSampling.OriginalScalarHistory
private def regular : Name := `JanetCartan.PhysicalInitialization.OriginalRegular

private def store (name : Name) (params : Array Expr) (value : Expr)
    (expected : Option Expr := none) : MetaM Expr := do
  let rawType ← match expected with
    | some type => pure type
    | none => inferType value
  let type ← instantiateMVars rawType
  let value ← instantiateMVars value
  let type ← mkForallFVars params type
  let value ← mkLambdaFVars params value
  if type.hasMVar || value.hasMVar || type.hasSorry || value.hasSorry ||
      type.hasFVar || value.hasFVar then
    throwError "actual scalar budgets: open or recovered declaration {name}"
  if ← isProp type then
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  else
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe})
      (forceExpose := true)
  logInfo m!"checked actual scalar numerical source {name}"
  return mkAppN (mkConst name) params

private def withBefore (k : Array Expr → MetaM Unit) : MetaM Unit := do
  let source := `JanetCartan.PhysicalSampling.OriginalPhaseMargins.raw_frame_margin
  forallBoundedTelescope (← getConstInfo source).type (some 36) fun xs _ => do
    unless xs.size == 36 do throwError "actual scalar budgets: expected original prehistory prefix"
    k xs

private def originalArgs (xs : Array Expr) : Array Expr :=
  let merged := mkAppN (mkConst `JanetCartan.PhysicalSampling.samplingCappedExtra)
    #[xs[0]!, xs[1]!, xs[2]!, xs[21]!]
  (xs[:2].toArray ++ xs[3:24].toArray).set! 20 merged

private def referenceArgs (xs : Array Expr) : Array Expr :=
  xs[:26].toArray ++ xs[27:29].toArray

private def xsReserve (xs : Array Expr) : Array Expr :=
  xs[:26].toArray ++ xs[27:].toArray

private def withBudget (k : Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit :=
  withBefore fun xs => do
    let G := mkAppN (mkConst (target ++ `Gref)) (referenceArgs xs)
    let n := (← inferType G).appArg!
    let orig (name : Name) := mkAppN
      (mkConst (`JanetCartan.PhysicalSeed.OriginalBoundary ++ name)) #[n, xs[1]!]
    let hR := mkAppN (mkConst (target ++ `radius_lt_chartRadius)) (referenceArgs xs)
    let budgetPrefix := mkAppN
      (mkConst `JanetCartan.PhysicalSampling.exists_scalar_physical_history_budgets)
      #[n, G, orig `b, orig `R, orig `b_pos, orig `b_lt_R, hR,
        xs[29]!, xs[30]!, xs[31]!, xs[32]!]
    forallBoundedTelescope (← inferType budgetPrefix) (some 1) fun reserve _ => do
      unless reserve.size == 1 do throwError "actual scalar budgets: missing fixed derivative reserve"
      k xs (xsReserve xs ++ reserve) (mkAppN budgetPrefix #[reserve[0]!, xs[35]!])

/-- Cache the exact original Gref and its unchanged coefficient-domain certificate. -/
elab "cache_original_scalar_reference" : command =>
    liftTermElabM <| withTransparency .reducible <| withBefore fun xs => do
  let original := originalArgs xs
  let scale := xs[27:29].toArray
  let graphFixed := original ++ xs[24:26].toArray
  let regScale := mkAppN (mkConst (regular ++ `Graph.regular_scale)) (graphFixed ++ scale)
  let refParams := original ++ #[scale[0]!, regScale]
  let G ← store (target ++ `Gref) (referenceArgs xs)
    (mkAppN (mkConst (regular ++ `Gref)) refParams)
  let n := (← inferType G).appArg!
  let sourceArgs := #[n] ++ original[1:21].toArray
  let hR ← withTransparency .default <| mkAppOptM (regular ++ `radius_lt_same_chart)
    #[some n, some G, none, none,
      some (mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5) sourceArgs[:18].toArray),
      some (mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.R_lt_chartRadius)
        #[n, xs[1]!])]
  discard <| store (target ++ `radius_lt_chartRadius) (referenceArgs xs) hR

/-- Extract exactly one successive field of the SAME retained scalar budget proof. -/
elab "cache_original_scalar_budget_field " which:num : command =>
    liftTermElabM <| withTransparency .reducible do
  let index := which.getNat
  let names : Array Name := #[`S, `hS, `M, `hM, `κ, `hκ]
  unless index < names.size do throwError "actual scalar budgets: invalid field index"
  withBudget fun _ params initial => do
    let ns := target ++ `History
    let proof := if index == 0 then initial else mkAppN (mkConst (ns.str s!"spec{index}")) params
    let type ← whnf (← inferType proof)
    let tail ← if type.isAppOfArity ``Exists 2 then do
      let witness ← store (ns ++ names[index]!) params (← mkAppM ``Classical.choose #[proof])
      store (ns.str s!"spec{index + 1}") params (← mkAppM ``Classical.choose_spec #[proof])
        (some (type.appArg!.beta #[witness]))
    else if type.isAppOfArity ``And 2 then do
      discard <| store (ns ++ names[index]!) params (.proj ``And 0 proof)
      store (ns.str s!"spec{index + 1}") params (.proj ``And 1 proof)
    else throwError "actual scalar budgets: unexpected prefix at {names[index]!}"
    if index == names.size - 1 then
      discard <| store (ns ++ `continuation) params tail

/-- Name the actual existing graph threshold, without another graph choice. -/
elab "cache_original_scalar_graph_threshold" : command =>
    liftTermElabM <| withTransparency .reducible <| withBefore fun xs => do
  let graph := originalArgs xs ++ xs[24:26].toArray ++ xs[27:].toArray
  let params := xsReserve xs
  discard <| store (target ++ `Sgraph) params (mkAppN (mkConst (regular ++ `Graph.S)) graph)
  discard <| store (target ++ `hSgraph) params (mkAppN (mkConst (regular ++ `Graph.hS)) graph)

/-- Take the common maximum of the exact graph and scalar history thresholds. -/
elab "cache_original_scalar_common_threshold" : command =>
    liftTermElabM <| withTransparency .reducible <| withBudget fun xs params _ => do
  let Sgraph := mkAppN (mkConst (target ++ `Sgraph)) (xsReserve xs)
  let hSgraph := mkAppN (mkConst (target ++ `hSgraph)) (xsReserve xs)
  let Sgeom := mkAppN (mkConst (target ++ `History.S)) params
  discard <| store (target ++ `S) params (← mkAppM ``Max.max #[Sgraph, Sgeom])
  discard <| store (target ++ `hS) params (← mkAppM `le_trans
    #[hSgraph, ← mkAppM `le_max_left #[Sgraph, Sgeom]])

end JanetCartan.PhysicalSampling.OriginalScalarHistoryApplication
