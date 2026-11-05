module

public meta import Lean

/-!
# Applying cached scalar budgets to the actual original histories

Each command checks one named step at the unchanged per-command resource
limit. Row constants precede histories; every analytic current-map and phase
input comes from the SAME original source, not an extra premise. The final
continuation preserves the literal finite-rate scalar kernels and native
normalization (`app:ch_waves:thm:sampling`, `new:eq:amplitude-test`).
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalScalarBoundsApplication
open Lean Meta Elab Command

private def target : Name := `JanetCartan.PhysicalSampling.OriginalScalarHistory

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
    throwError "actual scalar application: open or recovered declaration {name}"
  if ← isProp type then
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  else
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe})
      (forceExpose := true)
  logInfo m!"checked actual scalar history application {name}"
  return mkAppN (mkConst name) params

private def field (proof : Expr) (index : Nat) : MetaM Expr := do
  let mut proof := proof
  for _ in [:index] do proof := .proj ``And 1 proof
  if (← whnf (← inferType proof)).isAppOfArity ``And 2 then pure (.proj ``And 0 proof)
  else pure proof

private def patchOf (i : Expr) (patchType : Expr) : MetaM Expr := do
  let q ← mkAppM ``Subtype.val #[← mkAppM ``Sigma.fst #[i]]
  let qv ← mkAppM ``Subtype.val #[q]
  let chart ← mkAppM ``Prod.fst #[qv]
  let patchNumber ← mkAppM ``Sigma.snd #[i]
  let patchType ← whnf patchType
  unless patchType.isAppOfArity ``Sigma 2 do
    throwError "actual scalar application: expected original patch type"
  return mkAppN (mkConst ``Sigma.mk [.zero, .zero]) (patchType.getAppArgs ++ #[chart, patchNumber])

private def withBudgets
    (k : Array Expr → Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  let source := `JanetCartan.PhysicalSampling.OriginalPhaseMargins.raw_frame_margin
  forallBoundedTelescope (← getConstInfo source).type (some 36) fun xs _ => do
    unless xs.size == 36 do throwError "actual scalar application: expected original prehistory prefix"
    let fixed := xs[:26].toArray ++ xs[27:].toArray
    let Spartial := mkAppN (mkConst (target ++ `S)) fixed
    forallBoundedTelescope (← inferType Spartial) (some 1) fun reserve _ => do
      unless reserve.size == 1 do throwError "actual scalar application: missing fixed derivative reserve"
      let index := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalWeights.Index)
        xs[:22].toArray
      k xs reserve (fixed ++ reserve) index

private def withRow (k : Array Expr → Expr → MetaM Unit) : MetaM Unit :=
  withBudgets fun xs _ params index => do
    let samplingType := (← getConstInfo `JanetCartan.PhysicalSampling.samplingCappedExtra).type
    let n := (samplingType.bindingBody!.instantiate1 xs[0]!).bindingDomain!.appArg!
    let geometry := mkAppN
      (mkConst `JanetCartan.PhysicalSampling.original_scalar_coefficient_ball) #[n, xs[1]!]
    let hK ← field geometry 0
    let hKU ← field geometry 1
    let state ← field geometry 2
    let positiveNumeral (name : Name) := do
      let arity := (← getConstInfo name).type.getForallArity
      mkAppOptM name (#[some (mkConst `Real)] ++ Array.replicate (arity - 1) none)
    let hquarter ← mkAppM `div_pos
      #[← positiveNumeral `zero_lt_one', ← positiveNumeral `zero_lt_four']
    let quarter := (← inferType hquarter).appArg!
    let get (name : Name) := mkAppN (mkConst (target ++ `History ++ name)) params
    withLocalDeclD `i index fun i => do
      let patch ← patchOf i (← whnf (← inferType state)).bindingDomain!
      let hstate := mkApp state patch
      let K := (← inferType hstate).appArg!
      let scalar := mkAppN
        (mkConst `JanetCartan.PhysicalSampling.OriginalAdmission.scalar_on_actual_selected_row)
        (xs[:22].toArray.push i)
      k (params.push i) (mkAppN scalar
        #[K, hK, hKU, hstate, get `M, quarter, get `κ, hquarter, get `hκ, xs[2]!])

/-- Retain one sharp/mean constant or positivity fact before any history. -/
elab "cache_original_scalar_row_field " which:num : command =>
    liftTermElabM <| withTransparency .reducible do
  let index := which.getNat
  let names : Array Name := #[`Csharp, `Cmean, `hCsharp, `hCmean]
  unless index < names.size do throwError "actual scalar application: invalid field index"
  withRow fun params initial => do
    let ns := target ++ `Row
    let proof := if index == 0 then initial else mkAppN (mkConst (ns.str s!"spec{index}")) params
    let type ← whnf (← inferType proof)
    let tail ← if type.isAppOfArity ``Exists 2 then do
      let witness ← store (ns ++ names[index]!) params (← mkAppM ``Classical.choose #[proof])
      store (ns.str s!"spec{index + 1}") params (← mkAppM ``Classical.choose_spec #[proof])
        (some (type.appArg!.beta #[witness]))
    else if type.isAppOfArity ``And 2 then do
      discard <| store (ns ++ names[index]!) params (.proj ``And 0 proof)
      store (ns.str s!"spec{index + 1}") params (.proj ``And 1 proof)
    else throwError "actual scalar application: unexpected prefix at {names[index]!}"
    if index == names.size - 1 then
      discard <| store (ns ++ `continuation) params tail

private def withReached
    (k : Array Expr → Array Expr → Array Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit :=
  withBudgets fun xs reserve params index => do
    let S := mkAppN (mkConst (target ++ `S)) params
    withLocalDeclD `R₀ (mkConst `Real) fun R₀ => do
      withLocalDeclD `hR₀ (← mkAppM ``LE.le #[S, R₀]) fun hR₀ => do
        k xs reserve (params ++ #[R₀, hR₀]) index R₀ hR₀

/-- The same maximum threshold reaches both existing producers. -/
elab "cache_original_scalar_reached_thresholds" : command =>
    liftTermElabM <| withTransparency .reducible <| withReached fun xs _ current _ _ hR₀ => do
  let fixed := xs[:26].toArray ++ xs[27:].toArray
  let params := current[:current.size - 2].toArray
  let Sgraph := mkAppN (mkConst (target ++ `Sgraph)) fixed
  let Sgeom := mkAppN (mkConst (target ++ `History.S)) params
  discard <| store (target ++ `graph_reached) current (← mkAppM `le_trans
    #[← mkAppM `le_max_left #[Sgraph, Sgeom], hR₀])
  discard <| store (target ++ `geometry_reached) current (← mkAppM `le_trans
    #[← mkAppM `le_max_right #[Sgraph, Sgeom], hR₀])

private def withHistory
    (k : Array Expr → Array Expr → Array Expr → Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit :=
  withReached fun xs reserve current index R₀ _ => do
    let params := current[:current.size - 2].toArray
    let hgeom := mkAppN (mkConst (target ++ `geometry_reached)) current
    let history := mkAppN (mkConst (target ++ `History.continuation)) (params ++ #[R₀, hgeom])
    forallBoundedTelescope (← inferType history) (some 4) fun data _ => do
      unless data.size == 4 do throwError "actual scalar application: expected the actual Schwartz history"
      k xs reserve current data index (mkAppN history data)

/-- Produce all scalar map/gap inputs from the actual admissible Schwartz history. -/
elab "cache_original_scalar_current_inputs" : command =>
    liftTermElabM <| withTransparency .reducible <| withHistory fun _ _ current data _ proof => do
  discard <| store (target ++ `current_inputs) (current ++ data) proof

/-- Close the full sharp/mean continuation on the SAME current and source. -/
elab "realize_original_scalar_physical_history" : command =>
    liftTermElabM <| withTransparency .reducible <| withHistory fun xs reserve current data index _ => do
  let params := current[:current.size - 2].toArray
  let R₀ := current[current.size - 2]!
  let hR₀ := current[current.size - 1]!
  let hgraph := mkAppN (mkConst (target ++ `graph_reached)) current
  let inputs := mkAppN (mkConst (target ++ `current_inputs)) (current ++ data)
  let hF ← field inputs 0
  let F := (← inferType hF).appFn!.appArg!
  withLocalDeclD `i index fun i => do
    let small := mkAppN
      (mkConst `JanetCartan.PhysicalSampling.OriginalPhaseMargins.all_four_phase_margins)
      (xs ++ #[R₀, hgraph] ++ data ++ #[i])
    let scalar := mkAppN (mkConst (target ++ `Row.continuation)) (params.push i)
    let result := mkAppN scalar #[F, hF, ← field inputs 1, ← field inputs 2,
      ← field inputs 3, ← field inputs 4, ← field inputs 5, ← field small 0]
    discard <| store (target ++ `current_bounds)
      (xs ++ reserve ++ #[R₀, hR₀] ++ data ++ #[i]) result
  logInfo "all scalar map, gap and phase inputs proved on SAME original source/current"

end JanetCartan.PhysicalSampling.OriginalScalarBoundsApplication
