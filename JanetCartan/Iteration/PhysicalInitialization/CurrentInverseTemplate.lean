module

public meta import Lean

/-!
# Native same-source current inverse from actual leading cells

Safe, kernel-checked specialization of the actual `StrongCurrent` theorem.
Choose the leading and inverse constants before the history, combine their two
thresholds, and apply the three leading inputs already proved for the actual
selected cells. No leading chart, norm, compatibility, or solution hypothesis
survives. Consumer: the same-source raw-continuity and positive-background joins.
-/

public meta section
namespace JanetCartan.PhysicalInitialization.CurrentInverseTemplate
open Lean Meta Elab Command

private def addDef (name : Name) (params : Array Expr) (value : Expr) : MetaM Expr := do
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← inferType value)
  if value.hasMVar || type.hasMVar || value.hasFVar || type.hasFVar || value.hasSorry || type.hasSorry then
    throwError "actual current inverse: incomplete definition {name}"
  addDecl (.defnDecl {
    name, levelParams := [], type, value,
    hints := .abbrev, safety := .safe }) (forceExpose := true)
  return mkAppN (mkConst name) params

private def addThm (name : Name) (params : Array Expr) (value : Expr)
    (target : Option Expr := none) : MetaM Expr := do
  let rawType ← inferType value
  let resultType := target.getD rawType
  unless ← isDefEq resultType rawType do
    throwError "actual current inverse: theorem target mismatch {name}"
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← mkForallFVars params resultType)
  if value.hasMVar || type.hasMVar || value.hasFVar || type.hasFVar || value.hasSorry || type.hasSorry then
    throwError "actual current inverse: incomplete theorem {name}"
  addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
  return mkAppN (mkConst name) params

private partial def cache (base : Name) (params : Array Expr) (proof : Expr)
    (index : Nat := 0) : MetaM Unit := do
  let raw ← inferType proof
  if let .letE name _ value body _ := raw then
    let value ← addDef (base ++ name) params value
    let next ← addThm (base ++ Name.mkSimple s!"afterLet_{name}") params proof
      (some (body.instantiate1 value))
    cache base params next index
  else
    let type ← whnf raw
    if type.isAppOfArity ``Exists 2 then
      let .lam name _ body _ := type.appArg! | throwError "expected native current witness"
      let witness ← addDef (base ++ name) params (← mkAppM ``Classical.choose #[proof])
      let next ← addThm (base ++ Name.mkSimple s!"afterChoice_{name}") params
        (← mkAppM ``Classical.choose_spec #[proof]) (some (body.instantiate1 witness))
      cache base params next index
    else if type.isAppOfArity ``And 2 then
      discard <| addThm (base ++ Name.mkSimple s!"fact{index}") params (.proj ``And 0 proof)
      let next ← addThm (base ++ Name.mkSimple s!"afterFact{index}") params (.proj ``And 1 proof)
      cache base params next (index+1)
    else
      discard <| addThm (base ++ `continuation) params proof

/-- Fix every native inverse budget before any physical history. The inverse's
shift14 budget is the actual leading `E`, and shift13 is `B` on the selected cell. -/
elab "cache_original_current_inverse_budgets" : command => liftTermElabM do
  let leading := `JanetCartan.PhysicalInitialization.CurrentLeading
  let root := `JanetCartan.PhysicalInitialization.OriginalCurrent
  let source := `JanetCartan.PhysicalNormalInverse.StrongCurrent.source_continuation
  let selectedNS := `JanetCartan.PhysicalSeed.SelectedBoundary
  let info ← getConstInfo (leading ++ `initialized)
  forallBoundedTelescope info.type (some 31) fun params _ => do
    unless params.size == 31 do throwError "original current: expected original30 plus numerical leading tolerance"
    let source := mkAppN (mkConst source) params[:30].toArray
    let .forallE _ budgetType _ _ ← whnf (← inferType source)
      | throwError "original current: expected native leading budget"
    let original := params[:21].toArray
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[original[0]!, original[1]!, original[20]!]
    let selected := original.set! 20 capped
    let (bFull, bNull, hFull) ← forallBoundedTelescope budgetType (some 1) fun indices _ => do
      let i := indices[0]!
      let center ← mkAppM ``Sigma.fst #[i]
      let incidence ← mkAppM ``Subtype.val #[center]
      let incidencePair ← mkAppM ``Subtype.val #[incidence]
      let chart ← mkAppM ``Prod.fst #[incidencePair]
      let patchNumber ← mkAppM ``Sigma.snd #[i]
      let E := mkAppN (mkConst (leading ++ `E)) params
      let .forallE _ patchType _ _ ← whnf (← inferType E)
        | throwError "original current: expected original leading patch"
      let patchType ← whnf patchType
      let patch ← mkAppOptM ``Sigma.mk
        #[some patchType.appFn!.appArg!, some patchType.appArg!, some chart, some patchNumber]
      let cell := mkAppN (mkConst (selectedNS ++ `cell)) (selected ++ #[incidence, patchNumber])
      let bFull ← addDef (root ++ `Bfull) params (← mkLambdaFVars indices (mkApp E patch))
      let bNull ← addDef (root ++ `Bnull) params (← mkLambdaFVars indices
        (mkAppN (mkConst (leading ++ `B)) (params ++ #[patch, cell])))
      let hFull ← addThm (root ++ `hBfull) params (← mkLambdaFVars indices
        (mkAppN (mkConst (leading ++ `fact3)) (params ++ #[patch])))
      return (bFull, bNull, hFull)
    let proof ← addThm (root ++ `native_initialized) params (mkAppN source #[bFull,bNull,hFull])
    cache (root ++ `Native) params proof
    for field in #[`Cinv, `Cadj, `Cpair, `Czero] do
      discard <| addDef (root ++ field) params (mkAppN (mkConst (root ++ `Native ++ field)) params)
    for index in [:4] do
      discard <| addThm (root ++ Name.mkSimple s!"nonnegative{index}") params
        (mkAppN (mkConst (root ++ `Native ++ Name.mkSimple s!"fact{index}")) params)
    let Snative := mkAppN (mkConst (root ++ `Native.S)) params
    let Sleading := mkAppN (mkConst (leading ++ `threshold)) params
    let S ← addDef (root ++ `S) params (← mkAppM ``Max.max #[Snative,Sleading])
    let hLeft ← mkAppM `le_max_left #[Snative,Sleading]
    let hRight ← mkAppM `le_max_right #[Snative,Sleading]
    unless ← isDefEq (← inferType hLeft).appArg! S do throwError "original current: threshold identification"
    discard <| addThm (root ++ `native_threshold_le) params hLeft
    discard <| addThm (root ++ `leading_threshold_le) params hRight
    discard <| addThm (root ++ `hS) params (← mkAppM `le_trans
      #[mkAppN (mkConst (root ++ `Native.fact4)) params,hLeft])
  logInfo "kernel-checked all native inverse constants before history using actual shift13 B and shift14 E"

/-- Consume the actual leading cells, all seven geometry clauses, literal
compatibility and solution estimates. All density/native regularity remains
unmodified in the returned continuation. -/
elab "apply_original_current_inverse_leading" : command => liftTermElabM do
  let leading := `JanetCartan.PhysicalInitialization.CurrentLeading
  let root := `JanetCartan.PhysicalInitialization.OriginalCurrent
  let info ← getConstInfo (root ++ `Native.continuation)
  forallBoundedTelescope info.type (some 31) fun params type => do
    let S := mkAppN (mkConst (root ++ `S)) params
    let .forallE name realType _ _ ← whnf type | throwError "original current: expected history frequency"
    withLocalDeclD name realType fun R => do
      let hLeType ← mkAppM ``LE.le #[S,R]
      withLocalDeclD `hR hLeType fun hR => do
        let hNative ← mkAppM `le_trans
          #[mkAppN (mkConst (root ++ `native_threshold_le)) params,hR]
        let hLeading ← mkAppM `le_trans
          #[mkAppN (mkConst (root ++ `leading_threshold_le)) params,hR]
        let native := mkAppN (mkConst (root ++ `Native.continuation)) (params ++ #[R,hNative])
        forallBoundedTelescope (← inferType native) (some 4) fun history _ => do
          unless history.size == 4 do throwError "original current: expected stage/history/orders/admissibility"
          let leadingParams := params ++ #[R,hLeading] ++ history
          let publicParams := params ++ #[R,hR] ++ history
          let mut inputs := #[]
          for field in #[`current, `Φ, `Y, `O, `Vcomp] do
            let value := mkAppN (mkConst (leading ++ `Selected ++ field)) leadingParams
            let value ← addDef (root ++ field) publicParams value
            inputs := inputs.push value
          for field in #[`geometry, `compatible, `solution] do
            let value := mkAppN (mkConst (leading ++ `Selected ++ field)) leadingParams
            let value ← addThm (root ++ field) publicParams value
            inputs := inputs.push value
          let proof := mkAppN (mkAppN native history) inputs
          discard <| addThm (root ++ `continuation) publicParams proof
  logInfo "kernel-checked actual original current inverse; no chart, leading geometry, compatibility or solution premise"

end JanetCartan.PhysicalInitialization.CurrentInverseTemplate
