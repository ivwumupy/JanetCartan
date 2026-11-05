module

public meta import Lean

/-!
# Select actual supplied-source leading budgets before the physical history

Apply `SuppliedLeading` to the scalar cap of the SAME `StrongCurrent` callback.
Every generated declaration is safe and kernel checked. In particular, no
leading datum, frame bound, or successful inverse is added as a hypothesis.
Consumer: the actual original current-inverse application in task17.
-/

public meta section
namespace JanetCartan.PhysicalInitialization.CurrentLeadingTemplate
open Lean Meta Elab Command

private def addDef (name : Name) (params : Array Expr) (value : Expr) : MetaM Expr := do
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← inferType value)
  if value.hasMVar || type.hasMVar || value.hasFVar || type.hasFVar || value.hasSorry || type.hasSorry then
    throwError "actual current leading: incomplete definition {name}"
  addDecl (.defnDecl {
    name, levelParams := [], type, value,
    hints := .abbrev, safety := .safe }) (forceExpose := true)
  return mkAppN (mkConst name) params

private def addThm (name : Name) (params : Array Expr) (value : Expr)
    (target : Option Expr := none) : MetaM Expr := do
  let rawType ← inferType value
  let resultType := target.getD rawType
  unless ← isDefEq resultType rawType do
    throwError "actual current leading: theorem target mismatch {name}"
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← mkForallFVars params resultType)
  if value.hasMVar || type.hasMVar || value.hasFVar || type.hasFVar || value.hasSorry || type.hasSorry then
    throwError "actual current leading: incomplete theorem {name}"
  addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
  return mkAppN (mkConst name) params

private partial def cache (base : Name) (params : Array Expr) (proof : Expr)
    (index : Nat := 0) : MetaM Unit := do
  let raw ← inferType proof
  if let .letE name _ value body _ := raw then
    let value ← addDef (base ++ name) params value
    let nextType := body.instantiate1 value
    unless ← isDefEq nextType (← inferType proof) do
      throwError "actual current leading: let identification failed"
    let next ← addThm (base ++ Name.mkSimple s!"afterLet_{name}") params proof (some nextType)
    cache base params next index
  else
    let type ← whnf raw
    if type.isAppOfArity ``Exists 2 then
      let .lam name _ body _ := type.appArg! | throwError "expected original leading witness"
      let witness ← addDef (base ++ name) params (← mkAppM ``Classical.choose #[proof])
      let next ← addThm (base ++ Name.mkSimple s!"afterChoice_{name}") params
        (← mkAppM ``Classical.choose_spec #[proof]) (some (body.instantiate1 witness))
      cache base params next index
    else if type.isAppOfArity ``And 2 then
      discard <| addThm (base ++ Name.mkSimple s!"fact{index}") params
        (← mkAppM ``And.left #[proof])
      let next ← addThm (base ++ Name.mkSimple s!"afterFact{index}") params
        (← mkAppM ``And.right #[proof])
      cache base params next (index+1)
    else
      discard <| addThm (base ++ `continuation) params proof

/-- Fix the actual budgets and same-history leading witnesses using the original
reference prefix and exactly its already-selected current inverse scalar cap. -/
elab "cache_actual_current_leading" : command => liftTermElabM do
  let current := `JanetCartan.PhysicalNormalInverse.StrongCurrent.source_continuation
  let source := `JanetCartan.PhysicalInitialization.exists_supplied_original_retained_physical_leading
  let capNS := `JanetCartan.PhysicalNormalInverse.StrongCurrent.Cap
  let root := `JanetCartan.PhysicalInitialization.CurrentLeading
  let info ← getConstInfo current
  forallBoundedTelescope info.type (some 30) fun fixed _ => do
    unless fixed.size == 30 do throwError "actual current leading: expected original30"
    let original := fixed[:21].toArray
    let sourceAtReference := mkAppN (mkConst source) fixed[:18].toArray
    forallBoundedTelescope (← inferType sourceAtReference) (some 1) fun tolerance _ => do
      unless tolerance.size == 1 do throwError "actual current leading: expected numerical leading tolerance"
      let n := fixed[0]!
      let sigma := fixed[21]!
      let hSigma ← mkAppM ``And.left #[fixed[22]!]
      let hSigmaCap ← mkAppM ``And.right #[fixed[22]!]
      let hCapOne := mkAppN (mkConst (capNS ++ `fact2)) original
      let hSigmaOne ← mkAppM `le_trans #[hSigmaCap, hCapOne]
      let hCscalar := mkAppN (mkConst (capNS ++ `fact4)) original
      let hSigmaNonneg ← mkAppM `le_of_lt #[hSigma]
      let hCscalarNonneg ← mkAppM `le_of_lt #[hCscalar]
      let hMscalar ← mkAppM `mul_nonneg #[hSigmaNonneg, hCscalarNonneg]
      let Mscalar := (← inferType hMscalar).appArg!
      let hmscalar ← mkAppM
        `JanetCartan.PhysicalInitialization.positive_leading_scalar_lower_bound #[hSigma]
      let mscalar := (← inferType hmscalar).appArg!
      let h14base ← mkAppM
        `JanetCartan.PhysicalInitialization.leading_reserve_le_canonical_low_order #[n]
      let h14 ← mkAppM ``Nat.le_trans #[h14base, fixed[28]!]
      let proof := mkAppN sourceAtReference (tolerance ++
        #[sigma, hSigma, hSigmaOne, fixed[24]!, fixed[25]!, fixed[26]!, fixed[27]!,
          h14, fixed[29]!, Mscalar, mscalar, hMscalar, hmscalar])
      let params := fixed ++ tolerance
      let proof ← addThm (root ++ `initialized) params proof
      cache root params proof
  let continuation := root ++ `continuation
  let info ← getConstInfo continuation
  forallBoundedTelescope info.type (some 37) fun params _ => do
    unless params.size == 37 do throwError "actual current leading: expected fixed31/history6"
    cache (root ++ `History) params (mkAppN (mkConst continuation) params)
  let atPatch := root ++ `History.continuation
  let info ← getConstInfo atPatch
  forallBoundedTelescope info.type (some 38) fun params _ => do
    unless params.size == 38 do throwError "actual current leading: expected fixed31/history6/patch1"
    cache (root ++ `AtPatch) params (mkAppN (mkConst atPatch) params)
  logInfo "kernel-checked actual supplied-source leading and scalar-cap application; budgets precede history"

private def component (proof : Expr) (index : Nat) : MetaM Expr := do
  let mut proof := proof
  for _ in [:index] do proof ← mkAppM ``And.right #[proof]
  let type ← whnf (← inferType proof)
  if type.isAppOfArity ``And 2 then mkAppM ``And.left #[proof] else pure proof

/-- Use the actual nonzero selected carrier cell, never a guessed cell0. The
original comparison/outer-product certificates discharge all geometric inputs. -/
elab "cache_actual_selected_leading" : command => liftTermElabM do
  let root := `JanetCartan.PhysicalInitialization.CurrentLeading
  let selectedNS := `JanetCartan.PhysicalSeed.SelectedBoundary
  let originalNS := `JanetCartan.PhysicalSeed.OriginalBoundary
  let cellNS := `JanetCartan.PhysicalPrimary.LeadingCell
  let atPatch := root ++ `AtPatch.fact0
  let info ← getConstInfo atPatch
  forallBoundedTelescope info.type (some 37) fun params _ => do
    unless params.size == 37 do throwError "selected current leading: expected fixed31/history6"
    let original := params[:21].toArray
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[original[0]!, original[1]!, original[20]!]
    let selected := original.set! 20 capped
    let currentPrefix := mkAppN
      (mkConst `JanetCartan.PhysicalNormalInverse.StrongCurrent.source_continuation) params[:30].toArray
    let .forallE _ budgetType _ _ ← whnf (← inferType currentPrefix)
      | throwError "selected current leading: expected uniform budgets"
    forallBoundedTelescope budgetType (some 1) fun indices _ => do
      unless indices.size == 1 do throwError "selected current leading: expected one carrier index"
      let i := indices[0]!
      let center ← mkAppM ``Sigma.fst #[i]
      let incidence ← mkAppM ``Subtype.val #[center]
      let incidencePair ← mkAppM ``Subtype.val #[incidence]
      let chart ← mkAppM ``Prod.fst #[incidencePair]
      let patchNumber ← mkAppM ``Sigma.snd #[i]
      let dataPrefix := mkAppN (mkConst atPatch) params
      let .forallE _ patchType _ _ ← whnf (← inferType dataPrefix)
        | throwError "selected current leading: expected original patch"
      let patchType ← whnf patchType
      unless patchType.isAppOfArity ``Sigma 2 do throwError "selected current leading: expected patch sigma"
      let patch ← mkAppOptM ``Sigma.mk
        #[some patchType.appFn!.appArg!, some patchType.appArg!, some chart, some patchNumber]
      let cell := mkAppN (mkConst (selectedNS ++ `cell)) (selected ++ #[incidence, patchNumber])
      let data := mkApp dataPrefix patch
      let dataType ← inferType data
      unless dataType.getAppFn.isConstOf `JanetCartan.PhysicalPrimary.RetainedLeadingData do
        throwError "selected current leading: unexpected data type {dataType.getAppFn}"
      let args := dataType.getAppArgs ++ #[data, cell]
      let allParams := params ++ indices
      for field in #[`current, `Φ, `Y] do
        discard <| addDef (root ++ `Selected ++ field) allParams
          (mkAppN (mkConst (cellNS ++ field)) args)
      discard <| addThm (root ++ `Selected.compatible) allParams
        (mkAppN (mkConst (cellNS ++ `compatible)) args)
      discard <| addThm (root ++ `Selected.solution) allParams
        (mkAppN (mkConst (cellNS ++ `solution)) args)
      let originalCell (field : Name) :=
        mkAppN (mkConst (originalNS ++ field)) #[params[0]!, params[1]!, patch, cell]
      let positive := originalCell `comparison_pos
      let hR ← component positive 1
      let hTau ← component positive 2
      let hSigma ← component positive 8
      let hCover ← component (originalCell `comparison_cover) 0
      let hProduct ← component (originalCell `density_product_geometry) 6
      let hCell := originalCell `carrier_cells
      let hGraphBall ← mkAppM `Set.MapsTo.mono_left #[← component hCell 2, hProduct]
      let hCoordinates ← mkAppM `Set.MapsTo.mono_left #[← component hCell 3, hProduct]
      let graphType ← inferType hGraphBall
      unless graphType.isAppOfArity `Set.MapsTo 5 do
        throwError "selected current leading: expected original graph MapsTo"
      let graphArgs := graphType.getAppArgs
      let Eouter := graphArgs[3]!
      let ballArgs := graphArgs[4]!.getAppArgs
      unless graphArgs[4]!.getAppFn.isConstOf `Metric.ball && ballArgs.size == 4 do
        throwError "selected current leading: expected original comparison ball"
      let hClosed ← mkAppOptM `Metric.ball_subset_closedBall
        #[some graphArgs[1]!, none, some ballArgs[2]!, some ballArgs[3]!]
      let hGraph ← mkAppM `Set.MapsTo.mono_right #[hGraphBall, hClosed]
      let hBR := mkAppN (mkConst (originalNS ++ `b_lt_R)) #[params[0]!, params[1]!]
      let Rwork := mkAppN (mkConst (originalNS ++ `R)) #[params[0]!, params[1]!]
      let EuclideanN ← mkAppM `JanetCartan.Euclidean #[params[0]!]
      let physicalK := dataType.getAppArgs[5]!
      let kArgs := physicalK.getAppArgs
      unless physicalK.getAppFn.isConstOf `Metric.closedBall && kArgs.size == 4 do
        throwError "selected current leading: expected actual physical closed ball"
      let hK ← mkAppOptM `Metric.closedBall_subset_ball
        #[some EuclideanN, none, some kArgs[2]!, some kArgs[3]!, some Rwork, some hBR]
      let geometry := mkAppN
        (mkConst `JanetCartan.PhysicalInitialization.retained_leading_inverse_geometry)
        (args ++ #[hR, hTau, hSigma, Rwork, hK, hCover, Eouter, hGraph, hCoordinates])
      let geometry ← addThm (root ++ `Selected.geometry) allParams geometry
      let hOpen ← component geometry 0
      let O := (← inferType hOpen).appArg!
      discard <| addDef (root ++ `Selected.O) allParams O
      let hComp ← component geometry 6
      let Vcomp := (← inferType hComp).appArg!
      discard <| addDef (root ++ `Selected.Vcomp) allParams Vcomp
  logInfo "kernel-checked same selected current/phase/geometry/compatibility/solution; no leading input premise"

end JanetCartan.PhysicalInitialization.CurrentLeadingTemplate
