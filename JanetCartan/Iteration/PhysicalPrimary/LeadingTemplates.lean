module

public meta import Lean

/-!
# Exact retained leading conclusion template

This only names the literal conclusion of the already checked arbitrary-map
callback. It does not select rows, assume an analytic conclusion, or construct
a proof. The ordinary proof in `LeadingHistory` applies that original callback
to the actual revised physical map.
-/

public meta section
namespace JanetCartan.PhysicalPrimary.LeadingTemplates
open Lean Meta Elab Command

private partial def extract (params : Array Expr) (type : Expr) : MetaM Unit := do
  if type.isAppOfArity ``Exists 2 then
    let .lam name domain body _ := type.appArg! | throwError "expected retained witness predicate"
    withLocalDeclD name domain fun witness => extract (params.push witness) (body.instantiate1 witness)
  else if type.isAppOfArity ``And 2 then
    extract params type.appArg!
  else
    forallBoundedTelescope type (some 8) fun current conclusion => do
      unless current.size == 8 && conclusion.isAppOfArity ``Exists 2 do
        throwError "expected original current-map eight inputs and low-frame conclusion"
      let params := params ++ current
      let used := params.filter fun p => conclusion.containsFVar p.fvarId!
      addDecl (.defnDecl {
        name := `JanetCartan.PhysicalPrimary.RetainedLeadingData,
        levelParams := [], type := ← mkForallFVars used (mkSort 0),
        value := ← mkLambdaFVars used conclusion, hints := .abbrev, safety := .safe })
        (forceExpose := true)

/-- Name, without weakening, the exact original same-row leading conclusion. -/
elab "declare_physical_primary_retained_leading_data" : command => liftTermElabM do
  let name := `JanetCartan.PhysicalSeed.GenericLeading
  let info ← getConstInfo name
  unless info.levelParams.isEmpty do throwError "unexpected retained callback universes"
  forallTelescope info.type fun fixed _ => do
    let continuation ← whnf (mkAppN (mkConst name) fixed)
    forallBoundedTelescope continuation (some 10) fun budgets tail => do
      unless budgets.size == 10 do throwError "expected original five budgets and five sign proofs"
      extract (fixed ++ budgets) tail

private def addDef (name : Name) (params : Array Expr) (value : Expr) : MetaM Expr := do
  addDecl (.defnDecl {
    name, levelParams := [], type := ← mkForallFVars params (← inferType value),
    value := ← mkLambdaFVars params value, hints := .abbrev, safety := .safe }) (forceExpose := true)
  return mkAppN (mkConst name) params

private def addThm (name : Name) (params : Array Expr) (type value : Expr) : MetaM Expr := do
  unless ← isDefEq type (← inferType value) do throwError "retained leading proof type mismatch: {name}"
  addDecl (.thmDecl {
    name, levelParams := [], type := ← mkForallFVars params type,
    value := ← mkLambdaFVars params value }) (forceExpose := true)
  return mkAppN (mkConst name) params

private partial def cache (base : Name) (params : Array Expr) (proof : Expr)
    (index : Nat := 0) : MetaM Unit := do
  let raw ← inferType proof
  if let .letE name _ value body _ := raw then
    let value ← addDef (base ++ name) params value
    let next ← addThm (base ++ Name.mkSimple s!"afterLet_{name}") params
      (body.instantiate1 value) proof
    cache base params next index
  else
    let type ← whnf raw
    if type.isAppOfArity ``Exists 2 then
      let .lam name _ body _ := type.appArg! | throwError "expected retained witness"
      let value ← addDef (base ++ name) params (← mkAppM ``Classical.choose #[proof])
      let next ← addThm (base ++ Name.mkSimple s!"afterChoice_{name}") params
        (body.instantiate1 value) (← mkAppM ``Classical.choose_spec #[proof])
      cache base params next index
    else if type.isAppOfArity ``And 2 then
      let left ← mkAppM ``And.left #[proof]
      discard <| addThm (base ++ Name.mkSimple s!"fact{index}") params (← inferType left) left
      let right ← mkAppM ``And.right #[proof]
      let next ← addThm (base ++ Name.mkSimple s!"afterFact{index}") params (← inferType right) right
      cache base params next (index+1)
    else
      discard <| addThm (base ++ `continuation) params type proof

private def chainAnd (proofs : Array Expr) : MetaM Expr := do
  let mut proof := proofs.back!
  for i in (List.range (proofs.size-1)).reverse do
    proof ← mkAppM ``And.intro #[proofs[i]!, proof]
  return proof

/-- Pick a single retained leading tuple, shared by every later consumer, and
construct its literal carrier chart from its original coefficient/ODE clauses. -/
elab "cache_physical_primary_retained_leading" : command => liftTermElabM do
  let root := `JanetCartan.PhysicalPrimary
  let source := root ++ `RetainedLeadingData
  let info ← getConstInfo source
  forallTelescope info.type fun params _ => do
    let type := mkAppN (mkConst source) params
    withLocalDeclD `hdata type fun hdata => cache (root ++ `LeadingData) (params.push hdata) hdata
  let cells := root ++ `LeadingData.continuation
  let info ← getConstInfo cells
  forallTelescope info.type fun params _ => do
    cache (root ++ `LeadingCell) params (mkAppN (mkConst cells) params)
  let cellsInfo ← getConstInfo cells
  forallTelescope cellsInfo.type fun params _ => do
    let lookup (name : Name) : MetaM Expr := do
      let some value ← params.findM? fun p => return (← getFVarLocalDecl p).userName == name
        | throwError "missing retained leading parameter {name}"
      return value
    let T ← lookup `T
    let F ← lookup `F
    let Q := mkAppN (mkConst (root ++ `LeadingData.Q)) params.pop
    let field (name : Name) := mkAppN (mkConst (root ++ `LeadingCell ++ name)) params
    let hflow ← chainAnd ((List.range 10).toArray.map fun i => field (Name.mkSimple s!"fact{i+4}"))
    let frame ← mkAppM ``Eq.refl #[← mkAppM `JanetCartan.ProjectedStressFrame.projectedStress #[F]]
    let args := #[T,Q,frame,field `Dc,field `φ,field `y,field `fact3,hflow]
    let current ← mkAppM
      `JanetCartan.ContinuumInverse.InitializedCappedHistory.chartOfOriginalLeading args
    discard <| addDef (root ++ `LeadingCell.current) params current
    let same ← mkAppM
      `JanetCartan.ContinuumInverse.InitializedCappedHistory.chartOfOriginalLeading_same_witnesses args
    discard <| addThm (root ++ `LeadingCell.same_witnesses) params (← inferType same) same
    let env ← getEnv
    let mut lastIndex := 0
    while env.contains (root ++ `LeadingCell ++ Name.mkSimple s!"fact{lastIndex+1}") do
      lastIndex := lastIndex+1
    let compatibility := field (Name.mkSimple s!"fact{lastIndex}")
    let compatible ← forallBoundedTelescope (← inferType compatibility) (some 2) fun qs _ => do
      let mut rest := mkAppN compatibility qs
      for _ in [:4] do rest ← mkAppM ``And.right #[rest]
      forallBoundedTelescope (← inferType rest) (some 1) fun initial _ => do
        let value ← mkAppM ``And.left #[mkAppN rest initial]
        mkLambdaFVars (initial ++ qs) value
    discard <| addThm (root ++ `LeadingCell.compatible) params (← inferType compatible) compatible
    let solution ← forallBoundedTelescope (← inferType (field `continuation)) (some 4) fun inputs _ => do
      let mut rest := mkAppN (field `continuation) inputs
      let mut fields : Array Expr := #[]
      for _ in [:9] do
        fields := fields.push (← mkAppM ``And.left #[rest])
        rest ← mkAppM ``And.right #[rest]
      let value ← chainAnd #[fields[1]!,fields[7]!,rest]
      mkLambdaFVars inputs value
    discard <| addThm (root ++ `LeadingCell.solution) params (← inferType solution) solution

end JanetCartan.PhysicalPrimary.LeadingTemplates
