module

public meta import Lean

/-! Kernel-checked selection from the original protected signed product. The
later fixed inverse reuses exactly these sectors, rather than selecting a
second signed menu. -/

public meta section
namespace JanetCartan.PhysicalInitialization.OriginalProtectedTemplate
open Lean Meta Elab Command

def store (name : Name) (params : Array Expr) (v : Expr) (isDef := false)
    (target : Option Expr := none) : MetaM Expr := do
  let value ← instantiateMVars (← mkLambdaFVars params v)
  let type ← instantiateMVars (← mkForallFVars params (target.getD (← inferType v)))
  if type.hasFVar || type.hasMVar || type.hasSorry || value.hasFVar || value.hasMVar || value.hasSorry then
    throwError "original physical selection: open or incomplete term {name}"
  if isDef then
    addDecl (.defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }) (forceExpose := true)
  else
    addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
  return mkAppN (mkConst name) params

/-- Preserve larger conjunctions under `∀` intact. Each chosen scalar, chart,
compact set, and regular operator has a stable name from this *one* witness. -/
partial def select (ns : Name) (params : Array Expr) (h : Expr)
    (index : Nat := 0) : MetaM Unit := do
  let t ← inferType h
  if let .letE name _ v body _ := t then
    let v ← store (ns ++ name) params v true
    let rest ← store (ns ++ Name.mkSimple s!"afterLet_{name}") params h false (some (body.instantiate1 v))
    select ns params rest index
  else
    let t ← whnf t
    if t.isAppOfArity ``Exists 2 then
      let .lam name _ body _ := t.appArg! | throwError "original physical selection: expected named witness"
      let v ← store (ns ++ name) params (← mkAppM ``Classical.choose #[h]) true
      let rest ← store (ns ++ Name.mkSimple s!"afterChoice_{name}") params (← mkAppM ``Classical.choose_spec #[h]) false
        (some (body.instantiate1 v))
      select ns params rest index
    else if t.isAppOfArity ``And 2 then
      discard <| store (ns ++ Name.mkSimple s!"fact{index}") params (.proj ``And 0 h)
      let rest ← store (ns ++ Name.mkSimple s!"afterFact{index}") params (.proj ``And 1 h)
      select ns params rest (index + 1)
    else
      discard <| store (ns ++ `continuation) params h

/-- Replay the original strong current input prefix, strengthening the raw
extra callback exactly once, as in the native current and source inverse. -/
elab "construct_original_projected_protection" : command => liftTermElabM do
  let ns := `JanetCartan.PhysicalInitialization.OriginalProtected
  let native := `JanetCartan.PhysicalNormalInverse.StrongCurrent.source_continuation
  let info ← getConstInfo native
  forallBoundedTelescope info.type (some 21) fun x _ => do
    unless x.size == 21 do throwError "original protected geometry: expected native original21"
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[x[0]!, x[1]!, x[20]!]
    let centers := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.centers) (x.set! 20 capped)
    let groups ← store (ns ++ `Groups) x (mkAppN (mkConst (ns ++ `CellGroup)) #[x[0]!, x[1]!, centers]) true
    let assign ← store (ns ++ `assign) x (mkAppN (mkConst (ns ++ `cellPatch)) #[x[0]!, x[1]!, centers]) true
    let h := mkAppN (mkConst (ns ++ `protection_on_selected_centers)) #[x[0]!, x[1]!, centers, x[4]!, x[5]!, x[6]!]
    let t := (← inferType h).replace fun e =>
      if e.isAppOf (ns ++ `CellGroup) && e.appArg! == centers then some groups
      else if e.isAppOf (ns ++ `cellPatch) && e.appArg! == centers then some assign else none
    let actual ← store (ns ++ `signed_protection) x h false (some t)
    select ns x actual
  logInfo "original21 strong selected incidence group/patch assignment: complete projected signed product, actual protected radii/cones/charts and all finite chains"

end JanetCartan.PhysicalInitialization.OriginalProtectedTemplate
end
