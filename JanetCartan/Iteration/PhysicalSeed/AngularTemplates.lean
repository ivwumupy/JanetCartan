module

public meta import Lean

/-!
# Statement and proof templates for the same angular-capped initializer

These commands only reuse the literal original statement telescopes. The
strengthened declarations still require ordinary Lean proofs, checked by the
kernel. They neither postulate the new cap nor identify a weak choice with a
stronger one. Their concrete consumer is the same 21-argument PhysicalSeed
initializer used by `PhysicalSampling.exists_original_scalar_sampling_bounds`.
-/

public meta section
namespace JanetCartan.PhysicalSeed.AngularTemplates
open Lean Meta Elab Term Command

private partial def insertPrefix (type : Expr) (stop : Name) (extra : Syntax) : TermElabM Expr := do
  if let .letE name domain value body _ := type then
    withLetDecl name domain value fun witness => do
      mkLetFVars #[witness] (← insertPrefix (body.instantiate1 witness) stop extra)
        (usedLetOnly := false)
  else if type.isAppOfArity ``Exists 2 then
    let .lam name domain body bi := type.appArg! | throwError "angular retention: expected predicate"
    if name == stop then
      return mkApp2 (mkConst ``And) (← elabTermEnsuringType extra (mkSort 0)) type
    withLocalDecl name bi domain fun witness => do
      mkAppM ``Exists #[← mkLambdaFVars #[witness] (← insertPrefix (body.instantiate1 witness) stop extra)]
  else if type.isAppOfArity ``And 2 then
    return mkApp2 (mkConst ``And) type.appFn!.appArg! (← insertPrefix type.appArg! stop extra)
  else
    let .forallE name _ _ _ := type | throwError "angular retention: unexpected tail"
    unless name == stop do throwError "angular retention: expected {stop}, got {name}"
    return mkApp2 (mkConst ``And) (← elabTermEnsuringType extra (mkSort 0)) type

/-- Reuse an original telescope but demand the genuinely stronger retained
prefix, with a supplied kernel-checked ordinary proof. -/
syntax "declare_angular_retained " ident " from " ident " before " ident
  " retaining " term " := " term : command

elab_rules : command
  | `(declare_angular_retained $target:ident from $source:ident before $stop:ident
      retaining $extra:term := $proof:term) => liftTermElabM do
    let old ← resolveGlobalConstNoOverload source
    let info ← getConstInfo old
    let name := (← getCurrNamespace) ++ target.getId
    forallTelescope info.type fun params body => do
      let statement ← insertPrefix body stop.getId extra
      let value ← elabTermEnsuringType proof statement
      synthesizeSyntheticMVarsNoPostponing
      let statement ← instantiateMVars statement
      let value ← instantiateMVars value
      let type ← mkForallFVars params statement
      let value ← mkLambdaFVars params value
      addDecl (.thmDecl { name, levelParams := info.levelParams, type, value }) (forceExpose := true)

/-- Traverse the literal initializer callbacks without opening unrelated
analytic predicates. Only the selected carrier context can receive the cap. -/
private partial def insertDeep (type : Expr) (stop : Name) (extra : Syntax) :
    TermElabM (Expr × Nat) := do
  if let .letE name domain value body _ := type then
    withLetDecl name domain value fun witness => do
      let (tail, count) ← insertDeep (body.instantiate1 witness) stop extra
      return (← mkLetFVars #[witness] tail (usedLetOnly := false), count)
  else if type.isAppOfArity ``Exists 2 then
    let .lam name domain body bi := type.appArg! | throwError "angular retention: expected predicate"
    withLocalDecl name bi domain fun witness => do
      let (tail, count) ← insertDeep (body.instantiate1 witness) stop extra
      return (← mkAppM ``Exists #[← mkLambdaFVars #[witness] tail], count)
  else if type.isAppOfArity ``And 2 then
    let (left, nleft) ← insertDeep type.appFn!.appArg! stop extra
    let (right, nright) ← insertDeep type.appArg! stop extra
    return (mkApp2 (mkConst ``And) left right, nleft + nright)
  else if let .forallE name domain body bi := type then
    let ctx ← getLCtx
    let selected := [(`ηb : Name), `r', `cell, `aExtra].all
      (fun name ↦ (ctx.findFromUserName? name).isSome)
    if name == stop && selected then
      return (mkApp2 (mkConst ``And) (← elabTermEnsuringType extra (mkSort 0)) type, 1)
    withLocalDecl name bi domain fun witness => do
      let (tail, count) ← insertDeep (body.instantiate1 witness) stop extra
      return (← mkForallFVars #[witness] tail, count)
  else
    return (type, 0)

/-- Strengthen exactly one selected incidence callback inside an already
specified original initializer proposition. No additional input is introduced. -/
syntax "retain_angular_seed_type% " term " before " ident " retaining " term : term
elab_rules : term
  | `(retain_angular_seed_type% $source:term before $stop:ident retaining $extra:term) => do
    let type ← elabTermEnsuringType source (mkSort 0)
    let (result, count) ← insertDeep type stop.getId extra
    unless count == 1 do throwError "angular retention: expected one selected callback, got {count}"
    return result

/-- The corresponding proof-type inspection form, used to validate the exact
unchanged outer argument telescope before replacing its producer. -/
syntax "retain_angular_seed% " term " before " ident " retaining " term : term
elab_rules : term
  | `(retain_angular_seed% $source:term before $stop:ident retaining $extra:term) => do
    let proof ← elabTerm source none
    let (result, count) ← insertDeep (← inferType proof) stop.getId extra
    unless count == 1 do throwError "angular retention: expected one selected callback, got {count}"
    return result

end JanetCartan.PhysicalSeed.AngularTemplates
