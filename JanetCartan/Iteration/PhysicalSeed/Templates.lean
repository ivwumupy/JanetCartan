module

public meta import Lean

/-! Kernel-checked statement templates for the actual strengthened seed. -/

public meta section
namespace JanetCartan.PhysicalSeed.Templates
open Lean Meta Elab Term Command

private def finiteProducer : Name :=
  `JanetCartan.CurrentCoefficientProfiles.exists_finite_retained_leading_family_before_geometry_with_source_geometry

private partial def callback (params : Array Expr) (type : Expr) : MetaM Unit := do
  if type.isAppOfArity ``Exists 2 then
    let .lam name domain body _ := type.appArg! | throwError "expected literal predicate"
    withLocalDeclD name domain fun witness =>
      callback (params.push witness) (body.instantiate1 witness)
  else if type.isAppOfArity ``And 2 then
    callback params type.appArg!
  else
    let .forallE name _ _ _ := type | throwError "expected leading callback"
    unless name == `M do throwError "expected geometric budgets, got {name}"
    let used := params.filter fun p => type.containsFVar p.fvarId!
    let name := `JanetCartan.PhysicalSeed.GenericLeading
    addDecl (.defnDecl {
      name, levelParams := [], type := ← mkForallFVars used (mkSort 0),
      value := ← mkLambdaFVars used type,
      hints := .abbrev, safety := .safe }) (forceExpose := true)

/-- Retain the literal arbitrary-map callback, with only its used parameters. -/
elab "declare_physical_seed_generic_leading" : command => liftTermElabM do
  let info ← getConstInfo finiteProducer
  unless info.levelParams.isEmpty do throwError "unexpected producer universes"
  forallTelescope info.type fun params body => callback params body

private partial def insert (type : Expr) (stop : Name) (extra : Syntax) : TermElabM Expr := do
  if type.isAppOfArity ``Exists 2 then
    let .lam name domain body bi := type.appArg! | throwError "expected existential predicate"
    if name == stop then
      let field ← elabTermEnsuringType extra (mkSort 0)
      return mkApp2 (mkConst ``And) field type
    withLocalDecl name bi domain fun witness => do
      let tail ← insert (body.instantiate1 witness) stop extra
      mkAppM ``Exists #[← mkLambdaFVars #[witness] tail]
  else if type.isAppOfArity ``And 2 then
    return mkApp2 (mkConst ``And) type.appFn!.appArg! (← insert type.appArg! stop extra)
  else
    let .forallE name _ _ _ := type | throwError "unexpected initializer tail"
    unless name == stop do throwError "expected insertion before {stop}, got {name}"
    let field ← elabTermEnsuringType extra (mkSort 0)
    return mkApp2 (mkConst ``And) field type

/-- Insert a retained field into a type; an ordinary proof is still required. -/
syntax "retain_physical_seed% " term " before " ident " retaining " term : term
elab_rules : term
  | `(retain_physical_seed% $source:term before $stop:ident retaining $extra:term) => do
    let proof ← elabTerm source none
    insert (← inferType proof) stop.getId extra

end JanetCartan.PhysicalSeed.Templates
