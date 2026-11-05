module

public meta import Lean

/-!
# Name the retained original angular-cap certificate

This command projects the final prefix fact of the one stronger original
21-argument selection. It refuses a weak selection whose final fact does not
contain the original angular width. The actual bound is already proved by
AngularInitializer; this command adds no hypothesis or additional selection.
Consumer: `PhysicalSampling.exists_original_scalar_sampling_bounds`
(`app:ch_waves:eq:sampling-operator-bounds`, `new:sec:order-of-choices`).
-/

public meta section
namespace JanetCartan.PhysicalSeed.AngularCache
open Lean Meta Elab Command

private partial def prefixLength (ns : Name) (index : Nat) : MetaM Nat := do
  if (← getEnv).contains (ns.str s!"Prefix{index}") then
    prefixLength ns (index + 1)
  else
    return index

/-- Expose the extra angular bound without changing any old prefix fact,
parameter, witness or continuation of the original selected initializer. -/
elab "cache_physical_seed_angular_width_cap" : command => liftTermElabM do
  let ns := `JanetCartan.PhysicalSeed.SelectedBoundary
  let info ← getConstInfo (ns.str "initialized")
  unless info.levelParams.isEmpty do
    throwError "original angular cap: unexpected universe parameters"
  forallTelescopeReducing info.type fun params _ => do
    unless params.size == 21 do
      throwError "original angular cap: expected 21 unchanged parameters, got {params.size}"
    let count ← prefixLength ns 0
    unless 0 < count do throwError "original angular cap: no selected prefix"
    let proof := mkAppN (mkConst (ns.str s!"fact{count - 1}")) params
    let statement ← inferType proof
    unless (statement.find? fun expr ↦ expr.isConstOf
        `JanetCartan.ContinuumRow.CanonicalConic.angularWidth).isSome do
      throwError "original angular cap: final fact is not the retained angular certificate"
    let type ← mkForallFVars params statement
    let value ← mkLambdaFVars params proof
    addDecl (.thmDecl {
      name := ns.str "angularWidth_le_aExtra"
      levelParams := []
      type
      value
    }) (forceExpose := true)

end JanetCartan.PhysicalSeed.AngularCache
