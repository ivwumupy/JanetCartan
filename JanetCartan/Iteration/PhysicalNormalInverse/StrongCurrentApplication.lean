module

public meta import JanetCartan.Iteration.PhysicalNormalInverse.StrongGeometryApplication

/-! Safe ordinary proof elaboration and exact notation for the ONE strengthened
initializer's current-inverse geometric application. No weak tuple is used. -/

public meta section
namespace JanetCartan.PhysicalNormalInverse.StrongCurrentApplication
open Lean Meta Elab Command Term

/-- Elaborate the original proof template against its literal selected callback
parameters.  The ordinary theorem and every generated proof are kernel checked;
no inverse conclusion is assumed by this command. -/
elab "check_strong_physical_inverse_application " name:ident " := " value:term : command =>
  liftTermElabM do
    let source ← getConstInfo
      `JanetCartan.PhysicalSeed.SelectedBoundary.centers
    forallTelescopeReducing source.type fun params _ => do
      unless params.size == 21 do
        throwError "physical original inverse: expected 21 selected inputs"
    let value ← elabTerm value none
    synthesizeSyntheticMVarsNoPostponing
    let value ← instantiateMVars value
    let type ← instantiateMVars (← inferType value)
    if value.hasMVar || type.hasMVar || value.hasLevelMVar || type.hasLevelMVar then
      throwError "physical original inverse: unresolved metavariable"
    if value.hasFVar || type.hasFVar then
      throwError "physical original inverse: unbound original input"
    if value.hasSorry || type.hasSorry then
      throwError "strong inverse: elaboration recovery is not a proof"
    unless ← isProp type do
      throwError "physical original inverse: expected a proved proposition"
    let name := (← getCurrNamespace) ++ name.getId
    addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)

end JanetCartan.PhysicalNormalInverse.StrongCurrentApplication
end

public meta section
namespace JanetCartan.PhysicalNormalInverse.StrongCurrentApplication
open Lean

private def applied (ns : Name) (field : Ident) (names : Array Name) : MacroM (TSyntax `term) := do
  let head : TSyntax `term := ⟨(mkIdent (ns ++ field.getId)).raw⟩
  let args : Array (TSyntax `term) := names.map fun n ↦ ⟨(mkIdent n).raw⟩
  `($head $args*)

private def referenceInputs : Array Name :=
  #[`hn, `εframe, `hεframe, `qext, `hqcenter, `hqradius, `k, `hk, `hkD,
    `p, `orders, `margin, `extendedMargin, `hmargin, `hextendedMargin, `cap, `hcap]

macro "strong_boundary% " field:ident : term =>
  applied `JanetCartan.PhysicalSeed.OriginalBoundary field #[`hn]

macro "strong_reference% " field:ident : term =>
  applied `JanetCartan.PhysicalSeed.ReferenceBoundary field referenceInputs

macro "strong_selected% " field:ident : term =>
  applied `JanetCartan.PhysicalSeed.SelectedBoundary field
    (referenceInputs ++ #[`incidenceCap, `hincidenceCap, `cappedExtra])

macro "strong_conic% " field:ident : term =>
  applied `JanetCartan.PhysicalNormalInverse.StrongConic field
    (referenceInputs ++ #[`incidenceCap, `hincidenceCap, `cappedExtra])

end JanetCartan.PhysicalNormalInverse.StrongCurrentApplication
end
