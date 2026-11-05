module

public meta import Lean

/-!
# Literal conic clauses for the original selected history row

Project only the actual `SelectedBoundary.fact52`, keeping its original
21 callback inputs and its same selected cell. These ordinary kernel-checked
clauses instantiate `exists_prescribed_source_history_coercivity`; no new
geometry or norm certificate is a public hypothesis.
-/

public meta section
namespace JanetCartan.ContinuumInverse.InitializedCappedHistory.OriginalHistoryGap.Generator
open Lean Meta Elab Command

private def conicNamespace : Name :=
  `JanetCartan.ContinuumInverse.InitializedCappedHistory.OriginalHistoryGap.Conic

private def cacheConicTheorem (name : Name) (params : Array Expr) (proof : Expr) : MetaM Expr := do
  let fullName := conicNamespace ++ name
  addDecl (.thmDecl {
    name := fullName, levelParams := [], type := ← mkForallFVars params (← inferType proof),
    value := ← mkLambdaFVars params proof }) (forceExpose := true)
  return mkAppN (mkConst fullName) params

/-- Keep the literal conic clauses on the original selected row for the
actual history-coercivity application (`new:sec:order-of-choices`). -/
elab "project_original_history_conic" : command => liftTermElabM do
  let source := `JanetCartan.ContinuumInverse.InitializedCappedHistory.SelectedBoundary.fact52
  let info ← getConstInfo source
  unless info.levelParams.isEmpty do
    throwError "original history conic: unexpected universe parameters"
  forallBoundedTelescope info.type (some 21) fun params tail => do
    unless params.size == 21 do
      throwError "original history conic: expected all original 21 callback parameters"
    forallBoundedTelescope tail (some 1) fun indices _ => do
      unless indices.size == 1 do
        throwError "original history conic: expected the original selected-cell index"
      let allParams := params ++ indices
      let mut rest := mkAppN (mkConst source) allParams
      let names : Array Name := #[`first, `origin, `compact_eq, `conic_eq,
        `hρi, `hτi, `hW, `hKiW, `hBi, `hWBi, `hBiDom, `hDregion, `hcontains,
        `hsupportD, `hIt, `hIIt, `hsegT, `hseg, `density_endpoints, `hη,
        `hfreq, `hgap, `hQ, `hΩi, `hQΩi, `hQradius, `hne, `hscale, `geometry]
      for index in [:names.size - 1] do
        let type ← whnf (← inferType rest)
        unless type.isAppOfArity ``And 2 do
          throwError "original history conic: expected original clause {index}"
        discard <| cacheConicTheorem names[index]! allParams (← mkAppM ``And.left #[rest])
        rest ← cacheConicTheorem (.mkSimple s!"tail{index + 1}") allParams
          (← mkAppM ``And.right #[rest])
      discard <| cacheConicTheorem names.back! allParams rest

end JanetCartan.ContinuumInverse.InitializedCappedHistory.OriginalHistoryGap.Generator
