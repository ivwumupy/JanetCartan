module

public meta import Lean

/-! Project the actual SAME-source uncorrected Sobolev/raw estimates. The
source constructor chose Kraw and Cfull before the source scale and density. -/

public meta section
namespace JanetCartan.PhysicalNormalInverse.StrongReferenceApplication
open Lean Meta Elab Command

elab "project_strong_reference_uncorrected_raw" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalNormalInverse.StrongSourceGap.operatorTail6
  let info ← getConstInfo source
  unless info.levelParams.isEmpty do
    throwError "strong reference raw: unexpected universe parameters"
  forallTelescopeReducing info.type fun params _ => do
    unless params.size == 28 do
      throwError "strong reference raw: expected original23 and density5 inputs"
    let mut rest := mkAppN (mkConst source) params
    for _ in [:10] do
      rest ← mkAppM ``And.right #[rest]
    let zeroBranch ← mkAppM ``And.left #[rest]
    forallBoundedTelescope (← inferType zeroBranch) (some 1) fun zeroParams _ => do
      unless zeroParams.size == 1 do
        throwError "strong reference raw: expected the literal v=0 clause"
      let atZero := mkAppN zeroBranch zeroParams
      let rawAdjoint ← mkAppM ``And.left #[atZero]
      let rawInverse ← mkAppM ``And.left #[← mkAppM ``And.right #[atZero]]
      let proof ← mkAppM ``And.intro #[rawAdjoint, rawInverse]
      let allParams := params ++ zeroParams
      let name := `JanetCartan.PhysicalNormalInverse.StrongSourceGap.reference_uncorrected_raw
      addDecl (.thmDecl {
        name, levelParams := [],
        type := ← mkForallFVars allParams (← inferType proof),
        value := ← mkLambdaFVars allParams proof }) (forceExpose := true)
      logInfo "retained actual reference Kraw/Cfull bounds chosen before sigma; no current inverse identification"

end JanetCartan.PhysicalNormalInverse.StrongReferenceApplication
