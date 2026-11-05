module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Retain the already proved global coefficient profiles at the SAME native
regular reference and prescribed extension. No frame tolerance, coefficient
estimate or response estimate is supplied as a new premise. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalOperatorProfilesTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def original := `JanetCartan.PhysicalSeed.OriginalBoundary
private def ns := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles

/-- The history cap and coefficient reserve are separate: the former is at
least two larger. Select the SAME global Q/full-B profiles before any history,
source frequency or finite residual word. -/
elab "retain_original_operator_coefficient_profiles" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (regular ++ `Gref)).type (some 25) fun fixed _ => do
    unless fixed.size == 25 do
      throwError "native operator profiles: expected original23 and the same source scale"
    let n := mkApp (mkConst ``Nat.succ) fixed[0]!
    let hn := fixed[1]!
    let source := #[n] ++ fixed[1:21].toArray
    let G := mkAppN (mkConst (regular ++ `Gref)) fixed
    let orig (q : Name) := mkAppN (mkConst (original ++ q)) #[n, hn]
    let same := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5)
      source[:18].toArray
    let hR ← mkAppM (regular ++ `radius_lt_same_chart) #[same, orig `R_lt_chartRadius]
    let raw := mkAppN (mkConst `JanetCartan.PhysicalGeometry.exists_retained_coefficient_profiles)
      #[n, G, orig `b, orig `R, orig `b_pos, orig `b_lt_R, hR,
        fixed[4]!, fixed[5]!, fixed[6]!]
    forallBoundedTelescope (← inferType raw) (some 8) fun order _ => do
      unless order.size == 8 do
        throwError "native operator profiles: expected B, hB, history cap, coefficient reserve, kMin and three numeric certificates"
      let params := fixed ++ order
      let actual ← store (ns ++ `exists_profiles) params (mkAppN raw order)
      select ns params actual
  logInfo "native original25 Q and FULL B all-order profiles: one S/AQ/AB before every history, arbitrary compact K, separate history cap and coefficient reserve, no new admission premise"

end JanetCartan.PhysicalPrimary.OriginalOperatorProfilesTemplate
