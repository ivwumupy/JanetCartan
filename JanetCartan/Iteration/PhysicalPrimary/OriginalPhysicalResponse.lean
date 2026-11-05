module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalResponseJets

/-! # Original-data complete-response consumer
The reserve, profile constants and common threshold all precede the history.
One common reached-threshold premise supplies the complete inverse, full
uncontracted source and reconstruction coefficients on the same original data.
No further response estimate or choice is passed by a caller. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalResponseTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponse
private def jets := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseJets
private def inputs := `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseInputProfiles
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def emit (k : Name) (xs : Array Expr) (v : Expr) (data := false) (t : Option Expr := none) : MetaM Expr := do
  let h ← store (ns ++ k) xs v data t
  addDocStringCore (ns ++ k) "Actual original-data response with the reserve and its common all-history threshold fixed first; the original full inverse and complete strain deliver the sharp quadratic displacement and linear derivative grade on the unchanged current window (app:ch_response:eq:current-atomic-amplitudes)."
  logInfo m!"original response consumer: checked {k}"
  return h

/-- Open exactly the common prehistory44 and actual physical16, deriving the
inverse threshold from the one common reached proof. No new data are chosen. -/
def withCommonPhysicalResponseInputs
    (go : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (jets ++ `S)).type (some 44) fun fixed _ => do
    let p := fixed[:42].toArray
    let partially := app (jets ++ `derivative_jets) p
    forallBoundedTelescope (← inferType partially) (some 1) fun rr _ => do
      let R := rr[0]!
      withLocalDeclD `hReached (← mkAppM ``LE.le #[app (jets ++ `S) fixed,R]) fun hR => do
        let hInv ← mkAppM `le_trans #[app (inputs ++ `inverse_threshold) fixed,hR]
        let reached := app (jets ++ `derivative_jets) (p ++ #[R,hInv])
        forallBoundedTelescope (← inferType reached) (some 14) fun history _ => do
          unless history.size == 14 do throwError "original response consumer: physical14 changed"
          let xs := p ++ #[R,hInv] ++ history
          let all := xs ++ #[fixed[42]!,fixed[43]!,hR]
          let params := fixed ++ #[R,hR] ++ history
          unless params.size == 60 && xs.size == 58 && all.size == 61 do
            throwError "original response consumer: common original input spine changed"
          go params fixed xs all

elab "publish_original_physical_response" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (jets ++ `S)).type (some 44) fun fixed _ => do
    for k in [`S,`Cresp,`Cdisp] do
      discard <| emit k fixed (app (jets ++ k) fixed) true
    for k in [`S_ge_two,`Cresp_nonneg,`Cdisp_nonneg] do
      discard <| emit k fixed (app (jets ++ k) fixed)
  withCommonPhysicalResponseInputs fun params fixed xs all => do
    let oldRegion := app (jets ++ `region) xs
    let region ← emit `region params oldRegion true
    let rename (t : Expr) := t.replace fun e =>
      if e == oldRegion then some region
      else if e == app (jets ++ `Cresp) fixed then some (app (ns ++ `Cresp) fixed)
      else if e == app (jets ++ `Cdisp) fixed then some (app (ns ++ `Cdisp) fixed)
      else none
    for k in [`region_open,`response_smooth,`displacement_smooth,`derivative_smooth] do
      let v := app (jets ++ k) xs
      discard <| emit k params v false (some (rename (← inferType v)))
    for k in [`derivative_jets,`displacement_jets,`derivative_cNorm,`displacement_cNorm] do
      let v := app (jets ++ k) all
      discard <| emit k params v false (some (rename (← inferType v)))
  logInfo "actual common original44+physical16 response consumer: only one original reached threshold, no response/profile hypotheses, unchanged source/scalar size and full native B"

end JanetCartan.PhysicalPrimary.OriginalPhysicalResponseTemplate
end
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000
set_option backward.isDefEq.respectTransparency false
publish_original_physical_response
