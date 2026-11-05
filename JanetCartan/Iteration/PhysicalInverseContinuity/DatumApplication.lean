module

public meta import Lean

/-! Apply the actual retained density family to the exact measured datum and
cache its fixed reference representative. Only regular closed definitions and
theorems are emitted. No source or scalar amplitude is selected afresh. -/

public meta section
namespace JanetCartan.PhysicalInverseContinuity.DatumApplication
open Lean Meta Elab Term Command

def datumNS := `JanetCartan.PhysicalInverseContinuity.StrongDatum

/-- Keep only closed, kernel-checked terms. A definitional type alias may be
supplied to display the fixed datum without repeating all of its constituents. -/
def store (name : Name) (xs : Array Expr) (value : Expr) (data := false)
    (type? : Option Expr := none) : TermElabM Expr := do
  let type ← match type? with | some type => pure type | none => inferType value
  let type ← instantiateMVars (← mkForallFVars xs type)
  let value ← instantiateMVars (← mkLambdaFVars xs value)
  if type.hasMVar || value.hasMVar || type.hasLevelMVar || value.hasLevelMVar ||
      type.hasFVar || value.hasFVar || type.hasSorry || value.hasSorry then
    throwError "open or recovered actual measured source declaration {name}"
  let name := datumNS ++ name
  if data then
    addDecl (.defnDecl { name, type, value, levelParams := [], hints := .abbrev, safety := .safe }) (forceExpose := true)
  else
    addDecl (.thmDecl { name, type, value, levelParams := [] }) (forceExpose := true)
  return mkAppN (mkConst name) xs

/-- Use the same source contraction and the same finite physical carrier masks
as the original inverse, obtaining the all-grade measured source tolerance. -/
elab "apply_actual_original_density_to_measured " density:ident : command => liftTermElabM do
  let name ← realizeGlobalConstNoOverloadWithInfo density
  let info ← getConstInfo name
  forallBoundedTelescope info.type (some 27) fun params _ => do
    unless params.size == 27 do throwError "strong datum: expected original23 and four original density mask arguments"
    let fields (ns : Name) (q : Name) (count : Nat) := mkAppN (mkConst (ns ++ q)) params[:count]
    let H := fields `JanetCartan.PhysicalSeed.ReferenceBoundary `H 18
    let selected (q : Name) := fields `JanetCartan.PhysicalSeed.SelectedBoundary q 21
    let sourceOne := fields `JanetCartan.PhysicalSeed.SourceInverseBoundary `fact13 21
    let hσ := params[22]!
    let hσpos ← mkAppM ``And.left #[hσ]
    let hσone ← mkAppM `le_trans #[← mkAppM ``And.right #[hσ], sourceOne]
    let G ← mkAppM `JanetCartan.sourceDilationReference #[H, hσpos, hσone]
    let mean := mkAppN (mkConst name) params
    let original ← mkAppM `JanetCartan.PhysicalInverseContinuity.exists_measured_retained_source_tolerance
      #[G, selected `hrMeasure, selected `hMeasureCell, selected `fact58, mean]
    let q₀ ← store `reference_stress_smooth params (← mkAppM ``Classical.choose #[original])
    let spec₀ := (← whnf (← inferType original)).appArg!.beta #[q₀]
    let p₀ ← store `reference_stress_spec params (← mkAppM ``Classical.choose_spec #[original]) false (some spec₀)
    let h₀ ← store `reference_mean_smooth params (← mkAppM ``Classical.choose #[p₀])
    let spec := (← whnf (← inferType p₀)).appArg!.beta #[h₀]
    let fixed ← store `source_spec params (← mkAppM ``Classical.choose_spec #[p₀]) false (some spec)
    forallBoundedTelescope (← inferType fixed) (some 2) fun x _ => do
      let full := params ++ x
      let source := mkAppN fixed x
      let mem ← mkAppM ``And.left #[source]
      let e₀ ← forallBoundedTelescope (← inferType mem) (some 1) fun _ body => do
        let some e := body.find? (·.isAppOf `JanetCartan.PhysicalBackground.measuredSourceToL2) |
          throwError "strong datum: reference element is not the actual measured physical residual"
        return e
      let eRef ← store `reference full e₀ true
      let memType := (← inferType mem).replace fun e => if e == e₀ then some eRef else none
      discard <| store `reference_mem full mem false (some memType)
      let tol ← mkAppM ``And.right #[source]
      let tolType := (← inferType tol).replace fun e => if e == e₀ then some eRef else none
      discard <| store `exists_source_measured_tolerance full tol false (some tolType)
    logInfo "original23 + original mask and tangent field: exact original measured datum, fixed high cap and arbitrary low accuracy"

end JanetCartan.PhysicalInverseContinuity.DatumApplication
end
