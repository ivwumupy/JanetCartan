module

public import JanetCartan.Iteration.PhysicalPrimary.LeadingCurrent
public meta import Lean

/-!
# Scalar source facts from the same retained leading tuple

These are proof projections of `LeadingCell.continuation`, with precisely the
same scalar, row, column, full transports and current map. No witness is chosen.
They supply the original primitive hypotheses of the actual full-strain source
and its retained correction (`app:ch_response:eq:response-graded-source`).
-/

public meta section
namespace JanetCartan.PhysicalPrimary.LeadingSourceFacts
open Lean Meta Elab Command

private def publish (name : Name) (params : Array Expr) (value : Expr) : MetaM Unit := do
  addDecl (.thmDecl {
    name, levelParams := [], type := ← mkForallFVars params (← inferType value),
    value := ← mkLambdaFVars params value }) (forceExpose := true)

/-- Project the exact original scalar equations, without any new selector. -/
elab "cache_physical_primary_scalar_source_facts" : command => liftTermElabM do
  let root := `JanetCartan.PhysicalPrimary.LeadingCell
  let cellsInfo ← getConstInfo `JanetCartan.PhysicalPrimary.LeadingData.continuation
  forallTelescope cellsInfo.type fun params _ => do
    let original := mkAppN (mkConst (root ++ `continuation)) params
    forallBoundedTelescope (← inferType original) (some 4) fun scalarInputs _ => do
      let mut rest := mkAppN original scalarInputs
      let mut fields : Array Expr := #[]
      for _ in [:8] do
        fields := fields.push (← mkAppM ``And.left #[rest])
        rest ← mkAppM ``And.right #[rest]
      let allParams := params ++ scalarInputs
      publish (root ++ `scalar_regular) allParams fields[0]!
      publish (root ++ `scalar_transport) allParams fields[6]!
      publish (root ++ `scalar_bound) allParams fields[7]!
      let nonzero ← forallBoundedTelescope (← inferType fields[3]!) (some 2) fun points _ => do
        let mut rest := mkAppN fields[3]! points
        rest ← mkAppM ``And.right #[rest]
        rest ← mkAppM ``And.right #[rest]
        let left ← mkAppM ``And.left #[rest]
        let right ← mkAppM ``And.left #[← mkAppM ``And.right #[rest]]
        mkLambdaFVars points (← mkAppM ``And.intro #[left,right])
      publish (root ++ `scalar_nonzero) allParams nonzero
      let source ← mkAppM ``And.intro #[fields[0]!, ← mkAppM ``And.intro #[nonzero,
        ← mkAppM ``And.intro #[fields[6]!,fields[7]!]]]
      publish (root ++ `scalar_source_data) allParams source

end JanetCartan.PhysicalPrimary.LeadingSourceFacts

cache_physical_primary_scalar_source_facts
