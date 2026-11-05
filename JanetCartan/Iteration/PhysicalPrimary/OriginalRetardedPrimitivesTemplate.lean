module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Named exact primitive projections on the already chosen critical graph. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalRetardedPrimitivesTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate
private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | i+1 => part (.proj ``And 1 e) i
private def tail (e : Expr) : Nat → Expr
  | 0 => e
  | i+1 => tail (.proj ``And 1 e) i

elab "retain_original_critical_primitive_projections" : command => liftTermElabM do
  let stationary := `JanetCartan.PhysicalPrimary.OriginalRetardedStationary
  let ns := `JanetCartan.PhysicalPrimary.OriginalRetardedPrimitives
  forallBoundedTelescope (← getConstInfo (stationary ++ `pointwise)).type (some 42) fun x _ => do
    unless x.size == 42 do throwError "native critical primitives: changed source/adjoint42 spine"
    let pointwise := mkAppN (mkConst (stationary ++ `pointwise)) x
    forallBoundedTelescope (← inferType pointwise) (some 2) fun point _ => do
      let cert := mkAppN pointwise point
      let zeroPair ← mkAppM ``And.intro #[part cert 1,part cert 2]
      let critical ← mkAppM ``And.intro #[part cert 0,zeroPair]
      discard <| store (ns ++ `critical) x (← mkLambdaFVars point critical)
      discard <| store (ns ++ `hessian) x (← mkLambdaFVars point (part cert 4))
      let full := tail cert 5
      forallBoundedTelescope (← inferType full) (some 6) fun segment _ => do
        unless segment.size == 6 do throwError "native critical primitives: changed complete segment spine"
        let segmentProof := mkAppN full segment
        discard <| store (ns ++ `segments) x
          (← mkLambdaFVars (point ++ segment) (.proj ``And 0 segmentProof))
        discard <| store (ns ++ `graph_segments) x
          (← mkLambdaFVars (point ++ segment) (.proj ``And 1 segmentProof))
  logInfo "same native four critical graphs: exact critical/phase-zero, averaged Hessian and full retained-segment inputs, preserving both independent signs"

end JanetCartan.PhysicalPrimary.OriginalRetardedPrimitivesTemplate
