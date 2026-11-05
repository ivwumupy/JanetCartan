module

public import Mathlib.Basic.SProd
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Preserve the actual native critical branch, every pointwise stationary
certificate and both independent orientation flags while restricting time. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalRetardedStationaryTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
private def ns := `JanetCartan.PhysicalPrimary.OriginalRetardedStationary

private def part (e : Expr) : Nat → Expr
  | 0 => .proj ``And 0 e
  | i+1 => part (.proj ``And 1 e) i

/-- Instantiate the restriction on the actual current, not on a new flow or
critical-point witness. The last two flags are never identified. -/
elab "retain_original_mask_window_stationary" : command => liftTermElabM do
  let nativeName := regular ++ `Current.stationary
  forallBoundedTelescope (← getConstInfo nativeName).type (some 42) fun x _ => do
    unless x.size == 42 do
      throwError "native mask critical branches: expected current38, sector, SOURCE sign, original patch and independent ADJOINT sign"
    let sx := x[:23].toArray ++ #[x[38]!]
    let ht := mkAppN (mkConst (regular ++ `Sector.fact0)) sx
    let t := ← inferType ht
    let r := t.appFn!.appArg!
    let τ := t.appArg!
    let native := mkAppN (mkConst nativeName) x
    let hj := part native 0
    let hk := part native 1
    let hi := part native 2
    let hp := .proj ``And 1 (.proj ``And 1 (.proj ``And 1 native))
    let tj ← inferType hj
    let tk ← inferType hk
    let Ψ := tj.appFn!.appArg!
    let κ := tk.appFn!.appArg!
    let jointDomain := tj.appArg!
    let oldWindow := tk.appArg!
    unless jointDomain.isAppOfArity ``SProd.sprod 6 && oldWindow.isAppOfArity ``SProd.sprod 6 do
      throwError "native critical branches: original time/source/integration product changed"
    let U := oldWindow.appArg!
    let D := jointDomain.appArg!
    forallBoundedTelescope (← inferType hp) (some 2) fun point body => do
      unless point.size == 2 do throwError "native critical branch has no original pointwise certificate"
      if (body.find? (fun e => e == point[1]!)).isSome then
        throwError "native critical predicate unexpectedly depends on the membership proof"
      let P ← mkLambdaFVars #[point[0]!] body
      let h := mkAppN (mkConst (ns ++ `restrict_stationary_to_mask))
        #[x[0]!, r, τ, ht, U, D, Ψ, κ, P, hj, hk, hp]
      let h ← store (ns ++ `mask_data) x h
      discard <| store (ns ++ `phase_smooth) x (part h 0)
      discard <| store (ns ++ `κ_smooth) x (part h 1)
      discard <| store (ns ++ `pointwise) x (.proj ``And 1 (.proj ``And 1 h))
      discard <| store (ns ++ `initial) x hi
  logInfo "all four native SOURCE-sign/ADJOINT-sign critical branches retained on the original mask window: same kappa, exact phase zero, averaged Hessians and complete original segments"

end JanetCartan.PhysicalPrimary.OriginalRetardedStationaryTemplate
