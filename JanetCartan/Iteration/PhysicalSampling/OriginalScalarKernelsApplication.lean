module

public meta import Lean

/-!
# The literal scalar kernels of the proved original current bound

Expose the kernels already present in `OriginalScalarHistory.current_bounds`.
The low-frame proof is retained once, and all kernel/band/mean fields use that
SAME proof and current map. There is no new scalar kernel selector, phase,
source, sample or successful analytic premise (`new:eq:amplitude-test`).
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalScalarKernelsApplication
open Lean Meta Elab Command

private def source : Name := `JanetCartan.PhysicalSampling.OriginalScalarHistory.current_bounds
private def target : Name := `JanetCartan.PhysicalSampling.OriginalScalarFamily.Row

private def store (name : Name) (params : Array Expr) (value : Expr)
    (expected : Option Expr := none) : MetaM Expr := do
  let rawType ← match expected with
    | some type => pure type
    | none => inferType value
  let type ← instantiateMVars rawType
  let value ← instantiateMVars value
  let type ← mkForallFVars params type
  let value ← mkLambdaFVars params value
  if type.hasMVar || value.hasMVar || type.hasSorry || value.hasSorry ||
      type.hasFVar || value.hasFVar then
    throwError "actual scalar kernels: open or recovered declaration {name}"
  if ← isProp type then
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  else
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe})
      (forceExpose := true)
  logInfo m!"checked SAME original scalar current kernel field {name}"
  return mkAppN (mkConst name) params

private partial def zetaOuter : Expr → Expr
  | .letE _ _ value body _ => zetaOuter (body.instantiate1 value)
  | .mdata _ body => zetaOuter body
  | body => body

/-- Retain only the low-frame proof already supplied by the actual history. -/
elab "cache_original_scalar_kernel_frame" : command =>
    liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo source).type (some 44) fun params _ => do
    unless params.size == 44 do throwError "actual scalar kernels: expected original current44 parameters"
    let proof := mkAppN (mkConst source) params
    let type ← whnf (← inferType proof)
    unless type.isAppOfArity ``Exists 2 do
      throwError "actual scalar kernels: expected the proved low-frame existential"
    let low ← store (target ++ `low_frame) params (← mkAppM ``Classical.choose #[proof])
    discard <| store (target ++ `after_low_frame) params
      (← mkAppM ``Classical.choose_spec #[proof]) (some (type.appArg!.beta #[low]))

/-- Name the exact two physical kernels and project their proved bounds.
No carrier, rate, cutoff, mask or full finite-rate phase is changed. -/
elab "cache_original_scalar_current_kernel_field " which:num : command =>
    liftTermElabM <| withTransparency .reducible do
  let index := which.getNat
  unless index < 5 do throwError "actual scalar kernels: invalid field index"
  let continuation := target ++ `after_low_frame
  forallBoundedTelescope (← getConstInfo continuation).type (some 44) fun params _ => do
    unless params.size == 44 do throwError "actual scalar kernels: lost original current44 prefix"
    let rowContinuation := mkAppN (mkConst continuation) params
    forallBoundedTelescope (← inferType rowContinuation) (some 4) fun rates body => do
      unless rates.size == 4 do throwError "actual scalar kernels: expected J, rates, positivity and band admission"
      let body := zetaOuter body
      let some raw := body.find? (fun e =>
          e.isAppOf `JanetCartan.PhysicalSampling.originalScalarKernelData && !e.hasLooseBVars)
        | throwError "actual scalar kernels: literal original scalar kernel missing"
      let some cut := body.find? (fun e =>
          e.isAppOf `JanetCartan.PhysicalSampling.scalarCarrierCutKernel && !e.hasLooseBVars)
        | throwError "actual scalar kernels: literal existing carrier cut missing"
      let rawType ← inferType raw
      unless rawType.isAppOf `JanetCartan.SamplingKernelBounds.BandKernelData do
        throwError "actual scalar kernels: unexpected physical kernel type {rawType.getAppFn}"
      -- Neither kernel depends on the band-admission proof. Omitting it is
      -- checked by the closed-expression guard, not by erasing a hypothesis.
      let kernelParams := params ++ rates[:3].toArray
      let allParams := params ++ rates
      let proof := mkAppN rowContinuation rates
      match index with
      | 0 => discard <| store (target ++ `kernel) kernelParams raw
      | 1 =>
          let rawNamed := mkAppN (mkConst (target ++ `kernel)) kernelParams
          let cut := cut.replace fun e => if e == raw then some rawNamed else none
          discard <| store (target ++ `cut_kernel) kernelParams cut
      | 2 => discard <| store (target ++ `sharp_bound) allParams (.proj ``And 0 proof)
      | 3 => discard <| store (target ++ `mean_bound) allParams (.proj ``And 0 (.proj ``And 1 proof))
      | _ => discard <| store (target ++ `carrier_plateau) allParams (.proj ``And 1 (.proj ``And 1 proof))

end JanetCartan.PhysicalSampling.OriginalScalarKernelsApplication
