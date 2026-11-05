module

public import JanetCartan.Iteration.PhysicalBackground.SourceBounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.RetainedSource
import all JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.RetainedSource
public meta import Lean

/-!
# Retained source bounds at the actual measurement cutoff

Reuse the proved retained-source geometry, but apply the underlying source
producer directly at physical cutoff index 1. This is NOT an identity between
index 0 and index 1. The external χ, χ² mass, source chart family and all
geometric witnesses are kept literally unchanged. The resulting cut source
has the producer's -1/2 normalization; the actual measured source is twice
this same index-1 source (`app:ch_background:prop:bg-current`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

public meta section
namespace JanetCartan.PhysicalBackground.RetainedMeasuredSourceApplication
open Lean Meta Elab Command Term

def storeMeasured (suffix : Name) (params : Array Expr) (term : Expr)
    (isDef : Bool := false) : MetaM Expr := do
  let name := `JanetCartan.PhysicalBackground.RetainedMeasuredSource ++ suffix
  let type ← instantiateMVars (← mkForallFVars params (← inferType term))
  let value ← instantiateMVars (← mkLambdaFVars params term)
  if type.hasMVar || value.hasMVar || type.hasFVar || value.hasFVar ||
      type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then
    throwError "measured source: incomplete final normalized bound {name}"
  if isDef then
    addDecl (.defnDecl { name, type, value, levelParams := [], hints := .abbrev, safety := .safe })
      (forceExpose := true)
  else
    addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
  return mkAppN (mkConst name) params

/-- Reapply the native source theorem, changing only its arbitrary physical
cutoff and the corresponding already proved smoothness/support certificates. -/
elab "apply_retained_source_at_measurement_cutoff" : command => liftTermElabM do
  let outer := `JanetCartan.PositiveBackground.exists_retained_fixedSource_sobolev_bounds
  let inner := `JanetCartan.RetainedAssembly.NormalizedMeanSource.exists_current_referenceSource_sobolev_bounds
  let info ← getConstInfo outer
  let some body := info.value? (allowOpaque := true) |
    throwError "measured source: retained proof body must be imported with import all"
  let arity ← forallTelescope (← getConstInfo inner).type fun xs _ => pure xs.size
  forallTelescope info.type fun params _ => do
    let proof ← Core.betaReduce (← zetaReduce (body.beta params))
    let some application := proof.find? (·.isAppOfArity inner arity) |
      throwError "measured source: the supplied retained-source producer application is missing"
    if application.hasLooseBVars then
      throwError "measured source: the source application depends on an unretained witness"
    let one ← Term.elabTerm (← `((1 : Fin 3))) none
    let names := #[`JanetCartan.ContinuumRow.FixedCutoffs.physical,
      `JanetCartan.ContinuumRow.FixedCutoffs.physical_tsupport_four]
    let changeCutoff (arg : Expr) := arg.replace fun e =>
      if names.any (fun name => e.isAppOfArity name 4) then
        some (mkAppN e.getAppFn (e.getAppArgs.set! 3 one))
      else none
    let mut args := application.getAppArgs
    -- The final four arguments are θ, hθ, hθD and hθsupport.
    for i in [args.size-4:args.size] do
      args := args.set! i (changeCutoff args[i]!)
    let result := mkAppN application.getAppFn args
    let type ← instantiateMVars (← mkForallFVars params (← inferType result))
    let value ← instantiateMVars (← mkLambdaFVars params result)
    if type.hasMVar || value.hasMVar || type.hasFVar || value.hasFVar ||
        type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then
      throwError "measured source: incomplete same-witness source application"
    addDecl (.thmDecl {
      name := `JanetCartan.PhysicalBackground.retained_measured_cut_source_bounds,
      levelParams := [], type, value }) (forceExpose := true)
    let retained := mkAppN
      (mkConst `JanetCartan.PhysicalBackground.retained_measured_cut_source_bounds) params
    let bspec ← mkAppM ``Classical.choose_spec #[retained]
    let capExists := Expr.proj ``And 1 (.proj ``And 1 bspec)
    discard <| storeMeasured `cap params (← mkAppM ``Classical.choose #[capExists]) true
    let capSpec ← mkAppM ``Classical.choose_spec #[capExists]
    discard <| storeMeasured `cap_pos params (.proj ``And 0 capSpec)
    discard <| storeMeasured `cap_le params (.proj ``And 0 (.proj ``And 1 capSpec))
    let mut periodicExists := capSpec
    for _ in [:10] do periodicExists := .proj ``And 1 periodicExists
    let periodicSpec ← mkAppM ``Classical.choose_spec #[periodicExists]
    let bounds := Expr.proj ``And 0 (.proj ``And 1 periodicSpec)
    let nativeSource := mkAppN (mkConst outer) params
    let hQExists := Expr.proj ``And 1 nativeSource
    let hQ ← storeMeasured `stress_smooth params (← mkAppM ``Classical.choose #[hQExists])
    let hRExists ← mkAppM ``Classical.choose_spec #[hQExists]
    let hR ← storeMeasured `residual_smooth params (← mkAppM ``Classical.choose #[hRExists])
    let mut names := #[]
    for p in params do names := names.push (← p.fvarId!.getDecl).userName
    let arg (name : Name) : TermElabM Expr := do
      let some i := names.idxOf? name | throwError "measured source: missing physical argument {name}"
      pure params[i]!
    let hr ← arg `hr
    let hcell ← arg `hcell
    forallTelescope (← inferType bounds) fun orders _ => do
      unless orders.size == 1 do throwError "measured source: all-order source-bound signature changed"
      let existsC := mkAppN bounds orders
      let C ← mkAppM ``Classical.choose #[existsC]
      let cSpec ← mkAppM ``Classical.choose_spec #[existsC]
      let cPositive := Expr.proj ``And 0 cSpec
      let two ← Term.elabTerm (← `((2 : ℝ))) none
      let twoNonneg ← Term.elabTerm (← `(show (0 : ℝ) ≤ 2 by norm_num)) none
      let twoPositive ← Term.elabTerm (← `(show (0 : ℝ) < 2 by norm_num)) none
      Term.synthesizeSyntheticMVarsNoPostponing
      let measuredC ← mkAppM ``HMul.hMul #[two, C]
      discard <| storeMeasured `C (params ++ orders) measuredC true
      discard <| storeMeasured `C_pos (params ++ orders)
        (← mkAppM ``mul_pos #[twoPositive, cPositive])
      let family := Expr.proj ``And 1 cSpec
      forallTelescope (← inferType family) fun scales _ => do
        unless scales.size == 3 do throwError "measured source: small-scale source-bound signature changed"
        let sourceBound := mkAppN family scales
        let boundType ← inferType sourceBound
        let some source := boundType.find? (·.isAppOfArity
            `JanetCartan.PositiveBackground.sourceToL2 3) |
          throwError "measured source: exact cut-source L² element is missing"
        let sourceArgs := source.getAppArgs
        let cut := sourceArgs[1]!.headBeta
        unless cut.isAppOfArity `JanetCartan.PositiveBackground.cutReducedSource 4 do
          throwError "measured source: exact physical cut-source formula changed"
        let physicalArgs := cut.getAppArgs
        let q := physicalArgs[2]!
        let r := physicalArgs[3]!
        let measuredEq ← mkAppM `JanetCartan.PhysicalBackground.measuredSourceToL2_gradeNorm
          #[hr, hcell, q, r, mkAppN hQ scales[:2].toArray, mkAppN hR scales[:2].toArray, orders[0]!]
        let sourceEq ← mkAppM `JanetCartan.PositiveBackground.sourceToL2_gradeNorm
          #[cut, sourceArgs[2]!, orders[0]!]
        let multiplyTwo ← Term.elabTerm (← `(fun x : ℝ => 2 * x)) none
        let scaledEq ← mkAppM ``congrArg #[multiplyTwo, ← mkAppM ``Eq.symm #[sourceEq]]
        let exactEq ← mkAppM ``Eq.trans #[measuredEq, scaledEq]
        let twiceBound ← mkAppM ``mul_le_mul_of_nonneg_left #[sourceBound, twoNonneg]
        let resultBound ← mkAppM ``le_of_eq_of_le #[exactEq, twiceBound]
        let assoc ← mkAppM ``mul_assoc #[two, C, scales[0]!]
        let resultBound ← mkAppM ``LE.le.trans_eq #[resultBound, ← mkAppM ``Eq.symm #[assoc]]
        discard <| storeMeasured `bound (params ++ orders ++ scales) resultBound
    logInfo "checked direct index-1 retained source and literal factor-two measured bound; same χ/current"

end JanetCartan.PhysicalBackground.RetainedMeasuredSourceApplication
end

apply_retained_source_at_measurement_cutoff
