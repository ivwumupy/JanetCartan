module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFullResponse
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamily
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedCutoff
public meta import Lean

/-!
# The literal row of the actual measured finite family

The compactly cut corrected amplitude is continuous because its four retained
coefficient fields and the SAME full physical response are jointly smooth on
the actual doubled ball. Its global continuity is not an independent input.
The raw kernel below does not require a band bound, a small-rate condition,
any derivative bound for the uncut response, or a successful sample. Only the
true qualitative response smoothness is still required from the producer
(`app:ch_mean_pairs:defn:mean-canonical`, `app:ch_waves:eq:sampling-prefix-normal`).
-/

@[expose] public noncomputable section
namespace JanetCartan.PhysicalSampling.OriginalMeasuredKernelsApplication
private theorem original_mask_unit_nonnegative : (0 : ℝ) ≤ 1 := zero_le_one

end JanetCartan.PhysicalSampling.OriginalMeasuredKernelsApplication
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalMeasuredKernelsApplication
open Lean Meta Elab Command

private def sampling := `JanetCartan.PhysicalSampling
private def current := sampling ++ `OriginalMeasuredCurrent
private def ns := sampling ++ `OriginalMeasuredFamily.Row

def save (name : Name) (xs : Array Expr) (term : Expr) (data := false)
    (result : Option Expr := none) : MetaM Expr := do
  let name := ns ++ name
  let t ← match result with
    | some s => pure s
    | none => inferType term
  let type ← instantiateMVars (← mkForallFVars xs t)
  let value ← instantiateMVars (← mkLambdaFVars xs term)
  if type.hasMVar || value.hasMVar || type.hasLevelMVar || value.hasLevelMVar ||
      type.hasFVar || value.hasFVar || type.hasSorry || value.hasSorry then
    throwError "original measured kernel: unresolved or unwanted analytic parameter in {name}"
  if data then
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  logInfo m!"checked original physical measured kernel field {name} with {xs.size} parameters"
  return mkAppN (mkConst name) xs

private def body (name : Name) : MetaM Expr := do
  let some b := (← getConstInfo name).value? (allowOpaque := true)
    | throwError "original measured kernel: expected actual proof body {name}"
  return b

def withRow (k : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let source := current ++ `mean_on_full_response
  forallBoundedTelescope (← getConstInfo source).type (some 60) fun x remaining => do
    let full := ((← body source).beta x).headBeta
    unless full.isAppOfArity (current ++ `mean_before_response) 62 do
      throwError "original measured kernel: original actual chi2/B data not retained"
    let mean := ((← body (current ++ `mean_before_response)).beta full.getAppArgs).headBeta
    unless mean.isAppOfArity (sampling ++ `OriginalMeasuredMean.continuation) 70 do
      throwError "original measured kernel: actual full mean geometry/profile spine changed ({mean.getAppNumArgs})"
    let m := mean.getAppArgs
    let initial := ((← body (sampling ++ `OriginalMeasuredMean.initialized)).beta m[:37].toArray).headBeta
    unless initial.isAppOfArity (sampling ++ `OriginalChoices.Mean.continuation) 62 do
      throwError "original measured kernel: original cutoff/geometry spine changed"
    forallBoundedTelescope remaining (some 6) fun later _ => do
      unless later.size == 6 do throwError "original measured kernel: expected J/rate/positive/unit, response smoothness/jets"
      k x later initial.getAppArgs m

/-- Deduce the global cut-amplitude continuity needed to construct actual D.
The proof does not mention J, upper rate, response jets, smallness or a sample. -/
elab "prove_original_cut_corrected_amplitude_continuous" : command => liftTermElabM <| withTransparency .reducible <| withRow fun x later init mean => do
  let Jfree := #[later[1]!, later[2]!, later[4]!]
  let hκΩ ← mkAppM `Set.Subset.trans #[init[36]!, init[32]!]
  let hν := mean[56]!
  let t ← inferType hν
  let A := t.getAppArgs[t.getAppNumArgs - 2]!
  unless A.isAppOfArity `JanetCartan.RawPrimary.AmplitudeGrades.Polynomial.fullLeadingNormal 13 do
    throwError "original measured kernel: original smooth leading normal missing"
  let a := A.getAppArgs
  let positive := later[2]!
  let result ← forallBoundedTelescope (← inferType positive) (some 1) fun color _ => do
    let c := color[0]!
    let inputs := a[5:12].toArray ++ #[mean[52]!, mean[53]!, a[12]!, init[33]!, init[31]!, init[34]!,
      hκΩ, mean[55]!, hν, mean[57]!, mean[58]!, mean[59]!, ← mkAppM `ne_of_gt #[mkApp positive c], mkApp later[4]! c]
    let smooth ← mkAppM `JanetCartan.Sampling.contDiff_cutCorrectedDerivativeAmplitude inputs
    mkLambdaFVars color (← mkAppM `ContDiff.continuous #[smooth])
  discard <| save `cut_amplitude_continuous (x ++ Jfree) result

def withRaw (x later init : Array Expr) (k : Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let compact := mkAppN (mkConst (ns ++ `cut_amplitude_continuous)) (x ++ #[later[1]!, later[2]!, later[4]!])
  let angle := init[39]!
  unless angle.isAppOf `JanetCartan.Sampling.originalConicDetector do
    throwError "original measured kernel: actual conic detector missing"
  let unit ← mkNumeral (mkConst ``Real) 1
  let sign := mkConst ``original_mask_unit_nonnegative
  let maskBound := mkAppN (mkConst `JanetCartan.Sampling.norm_originalConicDetectorMask_le_one) angle.getAppArgs
  let pre := mkAppN (mkConst (current ++ `mean_on_full_response))
    (x ++ later ++ #[compact, unit, sign, maskBound])
  let params := x ++ #[later[0]!, later[1]!, later[2]!, later[4]!]
  forallBoundedTelescope (← inferType pre) (some 1) fun _ tail => do
    let some D := tail.find? (fun e => e.isAppOf `JanetCartan.CanonicalRowComparison.correctedColoredCrossBandData && e.appArg! == later[0]!)
      | throwError "original measured kernel: actual same correctedColoredCrossBandData not present in mean"
    k D params

/-- The support and mask facts are the corresponding fields of the literal
native kernel. Its qualitative amplitude-bound witness is intentionally NOT
used for the common event's uniform numerical budget. -/
elab "retain_original_measured_row_kernel_field " which:num : command => liftTermElabM <| withTransparency .reducible do
  if which.getNat == 0 then
    withRow fun x later init _ => withRaw x later init fun D params => do
      discard <| save `kernel params D true
  else
    forallBoundedTelescope (← getConstInfo (ns ++ `kernel)).type (some 64) fun params _ => do
      unless params.size == 64 do throwError "original measured kernel: changed actual kernel64"
      let named := mkAppN (mkConst (ns ++ `kernel)) params
      match which.getNat with
      | 1 =>
        let proof ← mkAppM `JanetCartan.SamplingKernelBounds.BandKernelData.amplitude_eq_zero #[named]
        let type ← inferType proof
        let S := mkAppN (mkConst (sampling ++ `OriginalMeasuredFamily.support)) (params[:22].toArray.push params[40]!)
        let support ← mkAppM `JanetCartan.SamplingKernelBounds.BandKernelData.physicalSupport #[named]
        let type := type.replace fun e => if e == support then some S else none
        discard <| save `amplitude_support params proof false (some type)
      | 2 =>
        let proof ← mkAppM `JanetCartan.SamplingKernelBounds.BandKernelData.mask_le #[named]
        let type ← inferType proof
        let unit ← mkNumeral (mkConst ``Real) 1
        let bound ← mkAppM `JanetCartan.SamplingKernelBounds.BandKernelData.maskBound #[named]
        let type := type.replace fun e => if e == bound then some unit else none
        discard <| save `mask_bound params proof false (some type)
      | _ => throwError "original measured kernel: invalid kernel field"


end JanetCartan.PhysicalSampling.OriginalMeasuredKernelsApplication
end
