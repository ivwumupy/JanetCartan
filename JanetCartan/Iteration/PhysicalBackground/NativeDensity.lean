module

public import JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public import JanetCartan.Iteration.PhysicalInverseContinuity.Original
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.IncidenceSourceDomain
public meta import Lean

/-!
# The literal uncut density of the original current raw initializer

Apply the synthesis producer to `StrongDatum.Original.rawCurrent` and its
proved all-order membership. The actual current carrier and external weight
are extracted from its literal measured datum. No carrier, raw inverse, source,
current chart or weight is chosen again. Fourier constants are chosen using
only the original canonical masks, before σ and every physical history.
The smooth density is chosen once and the physical affine mean uses that same
representative (`app:ch_background:eq:bg-density-input`). The source-smallness
and current-profile joins remain separate obligations of the positive parent.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 2400000

public meta section
namespace JanetCartan.PhysicalBackground.NativeDensityApplication
open Lean Meta Elab Command Term

def nativeNS := `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original
def resultNS := `JanetCartan.PhysicalBackground.NativeDensity

def store (name : Name) (params : Array Expr) (value : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let rawType ← inferType value
  let target := target?.getD rawType
  unless ← isDefEq target rawType do throwError "native density: target mismatch {name}"
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← mkForallFVars params target)
  if value.hasMVar || type.hasMVar || value.hasFVar || type.hasFVar ||
      value.hasLevelMVar || type.hasLevelMVar || value.hasSorry || type.hasSorry then
    throwError "native density: incomplete or non-original declaration {name}"
  let name := resultNS ++ name
  if data then
    addDecl (.defnDecl { name, type, value, levelParams := [], hints := .abbrev, safety := .safe })
      (forceExpose := true)
  else
    addDecl (.thmDecl { name, type, value, levelParams := [] }) (forceExpose := true)
  return mkAppN (mkConst name) params

def project (name : Name) (d : Expr) : MetaM Expr :=
  mkAppM (`JanetCartan.ContinuumRow.CarrierData ++ name) #[d]

elab "construct_original_uncut_density" : command => liftTermElabM do
  let rawInfo ← getConstInfo (nativeNS ++ `rawCurrent)
  forallTelescope rawInfo.type fun params _ => do
    let native (field : Name) := mkAppN (mkConst (nativeNS ++ field)) params
    let datumInfo ← getConstInfo (nativeNS ++ `measuredDatum)
    let datum := (datumInfo.value! (allowOpaque := true)).beta params
    let some mean := datum.find? (·.isAppOfArity `JanetCartan.PositiveBackground.physicalDensityMean 7) |
      throwError "native density: the literal measured datum has no physical-density mean"
    let n := mean.getAppArgs[0]!
    let N := mean.getAppArgs[1]!
    let index := mean.getAppArgs[2]!
    let inst := mean.getAppArgs[3]!
    let actualData := mean.getAppArgs[4]!
    let weights := mean.getAppArgs[5]!
    let d ← store `carrier params actualData true
    let χ ← store `weight params weights true
    let raw ← store `raw params (native `rawCurrent) true
    let regularity := native `rawCurrent_mem
    let regType := (← inferType regularity).replace fun e =>
      if e == native `rawCurrent then some raw else none
    let hraw ← store `raw_mem params regularity false (some regType)
    let (z, θ, a, w, ha, hw) ← withLocalDeclD `i index fun i => do
      let dataAt := (mkApp actualData i).headBeta
      let some mask := dataAt.find? (·.isAppOfArity `JanetCartan.ContinuumRow.CanonicalConic.angularMask 7) |
        throwError "native density: no retained canonical mask in actual carrier body ({dataAt.getAppFn.constName!})"
      let fields ← mask.getAppArgs[1:].toArray.mapM fun e => return ← mkLambdaFVars #[i] e
      pure (fields[0]!, fields[1]!, fields[2]!, fields[3]!, fields[4]!, fields[5]!)
    let densities := native `all_densities
    let (Kin, hKin) ← forallBoundedTelescope (← inferType densities) (some 5) fun densityParams _ => do
      unless densityParams.size == 5 do throwError "native density: original density class changed"
      forallBoundedTelescope (← inferType densityParams[4]!) (some 1) fun ix body => do
        let some norm := body.find? (·.isAppOf `JanetCartan.cNorm) |
          throwError "native density: missing original initial-label seminorm"
        let args := norm.getAppArgs
        let K := args[args.size-3]!
        unless K.isAppOf ``Metric.closedBall do throwError "native density: label set is not the original closed ball"
        let kargs := K.getAppArgs
        let compact ← mkAppM `ProperSpace.isCompact_closedBall #[kargs[kargs.size-2]!, kargs.back!]
        pure (← mkLambdaFVars ix K, ← mkLambdaFVars ix compact)
    let fixed := params[:21].toArray
    let estimates := mkAppN (mkConst `JanetCartan.PhysicalBackground.canonicalDensityEstimates)
      #[n, N, index, inst, z, θ, a, w, ha, hw, Kin, hKin]
    let C ← store `C fixed (← mkAppM ``Classical.choose #[estimates]) true
    let chosenType := (← whnf (← inferType estimates)).appArg!.beta #[C]
    let chosen ← store `mask_spec fixed (← mkAppM ``Classical.choose_spec #[estimates]) false (some chosenType)
    discard <| store `C_pos fixed (.proj ``And 0 chosen)
    let construct ← store `construct fixed (.proj ``And 1 chosen)
    let hangular ← withLocalDeclD `i index fun i => do
      mkLambdaFVars #[i] (← mkEqRefl (← project `angularCutoff (mkApp d i)))
    let hhigh ← withLocalDeclD `i index fun i => do
      mkLambdaFVars #[i] (← mkEqRefl (← project `highCutoff (mkApp d i)))
    let positive := mkAppN construct #[d, hangular, hhigh, raw, hraw]
    let existsDensity ← store `exists_density params positive
    let v ← store `v params (← mkAppM ``Classical.choose #[existsDensity]) true
    let specType := (← whnf (← inferType existsDensity)).appArg!.beta #[v]
    let spec ← store `spec params (← mkAppM ``Classical.choose_spec #[existsDensity]) false (some specType)
    let smooth ← store `smooth params (.proj ``And 0 spec)
    let tail := Expr.proj ``And 1 spec
    let ae ← store `ae params (.proj ``And 0 tail)
    let tail := Expr.proj ``And 1 tail
    discard <| store `ae_all_positions params (.proj ``And 0 tail)
    let tail := Expr.proj ``And 1 tail
    discard <| store `global_estimate params (.proj ``And 0 tail)
    let tail := Expr.proj ``And 1 tail
    discard <| store `jet_estimate params (.proj ``And 0 tail)
    discard <| store `label_estimate params (.proj ``And 1 tail)
    -- This is an explicitly conditional consequence, not source-smallness:
    -- the positive parent must still prove the displayed bound on its actual h0.
    let κ := params[37]!
    let fixedLow := fixed ++ #[κ]
    let admission := mkAppN (mkConst `JanetCartan.PhysicalBackground.canonicalDensityAdmission)
      #[n, N, index, inst, z, θ, a, w, ha, hw, Kin, hKin, κ]
    let CAdm ← store `admissionC fixedLow (← mkAppM ``Classical.choose #[admission]) true
    let admType := (← whnf (← inferType admission)).appArg!.beta #[CAdm]
    let admSpec ← store `admission_mask_spec fixedLow
      (← mkAppM ``Classical.choose_spec #[admission]) false (some admType)
    let thresholdExists := Expr.proj ``And 1 admSpec
    let δ ← store `threshold fixedLow (← mkAppM ``Classical.choose #[thresholdExists]) true
    let thresholdType := (← whnf (← inferType thresholdExists)).appArg!.beta #[δ]
    let thresholdSpec ← store `threshold_spec fixedLow
      (← mkAppM ``Classical.choose_spec #[thresholdExists]) false (some thresholdType)
    discard <| store `threshold_pos fixedLow (.proj ``And 0 thresholdSpec)
    let admitted := mkAppN (.proj ``And 1 thresholdSpec) #[d, hangular, hhigh, raw, hraw]
    forallBoundedTelescope (← inferType admitted) (some 1) fun small _ => do
      let otherExists := mkAppN admitted small
      let other ← mkAppM ``Classical.choose #[otherExists]
      let otherSpec ← mkAppM ``Classical.choose_spec #[otherExists]
      let otherSmooth := Expr.proj ``And 0 otherSpec
      let otherAE := Expr.proj ``And 0 (.proj ``And 1 otherSpec)
      let equality ← withLocalDeclD `i index fun i => do
        let aeEq ← mkAppM `Filter.EventuallyEq.trans
          #[mkApp otherAE i, ← mkAppM `Filter.EventuallyEq.symm #[mkApp ae i]]
        let hOpen ← mkAppM `JanetCartan.PhysicalBackground.densityCarrierMeasure_open_pos #[n]
        let pointEq ← withLetDecl `carrierOpenPos (← inferType hOpen) hOpen fun localInstance => do
          let result ← withLocalInstances [← localInstance.fvarId!.getDecl] <|
            mkAppM `MeasureTheory.Measure.eq_of_ae_eq
              #[aeEq, ← mkAppM `ContDiff.continuous #[mkApp otherSmooth i],
                ← mkAppM `ContDiff.continuous #[mkApp smooth i]]
          return result.replaceFVar localInstance hOpen
        mkAppM ``funext #[← mkLambdaFVars #[i] pointEq]
      let otherType ← inferType otherSpec
      let predicate ← withLocalDeclD `w (← inferType v) fun t =>
        mkLambdaFVars #[t] (otherType.replace fun e => if e == other then some t else none)
      let propEq ← mkAppM ``congrArg #[predicate, equality]
      let same ← mkAppM ``Eq.mp #[propEq, otherSpec]
      discard <| store `admission_from_raw_small (params ++ small) same
    let physical := mkAppN mean.getAppFn
      #[n, N, index, inst, d, χ, v]
    discard <| store `physicalMean params physical true
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[params[0]!, params[1]!, params[20]!]
    let selected := fixed.set! 20 capped
    let selectedField (name : Name) := mkAppN
      (mkConst (`JanetCartan.PhysicalSeed.SelectedBoundary ++ name)) selected
    let hD := mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.hD)
      #[params[0]!, params[1]!]
    let nonempty ← mkAppM `JanetCartan.ContinuumInverse.retained_incidence_channel_nonempty
      #[params[1]!, .proj ``And 0 hD, selectedField `centers, selectedField `εcover,
        selectedField `fact5, selectedField `fact7]
    let sampleIndex ← store `geometryIndex fixed (← mkAppM ``Classical.choice #[nonempty]) true
    unless ← isDefEq (← inferType sampleIndex) index do
      throwError "native density: geometric certificate index is not the same selected index"
    let mut current := mkApp (native `current) sampleIndex
    for _ in [:5] do
      if current.getAppFn.isConstOf `JanetCartan.PhysicalPrimary.LeadingCell.current then break
      let name := current.getAppFn.constName!
      let some body := (← getConstInfo name).value? (allowOpaque := true) |
        throwError "native density: current definition unavailable {name}"
      current := (body.beta current.getAppArgs).headBeta
    unless current.isAppOfArity `JanetCartan.PhysicalPrimary.LeadingCell.current 36 do
      throwError "native density: actual leading-cell current signature changed"
    let currentArgs := current.getAppArgs
    discard <| store `current_hF_on params currentArgs[31]!
    discard <| store `current_immersion params currentArgs[32]!
    discard <| store `current_fullNormalRank params currentArgs[33]!
    logInfo "constructed actual native h0/density/Hp; constants use original21 only, no inverse or source replaced"

end JanetCartan.PhysicalBackground.NativeDensityApplication
end

construct_original_uncut_density
