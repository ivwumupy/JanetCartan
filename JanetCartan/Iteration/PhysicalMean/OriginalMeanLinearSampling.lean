module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSelection
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearEstimatesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSelectionApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularity
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSelectionApplication
public meta import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearEstimatesTemplate
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
public meta import JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
public meta import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
public meta import JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularity
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate
public meta import JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfilesTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfilesTemplate
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfilesTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearEstimates
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSamplingTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearEstimatesTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCurrent
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCurrentApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearComparisonBudgets
public meta import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSamplingTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourceLinear
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalLinearApplication
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalLinearApplication
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticStatic
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticStatic
public meta import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticStatic
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSamplingCore
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSourceProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalParameterRemainders
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanLinearSamplingBounds
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticPrimitives
public meta import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticPrimitives
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowRawIdentity

/-!
# Actual original mean source estimates

This final consumer uses the ONE original selected shift, the full positive
baseline and uncut angular response, the SAME global39 current inverse, and
J=cutoffCount(R^fineExponent), fixed before Picard N. The complete original raw
cross-response identity is applied from its actual selected51 producer; it is
not an assumption of the resulting low or high estimate.

The high application consumes the ONE canonical original primitive tuple and
its real measured-row identity, retaining the full original weighted mask and
zero-allowed weights. Cnormal, Ctail and Chigh are the frozen before-history
budgets; no scale, sample-cardinality or cutoff-prefix count is absorbed.
The three genuine high numerical reach/moment guards remain explicit for the
original prehistory construction to discharge. The high order-zero term is
converted exactly to the residual seminorm, without coefficient loss.

Consumer: the fixed-forcing finite Picard source in new:eq:source-bound and
new:sec:mean-source-equation. No second sampler, inverse, primitive factory or
success event is constructed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSampling
open PhysicalSamplingShells CurrentMean
/-- The actual full weighted mask can be nonzero only on the original mask.
Zero sample weights remain allowed (new:eq:source-bound). -/
theorem weighted_mask_nonzero_base {n : ℕ} {I B : Type}
    (w : I → ℝ) (m : (I × B) × Euclidean (n-1) → ℝ)
    (z : (I × B) × Euclidean (n-1))
    (hz : originalWeightedHalfMask w m z ≠ 0) : m z ≠ 0 := by
  intro hzero
  apply hz
  simp only [originalWeightedHalfMask, hzero, zero_mul, mul_zero]
/-- The original high-frequency exclusion is unchanged by the full mask. -/
theorem weighted_mask_high {n : ℕ} {I B : Type}
    (w : I → ℝ) (m : (I × B) × Euclidean (n-1) → ℝ)
    (hhigh : ∀ z, ‖z.2‖ ≤ 1 → m z = 0)
    (z : (I × B) × Euclidean (n-1))
    (hz : originalWeightedHalfMask w m z ≠ 0) : 1 ≤ ‖z.2‖ := by
  exact (lt_of_not_ge (fun hle ↦ weighted_mask_nonzero_base w m z hz (hhigh z hle))).le
/-- The fixed source reserve contributes no power at order zero. -/
theorem zero_order_source_factor (C T : ℝ) (r : ℕ) : C*T^(0-r) = C := by simp
/-- The actual high source RHS uses exactly the same order-zero seminorm as
its low defect; no coefficient or power is lost (new:eq:source-bound). -/
private theorem source_high_rhs_zero {n : ℕ} (e : SmoothResidual n) (C T : ℝ) (s r : ℕ) :
    C*(residualSobolevSeminorm n s e + T^(s-r)*‖smoothResidualToL2 n e‖) =
    C*(residualSobolevSeminorm n s e + T^(s-r)*residualSobolevSeminorm n 0 e) := by
  rw [residualSobolevSeminorm_zero]
end JanetCartan.PhysicalMean.OriginalMeanLinearSampling
end
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSampling.HighCommands
open Lean Meta Elab Command
open PhysicalBackground.NativeReferenceSourceTemplate (termWith)
private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling
private def budgets := `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles
private def auxiliary := `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def get (fs : Array (Name × Expr)) (k : Name) : MetaM Expr := do
  let some (_,v) := fs.find? (·.1 == k) | throwError "actual linear high: missing original field {k}"
  return v
private def typeAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let mut ty := (← getConstInfo n).type
  for x in xs do
    let .forallE _ _ body _ := ty.consumeMData
      | throwError "actual linear high: explicit telescope changed at {n}"
    ty := body.instantiate1 x
  return ty
private def save (key : Name) (xs : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars xs target)
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual linear high {key}: unresolved or extraneous field"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual linear high {key}: missing producers {missing.toList}"
  addDecl (.thmDecl {name := root ++ key,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore (root ++ key) "Actual original source high estimate and exact normal identity, with the complete raw response applied on the SAME canonical tuple, shift, baseline and prefix (new:eq:source-bound)."
  logInfo m!"actual linear high {key}: original{xs.size}; actual93 raw identity applied; no remaining analytic primitive"
private def zeroBound (high C T n : Expr) : MetaM Expr := do
  let hz := mkApp high (mkNatLit 0)
  let tz ← inferType hz
  let mut leaf := tz
  while leaf.isForall do leaf := leaf.bindingBody!
  unless leaf.isAppOfArity ``LE.le 4 do throwError "actual linear high: zero jet bound disappeared"
  let delta := leaf.getAppArgs[3]!
  if delta.hasLooseBVars then throwError "actual linear high: zero coefficient depends on a point"
  let r := app `JanetCartan.RevisedScales.sourceOrder #[n]
  let heq := app (root ++ `zero_order_source_factor) #[mkApp C (mkNatLit 0),T,r]
  let eqa := (← inferType heq).getAppArgs
  let predicate ← withLocalDeclD `bound (mkConst ``Real) fun b =>
    mkLambdaFVars #[b] (tz.replace fun e => if e == delta then some b else none)
  let heqP := mkAppN (mkConst ``congrArg [.succ .zero,.succ .zero])
    #[mkConst ``Real,mkSort .zero,eqa[1]!,eqa[2]!,predicate,heq]
  let pa := (← inferType heqP).getAppArgs
  return mkAppN (mkConst ``Eq.mp [.zero]) #[pa[1]!,pa[2]!,heqP,hz]

/-- All actual fields and the genuine93 complete raw identity are applied to the
SAME original tuple. No raw-response or high-estimate premise remains. -/
public def publishOriginalHigh (p : Array Expr) (fs : Array (Name × Expr)) : MetaM Unit := do
  unless p.size == 53 do throwError "actual linear high: shared native50+guards+prefix changed"
  let orig := p[:50].toArray
  let fixed := p[:44].toArray
  let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift orig
  let sourceArgs := orig ++ #[shift,p[52]!]
  let sourceName := `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear
  let some sourceBody := (← getConstInfo sourceName).value? (allowOpaque := true)
    | throwError "actual linear high: source52 missing"
  let rawLinear := (sourceBody.beta sourceArgs).headBeta
  unless rawLinear.isAppOfArity `JanetCartan.PhysicalMean.fixedSourceLinear 28 do
    throwError "actual linear high: original source28 changed"
  let a := rawLinear.getAppArgs
  let native := a[20]!.getAppArgs
  unless a[20]!.isAppOfArity `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.Q0 39 do
    throwError "actual linear high: original global39 inverse changed"
  let hrow ← get fs `hrow
  let rowType ← inferType hrow
  let some row := rowType.find? (·.isAppOf `JanetCartan.PhysicalMean.nativeMeasuredRow)
    | throwError "actual linear high: same measured full row absent"
  let some input := rowType.find? (·.isAppOf `JanetCartan.PhysicalSamplingShells.sampledShellEquiv)
    | throwError "actual linear high: same original sampled scalar isometry absent"
  let ci ← getConstInfo row.getAppFn.constName!
  let mut rt := ci.type.instantiateLevelParams ci.levelParams row.getAppFn.constLevels!
  let mut rowFields := #[]
  let mut rowClasses := #[]
  for value in row.getAppArgs do
    let .forallE k domain body bi := rt.consumeMData
      | throwError "actual linear high: measured-row parameter telescope changed"
    if bi == .instImplicit then rowClasses := rowClasses.push (domain.getAppFn.constName!,value)
    else rowFields := rowFields.push (k.eraseMacroScopes,value)
    rt := body.instantiate1 value
  let n := a[0]!
  let Ccoef := app (auxiliary ++ `Ccoef) fixed
  let T ← get fs `T
  let reachBase ← typeAt (auxiliary ++ `hSaux) fixed
  let reachType := mkAppN reachBase.getAppFn
    ((reachBase.getAppArgs.set! 2 (app (auxiliary ++ `Saux) fixed)).set! 3 p[44]!)
  withLocalDeclD `hAuxiliaryReached reachType fun hAux => do
    let jets := app (auxiliary ++ `actual_jets) (orig.push hAux)
    let hi := Expr.proj ``And 0 (.proj ``And 1 jets)
    let he := Expr.proj ``And 1 (.proj ``And 1 jets)
    let consumer := budgets ++ `high_continuation
    let mut args := fixed ++ #[T,← get fs `hT,a[11]!,a[12]!,a[13]!,a[14]!,a[15]!,
      a[16]!,a[17]!,a[18]!,← zeroBound hi Ccoef T n,hi,← zeroBound he Ccoef T n,he,
      a[19]!,a[20]!,a[21]!,
      app `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.Q0_regular native,
      app `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles.paired_profile orig]
    args := args ++ #[a[1]!,← get rowFields `ι,a[3]!,a[4]!,a[6]!,
      ← get rowClasses ``Fintype,← get rowClasses ``MetricSpace,← get rowClasses ``DiscreteTopology,
      ← get rowClasses ``MeasurableSpace,← get rowClasses ``BorelSpace,
      a[7]!,a[8]!,a[9]!,a[10]!,a[22]!,← get fs `hweight,a[23]!,a[24]!,a[25]!,a[26]!,a[27]!]
    let rawType ← typeAt consumer args
    let .forallE _ rawAction _ _ := rawType.consumeMData
      | throwError "actual linear high: exact raw-action binder changed"
    unless (rawAction.find? (·.isAppOf `JanetCartan.CanonicalChange.smoothRawCrossResponse)).isSome do
      throwError "actual linear high: missing task93's exact primitive identity"
    let rawName := `JanetCartan.PhysicalMean.OriginalCanonicalRow.hraw_original_sample
    discard <| getConstInfo rawName
    let hraw := app rawName (orig.push p[52]!)
    args := args ++ #[hraw,← get rowFields `μ]
    for _ in [0:2] do
      let ty ← typeAt consumer args
      let .forallE _ d _ .instImplicit := ty.consumeMData
        | throwError "actual linear high: native measure instance changed"
      args := args.push (← get rowClasses d.getAppFn.constName!)
    let eqType ← typeAt consumer args
    let .forallE _ inputType _ _ := eqType.consumeMData
      | throwError "actual linear high: real scalar input equivalence changed"
    unless inputType.isAppOf ``LinearIsometryEquiv do
      throwError "actual linear high: unchanged real input isometry type missing"
    let originalInputType ← inferType input
    let originalInputArgs := originalInputType.getAppArgs.push input
    let originalInputLevels := originalInputType.getAppFn.constLevels!
    let toLinear := mkAppN (mkConst ``LinearIsometryEquiv.toLinearEquiv originalInputLevels) originalInputArgs
    let normMap := mkAppN (mkConst ``LinearIsometryEquiv.norm_map' originalInputLevels) originalInputArgs
    let realLinear ← mkAppM ``LinearEquiv.restrictScalars #[mkConst ``Real,toLinear]
    let eInput := mkAppN (mkConst ``LinearIsometryEquiv.mk inputType.getAppFn.constLevels!)
      (inputType.getAppArgs ++ #[realLinear,normMap])
    args := args ++ #[eInput,← get rowFields `φ,← get fs `Φ,← get rowFields `a,← get rowFields `m,
      ← get rowFields `hφ,← get fs `hΦ,← get rowFields `ha,← get rowFields `hm,← get rowFields `hms]
    let weight := a[22]!
    let mask ← get fs `m
    let maskType ← inferType mask
    let .forallE _ zType _ _ := maskType.consumeMData
      | throwError "actual linear high: original mask domain changed"
    let zparts := zType.getAppArgs
    let sigma := zparts[0]!
    let sigmaparts := sigma.getAppArgs
    let maskArgs := #[n,sigmaparts[0]!,sigmaparts[1]!,weight,mask]
    let high := app (root ++ `weighted_mask_high) (maskArgs.push (← get fs `hhigh))
    args := args ++ #[high,← get rowFields `K,← get rowFields `hK,← get rowFields `has]
    let adapt (args : Array Expr) (key : Name) (binders : Nat) : MetaM Expr := do
      let ty ← typeAt consumer args
      let .forallE _ goal _ _ := ty.consumeMData
        | throwError "actual linear high: weighted-mask obligation {key} changed"
      forallBoundedTelescope goal (some binders) fun z _ => do
        let point ← if binders == 2 then pure z[0]! else
          mkAppM ``Prod.mk #[z[z.size-3]!,z[z.size-2]!]
        let hbase := app (root ++ `weighted_mask_nonzero_base) (maskArgs ++ #[point,z.back!])
        mkLambdaFVars z (mkAppN (← get fs key) (z.pop.push hbase))
    args := args.push (← adapt args `hagree 2)
    args := args ++ #[← get fs `L,← get fs `hL,← get fs `hχK,← get fs `hbox,
      ← get fs `Tfull,← get fs `hTfull,← get fs `hφs]
    args := args.push (← adapt args `hphase 2)
    args := args.push (← adapt args `haj 4)
    args := args.push (← adapt args `hLj 3)
    args := args.push (← adapt args `hΦj 3)
    args := args ++ #[← get fs `hTfullBound,hrow]
    let finalType ← typeAt consumer args
    forallBoundedTelescope finalType (some 2) fun es target => do
      let proof := app consumer (args ++ es)
      let linear := app sourceName sourceArgs
      let target := target.replace fun e =>
        if e.isAppOfArity `JanetCartan.PhysicalMean.fixedSourceLinear 28 then some linear else none
      save `source_spec_prefix (p ++ #[hAux] ++ es) proof target
end JanetCartan.PhysicalMean.OriginalMeanLinearSampling.HighCommands
end


public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSampling.SourceClosureCommands
open Lean Meta
private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling
private def profiles := `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles
private def rawName := `JanetCartan.PhysicalMean.OriginalCanonicalRow.hraw_original_sample
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def typeAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let mut ty := (← getConstInfo n).type
  for x in xs do
    let .forallE _ _ body _ := ty.consumeMData
      | throwError "actual source closure: exact telescope changed at {n}"
    ty := body.instantiate1 x
  return ty
private def bodyAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "actual source closure: missing original body {n}"
  return (value.beta xs).headBeta
private def fullPrefix (p : Array Expr) : MetaM Expr := do
  let gt ← typeAt (profiles ++ `source_transport) p
  let K := gt.getAppArgs[2]!.appArg!.getAppArgs[4]!.getAppArgs.back!
  return app `JanetCartan.RawInputPartition.cutoffCount #[K]
private def save (key : Name) (xs : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars xs target)
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual source closure {key}: unclosed input or remaining raw premise"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual source closure {key}: missing actual producer {missing.toList}"
  let name := root ++ key
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual original fixed source estimate at ONE selected shift and J=cutoffCount(R^fineExponent), with the complete raw identity and shared physical tuple discharged. The source, cutoff and event are fixed before Picard N (new:eq:source-bound)."
  logInfo m!"actual source closure {key}: original{xs.size}; no raw/source-estimate premise"

/-- Apply the genuine selected51 raw identity to the checked decayed low53. -/
public def publishOriginalLow : MetaM Unit := do
  discard <| getConstInfo rawName
  let lowName := root ++ `low_error_decay_of_original_raw
  forallBoundedTelescope (← getConstInfo lowName).type (some 50) fun p _ => do
    let J ← fullPrefix p
    let hraw := app rawName (p.push J)
    let args := p.push hraw
    forallBoundedTelescope (← typeAt lowName args) (some 2) fun qu target => do
      save `low_error (p ++ qu) (app lowName (args ++ qu)) target

/-- Fix the prefix before iteration, and convert the high source RHS exactly
from L² norm to the order-zero residual seminorm. -/
public def publishOriginalHighFull : MetaM Unit := do
  let specName := root ++ `source_spec_prefix
  forallBoundedTelescope (← getConstInfo specName).type (some 56) fun xs _ => do
    let p := xs[:50].toArray
    let J ← fullPrefix p
    let args := xs.set! 52 J
    let spec := app specName args
    let specType ← typeAt specName args
    unless specType.isAppOfArity ``And 2 do
      throwError "actual source high closure: full source specification changed"
    let highType := specType.getAppArgs[0]!
    unless highType.isAppOfArity ``LE.le 4 do
      throwError "actual source high closure: true source seminorm estimate missing"
    let current ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalCurrent.Q0 p
    unless current.isAppOfArity `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.Q0 39 do
      throwError "actual source high closure: same global39 current changed"
    let n := current.getAppArgs[0]!
    let e := xs[54]!
    let s := xs[55]!
    let C := mkApp (app (profiles ++ `Chigh) p[:44].toArray) s
    let T := app `JanetCartan.currentCoefficientScale #[p[44]!,p[46]!]
    let r := app `JanetCartan.RevisedScales.sourceOrder #[n]
    let eqArgs := #[n,e,C,T,s,r]
    let hEq := app ``source_high_rhs_zero eqArgs
    let eqType ← typeAt ``source_high_rhs_zero eqArgs
    let ea := eqType.getAppArgs
    let predicate ← withLocalDeclD `rhs (mkConst ``Real) fun z =>
      mkLambdaFVars #[z] (mkAppN highType.getAppFn (highType.getAppArgs.set! 3 z))
    let eqPred := mkAppN (mkConst ``congrArg [.succ .zero,.succ .zero])
      #[mkConst ``Real,mkSort .zero,ea[1]!,ea[2]!,predicate,hEq]
    let oldType := mkApp predicate ea[1]!
    let newType := mkApp predicate ea[2]!
    let proof := mkAppN (mkConst ``Eq.mp [.zero])
      #[oldType,newType,eqPred,Expr.proj ``And 0 spec]
    let target := mkAppN highType.getAppFn (highType.getAppArgs.set! 3 ea[2]!)
    let retained := xs[:52].toArray ++ xs[53:].toArray
    save `high_error retained proof target
end JanetCartan.PhysicalMean.OriginalMeanLinearSampling.SourceClosureCommands
end

run_meta do
  JanetCartan.PhysicalMean.OriginalMeanLinearSampling.SourceClosureCommands.publishOriginalLow
run_meta do
  JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives
    JanetCartan.PhysicalMean.OriginalMeanLinearSampling.HighCommands.publishOriginalHigh
run_meta do
  JanetCartan.PhysicalMean.OriginalMeanLinearSampling.SourceClosureCommands.publishOriginalHighFull
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.low_error
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.source_spec_prefix
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.high_error
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.weighted_mask_nonzero_base
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.weighted_mask_high
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.zero_order_source_factor
