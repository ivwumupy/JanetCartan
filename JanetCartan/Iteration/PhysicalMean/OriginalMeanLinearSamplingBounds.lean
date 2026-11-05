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

/-!
# Original quantitative sampling and low-source interfaces

The fixed-source consumer uses exactly ONE selected shift, the original full
positive baseline, full angular response, and J=cutoffCount(R^fineExponent),
chosen before Picard iteration. These interfaces retain the actual error rates
and the full static coefficient, including cF normalization and gamma^-1.

The low consequences have only the literal complete raw cross-response identity
from task93 explicit. They do not assume a small source error or a solver result.
The final OriginalMeanLinearSampling module must discharge that identity and
apply the canonical shared high tuple before an unconditional source release.
No sampled success record, second event, inverse or primitive factory is added.

Ctail is the absolute value of the original finite static row/inverse scalar
product. This pays no stage, sample-cardinality or cutoff-prefix growth.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSampling.SourceComparisonCommands
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling
private def estimates := `JanetCartan.PhysicalMean.OriginalMeanLinearEstimates
private def sampling := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def bodyAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "actual source normal: missing producer {n}"
  return (value.beta xs).headBeta
private def save (key : Name) (xs : Array Expr) (proof : Expr)
    (target : Option Expr := none) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars xs
    (← match target with | some t => pure t | none => inferType proof))
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual source normal {key}: extra or unresolved input"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual source normal {key}: missing producers {missing.toList}"
  let name := root ++ key
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The exact original uncut sampled normal and one-event bound, on the SAME global current, selected shift, full fixed prefix and original zero-allowed weights (new:eq:mean-operators, new:eq:source-bound)."
  logInfo m!"actual source normal {key}: original{xs.size}"
  return app name xs

elab "construct_original_linear_source_sampled_normal" : command => liftTermElabM do
  let source := estimates ++ `global_transport
  forallBoundedTelescope (← getConstInfo source).type (some 50) fun xs _ => do
    let globalProof := app source xs
    let gt ← inferType globalProof
    let globalLeading := gt.getAppArgs[2]!.appArg!.getAppArgs[4]!
    let K := globalLeading.getAppArgs.back!
    let J := app `JanetCartan.RawInputPartition.cutoffCount #[K]
    let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift xs
    let sourceArgs := xs ++ #[shift,J]
    let linear ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear sourceArgs
    unless linear.isAppOfArity `JanetCartan.PhysicalMean.fixedSourceLinear 28 do
      throwError "actual source normal: original linear28 packing changed"
    let a := linear.getAppArgs
    unless a[20]!.isAppOfArity
      `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.Q0 39 do
      throwError "actual source normal: actual global inverse39 changed"
    let sampleProof := app (sampling ++ `sampling_error) xs
    let st ← inferType sampleProof
    let sampled := st.getAppArgs[2]!.appArg!.getAppArgs[5]!
    let globalAux := sampled.getAppArgs[4]!
    let normalName := `JanetCartan.PhysicalMean.uncutSampledNormal
    let normalInfo ← getConstInfo normalName
    let sourceNormal := mkAppN (mkConst normalName (normalInfo.levelParams.map (fun _ => .zero)))
      #[a[0]!,a[1]!,a[4]!,a[7]!,a[8]!,a[9]!,a[10]!,a[11]!,
        a[13]!,a[14]!,a[15]!,a[22]!,a[26]!]
    let haux := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.global_auxiliary_eq_source xs
    let ea := (← inferType haux).getAppArgs
    let f ← withLocalDeclD `aux ea[0]! fun aux =>
      mkLambdaFVars #[aux] (sampled.replace fun e => if e == globalAux then some aux else none)
    let equality := mkAppN (mkConst ``congrArg [.succ .zero,.succ .zero])
      #[ea[0]!,← inferType sampled,ea[1]!,ea[2]!,f,haux]
    let target := mkAppN (mkConst ``Eq [.succ .zero])
      #[← inferType sampled,sampled,sourceNormal]
    let hEq ← save `sampled_eq_source xs equality (some target)
    let sa := (← inferType hEq).getAppArgs
    let predicate ← withLocalDeclD `N sa[0]! fun N =>
      mkLambdaFVars #[N] (st.replace fun e => if e == sampled then some N else none)
    let eq := mkAppN (mkConst ``congrArg [.succ .zero,.succ .zero])
      #[sa[0]!,mkSort .zero,sa[1]!,sa[2]!,predicate,hEq]
    let qa := (← inferType eq).getAppArgs
    let proof := mkAppN (mkConst ``Eq.mp [.zero]) #[qa[1]!,qa[2]!,eq,sampleProof]
    discard <| save `source_sampling_error xs proof
end JanetCartan.PhysicalMean.OriginalMeanLinearSampling.SourceComparisonCommands
end
construct_original_linear_source_sampled_normal
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.sampled_eq_source
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.source_sampling_error


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSampling
/-- Both literal original scalar error factors are nonnegative (new:eq:source-bound). -/
theorem original_error_factors_nonneg {R Ct Cs : ℝ} (hR : 1 ≤ R)
    (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs) :
    0 ≤ Ct*(R^carrierExponent)⁻¹*R^fineExponent/R^(-separationExponent) ∧
      0 ≤ Cs*R^(-((3 : ℝ)/512)) := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  exact ⟨div_nonneg (mul_nonneg (mul_nonneg hCt
    (inv_nonneg.mpr (Real.rpow_nonneg hR0 _))) (Real.rpow_nonneg hR0 _))
      (Real.rpow_nonneg hR0 _), mul_nonneg hCs (Real.rpow_nonneg hR0 _)⟩
/-- Preserve the full static inverse-gap coefficient, without replacing it by one (new:eq:source-bound). -/
theorem original_error_coefficient_nonneg {Ct Cs gamma : ℝ}
    (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs) (hgamma : 0 < gamma) :
    0 ≤ (Ct+Cs)*gamma⁻¹ :=
  mul_nonneg (add_nonneg hCt hCs) (inv_nonneg.mpr hgamma.le)
end JanetCartan.PhysicalMean.OriginalMeanLinearSampling
end
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSampling.NormalDecayCommands
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling
private def estimates := `JanetCartan.PhysicalMean.OriginalMeanLinearEstimates
private def sampling := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling
private def currentNS := `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def bodyAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "actual normal decay: missing producer {n}"
  return (value.beta xs).headBeta
private def typeAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let mut ty := (← getConstInfo n).type
  for x in xs do
    let .forallE _ _ body _ := ty.consumeMData
      | throwError "actual normal decay: explicit telescope changed at {n}"
    ty := body.instantiate1 x
  return ty
private def save (key : Name) (xs : Array Expr) (term : Expr) (data := false)
    (target : Option Expr := none) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars xs
    (← match target with | some t => pure t | none => inferType term))
  let value ← instantiateMVars (← mkLambdaFVars xs term)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual normal decay {key}: extra or unresolved input"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual normal decay {key}: missing producers {missing.toList}"
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The actual original scalar normal errors and fixed coefficient (Ct+Cs)*gamma^-1, retaining the exact sample exponent3/512 and transport31/640; no coefficient-one assumption (new:eq:source-bound)."
  logInfo m!"actual normal decay {key}: original{xs.size}"
  return app name xs
private def originalR (xs : Array Expr) : Expr :=
  app `JanetCartan.historyScale #[xs[44]!,mkConst `JanetCartan.growthExponent,xs[46]!]

elab "construct_original_linear_normal_decay" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (estimates ++ `global_transport)).type (some 50) fun xs _ => do
    let fixed := xs[:44].toArray
    let gt ← typeAt (estimates ++ `global_transport) xs
    let st ← typeAt (sampling ++ `sampling_error) xs
    let transportError := gt.getAppArgs[3]!
    let sampleError := st.getAppArgs[3]!
    let R := originalR xs
    let actualCurrent ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalCurrent.Q0 xs
    unless actualCurrent.isAppOfArity (currentNS ++ `Q0) 39 do
      throwError "actual normal decay: same global native39 missing"
    let original := actualCurrent.getAppArgs[:21].toArray
    let gamma := app (currentNS ++ `gamma) original
    let hgamma := app (currentNS ++ `gamma_pos) original
    let Ct := app (estimates ++ `Ctransport) fixed
    let Cs := app (sampling ++ `Csample) fixed
    let hCt := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Ctransport_nonneg fixed
    let auxiliary := gt.getAppArgs[2]!.appArg!.getAppArgs[5]!.getAppArgs[4]!
    let rawHCs := app
      `JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.normalized_sampling_factor_nonneg
      #[auxiliary.getAppArgs[0]!]
    let csType ← inferType rawHCs
    let hCs ← save `Csample_nonneg fixed rawHCs false
      (some (mkAppN csType.getAppFn (csType.getAppArgs.set! 3 Cs)))
    let stage := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.stage_scales xs
    let proof := app
      `JanetCartan.PhysicalMean.OriginalMeanLinearEstimatesTemplate.original_normal_error_decay
      #[R,Ct,Cs,gamma,.proj ``And 0 stage,hCt,hgamma]
    let pt ← typeAt proof.getAppFn.constName! proof.getAppArgs
    let rawCoefficient := pt.getAppArgs[3]!.getAppArgs[4]!
    let coefficient ← save `Cnormal fixed rawCoefficient true
    let hCoefficient := app (root ++ `original_error_coefficient_nonneg) #[Ct,Cs,gamma,hCt,hCs,hgamma]
    let coefficientType ← typeAt hCoefficient.getAppFn.constName! hCoefficient.getAppArgs
    discard <| save `Cnormal_nonneg fixed hCoefficient false
      (some (mkAppN coefficientType.getAppFn (coefficientType.getAppArgs.set! 3 coefficient)))
    let left := pt.getAppArgs[2]!
    let sum := left.getAppArgs[4]!
    let exactSum := mkAppN sum.getAppFn ((sum.getAppArgs.set! 4 transportError).set! 5 sampleError)
    let exactError := mkAppN left.getAppFn (left.getAppArgs.set! 4 exactSum)
    let target := (mkAppN pt.getAppFn (pt.getAppArgs.set! 2 exactError)).replace fun e =>
      if e == rawCoefficient then some coefficient else none
    discard <| save `normal_error_decay xs proof false (some target)

elab "construct_original_linear_normal_error_nonnegative" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (estimates ++ `global_transport)).type (some 50) fun xs _ => do
    let fixed := xs[:44].toArray
    let gt ← typeAt (estimates ++ `global_transport) xs
    let st ← typeAt (sampling ++ `sampling_error) xs
    let stage := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.stage_scales xs
    let proof := app (root ++ `original_error_factors_nonneg)
      #[originalR xs,app (estimates ++ `Ctransport) fixed,app (sampling ++ `Csample) fixed,
        .proj ``And 0 stage,
        app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Ctransport_nonneg fixed,
        app (root ++ `Csample_nonneg) fixed]
    let proofType ← typeAt proof.getAppFn.constName! proof.getAppArgs
    unless proofType.isAppOfArity ``And 2 do
      throwError "actual normal decay: scalar positivity conjunction changed"
    for (key,index,delta) in #[(`transport_error_nonneg,0,gt.getAppArgs[3]!),
        (`sampling_error_nonneg,1,st.getAppArgs[3]!)] do
      let part := Expr.proj ``And index proof
      let ty := proofType.getAppArgs[index]!
      let target := mkAppN ty.getAppFn (ty.getAppArgs.set! 3 delta)
      discard <| save key xs part false (some target)
end JanetCartan.PhysicalMean.OriginalMeanLinearSampling.NormalDecayCommands
end
construct_original_linear_normal_decay
construct_original_linear_normal_error_nonnegative
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.Csample_nonneg
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.Cnormal
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.Cnormal_nonneg
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.normal_error_decay
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.transport_error_nonneg
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.sampling_error_nonneg


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSampling.LowConsumerCommands
open Lean Meta Elab Command
open OriginalCanonicalInverseProfilesTemplate (withActualInverse)
private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def bodyAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "actual linear low: missing producer {n}"
  return (value.beta xs).headBeta
private def typeAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let mut ty := (← getConstInfo n).type
  for x in xs do
    let .forallE _ _ body _ := ty.consumeMData
      | throwError "actual linear low: explicit declaration telescope changed at {n}"
    ty := body.instantiate1 x
  return ty
private def save (key : Name) (xs : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars xs target)
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual linear low {key}: extra or unresolved input"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual linear low {key}: missing producers {missing.toList}"
  let name := root ++ key
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Literal u-Source.linear u for the ONE original selected shift and fixed full cutoff. All comparison/inverse/profile inputs are actual; only the complete task93 raw-action identity is explicit, for the final source consumer to discharge (new:eq:source-bound)."
  logInfo m!"actual linear low {key}: original{xs.size}; raw-action premise remains explicit until93"

/-- This isolated consequence is not an actual-low release: its sole remaining
primitive premise is exactly task93's complete raw cross-response identity.
Every current, profile, cutoff, selected event and normal estimate is actual. -/
elab "construct_original_linear_low_of_raw" : command => liftTermElabM do
  withActualInverse fun d => do
    let p := d.parameters
    let x := d.source45
    let n := x[0]!
    let two := mkNatLit 2
    let reserve := app ``Nat.mul #[two,app ``Nat.add #[app ``Nat.div #[n,two],two]]
    let sourceRoot := `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles
    let hScalar := app (sourceRoot ++ `sourceReserve_shift_le_density) #[n,x[1]!]
    let hMap := app (sourceRoot ++ `sourceReserve_shift_le_map) #[n,x[26]!,x[1]!,x[37]!]
    let originalSource := x[:38].toArray ++ #[reserve,hMap,hScalar] ++ x[38:].toArray
    let htransport := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.source_transport p
    let hsampling := app `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.source_sampling_error p
    let gt ← typeAt htransport.getAppFn.constName! p
    let st ← typeAt hsampling.getAppFn.constName! p
    let leading := gt.getAppArgs[2]!.appArg!.getAppArgs[4]!
    let corrected := gt.getAppArgs[2]!.appArg!.getAppArgs[5]!
    let K := leading.getAppArgs.back!
    let J := app `JanetCartan.RawInputPartition.cutoffCount #[K]
    let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift p
    let sourceArgs := p ++ #[shift,J]
    let linear := app `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear sourceArgs
    let rawLinear ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear sourceArgs
    unless rawLinear.isAppOfArity `JanetCartan.PhysicalMean.fixedSourceLinear 28 do
      throwError "actual linear low: fixed original source28 packing changed"
    let a := rawLinear.getAppArgs
    let hweights := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.sample_weights_nonneg
      (p.push shift)
    let rawTypes := #[a[1]!,a[3]!,a[4]!,a[6]!,a[7]!,a[8]!,a[9]!,a[10]!]
    let row := #[a[22]!,hweights,a[23]!,a[24]!,a[25]!,a[26]!,a[27]!]
    let lowName := `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Linear.low_error_of_original_row_comparisons
    let start := originalSource ++ rawTypes ++ row
    let openType ← typeAt lowName start
    let .forallE _ rawActionType _ _ := openType.consumeMData
      | throwError "actual linear low: raw-action binder changed"
    unless (rawActionType.find? (·.isAppOf
        `JanetCartan.CanonicalChange.smoothRawCrossResponse)).isSome do
      throwError "actual linear low: missing original complete cross-response premise"
    withLocalDeclD `hOriginalRawAction rawActionType fun hraw => do
      withLocalDeclD `q (mkConst ``Nat) fun q => do
        let scales := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.stage_scales p
        let hdt := app `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.transport_error_nonneg p
        let hds := app `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.sampling_error_nonneg p
        let args := start ++ #[hraw,q,K,gt.getAppArgs[3]!,st.getAppArgs[3]!,
          .proj ``And 1 scales,hdt,hds,corrected,htransport,hsampling]
        let rest ← typeAt lowName args
        let .forallE _ uType _ _ := rest.consumeMData
          | throwError "actual linear low: smooth source binder changed"
        withLocalDeclD `u uType fun u => do
          let arguments := args.push u
          let proof := app lowName arguments
          let pt ← typeAt lowName arguments
          let target := pt.replace fun e =>
            if e.isAppOfArity `JanetCartan.PhysicalMean.fixedSourceLinear 28 then some linear
            else none
          save `low_error_of_original_raw (p ++ #[hraw,q,u]) proof target
end JanetCartan.PhysicalMean.OriginalMeanLinearSampling.LowConsumerCommands
end
construct_original_linear_low_of_raw
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.low_error_of_original_raw


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSampling
open CurrentMean
/-- Pure scalar enlargement of the SAME low source RHS, retaining both scale
powers and the full before-history normal coefficient (new:eq:source-bound). -/
private theorem original_low_rhs_mono {n : ℕ} (u : SmoothResidual n) (q r : ℕ)
    {K T a A B : ℝ} (hK : 1 ≤ K) (hT : 1 ≤ T) (ha : a ≤ A) :
    a*residualSobolevSeminorm n 0 u+
      (B/K^q)*(residualSobolevSeminorm n q u+T^(q-r)*residualSobolevSeminorm n 0 u) ≤
    A*residualSobolevSeminorm n 0 u+
      (|B|/K^q)*(residualSobolevSeminorm n q u+T^(q-r)*residualSobolevSeminorm n 0 u) := by
  have hu0 : 0 ≤ residualSobolevSeminorm n 0 u := apply_nonneg _ _
  have htail : 0 ≤ residualSobolevSeminorm n q u+T^(q-r)*residualSobolevSeminorm n 0 u :=
    add_nonneg (apply_nonneg _ _) (mul_nonneg (pow_nonneg (zero_le_one.trans hT) _) hu0)
  exact add_le_add (mul_le_mul_of_nonneg_right ha hu0)
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self B)
      (pow_nonneg (zero_le_one.trans hK) _)) htail)
private theorem real_bound_trans {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  hab.trans hbc
end JanetCartan.PhysicalMean.OriginalMeanLinearSampling
end
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSampling.LowBudgetCommands
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling
private def decay := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def bodyAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "actual low budget: missing producer {n}"
  return (value.beta xs).headBeta
private def typeAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let mut ty := (← getConstInfo n).type
  for x in xs do
    let .forallE _ _ body _ := ty.consumeMData
      | throwError "actual low budget: explicit telescope changed at {n}"
    ty := body.instantiate1 x
  return ty
private def save (key : Name) (xs : Array Expr) (term : Expr) (data := false)
    (target : Option Expr := none) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars xs
    (← match target with | some t => pure t | none => inferType term))
  let value ← instantiateMVars (← mkLambdaFVars xs term)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual low budget {key}: unresolved field or late history/sample/prefix dependency"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual low budget {key}: missing producers {missing.toList}"
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Before-history nonnegative tail budget |Crow*Cinv q| and the actual coefficient-preserving decayed low bound. No R/sample/prefix count is absorbed; the sole intermediate primitive remains the exact complete task93 raw identity (new:eq:source-bound)."
  logInfo m!"actual original low budget {key}: original{xs.size}; raw identity remains93"
  return app name xs

elab "construct_original_linear_decayed_low_of_raw" : command => liftTermElabM do
  let lowName := `JanetCartan.PhysicalMean.OriginalMeanLinearSampling.low_error_of_original_raw
  forallBoundedTelescope (← getConstInfo lowName).type (some 53) fun xs lowType => do
    let orig := xs[:50].toArray
    let fixed := xs[:44].toArray
    let q := xs[51]!
    let u := xs[52]!
    unless lowType.isAppOfArity ``LE.le 4 do throwError "actual low budget: low inequality missing"
    let oldRhs := lowType.getAppArgs[3]!
    unless oldRhs.isAppOfArity ``HAdd.hAdd 6 do throwError "actual low budget: two exact errors changed"
    let main := oldRhs.getAppArgs[4]!
    let tail := oldRhs.getAppArgs[5]!
    let division := tail.getAppArgs[4]!
    unless division.isAppOfArity ``HDiv.hDiv 6 do throwError "actual low budget: fixed spectral tail missing"
    let B := division.getAppArgs[4]!
    let hAbs ← mkAppM ``abs_nonneg #[B]
    let absType ← inferType hAbs
    let absB := absType.getAppArgs[3]!
    let Ctail ← save `Ctail fixed (← mkLambdaFVars #[q] absB) true
    let namedCost := mkApp Ctail q
    let nnType ← mkForallFVars #[q] (mkAppN absType.getAppFn (absType.getAppArgs.set! 3 namedCost))
    discard <| save `Ctail_nonneg fixed (← mkLambdaFVars #[q] hAbs) false (some nnType)
    let current ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalCurrent.Q0 orig
    unless current.isAppOfArity `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.Q0 39 do
      throwError "actual low budget: original global native39 disappeared"
    let n := current.getAppArgs[0]!
    let r := app `JanetCartan.RevisedScales.sourceOrder #[n]
    let gt ← typeAt `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.source_transport orig
    let K := gt.getAppArgs[2]!.appArg!.getAppArgs[4]!.getAppArgs.back!
    let T := app `JanetCartan.currentCoefficientScale #[orig[44]!,orig[46]!]
    let stage := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.stage_scales orig
    let hInitial := app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed
    let initialType ← typeAt hInitial.getAppFn.constName! fixed
    unless initialType.isAppOfArity ``LE.le 4 do
      throwError "actual low budget: original initial threshold changed"
    let hR0 := app ``real_bound_trans
      #[initialType.getAppArgs[2]!,initialType.getAppArgs[3]!,orig[44]!,hInitial,orig[45]!]
    let hT := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
      #[orig[44]!,hR0,orig[46]!]
    let hdecay := app (decay ++ `normal_error_decay) orig
    let decayType ← typeAt (decay ++ `normal_error_decay) orig
    let monoArgs := #[n,u,q,r,K,T,main.getAppArgs[4]!,decayType.getAppArgs[3]!,B,
      .proj ``And 1 stage,hT,hdecay]
    let mono := app ``original_low_rhs_mono monoArgs
    let monoType ← typeAt ``original_low_rhs_mono monoArgs
    let newRhs := monoType.getAppArgs[3]!
    let proof := app ``real_bound_trans
      #[lowType.getAppArgs[2]!,oldRhs,newRhs,app lowName xs,mono]
    let target := (mkAppN lowType.getAppFn (lowType.getAppArgs.set! 3 newRhs)).replace fun e =>
      if e == absB then some namedCost else none
    discard <| save `low_error_decay_of_original_raw xs proof false (some target)
end JanetCartan.PhysicalMean.OriginalMeanLinearSampling.LowBudgetCommands
end
construct_original_linear_decayed_low_of_raw
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.Ctail
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.Ctail_nonneg
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSampling.low_error_decay_of_original_raw
