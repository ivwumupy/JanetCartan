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

/-!
# Actual original fixed-source profiles

These checked interfaces feed the literal original linear source low defect and
all-order high estimate (new:sec:mean-source-equation, new:eq:source-bound).
The auxiliary, carrier-index and leading-normal identities preserve the SAME
positive global current, full baseline, common cutoffs and fixed original sample.
The high budget uses the authoritative shared static dictionary; no second
primitive factory, sampled success premise or replacement operator is introduced.

The before-history44 dependency audit does not itself claim uniformity over
accuracy choices. The auxiliary jet theorem requires only Saux <= Rinit; the
fixed-reference reach producer supplies that numerical comparison separately.
This leaf intentionally has no SamplingCore or dynamic raw-response prerequisite.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.AuxiliaryCommands
open Lean Meta Elab Command
open OriginalCanonicalInverseProfilesTemplate (withActualInverse)
private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles
private def auxiliary := `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Auxiliary
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def save (key : Name) (params : Array Expr) (term : Expr) (data := false)
    (target : Option Expr := none) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars params
    (← match target with | none => inferType term | some ty => pure ty))
  let value ← instantiateMVars (← mkLambdaFVars params term)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "original auxiliary {key}: unresolved or extra parameter"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "original auxiliary {key}: missing producers {missing.toList}"
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual original auxiliary source reserve/coefficient, before history; the later bound uses the SAME current and only Saux <= Rinit (new:eq:source-bound)."
  logInfo m!"actual auxiliary {key}: native{params.size}"
  return app name params

elab "construct_original_linear_source_auxiliary" : command => liftTermElabM do
  withActualInverse fun d => do
    let p := d.parameters
    let x := d.source45
    let n := x[0]!
    let two := mkNatLit 2
    let reserve := app ``Nat.mul #[two,app ``Nat.add #[app ``Nat.div #[n,two],two]]
    let sourceRoot := `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles
    let hScalar := app (sourceRoot ++ `sourceReserve_shift_le_density) #[n,x[1]!]
    let hMap := app (sourceRoot ++ `sourceReserve_shift_le_map) #[n,x[26]!,x[1]!,x[37]!]
    let actual := x[:38].toArray ++ #[reserve,hMap,hScalar] ++ x[38:].toArray
    unless actual.size == 48 do throwError "original auxiliary: fixed source48 packing changed"
    let static := actual[:41].toArray
    let fixed := p[:44].toArray
    let S := app (auxiliary ++ `S) static
    let C := app (auxiliary ++ `Ccoef) static
    let namedS ← save `Saux fixed S true
    let namedC ← save `Ccoef fixed C true
    let hS := app (auxiliary ++ `hS) static
    let hC := app (auxiliary ++ `Ccoef_nonneg) static
    discard <| save `hSaux fixed hS false
      (some ((← inferType hS).replace fun e => if e == S then some namedS else none))
    discard <| save `Ccoef_nonneg fixed hC false
      (some ((← inferType hC).replace fun e => if e == C then some namedC else none))
    let some producer := (← getConstInfo (auxiliary ++ `exists_profiles)).value? (allowOpaque := true)
      | throwError "original auxiliary: coefficient-profile producer missing"
    let dependencies := (Lean.collectFVars {} (producer.beta static).headBeta).fvarSet
    for parameter in fixed do
      if dependencies.contains parameter.fvarId! then
        logInfo m!"Saux literal producer depends on static label: {(← parameter.fvarId!.getDecl).userName}"
end JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.AuxiliaryCommands
end
construct_original_linear_source_auxiliary
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Saux
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Ccoef
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.hSaux
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Ccoef_nonneg


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.AuxiliaryJetCommands
open Lean Meta Elab Command
open OriginalCanonicalInverseProfilesTemplate (withActualInverse)
private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles
private def auxiliary := `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Auxiliary
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
/-- Specialize the already explicit declaration telescope. The kernel still
checks the final term; no deep definitional-equality search is performed here. -/
private def typeAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let mut ty := (← getConstInfo n).type
  for x in xs do
    let .forallE _ _ body _ := ty.consumeMData
      | throwError "actual auxiliary jets: original explicit telescope changed at {n}"
    ty := body.instantiate1 x
  return ty
elab "construct_original_linear_source_auxiliary_jets" : command => liftTermElabM do
  withActualInverse fun d => do
    let p := d.parameters
    let x := d.source45
    let n := x[0]!
    let two := mkNatLit 2
    let reserve := app ``Nat.mul #[two,app ``Nat.add #[app ``Nat.div #[n,two],two]]
    let sourceRoot := `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles
    let hScalar := app (sourceRoot ++ `sourceReserve_shift_le_density) #[n,x[1]!]
    let hMap := app (sourceRoot ++ `sourceReserve_shift_le_map) #[n,x[26]!,x[1]!,x[37]!]
    let actual := x[:38].toArray ++ #[reserve,hMap,hScalar] ++ x[38:].toArray
    unless actual.size == 48 do throwError "actual auxiliary jets: source48 packing changed"
    let static := actual[:41].toArray
    let fixed := p[:44].toArray
    let C := app (auxiliary ++ `Ccoef) static
    let namedS := app (root ++ `Saux) fixed
    let namedC := app (root ++ `Ccoef) fixed
    let reachType ← typeAt (root ++ `hSaux) fixed
    unless reachType.isAppOfArity ``LE.le 4 do
      throwError "actual auxiliary jets: numerical reach order changed"
    let hReachedType := mkAppN reachType.getAppFn
      ((reachType.getAppArgs.set! 2 namedS).set! 3 p[44]!)
    withLocalDeclD `hAuxiliaryReached hReachedType fun reached => do
      let arguments := actual.push reached
      let hc := app (auxiliary ++ `coefficient_smooth) arguments
      let hi := app (auxiliary ++ `image_jets) arguments
      let he := app (auxiliary ++ `exterior_jets) arguments
      let hcType ← typeAt (auxiliary ++ `coefficient_smooth) arguments
      let hiType ← typeAt (auxiliary ++ `image_jets) arguments
      let heType ← typeAt (auxiliary ++ `exterior_jets) arguments
      let inner := mkAppN (mkConst ``And.intro) #[hiType,heType,hi,he]
      let oldType := mkApp2 (mkConst ``And) hcType (mkApp2 (mkConst ``And) hiType heType)
      let proof := mkAppN (mkConst ``And.intro)
        #[hcType,mkApp2 (mkConst ``And) hiType heType,hc,inner]
      let some oldCoefficient := hcType.find? (·.isAppOfArity
        `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.coefficient 39)
        | throwError "actual auxiliary jets: unchanged global coefficient missing"
      let actualCoefficient := app
        `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.coefficient d.native39
      let target := oldType.replace fun e =>
        if e == oldCoefficient then some actualCoefficient
        else if e == C then some namedC else none
      let params := p.push reached
      let type ← instantiateMVars (← mkForallFVars params target)
      let value ← instantiateMVars (← mkLambdaFVars params proof)
      let env ← getEnv
      for e in #[type,value] do
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
          throwError "actual auxiliary jets: extra or unresolved input"
        let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
        unless missing.isEmpty do throwError "actual auxiliary jets: missing producers {missing.toList}"
      let name := root ++ `actual_jets
      addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
      addDocStringCore name "All-order auxiliary jets of the SAME actual global current, under only the numerical original initial-radius reach (new:eq:source-bound)."
      logInfo "actual original auxiliary smooth coefficient/image+exterior jets: native50 plus Saux≤Rinit only"
end JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.AuxiliaryJetCommands
end
construct_original_linear_source_auxiliary_jets
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.actual_jets


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles
/-- The original physical initial threshold pays both current scale and the
fixed rounded cutoff, before any Picard iteration. -/
theorem original_stage_scales {R₀ : ℝ} (hR₀ : 2 ≤ R₀) (j : ℕ) :
    1 ≤ historyScale R₀ growthExponent j ∧
      1 ≤ historyScale R₀ growthExponent j ^ fineExponent := by
  have hR₀' : 1 ≤ R₀ := (by norm_num : (1 : ℝ) ≤ 2).trans hR₀
  have hR : 1 ≤ historyScale R₀ growthExponent j := hR₀'.trans (le_historyScale hR₀' j)
  exact ⟨hR,Real.one_le_rpow hR (by norm_num [fineExponent, meanSlack])⟩
end JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles
end
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.NumericalCommands
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles
private def estimates := `JanetCartan.PhysicalMean.OriginalMeanLinearEstimates
private def comparison := `JanetCartan.PhysicalMean.OriginalMeanLinearComparison
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def bodyAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "actual normal numeric: missing producer {n}"
  return (value.beta xs).headBeta
private def save (key : Name) (xs : Array Expr) (proof : Expr)
    (target : Option Expr := none) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars xs
    (← match target with | some t => pure t | none => inferType proof))
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual normal numeric {key}: extra or unresolved input"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual normal numeric {key}: missing producers {missing.toList}"
  let name := root ++ key
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual original transport budget positivity or fixed physical-stage admission; no sample or prefix count is absorbed (new:eq:source-bound)."
  logInfo m!"actual normal numeric {key}: original{xs.size}"

elab "construct_original_linear_transport_cost_nonnegative" : command => liftTermElabM do
  let source := estimates ++ `global_transport
  forallBoundedTelescope (← getConstInfo source).type (some 50) fun xs _ => do
    let fixed := xs[:44].toArray
    let ct := app (estimates ++ `Ctransport) fixed
    let raw ← bodyAt (estimates ++ `Ctransport) fixed
    let sum := raw.getAppArgs[5]!
    unless sum.isAppOfArity ``Finset.sum 5 do
      throwError "actual transport cost: original comparison sum missing"
    let sa := sum.getAppArgs
    unless sa[3]!.isAppOfArity ``Finset.univ 2 do
      throwError "actual transport cost: original full finite-index enumeration changed"
    let hC ← lambdaTelescope sa[4]! fun ix _ => do
      unless ix.size == 1 do throwError "actual transport cost: row binder changed"
      mkLambdaFVars ix (app (comparison ++ `Ccompare_positive) (fixed ++ ix))
    let gt ← inferType (app source xs)
    let auxiliary := gt.getAppArgs[2]!.appArg!.getAppArgs[5]!.getAppArgs[4]!
    let n := auxiliary.getAppArgs[0]!
    let name := `JanetCartan.PhysicalMean.OriginalMeanLinearSamplingTemplate.normalized_transport_factor_nonneg
    let info ← getConstInfo name
    let proof := mkAppN (mkConst name (info.levelParams.map (fun _ => .zero)))
      #[n,sa[0]!,sa[3]!.getAppArgs[1]!,sa[4]!,hC]
    let rawType ← inferType proof
    let target := mkAppN rawType.getAppFn (rawType.getAppArgs.set! 3 ct)
    save `Ctransport_nonneg fixed proof (some target)

elab "construct_original_linear_stage_scales" : command => liftTermElabM do
  let source := estimates ++ `global_transport
  forallBoundedTelescope (← getConstInfo source).type (some 50) fun xs _ => do
    let hInitial := app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS xs[:44].toArray
    let hR ← mkAppM ``le_trans #[hInitial,xs[45]!]
    let proof := app (root ++ `original_stage_scales) #[xs[44]!,hR,xs[46]!]
    save `stage_scales xs proof
end JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.NumericalCommands
end
construct_original_linear_transport_cost_nonnegative
construct_original_linear_stage_scales
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Ctransport_nonneg
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.stage_scales


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.SourceAuxiliaryCommands
open Lean Meta Elab Command
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def bodyAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "actual source auxiliary: missing producer {n}"
  return (value.beta xs).headBeta
/-- Only syntactically identical native operands and the definitional natural
number dimension conversion are allowed; the native analytic functions are
never unfolded by this congruence proof. -/
private partial def nativeCongr (a b : Expr) : MetaM Expr := do
  if a == b then return ← mkHEqRefl a
  let aType ← inferType a
  if aType.isConstOf ``Nat then return ← mkHEqRefl a
  unless a.isApp && b.isApp && a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs do
    throwError "actual source auxiliary: changed native data, not a dimension spelling"
  let congr ← mkHCongrWithArity a.getAppFn a.getAppNumArgs
  let aa := a.getAppArgs
  let ba := b.getAppArgs
  let mut arguments := #[]
  for j in [0:aa.size] do
    let heq ← nativeCongr aa[j]! ba[j]!
    let proof ← match congr.argKinds[j]! with
      | .eq => mkEqOfHEq heq
      | .heq => pure heq
      | _ => throwError "actual source auxiliary: dependent congruence kind changed"
    arguments := arguments ++ #[aa[j]!,ba[j]!,proof]
  return mkAppN congr.proof arguments

elab "construct_original_linear_source_auxiliary_identity" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalMean.OriginalMeanLinearEstimates.global_transport
  forallBoundedTelescope (← getConstInfo source).type (some 50) fun xs _ => do
    let globalType ← inferType (app source xs)
    let globalAux := globalType.getAppArgs[2]!.appArg!.getAppArgs[5]!.getAppArgs[4]!
    let current ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalCurrent.Q0 xs
    unless current.isAppOfArity
      `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.Q0 39 do
      throwError "actual source auxiliary: global current39 changed"
    let native := current.getAppArgs
    let image := app `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.image native
    let exterior := app `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.exterior native[:21].toArray
    let sourceAux := app `JanetCartan.CurrentMean.preparationAuxiliaryOutput
      #[native[0]!,image,exterior]
    let heq ← nativeCongr globalAux sourceAux
    let proof ← mkEqOfHEq heq
    let target := mkAppN (mkConst ``Eq [.succ .zero])
      #[← inferType globalAux,globalAux,sourceAux]
    let type ← instantiateMVars (← mkForallFVars xs target)
    let value ← instantiateMVars (← mkLambdaFVars xs proof)
    let env ← getEnv
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
        throwError "actual source auxiliary: extra or unresolved input"
      let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
      unless missing.isEmpty do throwError "actual source auxiliary: missing producers {missing.toList}"
    let name := `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.global_auxiliary_eq_source
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
    addDocStringCore name "The global transport auxiliary is exactly the original source auxiliary: only the definitional dimension spelling is transported, without unfolding analytic selectors (new:eq:mean-operators)."
    logInfo "actual transport auxiliary = original global-source auxiliary by native-argument congruence only"
end JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.SourceAuxiliaryCommands
end
construct_original_linear_source_auxiliary_identity
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.global_auxiliary_eq_source


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles
universe u
/-- The enumeration structure is unique on the unchanged original carrier
index; this statement changes neither the carriers nor their values. -/
theorem fintype_heq_of_type_eq {I J : Type u} (h : I = J)
    (f : Fintype I) (g : Fintype J) : HEq f g := by
  subst J
  exact heq_of_eq (Subsingleton.elim _ _)
end JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles
end
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.SourceIndexCommands
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def bodyAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "actual source index: missing producer {n}"
  return (value.beta xs).headBeta
private def save (key : Name) (xs : Array Expr) (proof target : Expr) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars xs target)
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual source index {key}: extra or unresolved input"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual source index {key}: missing producers {missing.toList}"
  let name := root ++ key
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The unchanged original carrier index and its unique finite enumeration, at the literal fixed-source operator (new:eq:mean-operators)."
  logInfo m!"actual source index {key}: original{xs.size}"
  return app name xs
elab "construct_original_linear_source_carrier_index" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalMean.OriginalMeanLinearEstimates.global_transport
  forallBoundedTelescope (← getConstInfo source).type (some 50) fun xs _ => do
    let globalType ← inferType (app source xs)
    let leading := globalType.getAppArgs[2]!.appArg!.getAppArgs[4]!
    let ga := leading.getAppArgs
    let K := ga.back!
    let J := app `JanetCartan.RawInputPartition.cutoffCount #[K]
    let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift xs
    let linear ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear (xs ++ #[shift,J])
    unless linear.isAppOfArity `JanetCartan.PhysicalMean.fixedSourceLinear 28 do
      throwError "actual source index: original source28 changed"
    let a := linear.getAppArgs
    let target ← mkEq ga[1]! a[2]!
    let hI ← save `carrier_index_eq_source xs (← mkEqRefl ga[1]!) target
    let hF := mkAppN (mkConst (root ++ `fintype_heq_of_type_eq) [.zero])
      #[ga[1]!,a[2]!,hI,ga[2]!,a[5]!]
    discard <| save `carrier_fintype_heq_source xs hF (← inferType hF)
end JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.SourceIndexCommands
end
construct_original_linear_source_carrier_index
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.carrier_index_eq_source
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.carrier_fintype_heq_source


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.SourceTransportCommands
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles
private def estimates := `JanetCartan.PhysicalMean.OriginalMeanLinearEstimates
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def bodyAt (n : Name) (xs : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo n).value? (allowOpaque := true)
    | throwError "actual source normal: missing producer {n}"
  return (value.beta xs).headBeta
private partial def nativeCongr (a b : Expr) (path : String := "root") : MetaM Expr := do
  if a == b then return ← mkHEqRefl a
  let aType ← inferType a
  if aType.isConstOf ``Nat then return ← mkHEqRefl a
  if a.isLambda && b.isLambda then
    return ← lambdaTelescope a fun xs body => do
      let other := (b.beta xs).headBeta
      let heq ← nativeCongr body other (path ++ "/lambda")
      let mut proof ← mkEqOfHEq heq
      for x in xs.reverse do
        proof ← mkAppM ``funext #[← mkLambdaFVars #[x] proof]
      mkHEqOfEq proof
  unless a.isApp && b.isApp && a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs do
    let head (e : Expr) := if e.getAppFn.isConst then e.getAppFn.constName!.toString
      else if e.isLambda then "lambda" else if e.isForall then "forall" else "other"
    throwError "actual source normal: changed operand at {path}; left={head a}/{a.getAppNumArgs}, right={head b}/{b.getAppNumArgs}"
  let congr ← mkHCongrWithArity a.getAppFn a.getAppNumArgs
  let aa := a.getAppArgs
  let ba := b.getAppArgs
  let mut arguments := #[]
  for j in [0:aa.size] do
    let heq ← nativeCongr aa[j]! ba[j]! (path ++ "/" ++ toString j)
    let proof ← match congr.argKinds[j]! with
      | .eq => mkEqOfHEq heq
      | .heq => pure heq
      | _ => throwError "actual source normal: dependent congruence kind changed"
    arguments := arguments ++ #[aa[j]!,ba[j]!,proof]
  return mkAppN congr.proof arguments
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
  addDocStringCore name "The actual original leading transport bound on the literal SAME source coefficient, carriers, exterior, inverse data and fixed cutoff (new:eq:source-bound)."
  logInfo m!"actual source normal {key}: original{xs.size}"
  return app name xs

elab "construct_original_linear_source_normal " mode:num : command => liftTermElabM do
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
    let native := a[20]!.getAppArgs
    unless a[20]!.isAppOfArity
      `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.Q0 39 do
      throwError "actual source normal: actual global inverse39 changed"
    if mode.getNat == 0 then
      let image := app `JanetCartan.PhysicalMean.OriginalMeanLinearProfiles.Current.image native
      let sourceLeading := mkAppN (mkConst `JanetCartan.PhysicalMean.leadingCarrierCutNormal [.zero])
        #[a[0]!,a[2]!,a[5]!,image,a[19]!,a[15]!,K]
      let congr ← mkHCongrWithArity globalLeading.getAppFn 7
      let ga := globalLeading.getAppArgs
      let sa := sourceLeading.getAppArgs
      let mut nativeArgs := #[]
      for j in [0:7] do
        let heq ← if j == 1 then
          mkHEqOfEq (app (root ++ `carrier_index_eq_source) xs)
        else if j == 2 then
          pure (app (root ++ `carrier_fintype_heq_source) xs)
        else nativeCongr ga[j]! sa[j]!
        let proof ← match congr.argKinds[j]! with
          | .eq => mkEqOfHEq heq
          | .heq => pure heq
          | _ => throwError "actual source normal: leading congruence kind changed"
        nativeArgs := nativeArgs ++ #[ga[j]!,sa[j]!,proof]
      let equality ← mkEqOfHEq (mkAppN congr.proof nativeArgs)
      let hEq ← save `leading_eq_source xs equality
      let ea := (← inferType hEq).getAppArgs
      let predicate ← withLocalDeclD `N ea[0]! fun N =>
        mkLambdaFVars #[N] (gt.replace fun e => if e == globalLeading then some N else none)
      let eq := mkAppN (mkConst ``congrArg [.succ .zero,.succ .zero])
        #[ea[0]!,mkSort .zero,ea[1]!,ea[2]!,predicate,hEq]
      let qa := (← inferType eq).getAppArgs
      let proof := mkAppN (mkConst ``Eq.mp [.zero]) #[qa[1]!,qa[2]!,eq,globalProof]
      discard <| save `source_transport xs proof
    else throwError "actual source transport: only the checked leading stage is published"
end JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.SourceTransportCommands
end
construct_original_linear_source_normal 0
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.leading_eq_source
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.source_transport


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
public meta section
namespace JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.HighBudgetCommands
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles
private def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def get (fields : Array (Name × Expr)) (key : Name) : MetaM Expr := do
  let some (_,e) := fields.find? (·.1 == key)
    | throwError "actual linear high: shared static tuple lacks {key}"
  return e
private def save (key : Name) (xs : Array Expr) (term target : Expr) (data := false) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars xs target)
  let value ← instantiateMVars (← mkLambdaFVars xs term)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual linear high {key}: later source/history/sample or unresolved input"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "actual linear high {key}: missing producers {missing.toList}"
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The linear all-order source budget chosen before history from the ONE shared static dictionary, actual global inverse cost and actual auxiliary coefficient cost; dynamic source instantiation remains separate (new:eq:source-bound)."
  logInfo m!"actual linear high static {key}: original{xs.size}"
  return app name xs

/-- Freeze the all-order LINEAR budget from the SAME static dictionary as89,
actual100 inverse budget and actual auxiliary coefficient budget. The final
history instance is a separate obligation, never assumed here. -/
elab "construct_original_linear_source_high_budget" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear
  let sourceInfo ← getConstInfo source
  let some sourceBody := sourceInfo.value? (allowOpaque := true)
    | throwError "actual linear high: literal source52 missing"
  forallBoundedTelescope sourceInfo.type (some 52) fun xs _ => do
    let linear := (sourceBody.beta xs).headBeta
    unless linear.isAppOfArity `JanetCartan.PhysicalMean.fixedSourceLinear 28 do
      throwError "actual linear high: original source28 packing changed"
    let a := linear.getAppArgs
    let fixed := xs[:44].toArray
    let fields ← OriginalMeanQuadraticRealization.staticFieldsAt fixed
    let Cinv := app `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles.Cinv fixed
    let hCinv := app `JanetCartan.PhysicalMean.OriginalCanonicalInverseProfiles.Cinv_nonneg fixed
    let Ccoef := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Ccoef fixed
    let hCcoef := app `JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Ccoef_nonneg fixed
    let M := mkApp Ccoef (mkNatLit 0)
    let hM := mkApp hCcoef (mkNatLit 0)
    let arguments := #[a[0]!,a[2]!,a[5]!,M,hM,Cinv,Ccoef,← get fields `Badj,← get fields `p,
      hCinv,hCcoef,← get fields `hBadj,← get fields `hp,← get fields `χ,← get fields `hχ,
      ← get fields `hχs,← get fields `hχcell,← get fields `Rbox,← get fields `hRbox,
      ← get fields `Ctest,← get fields `hCtest]
    let name := `JanetCartan.PhysicalMean.exists_fixedSourceLinear_source_profile
    let info ← getConstInfo name
    let levels := info.levelParams.map (fun _ => Level.zero)
    let proof := mkAppN (mkConst name levels) arguments
    let mut resultType := info.type.instantiateLevelParams info.levelParams levels
    for v in arguments do
      let .forallE _ _ body _ := resultType.consumeMData
        | throwError "actual linear high: static high-profile telescope changed"
      resultType := body.instantiate1 v
    while resultType.isLet do resultType := resultType.letBody!.instantiate1 resultType.letValue!
    unless resultType.isAppOfArity ``Exists 2 do
      throwError "actual linear high: static coefficient existential changed"
    let existsProof ← save `high_profiles_exists fixed proof resultType
    let et := resultType.getAppArgs
    let choose := mkAppN (mkConst ``Classical.choose [.succ .zero]) #[et[0]!,et[1]!,existsProof]
    let C ← save `Chigh fixed choose et[0]! true
    let spec := mkAppN (mkConst ``Classical.choose_spec [.succ .zero]) #[et[0]!,et[1]!,existsProof]
    let specType := (mkApp et[1]! C).headBeta
    unless specType.isAppOfArity ``And 2 do
      throwError "actual linear high: high-profile continuation changed"
    discard <| save `Chigh_nonneg fixed (.proj ``And 0 spec) specType.getAppArgs[0]!
    discard <| save `high_continuation fixed (.proj ``And 1 spec) specType.getAppArgs[1]!
end JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.HighBudgetCommands
end
construct_original_linear_source_high_budget
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.high_profiles_exists
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Chigh
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.Chigh_nonneg
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.high_continuation

#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.original_stage_scales
#print axioms JanetCartan.PhysicalMean.OriginalMeanLinearSourceProfiles.fintype_heq_of_type_eq
