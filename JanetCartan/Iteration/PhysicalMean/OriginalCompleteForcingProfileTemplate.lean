module
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSelected
public import JanetCartan.Iteration.PhysicalMean.OriginalLeadingContinuumProfileTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSelected
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcing
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSelected

/-!
# Join the original selected full forcing profiles

The actual source retains the signed leading-minus-corrected comparison.
Combine its sharp T-scale estimate with the existing R-scale sample-and-target
profile, using only the genuine T ≤ R. The named complete budget is selected
before the smoothing accuracy, history and target DATA (`new:eq:mean-source`,
`new:eq:source-bound`).

This leaf constructs the genuine complete budget before target accuracy and
history. The application leaf still must supply the checked original comparison
profile; no comparison or successful-source hypothesis is added to that actual
theorem. All command metadata is elaborated before generated declarations,
keeping the compilation boundary small.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalCompleteForcing
open CurrentMean

/-- Preserve the genuine leading comparison in the complete source
(`new:eq:mean-source`). -/
theorem completeSource_eq_partial_add_comparison {n : ℕ}
    (leading target sampledSelf quadrature : SmoothResidual n) :
    completeSource leading target sampledSelf =
      sumMeasuredSample quadrature target + leadingComparison leading quadrature sampledSelf := by
  rw [completeSource_eq_three_summands leading target sampledSelf quadrature]
  unfold sumMeasuredSample
  abel

/-- Combine the actual partial profile and sharp comparison profile. The
comparison must come from its original-data producer (`new:eq:source-bound`). -/
theorem completeSource_profile_of_partial {n : ℕ} (R₀ : ℝ) (hR₀ : 2 ≤ R₀)
    (j q : ℕ) (leading target sampledSelf quadrature : SmoothResidual n)
    (Q E : ℝ) (hE : 0 ≤ E) :
    let R := iterationScale R₀ growthExponent j
    let T := currentCoefficientScale R₀ j
    let h := R ^ (-separationExponent)
    let e := q - RevisedScales.sourceOrder n
    residualSobolevSeminorm n q (sumMeasuredSample quadrature target) ≤ Q*h*R^e →
    residualSobolevSeminorm n q (leadingComparison leading quadrature sampledSelf) ≤ E*h*T^e →
    residualSobolevSeminorm n q (completeSource leading target sampledSelf) ≤ (Q+E)*h*R^e := by
  intro R T h e hpartial hcomparison
  have hfacts := fixedPicard_history_scale_facts hR₀ j
  have hT : 0 ≤ T := zero_le_one.trans hfacts.2.1
  have hh : 0 ≤ h := hfacts.2.2.2.1
  have hcomparisonR : E*h*T^e ≤ E*h*R^e :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT hfacts.2.2.1 _)
      (mul_nonneg hE hh)
  rw [completeSource_eq_partial_add_comparison]
  exact (((residualSobolevSeminorm n q).add_le' _ _).trans
    (add_le_add hpartial (hcomparison.trans hcomparisonR))).trans_eq (by ring)
private theorem fullSourceCost_nonneg (Q E : ℝ) (hQ : 0 ≤ Q) (hE : 0 ≤ E) :
    0 ≤ Q + E := add_nonneg hQ hE

end JanetCartan.PhysicalMean.OriginalCompleteForcing
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalCompleteForcingProfileTemplate
open Lean Meta Elab Command
open OriginalSelectedMeasuredAssembly (withTarget withHistory tel save)
open OriginalBackgroundHermitianTemplate (bodyAt)
private def ns := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def quad := `JanetCartan.PhysicalMean.OriginalPeriodicBackground
private def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args

/-- Close the same complete budget on selected33, before history and target
DATA. The fixed44 comparison budget is applied to the original selected data. -/
def publishBudget (comparisonBudget : Name) : MetaM Unit :=
  withTransparency .reducible <| withHistory fun p vars => do
    unless p.size == 50 && vars.size == 39 do throwError "full forcing: changed native50/selected39"
    let fixed := vars[:33].toArray
    let nativeFixed := p[:44].toArray
    withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
      let Q := mkApp (app (ns ++ `selectedSampleTargetBudget) fixed) q
      let E := mkApp (app comparisonBudget nativeFixed) q
      let sum ← mkAppM ``HAdd.hAdd #[Q,E]
      save `selectedFullSourceBudget fixed (← mkLambdaFVars #[q] sum)
        (← mkArrow (mkConst ``Nat) (mkConst ``Real)) true

/-- Prove positivity using only the already-closed static33 budget. No native
history, target, or large dependent equality is reconstructed for this scalar fact. -/
def publishBudgetNonneg (comparisonBudget comparisonNonneg : Name) : MetaM Unit :=
  withTransparency .reducible do
    tel (← getConstInfo (ns ++ `selectedFullSourceBudget)).type 33 fun fixed _ => do
      withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
        let sum := ((← bodyAt (ns ++ `selectedFullSourceBudget) fixed).beta #[q]).headBeta
        unless sum.isAppOfArity ``HAdd.hAdd 6 do throwError "full forcing: changed budget sum"
        let Q := sum.getAppArgs[4]!
        let E := sum.getAppArgs[5]!
        unless Q.isAppOfArity (ns ++ `selectedSampleTargetBudget) 34 &&
            E.isAppOfArity comparisonBudget 45 do
          throwError "full forcing: changed original budget operands"
        let hQ := app (ns ++ `selectedSampleTargetBudget_nonneg) Q.getAppArgs
        let hE := app comparisonNonneg E.getAppArgs
        let proof := app ``JanetCartan.PhysicalMean.OriginalCompleteForcing.fullSourceCost_nonneg #[Q,E,hQ,hE]
        let type ← inferType proof
        unless type.isAppOfArity ``LE.le 4 do throwError "full forcing: changed nonnegative budget"
        let named := mkApp (app (ns ++ `selectedFullSourceBudget) fixed) q
        let target := mkAppN type.getAppFn (type.getAppArgs.set! 3 named)
        save `selectedFullSourceBudget_nonneg fixed (← mkLambdaFVars #[q] proof)
          (← mkForallFVars #[q] target)

/-- Apply the genuine original selected comparison and partial profiles to the
literal complete source, not a replacement or a conditional source witness. -/
def publishProfile (comparisonBudget comparisonNonneg comparisonProfile : Name) : MetaM Unit :=
  withTransparency .reducible <| withTarget fun p vars _ _ => do
    unless p.size == 50 && vars.size == 52 do throwError "full forcing: changed native50/selected52"
    let a := (← bodyAt (ns ++ `measured_target) p).getAppArgs
    let leading := app (ns ++ `leadingMean) p
    let sampledSelf := app (ns ++ `selectedSampleSelf) p
    let sample := app (quad ++ `selected_forcing) p
    let target := app (ns ++ `selectedMeasuredTarget) vars
    let rawSource := app (ns ++ `completeSource) #[a[0]!,leading,target,sampledSelf]
    let namedSource := app (ns ++ `selectedFullSource) vars
    let fixed := vars[:33].toArray
    let nativeFixed := p[:44].toArray
    withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
      let Q := mkApp (app (ns ++ `selectedSampleTargetBudget) fixed) q
      let E := mkApp (app comparisonBudget nativeFixed) q
      let hE := mkApp (app comparisonNonneg nativeFixed) q
      let hPartial := mkApp (app (ns ++ `selected_sample_and_target_profile) vars) q
      let hComparison := mkApp (app comparisonProfile p) q
      let proof := app (ns ++ `completeSource_profile_of_partial)
        #[a[0]!,a[5]!,a[6]!,a[7]!,q,leading,target,sampledSelf,sample,Q,E,hE,hPartial,hComparison]
      let type ← inferType proof
      unless type.isAppOfArity ``LE.le 4 do throwError "full forcing: changed source profile"
      let rhs := type.getAppArgs[3]!
      unless rhs.isAppOfArity ``HMul.hMul 6 && rhs.getAppArgs[4]!.isAppOfArity ``HMul.hMul 6 do
        throwError "full forcing: lost original h*R^e scale"
      let rawCost := rhs.getAppArgs[4]!.getAppArgs[4]!
      unless rawCost.isAppOfArity ``HAdd.hAdd 6 && rawCost.getAppArgs[4]! == Q && rawCost.getAppArgs[5]! == E do
        throwError "full forcing: missing actual partial/comparison costs"
      let namedCost := mkApp (app (ns ++ `selectedFullSourceBudget) fixed) q
      let statement := type.replace fun e =>
        if e == rawCost then some namedCost else if e == rawSource then some namedSource else none
      unless (statement.find? (· == namedSource)).isSome && (statement.find? (· == namedCost)).isSome do
        throwError "full forcing: lost the original full source or fixed budget"
      save `selected_full_source_profile vars (← mkLambdaFVars #[q] proof)
        (← mkForallFVars #[q] statement)
end JanetCartan.PhysicalMean.OriginalCompleteForcingProfileTemplate
end

public meta section
open Lean Elab Command
run_cmd liftTermElabM do
  JanetCartan.PhysicalMean.OriginalCompleteForcingProfileTemplate.publishBudget `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Ccomparison
run_cmd liftTermElabM do
  JanetCartan.PhysicalMean.OriginalCompleteForcingProfileTemplate.publishBudgetNonneg `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Ccomparison `JanetCartan.PhysicalMean.OriginalLeadingContinuumProfile.Ccomparison_nonneg
end

#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.completeSource_eq_partial_add_comparison
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.completeSource_profile_of_partial
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedFullSourceBudget
#print axioms JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedFullSourceBudget_nonneg
