module

public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.Components
public import JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrimaryNorms
public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryL2
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanProfileBudgets
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceSignedCorrection
public meta import JanetCartan.Iteration.RevisedUniform.OriginalStepFields.Template
import all JanetCartan.Iteration.PhysicalPrimary.OriginalFullSourcePhysicalPrimaryL2Statement
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Apply the original physical source norms without changing the fields

This elaboration helper builds proof terms for the existing actual primary,
mean and signed-response producers at one selected52, one original cutoff
count and one finite Picard count. It introduces no mathematical record or
assumption. Its execution must provide the original numerical gate proofs
and import the actual mean and pair norm producers.

The consumer is `OriginalStepEstimates.increment_estimates_of_source_profiles`
in the actual `main:thm:step` construction. The primary L² coefficient comes
from its existing prehistory existential, not a new norm estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalStepEstimatesTemplate

open Lean Meta Elab Command

private def primaryRoot := `JanetCartan.RevisedUniform.OriginalSelectedPrimaryNorms
private def primary := `JanetCartan.PhysicalPrimary.OriginalFullSourcePhysicalPrimary
private def meanRoot := `JanetCartan.PhysicalMean.OriginalSelectedMeanProfiles
private def meanData := `JanetCartan.PhysicalMean.OriginalSelectedMeanData
private def pairRoot := `JanetCartan.PhysicalPairs.OriginalSelectedPairEstimates
private def pairProfiles := `JanetCartan.PhysicalPairs.OriginalSelectedPairProfiles

private def app (key : Name) (p : Array Expr) : Expr := mkAppN (mkConst key) p

private partial def head (e : Expr) : Expr := match e.headBeta.consumeMData with
  | .letE _ _ value body _ => head (body.instantiate1 value)
  | value => value

private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "actual step norms: missing original body {key}"
  return head (value.beta p)

/-- Choose only the scalar in the existing primary L² theorem, before every
history. The same expression is reused by the final constant and its proof. -/
def originalPrimaryL2Witness (early : Array Expr) : MetaM (Expr × Expr) := do
  unless early.size == 34 do throwError "actual step norms: primary L2 static34 changed"
  let producer := app (primary ++ `L2_profiles) early
  let type ← bodyAt (primary ++ `L2_profiles_statement) early
  unless type.isAppOfArity ``Exists 2 do
    throwError "actual step norms: original L2 prehistory existential missing"
  let args := type.getAppArgs.push producer
  let cost := mkAppN (mkConst ``Classical.choose type.getAppFn.constLevels!) args
  let spec := mkAppN (mkConst ``Classical.choose_spec type.getAppFn.constLevels!) args
  let body := head (type.getAppArgs[1]!.beta #[cost])
  unless body.isAppOfArity ``And 2 do
    throwError "actual step norms: original L2 witness lost its positivity/estimate pair"
  return (cost,spec)

/-- Metaprogramming output only. Each proof is a direct application of its
named original producer, never an assumed physical estimate. -/
structure NormInputs where
  primaryField : Expr
  meanField : Expr
  signedField : Expr
  fullSelf : Expr
  CP : Expr
  CV : Expr
  CS : Expr
  CPL2 : Expr
  hCP : Expr
  hCV : Expr
  hCS : Expr
  primaryLow : Expr
  primaryHigh : Expr
  meanAll : Expr
  signedAll : Expr
  primaryL2 : Expr

/-- Apply the genuine three original norm families on exactly one selected
construction. All supplied proof arguments are the already named numerical
initial, current, size-cap and amplitude gates. -/
def originalNormInputs (selected native a : Array Expr) (J count Cscale kCut : Expr)
    (hAux hFullW hBuffer hTensor hSigned hCap hSize hDelta : Expr) : MetaM NormInputs := do
  unless selected.size == 52 && native.size == 50 && a.size == 10 do
    throwError "actual step norms: original selected52/native50/source10 changed"
  let early := selected[:33].toArray.push count
  let n := a[0]!
  let delta := a[6]!
  let baseOrder := app `JanetCartan.RevisedScales.baselineOrder #[n]
  let highOrder ← mkAppM ``HAdd.hAdd #[baseOrder,kCut]
  let primaryField := app (primary ++ `field) (selected ++ #[count,delta])
  let meanField := app (meanData ++ `physicalMean) (selected ++ #[J,count])
  let fullSelf := app (meanData ++ `fullSampledSelf) (selected ++ #[J,count])
  let full := app `JanetCartan.PhysicalMean.OriginalCompleteForcing.selectedFullSource selected
  let run := app `JanetCartan.PhysicalMean.OriginalCanonicalSource.selected_iterateWithForcing
    (native ++ #[J,full,count])
  let signedArgs := native[:44].toArray ++ #[Cscale] ++ native[44:].toArray ++
    #[J,run,hSigned,delta]
  unless signedArgs.size == 55 do throwError "actual step norms: signed field55 changed"
  let signedField := app `JanetCartan.PhysicalPairs.OriginalSourceSignedCorrection.correction signedArgs
  let CP := app (primaryRoot ++ `CP) early
  let CV := app (meanRoot ++ `CphysicalMean) early
  let pairEarly := early ++ #[Cscale,hCap]
  let CS := app (pairRoot ++ `Csize) pairEarly
  let hCP := app (primaryRoot ++ `CP_nonneg) early
  let hCV := app (meanRoot ++ `CphysicalMean_nonneg) early
  let hCS := app (pairProfiles ++ `Csize_nonneg) pairEarly
  let hDeltaNonneg ← mkAppM ``le_of_lt #[hDelta]
  let primaryArgs := early ++ selected[33:].toArray ++ #[hAux,delta,hDeltaNonneg]
  unless primaryArgs.size == 56 do throwError "actual step norms: original primary norm56 changed"
  let primaryLow := app (primaryRoot ++ `physical_profile) (primaryArgs.push baseOrder)
  let primaryHigh := app (primaryRoot ++ `high_profile) (primaryArgs.push highOrder)
  let meanArgs := selected ++ #[hAux,count,hFullW,hBuffer,hTensor]
  let signedPrefix := selected ++ #[hAux,count,Cscale,hSigned]
  let signedAll := app (pairRoot ++ `size) (signedPrefix ++ #[hCap,hSize,delta])
  let meanAll := app (meanRoot ++ `physicalMean_sobolev_profile) meanArgs
  let (CPL2,spec) ← originalPrimaryL2Witness early
  let primaryL2 := mkAppN (.proj ``And 1 spec)
    (selected[33:].toArray ++ #[hAux,delta,hDeltaNonneg])
  -- The L² projection's target is already the named original proposition;
  -- do not unfold its giant choose_spec proof merely for this metadata guard.
  -- The enclosing actual theorem still kernel-checks that proof at the SAME P.
  for (proof,field) in #[(primaryLow,primaryField),(primaryHigh,primaryField),
      (meanAll,meanField),(signedAll,signedField)] do
    let type ← inferType proof
    unless (type.find? (· == field)).isSome do
      throwError "actual step norms: an original norm changed its SAME physical field"
  for value in #[CP,CV,CS,CPL2,hCP,hCV,hCS] do
    if value.hasLooseBVars || value.hasMVar || value.hasLevelMVar || value.hasSorry then
      throwError "actual step norms: unresolved original prehistory coefficient"
  return {
    primaryField := primaryField
    meanField := meanField
    signedField := signedField
    fullSelf := fullSelf
    CP := CP
    CV := CV
    CS := CS
    CPL2 := CPL2
    hCP := hCP
    hCV := hCV
    hCS := hCS
    primaryLow := primaryLow
    primaryHigh := primaryHigh
    meanAll := meanAll
    signedAll := signedAll
    primaryL2 := primaryL2 }

end JanetCartan.RevisedUniform.OriginalStepEstimatesTemplate
end
