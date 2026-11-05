module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryForward
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticPrimitives
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticApplication
public import JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate

/-! The uncontracted BEFORE-B forward amplitude for the SAME native physical
moment field. Only the matrix amplitude is replaced by the actual independently
proved raw matrix; ψ, κ, carrier, affine covector shift, Fourier normalization,
scale and sample remain literal. This is not a relabeling of corrected G or an
estimate obtained from its response (main:eq:primary-strain). -/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPrimary.OriginalRawForwardSliceApplication
open Lean Meta Elab Command
private def ns := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward
private def actual := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def save (key : Name) (p : Array Expr) (value : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual raw slice: unresolved field {key}"
  let name := ns ++ key
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  liftM <| IO.eprintln s!"actual raw slice: checking {key}/{p.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "SAME original53 before-B raw forward amplitude and its true coefficient-scale physical jets; static budgets are fixed before history and samples. The independently proved raw matrix is not a corrected-response profile (main:eq:primary-strain; app:ch_regular:eq:source-tail)."
  logInfo m!"actual raw slice: checked {key}/{p.size}"

elab "check_actual_raw_forward_slice " which:num : command => liftTermElabM do
  let mode := which.getNat
  unless mode < 10 do throwError "actual raw slice: unknown field"
  let info ← getConstInfo (actual ++ `forwardAmplitude)
  forallBoundedTelescope info.type (some 53) fun p _ => do
    let original := ((info.value! (allowOpaque := true)).beta p).headBeta
    unless original.isAppOfArity (actual ++ `forwardSlice) 7 do
      throwError "actual raw slice: original literal forward slice changed"
    let a := original.getAppArgs
    let n := a[0]!
    let N := a[1]!
    let ψ := a[2]!
    let base := p[:52].toArray
    let B := app (ns ++ `cutAmplitude) base
    let sliceArgs := a.set! 3 B
    let slice := app (actual ++ `forwardSlice) sliceArgs
    let fixed := p[:44].toArray
    let row := fixed.push p[50]!
    let sampler ← PhysicalSampling.OriginalBareScaleApplication.originalSampler p[:24].toArray
    let hψ := app `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.observation_smooth sampler
    let hψK := app `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.observation_support sampler
    let K := (← inferType hψK).getAppArgs.back!
    let hB := app (ns ++ `cutSmooth) base
    let AB := app (ns ++ `cutCost) row
    let hAB := app (ns ++ `cutCost_nonneg) row
    if mode == 0 then save `forwardAmplitude p slice true
    else if mode == 1 then
      save `forwardSmooth p (app (actual ++ `forwardSlice_contDiff)
        #[n,N,ψ,B,hψ,hB,a[4]!,a[5]!,a[6]!])
    else if mode == 2 then
      save `forwardSupport p (app (actual ++ `forwardSlice_tsupport) sliceArgs)
    else if mode == 3 then
      let ka := K.getAppArgs
      let hK ← mkAppM ``ProperSpace.isCompact_closedBall #[ka[ka.size-2]!,ka.back!]
      let hr := app (actual ++ `mean_kernel_reserve_le_original) #[n]
      let order := (← inferType hr).getAppArgs
      let rK := order[order.size-2]!
      let rpar := order.back!
      let scale := app `JanetCartan.currentCoefficientScale #[p[44]!,p[46]!]
      let hR ← mkAppM `le_trans #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed,p[45]!]
      let hScale := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
        #[p[44]!,hR,p[46]!]
      let bound := app (actual ++ `observedForwardAmplitude_jets_on_compact)
        #[n,N,rK,rpar,ψ,B,hψ,hB,AB,hAB,scale,hScale,hr,app (ns ++ `cutJets) base,K,hK]
      let value ← forallBoundedTelescope (← inferType slice) (some 3) fun v _ => do
        let shifted ← mkAppM ``HAdd.hAdd #[a[5]!,← mkAppM ``HSMul.hSMul #[a[6]!,v[2]!]]
        let q ← mkAppM ``Prod.mk #[a[4]!,shifted]
        mkLambdaFVars v (mkAppN bound #[q,v[0]!,v[1]!])
      save `forwardJets p value
    else if mode == 4 then
      let Aψ ← withLocalDeclD `j (mkConst ``Nat) fun j => do
        mkLambdaFVars #[j] (← mkAppM `JanetCartan.cNorm #[K,j,ψ])
      save `forwardCost row (app (actual ++ `observedForwardBudget) #[n,N,Aψ,AB]) true
    else if mode == 5 then
      save `forwardCost_nonneg row (app (actual ++ `observedForwardBudget_cNorm_nonneg) #[n,N,K,ψ,AB,hAB])
    else if mode == 6 then
      let costs ← mkLambdaFVars #[p[50]!] (app (ns ++ `forwardCost) row)
      save `forwardCostTotal fixed (← mkAppM (actual ++ `fixedRowBudget) #[costs]) true
    else if mode < 9 then
      let nonneg ← mkLambdaFVars #[p[50]!] (app (ns ++ `forwardCost_nonneg) row)
      if mode == 7 then save `forwardCostTotal_nonneg fixed (← mkAppM (actual ++ `fixedRowBudget_nonneg) #[nonneg])
      else save `forwardCost_le_total row (← mkAppM (actual ++ `fixedRowBudget_le) #[nonneg,p[50]!])
    else
      let scale := app `JanetCartan.currentCoefficientScale #[p[44]!,p[46]!]
      let hR ← mkAppM `le_trans #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed,p[45]!]
      let hScale := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
        #[p[44]!,hR,p[46]!]
      let proof := app (actual ++ `forward_jet_budget_mono)
        #[n,N,app (ns ++ `forwardAmplitude) p,K,app (ns ++ `forwardCost) row,
          app (ns ++ `forwardCostTotal) fixed,scale,hScale,app (ns ++ `forwardCost_le_total) row,
          app (ns ++ `forwardJets) p]
      save `forwardTotalJets p proof

check_actual_raw_forward_slice 0
check_actual_raw_forward_slice 1
check_actual_raw_forward_slice 2
check_actual_raw_forward_slice 3
check_actual_raw_forward_slice 4
check_actual_raw_forward_slice 5
check_actual_raw_forward_slice 6
check_actual_raw_forward_slice 7
check_actual_raw_forward_slice 8
check_actual_raw_forward_slice 9
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.forwardTotalJets
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.forwardAmplitude
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.forwardSmooth
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.forwardSupport
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.forwardJets
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.forwardCost
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.forwardCost_nonneg
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.forwardCostTotal
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.forwardCostTotal_nonneg
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.forwardCost_le_total
end JanetCartan.PhysicalPrimary.OriginalRawForwardSliceApplication
end
