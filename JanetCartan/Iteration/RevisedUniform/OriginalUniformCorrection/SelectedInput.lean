module

public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.Target
public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.Orders
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
public import JanetCartan.Iteration.PhysicalMean.OriginalNormalizedTargetProfiles
public import JanetCartan.Iteration.PhysicalMean.OriginalFullSourcePicardPrecisionBudgets
public meta import JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Actual selected inputs from the original metric and one admissible history

The consumer is the original uniform step, `main:thm:step` in `paper-v2.tex`.
Insert the dimension-only native menu and the already selected normalization
into the real complete-source constructor.  The only remaining data are the
original metric, its fixed interval, an admissible physical prefix, the finite
smoothing order and the original defect bound.  Every extra gate is numerical.
The callback exposes the very selected52/native50 arguments used by the primary,
mean and pair producers; it never identifies independently chosen objects.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section

namespace JanetCartan.RevisedUniform.OriginalUniformCorrectionTemplate

open Lean Meta Elab Command
open OriginalSelectedPrehistoryTemplate (withDimensionStatic)

private def root := `JanetCartan.RevisedUniform.OriginalUniformCorrection
private def preparation := `JanetCartan.RevisedUniform.OriginalMetricPreparation
private def prehistory := `JanetCartan.RevisedUniform.OriginalSelectedPrehistory
private def forcing := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def app (name : Name) (args : Array Expr) := mkAppN (mkConst name) args
private def part (p : Expr) (i : Nat) := Expr.proj ``And 0
  (Nat.repeat (fun e => Expr.proj ``And 1 e) i p)
private partial def head (e : Expr) : Expr := match e.headBeta.consumeMData with
  | .letE _ _ v b _ => head (b.instantiate1 v)
  | t => t

private def progress (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "JANET_UNIFORM_INPUT_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn message
      handle.flush

/-- Metaprogramming metadata only: all seven mathematical inputs are the
dimension and the originally supplied metric/domain.  No success field occurs. -/
structure FixedMetric where
  parameters : Array Expr
  dimension : Array Expr
  selected33 : Array Expr
  native44 : Array Expr
  normalized6 : Array Expr
  cap : Expr
  capProof : Expr

/-- Substitute the original dimension-only choices before opening any target
or history data.  Both normalization and the interval are the existing ones. -/
def withFixedMetric (next : FixedMetric → MetaM Unit) : MetaM Unit := do
  progress "original input: entering fixed dimension"
  withDimensionStatic fun dh _ selected native => do
    progress "original input: actual fixed dimension recovered"
    let afterDimension ← instantiateForall
      (← getConstInfo (preparation ++ `metricCoordinates)).type dh
    forallBoundedTelescope afterDimension (some 5) fun metric _ => do
      unless dh.size == 2 && selected.size == 33 && native.size == 44 && metric.size == 5 do
        throwError "original uniform input: changed fixed dimension/metric boundary"
      let parameters := dh ++ metric
      let n := mkApp (mkConst ``Nat.succ) dh[0]!
      let A := app (preparation ++ `metricCoordinates) parameters
      let hA := app (preparation ++ `metricCoordinates_spec) parameters
      let domain := app (preparation ++ `pullback_domain_inputs)
        (#[n] ++ metric ++ #[A,part hA 0])
      let domainType ← inferType domain
      unless domainType.isAppOfArity ``And 2 &&
          domainType.getAppArgs[0]!.isAppOfArity ``IsOpen 3 do
        throwError "original uniform input: original pullback-domain producer changed"
      let U := domainType.getAppArgs[0]!.getAppArgs.back!
      let g := app `JanetCartan.coordinatePullback #[n,metric[0]!,A]
      let normalized := #[g,U,part domain 0,part domain 1,
        Expr.proj ``And 1 (Expr.proj ``And 1 domain),Expr.proj ``And 1 hA]
      progress "original input: actual normalized metric recovered"
      next {
        parameters, dimension := dh, selected33 := selected, native44 := native,
        normalized6 := normalized, cap := app (preparation ++ `metricCap) parameters,
        capProof := app (preparation ++ `metricCap_spec) parameters }

/-- Metadata for the literal selected source.  `stageParameters` contains only
original metric data, a physical prefix and numerical/initial-defect gates. -/
structure SelectedStage extends FixedMetric where
  stageParameters : Array Expr
  selected52 : Array Expr
  native50 : Array Expr
  scale : Expr
  delta : Expr

private def save (key : Name) (parameters : Array Expr) (value target : Expr)
    (data := true) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars parameters target)
  let value ← instantiateMVars (← mkLambdaFVars parameters value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "original uniform input: unresolved or extra input in {key}"
    let missing := e.getUsedConstants.filter (fun name => (env.find? name).isNone)
    unless missing.isEmpty do throwError "original uniform input: missing {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  progress s!"original input: checking {key}/{parameters.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  progress s!"original input: checked {key}/{parameters.size}"
  addDocStringCore name "Actual original dimension/metric specialization of the SAME selected complete-source construction. All geometry, source scales, interval, sample and cutoff come from the original producers. Only numerical gates and the original initial-defect/history assumptions remain (main:thm:step; new:sec:order-of-choices)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "original uniform input: nonstandard axioms {axioms}"
  logInfo m!"original uniform input {key}/{parameters.size}: {axioms}"

/-- Expose the dimension-only tensor and precision gates without placing a
finite accuracy inside an initial-reference threshold. -/
private def publishFrequencies : MetaM Unit := do
  progress "original input: entering frequency specialization"
  withDimensionStatic fun dh _ selected native => do
    progress "original input: frequency dimension recovered"
    let n := mkApp (mkConst ``Nat.succ) dh[0]!
    let D := app (prehistory ++ `Dsmoothing) dh
    let _ := native
    withLocalDeclD `m (mkConst ``Nat) fun m => do
      withLocalDeclD `hm (← mkAppM ``LE.le #[mkNatLit 1,m]) fun hm => do
        let args := #[n,D,m,hm]
        let tensor := app `JanetCartan.PhysicalMean.OriginalNormalizedTargetProfiles.Starget args
        save `tensorFrequency (dh ++ #[m,hm]) tensor (mkConst ``Real)
    withLocalDeclD `accuracy (mkConst ``Real) fun accuracy => do
      let precision := app `JanetCartan.PhysicalMean.OriginalFullSourcePicard.Sprecision
        (selected.push accuracy)
      save `precisionFrequency (dh.push accuracy) precision (mkConst ``Real)

run_meta publishFrequencies

/-- The actual preparation theorem already pays the measured source gate.
Read its chosen threshold and facts instead of reapplying the raw measurement
cost to another large specialization. -/
def withPreparationAt (fixed : FixedMetric) (k : Expr)
    (next : Expr → Expr → MetaM Unit) : MetaM Unit := do
  let proof := app (preparation ++ `original_smoothing_plan)
    (fixed.parameters ++ #[k,mkNatLit 0])
  let type := head (← inferType proof)
  unless type.isAppOfArity ``Exists 2 do
    throwError "original uniform input: genuine preparation threshold changed"
  let S := mkAppN (mkConst ``Classical.choose type.getAppFn.constLevels!) (type.getAppArgs.push proof)
  let spec := mkAppN (mkConst ``Classical.choose_spec type.getAppFn.constLevels!) (type.getAppArgs.push proof)
  let ctype := head (type.getAppArgs[1]!.beta #[S])
  unless ctype.isAppOfArity ``Exists 2 do
    throwError "original uniform input: genuine preparation cost changed"
  let cSpec := mkAppN (mkConst ``Classical.choose_spec ctype.getAppFn.constLevels!)
    (ctype.getAppArgs.push spec)
  next S cSpec

private def publishPreparation (data : Bool) : MetaM Unit := do
  withFixedMetric fun fixed => do
    withLocalDeclD `k (mkConst ``Nat) fun k => do
      withPreparationAt fixed k fun S spec => do
        let p := fixed.parameters.push k
        if data then
          save `preparationFrequency p S (mkConst ``Real)
        else
          let named := app (root ++ `preparationFrequency) p
          let two ← mkNumeral (mkConst ``Real) 2
          let target ← mkAppM ``LE.le #[two,named]
          save `preparationFrequency_two_le p (part spec 0) target false

run_meta publishPreparation true
run_meta publishPreparation false

/-- Build the actual selected52/native50 from one original metric and one
admissible prefix.  The starting threshold is the preliminary original Tref;
the final constructor supplies it from its stronger fixed initial maximum. -/
def withSelectedStage (next : SelectedStage → MetaM Unit) : MetaM Unit := do
  withFixedMetric fun fixed => do
    let start ← instantiateForall (← getConstInfo (forcing ++ `selectedFullSource)).type
      fixed.selected33
    forallBoundedTelescope start (some 1) fun initial afterInitial => do
      progress "original input: original initial frequency recovered"
      unless initial.size == 1 && afterInitial.isForall do
        throwError "original uniform input: missing original initial frequency"
      let R₀ := initial[0]!
      let Tref := app (prehistory ++ `Tref) fixed.dimension
      withLocalDeclD `hInitial (← mkAppM ``LE.le #[Tref,R₀]) fun hInitial => do
        let hCommon := app (prehistory ++ `common_reached) (fixed.dimension ++ #[R₀,hInitial])
        let atHistory := afterInitial.bindingBody!.instantiate1 hCommon
        forallBoundedTelescope atHistory (some 4) fun history afterHistory => do
          progress "original input: actual history recovered"
          unless history.size == 4 do throwError "original uniform input: changed actual history"
          let selected39 := fixed.selected33 ++ #[R₀,hCommon] ++ history
          let hNative := app `JanetCartan.PhysicalMean.OriginalCanonicalMomentAdmission.native_reached
            (fixed.selected33 ++ #[R₀,hCommon])
          let native50 := fixed.native44 ++ #[R₀,hNative] ++ history
          let atParameter ← instantiateForall afterHistory fixed.normalized6
          forallBoundedTelescope atParameter (some 1) fun point afterPoint => do
            unless point.size == 1 && afterPoint.isForall do
              throwError "original uniform input: changed original metric parameter"
            let s := point[0]!
            let zero ← mkNumeral (mkConst ``Real) 0
            withLocalDeclD `hs (← mkAppM ``LT.lt #[zero,s]) fun hs => do
              withLocalDeclD `hscap (← mkAppM ``LE.le #[s,fixed.cap]) fun hscap => do
                let hlo ← mkAppM ``le_of_lt #[hs]
                let hhi ← mkAppM ``le_trans #[hscap,part (Expr.proj ``And 1 fixed.capProof) 0]
                let hsInterval ← mkAppM ``And.intro #[hlo,hhi]
                let expected := afterPoint.bindingDomain!
                unless ← isDefEq (← inferType hsInterval) expected do
                  throwError "original uniform input: changed original physical target interval"
                progress "original input: original physical interval checked"
                let atOrders := afterPoint.bindingBody!.instantiate1 hsInterval
                withLocalDeclD `k (mkConst ``Nat) fun k => do
                  let n := mkApp (mkConst ``Nat.succ) fixed.dimension[0]!
                  let m := app (root ++ `smoothingOrder) #[n,k]
                  let hm := Expr.proj ``And 0 (app (root ++ `orders_spec) #[n,k])
                  let orders := #[m,hm,k]
                  let afterOrders ← instantiateForall atOrders orders
                  unless afterOrders.isForall do
                    throwError "original uniform input: changed original joint-order boundary"
                  let R := app `JanetCartan.iterationScale
                    #[R₀,mkConst `JanetCartan.growthExponent,history[0]!]
                  let threshold := app (root ++ `preparationFrequency) (fixed.parameters.push k)
                  let gate ← mkAppM ``LE.le #[threshold,R]
                  withLocalDeclD `hPreparationFrequency gate fun hFrequency => do
                    withPreparationAt fixed k fun _ spec => do
                      let hSource ← mkAppM ``le_trans #[part spec 2,hFrequency]
                      unless ← isDefEq (← inferType hSource) afterOrders.bindingDomain! do
                        throwError "original uniform input: the genuine preparation does not pay this source gate"
                      progress "original input: original source threshold supplied by preparation"
                      let atSmall := afterOrders.bindingBody!.instantiate1 hSource
                      forallBoundedTelescope atSmall (some 1) fun defect _ => do
                        unless defect.size == 1 do throwError "original uniform input: lost original defect bound"
                        let selected52 := selected39 ++ fixed.normalized6 ++ #[s,hsInterval] ++ orders ++
                          #[hSource,defect[0]!]
                        let parameters := fixed.parameters ++ #[R₀,hInitial] ++ history ++ #[s,hs,hscap] ++
                          #[k,hFrequency,defect[0]!]
                        unless selected52.size == 52 && native50.size == 50 && parameters.size == 19 do
                          throwError "original uniform input: an extra source or analytic premise entered"
                        let defectType ← inferType defect[0]!
                        unless defectType.isAppOfArity ``LE.le 4 &&
                            defectType.getAppArgs[3]!.isAppOfArity ``HPow.hPow 6 do
                          throwError "original uniform input: prescribed squared defect changed"
                        let delta := defectType.getAppArgs[3]!.getAppArgs[4]!
                        let negCast ← mkAppOptM ``Nat.cast #[some (mkConst ``Real),none,some k]
                        let desiredDelta ← mkAppM ``Real.rpow #[R,← mkAppM ``Neg.neg #[negCast]]
                        unless ← isDefEq delta desiredDelta do
                          throwError "original uniform input: prescribed original R^(-k) changed"
                        progress "original input: actual selected52 constructed"
                        next {
                          toFixedMetric := fixed, stageParameters := parameters, selected52, native50,
                          scale := R, delta }

run_meta do
  withSelectedStage fun d => do
    let source := app (forcing ++ `selectedFullSource) d.selected52
    save `selectedSource d.stageParameters source (← inferType source)

end JanetCartan.RevisedUniform.OriginalUniformCorrectionTemplate
end

#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.tensorFrequency
#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.precisionFrequency
#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.preparationFrequency
#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.selectedSource
