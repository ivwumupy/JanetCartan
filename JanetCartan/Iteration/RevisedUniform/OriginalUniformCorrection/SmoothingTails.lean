module

public import JanetCartan.Iteration.RevisedUniform.OriginalUniformCorrection.SmoothingCosts
public meta import JanetCartan.Iteration.RevisedUniform.OriginalMetricPreparationTemplate
import all JanetCartan.Iteration.RevisedUniform.OriginalMetricPreparationTemplate
import all JanetCartan.Iteration.RevisedUniform.OriginalSelectedPrehistoryTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
public meta import Lean

/-!
# Actual original-data smoothing tails before the source is assembled

The same finite-moment smoother supplies both errors needed by
`RevisedStage.increment_estimates_of_physicalSobolev_profiles`.  This deduction
uses only the originally supplied metric, its already chosen common interval,
an admissible history and the original defect bound.  It is independent of
constructing the complete measured source or any mean/pair field.  Its consumer
specializes the order and defect size to the original uniform step
(`main:lem:smoothing`, `main:eq:metric-two-errors` in `paper-v2.tex`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalUniformSmoothingTailsTemplate

open Lean Meta Elab Command

private def root := `JanetCartan.RevisedUniform.OriginalUniformCorrection
private def preparation := `JanetCartan.RevisedUniform.OriginalMetricPreparation
private def forcing := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def app (name : Name) (p : Array Expr) := mkAppN (mkConst name) p
private def tail (p : Expr) (i : Nat) := Nat.repeat (fun e => Expr.proj ``And 1 e) i p
private def part (p : Expr) (i : Nat) := Expr.proj ``And 0 (tail p i)
private partial def head (e : Expr) : Expr := match e.headBeta.consumeMData with
  | .letE _ _ v b _ => head (b.instantiate1 v)
  | t => t
private def typeTail (type : Expr) (i : Nat) : Expr :=
  Nat.repeat (fun e => (head e).getAppArgs[1]!) i type
private def typePart (type : Expr) (i : Nat) : Expr :=
  (head (typeTail type i)).getAppArgs[0]!

run_meta do
  OriginalMetricPreparationTemplate.withDimensionMetric fun d => do
    let fixed := d.dimension ++ d.metric
    let cap := app (preparation ++ `metricCap) fixed
    let hcap := app (preparation ++ `metricCap_spec) fixed
    let capType := head (← inferType hcap)
    let upper := typePart capType 1
    unless upper.isAppOfArity ``LE.le 4 &&
        upper.getAppArgs[3]!.isAppOfArity (forcing ++ `targetDilation) 50 do
      throwError "original smoothing tails: changed original physical interval"
    let arguments := upper.getAppArgs[3]!.getAppArgs
    withLocalDeclD `m (mkConst ``Nat) fun m => do
      withLocalDeclD `hm (← mkAppM ``LE.le #[mkNatLit 1,m]) fun hm => do
        let early := fixed ++ #[m,hm]
        OriginalUniformSmoothingTemplate.withSmoothing arguments m hm fun chosen spec specType => do
          let all := tail spec 6
          let allType := typeTail specType 6
          forallBoundedTelescope allType (some 1) fun point afterPoint => do
            unless point.size == 1 && afterPoint.isForall do
              throwError "original smoothing tails: changed original parameter boundary"
            let s := point[0]!
            let zero ← mkNumeral (mkConst ``Real) 0
            let interval ← mkAppM ``Set.Icc #[zero,cap]
            let hsType ← mkAppM ``Membership.mem #[interval,s]
            withLocalDeclD `hsCommon hsType fun hs => do
              let high ← mkAppM ``le_trans #[Expr.proj ``And 1 hs,part hcap 1]
              let originalInterval ← mkAppM ``And.intro #[Expr.proj ``And 0 hs,high]
              let atHistory := afterPoint.bindingBody!.instantiate1 originalInterval
              forallBoundedTelescope atHistory (some 6) fun history afterHistory => do
                unless history.size == 6 do
                  throwError "original smoothing tails: changed admissible physical history"
                let R := app `JanetCartan.iterationScale
                  #[history[0]!,mkConst `JanetCartan.growthExponent,history[2]!]
                let threshold := app (root ++ `smoothingFrequency) early
                let frequencyType ← mkAppM ``LE.le #[threshold,R]
                let afterHistory := head afterHistory
                unless afterHistory.isForall do
                  throwError "original smoothing tails: missing current smoothing frequency"
                withLocalDeclD `hSmoothingFrequency frequencyType fun hFrequency => do
                  let atDefect := afterHistory.bindingBody!.instantiate1 hFrequency
                  forallBoundedTelescope atDefect (some 3) fun defect result => do
                    unless defect.size == 3 do
                      throwError "original smoothing tails: changed positive defect/smallness boundary"
                    let full := mkAppN all (#[s,originalInterval] ++ history ++ #[hFrequency] ++ defect)
                    let result := head result
                    let lowType := typePart result 6
                    let highType := typePart result 7
                    let proof := mkAppN (mkConst ``And.intro)
                      #[lowType,highType,part full 6,part full 7]
                    let target := OriginalUniformSmoothingTemplate.renameCosts fixed m hm chosen
                      (mkApp2 (mkConst ``And) lowType highType)
                    let parameters := early ++ #[s,hs] ++ history ++ #[hFrequency] ++ defect
                    unless parameters.size == 21 do
                      throwError "original smoothing tails: an extra source or success input entered"
                    let type ← instantiateMVars (← mkForallFVars parameters target)
                    let value ← instantiateMVars (← mkLambdaFVars parameters proof)
                    let env ← getEnv
                    for e in #[type,value] do
                      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
                        throwError "original smoothing tails: unresolved original-data application"
                      let missing := e.getUsedConstants.filter (fun name => (env.find? name).isNone)
                      unless missing.isEmpty do throwError "original smoothing tails: missing {missing.toList}"
                    let (type,value) := Lean.ShareCommon.shareCommon (type,value)
                    let name := root ++ `original_smoothing_bounds
                    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
                    addDocStringCore name "Both true finite-moment smoothing tails on the SAME original final core and original normalized metric family, for every admissible physical prefix. The existing common metric interval is used; constants and current-frequency threshold precede every history, metric parameter and defect size. No complete source, mean, pair or smoothing-success input (main:lem:smoothing; main:eq:metric-two-errors)."
                    let axioms ← collectAxioms name
                    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
                      throwError "original smoothing tails: nonstandard axioms {axioms}"
                    logInfo m!"actual original-data two-tail smoothing21: SAME interval/core/tensor, {axioms}"

end JanetCartan.RevisedUniform.OriginalUniformSmoothingTailsTemplate
end

#print axioms JanetCartan.RevisedUniform.OriginalUniformCorrection.original_smoothing_bounds
