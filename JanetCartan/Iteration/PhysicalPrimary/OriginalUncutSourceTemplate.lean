module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate

/-! Exact original44 point specialization of the uncut source. These are
applications of the already retained Source53 and observation39 expressions;
no second family, retraction, source, extension, or cutoff is constructed. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalUncutSourceTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate
open OriginalLocalWaveGeometryTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalUncutSource.Actual
private def point := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family.Point
private def remn := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
private def obs := `JanetCartan.PhysicalPrimary.OriginalObservationPhase
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def original := `JanetCartan.PhysicalSeed.OriginalBoundary

private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs

private def emit (name : Name) (params : Array Expr) (value : Expr)
    (isDef := false) : MetaM Expr := do
  let name := ns ++ name
  let result ← store name params value isDef
  addDocStringCore name "Actual original44 source specialization on the SAME Source53 datum, observation39 phase, allowed qext and original masks. The proof never assumes source support lies in the defect core (app:ch_response:eq:response-actual-solver-formula)."
  return result

private def assertDefEq (label : String) (a b : Expr) : MetaM Unit := do
  unless ← isDefEq a b do throwError "original uncut source: {label} changed its native object"

/-- The existing native chart, including every χ₃ output point, is inside the
same original protected source. No mask or radius is selected here. -/
elab "retain_original_uncut_chart_source" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (reg ++ `χ₃)).type (some 23) fun fixed _ => do
    unless fixed.size == 23 do throwError "original uncut source: changed original23 masks"
    let n := mkApp (mkConst ``Nat.succ) fixed[0]!
    let hn := fixed[1]!
    let prior := #[n] ++ fixed[1:21].toArray
    let stat (name : Name) := app (reg ++ name) fixed
    let cap := app `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,hn,prior[20]!]
    let selected (name : Name) := app (`JanetCartan.PhysicalSeed.SelectedBoundary ++ name)
      (prior.set! 20 cap)
    let protect (name : Name) := app
      (`JanetCartan.PhysicalInitialization.OriginalProtected ++ name) prior
    let f := stat `f
    let fa := (← inferType f).getAppArgs
    unless fa.size == 7 do throwError "original uncut source: changed actual mask-family fields"
    let core := #[fixed[0]!,hn,protect `r,selected `rMeasure,protect `fact2,
      selected `hrMeasure,fa[5]!,fa[6]!,f]
    let h := app `JanetCartan.PhysicalPrimary.OriginalUncutSource.native_chart_subset_original_source
      (core.push (stat `r))
    discard <| emit `chart_in_source fixed h
    let hPhysical ← emit `physical_ball_in_source fixed
      (app `JanetCartan.PhysicalPrimary.OriginalUncutSource.native_physical_ball_subset_original_source core)
    let E := mkApp (mkConst `JanetCartan.Euclidean) n
    let zero ← mkAppOptM ``OfNat.ofNat #[E,mkNatLit 0,none]
    let radius := Expr.proj `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily 6 f
    discard <| emit `physical_closed_ball fixed (← mkAppM `Metric.closedBall #[zero,radius]) true
    let output := app `JanetCartan.PhysicalPrimary.OriginalSolverSupport.outputSupport_in_physical_ball fixed
    let hOutput ← forallBoundedTelescope (← inferType hPhysical) (some 1) fun patch _ => do
      let h ← forallBoundedTelescope (← inferType output) (some 2) fun point _ => do
        unless point.size == 2 do throwError "original uncut source: changed output support inclusion"
        let hclosed ← mkAppM `Metric.ball_subset_closedBall #[mkAppN output point]
        mkLambdaFVars point (mkAppN hPhysical (patch ++ #[point[0]!,hclosed]))
      mkLambdaFVars patch h
    discard <| emit `outputSupport_in_source fixed hOutput
  logInfo "actual original23 full native closed physical ball and entire original output support lie in every Xsrc; chart and chi3 shoulders included, no source-core/output-in-chart premise"

/-- Recover the literal producer spines from the actual point getters, not
from a fresh normalization or another admitted retraction. -/
def withPoint (go : Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (point ++ `source)).type (some 45) fun p _ => do
    unless p.size == 45 do throwError "original uncut source: expected actual full-inverse family point"
    let value ← bodyAt (point ++ `source) p
    let some application := value.find? (fun e => e.isAppOfArity (remn ++ `realization) 57)
      | throwError "original uncut source: lost Source.realization on the *same* original source"
    let s := application.getAppArgs[:53].toArray
    unless s.all (fun e => !e.hasLooseBVars) do
      throwError "original uncut source: original source data unexpectedly depends on the query parameter"
    let phase ← bodyAt (point ++ `φ) p
    unless phase.isAppOfArity (obs ++ `φ) 39 do
      throwError "original uncut source: lost the literal observation39 phase"
    go p s phase.getAppArgs

/-- Eliminate the phase-comparison hypothesis of the raw uncut source theorem
using original geometry and the given qext, not originalBallExtension. -/
elab "construct_actual_uncut_source_phase" : command => liftTermElabM do
  withPoint fun p s ph => do
    let sc ← sourceCurrent s
    logInfo "retained the native observed point's Source53 leading datum"
    let da := sc.dataArgs
    let fixed := s[:23].toArray
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let T := da[4]!
    let F := da[30]!
    let Qraw := app `JanetCartan.PhysicalPrimary.LeadingData.Q (da.push sc.datum)
    let some extBody := (← getConstInfo (obs ++ `φ_eq_retained)).value? (allowOpaque := true)
      | throwError "original uncut source: missing retained phase equality body"
    let extEq ← Core.betaReduce (extBody.beta ph)
    unless extEq.isAppOfArity (obs ++ `canonical_phase_eq_retained) 5 do
      throwError "original uncut source: changed retained phase equality"
    let Qext := extEq.getAppArgs[4]!
    assertDefEq "original patch" T (app (original ++ `T) #[n,s[1]!,sc.patch])
    let rawFrame ← mkAppM `JanetCartan.ProjectedStressFrame.projectedStress #[F]
    let extendedFrame ← mkAppM `JanetCartan.ProtectedFlow.extendedProjectedStress #[s[4]!,F]
    assertDefEq "raw projected stress" (← mkAppM ``Subtype.val #[Qraw]) rawFrame
    assertDefEq "same allowed qext" (← mkAppM ``Subtype.val #[Qext]) extendedFrame
    let hphases ← mkAppM `JanetCartan.PhysicalPrimary.OriginalUncutSource.original_native_extension_phase_eq
      #[s[1]!,sc.patch,F,s[4]!,s[5]!,s[6]!,Qraw,Qext,
        ← mkEqRefl rawFrame,← mkEqRefl extendedFrame]
    for (field,value) in #[(`T,T),(`F,F),(`Q,Qraw),(`Qext,Qext)] do
      discard <| emit field p value true
    let mask (name : Name) := app (masks ++ name) fixed
    let cellMask (name : Name) := app (masks ++ name) (fixed ++ #[sc.patch,sc.cell])
    let phaseData (name : Name) := app (reg ++ `Phase ++ name) (fixed.push sc.patch)
    let chartSupport := app (ns ++ `chart_in_source) (fixed.push sc.patch)
    let plateaux ← mkAppM
      `JanetCartan.PhysicalPrimary.OriginalUncutReconstruction.phase_cutoff_plateau_of_eventually_one
      #[phaseData `χ,phaseData `fact3]
    let domain := component (app `JanetCartan.PhysicalInitialization.OriginalProtected.source_domains
      #[n,s[1]!,sc.patch]) 3
    let φ := app (point ++ `φ) p
    let phaseEq := app (obs ++ `φ_eq_retained) ph
    let protectSupport (name : Name) := app (ns ++ name) (fixed.push sc.patch)
    for (label,K,support) in #[
        (`phase_on_chart,mask `chart,chartSupport),
        (`phase_on_physical_ball,app (ns ++ `physical_closed_ball) fixed,
          protectSupport `physical_ball_in_source),
        (`phase_on_output,app `JanetCartan.PhysicalPrimary.OriginalSolverSupport.outputSupport fixed,
          protectSupport `outputSupport_in_source)] do
      let result ← forallBoundedTelescope (← inferType φ) (some 1) fun cs _ => do
        let c := cs[0]!
        withLocalDeclD `hc (← mkAppM `Membership.mem #[cellMask `V,c]) fun hc => do
          let hcC := mkAppN (cellMask `V_closure_Csrc)
            #[c,← mkAppM `subset_closure #[hc]]
          forallBoundedTelescope (← inferType (mkApp φ c)) (some 1) fun xs _ => do
            let x := xs[0]!
            withLocalDeclD `hx (← mkAppM `Membership.mem #[K,x]) fun hx => do
              let hxX := mkAppN support #[x,hx]
              let pair ← mkAppM ``Prod.mk #[x,c]
              let hpair ← mkAppM ``And.intro #[hxX,hcC]
              let hp := mkAppN domain #[pair,hpair]
              let hplateau := mkAppN plateaux #[pair,hpair]
              let hretained ← mkAppM
                `JanetCartan.ResponsePrimarySources.retainedPhaseExtension_physical_eventuallyEq
                #[T,Qext,hplateau]
              let hvalue ← mkAppM `Filter.EventuallyEq.self_of_nhds #[hretained]
              let physicalPair ← mkAppM ``Prod.mk #[x,← mkAppM ``Prod.snd #[c]]
              let hrawPhase ← mkAppM ``Eq.symm #[mkAppN hphases #[physicalPair,hp]]
              let hphase ← mkAppM ``congrFun #[← mkAppM ``congrFun #[phaseEq,c],x]
              let h ← mkAppM ``Eq.trans #[hphase,← mkAppM ``Eq.trans #[hvalue,hrawPhase]]
              mkLambdaFVars #[c,hc,x,hx] h
      discard <| emit label p result
    let result := app (ns ++ `phase_on_chart) p
    for (label,support) in #[(`phase_on_source,mask `χ₂_support_chart),
        (`phase_on_solver_source,mask `χ₃_support_chart)] do
      let h ← forallBoundedTelescope (← inferType result) (some 2) fun cc _ => do
        let heq ← mkAppM `Set.EqOn.mono #[mkAppN result cc,support]
        mkLambdaFVars cc heq
      discard <| emit label p h
  logInfo "actual original44 phase bridge: same Source53 raw frame, allowed qext and retained observation39 phase on the full physical ball and original output support; original gap/flow ranges and plateau close every phase premise"

end JanetCartan.PhysicalPrimary.OriginalUncutSourceTemplate
end
