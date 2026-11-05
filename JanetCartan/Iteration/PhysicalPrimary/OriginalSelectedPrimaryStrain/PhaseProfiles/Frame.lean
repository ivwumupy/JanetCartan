module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Basic
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEvent
import all JanetCartan.Iteration.PhysicalPrimary.OriginalPrimarySourcePhaseGeometry
import all JanetCartan.Iteration.PhysicalPairs.OriginalMaskGeometry
import all JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean
/-!
# Actual original-frame input for the ordinary primary phase

The native event already reaches its original operator threshold. This leaf
uses that actual threshold and the original retained coefficient continuation
to obtain all frame profiles on the same current map. The consumer is the
finite-menu phase cost in `PhaseProfiles`, hence the first-mask phase input
for `main:eq:primary-strain` and `app:ch_regular:eq:source-tail` of paper-v2.
No new initial threshold or analytic success input is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Template
open Lean Meta Elab
private def ns := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Native
private def op := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
private def fr := `JanetCartan.PhysicalPairs.OriginalSignedFrames
private def quad := `JanetCartan.PhysicalPairs.SampledQuadrature
private def app (k : Name) (p : Array Expr) := mkAppN (mkConst k) p
private def bodyAt (e : Expr) : MetaM Expr := do
  let i ← getConstInfo e.getAppFn.constName!
  return ((i.value! (allowOpaque := true)).instantiateLevelParams i.levelParams e.getAppFn.constLevels!).beta e.getAppArgs |>.headBeta
private def resultAt (name : Name) (args : Array Expr) : MetaM Expr := do
  let mut type := (← getConstInfo name).type
  for _ in args do
    let .forallE _ _ body _ := type | throwError "ordinary phase: changed telescope {name}"
    type := body
  return type.instantiateRev args
private def leftOfLe (h : Expr) : MetaM Expr := do
  let t ← resultAt h.getAppFn.constName! h.getAppArgs
  unless t.isAppOfArity ``LE.le 4 do throwError "ordinary phase: not a numerical bound"
  return t.getAppArgs[2]!
private structure NativeInputs where
  params52 : Array Expr
  full60 : Array Expr
  goal : Expr
private def nativeTelescope (type : Expr) (go : Array Expr → Expr → MetaM Unit) : MetaM Unit :=
  loop 52 type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0,type,p => go p (type.instantiateRev p)
    | k+1,type,p => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "ordinary phase: saved native telescope ended at {p.size}"
      let domain := domain.instantiateRev p
      if bi == .instImplicit then
        withLocalDecl name bi domain fun x => loop k body (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi domain fun x => loop k body (p.push x)
private def withNativeInputs (go : NativeInputs → MetaM Unit) : MetaM Unit := do
  let info ← getConstInfo `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.uncut_response_jets
  let some body := info.value? (allowOpaque := true) |
    throwError "ordinary phase: saved native response proof missing"
  nativeTelescope info.type fun p goal => do
    let out ← IO.getStdout
    out.putStrLn "ordinary primary phase: opened saved native52"
    out.flush
    let proof := (body.beta p).headBeta
    let some full := proof.find? (·.isAppOfArity
        `JanetCartan.PhysicalPrimary.OriginalPhysicalResponse.derivative_jets 60) |
      throwError "ordinary phase: saved SAME full response60 missing"
    if full.hasLooseBVars then throwError "ordinary phase: full response depends on a later jet point"
    go ⟨p,full.getAppArgs,goal⟩
private structure Context where
  parent : NativeInputs
  graph42 : Array Expr
  fixed23 : Array Expr
  radial11 : Array Expr
  op33 : Array Expr
  hi : Expr
  hr : Expr
  hc : Expr
private def withPhase (go : Context → MetaM Unit) : MetaM Unit := withNativeInputs fun d => do
  let source := d.goal
  let some graph := source.find? (·.isAppOfArity `JanetCartan.PhysicalSampling.OriginalGraphResponse.B 42) |
    throwError "ordinary phase: no actual graph42"
  if graph.hasLooseBVars then throwError "ordinary phase: graph uses a later derivative binder"
  let gp := graph.getAppArgs
  let reachedType := (← resultAt (quad ++ `group_phase) gp[:37].toArray).bindingDomain!
  let stage := reachedType.getAppArgs[2]!
  unless stage.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalRegular.Graph.S 34 do
    throwError "ordinary phase: exact original graph threshold changed"
  let fixed := stage.getAppArgs[:23].toArray
  let raw ← bodyAt (app (quad ++ `group_phase) gp)
  unless raw.isAppOfArity (quad ++ `radialCarrier) 11 do throwError "ordinary phase: carrier changed"
  let hi := app `JanetCartan.PhysicalPrimary.OriginalPhysicalResponseInputProfiles.inverse_threshold d.full60[:44].toArray
  let si ← leftOfLe hi
  unless si.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalInverseEnvelopes.S 42 do throwError "inverse42 changed"
  let hr := app `JanetCartan.PhysicalPrimary.OriginalInverseEnvelopes.remainder_threshold si.getAppArgs
  let sr ← leftOfLe hr
  unless sr.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family.S 41 do throwError "remainder41 changed"
  let hc := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family.coefficient_threshold sr.getAppArgs
  let sc ← leftOfLe hc
  unless sc.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Coefficients.S 35 do throwError "coefficient35 changed"
  let so ← bodyAt sc
  unless so.isAppOfArity (op ++ `S) 33 do throwError "operator33 changed"
  go ⟨d,gp,fixed,raw.getAppArgs,so.getAppArgs,hi,hr,hc⟩
private def save (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "ordinary phase: unresolved or later input in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let out ← IO.getStdout
  out.putStrLn s!"ordinary primary phase: checking {key}/{p.size}"
  out.flush
  if data then
    addDecl (.defnDecl {name := ns ++ key,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name := ns ++ key,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore (ns ++ key) "The SAME ordinary group_phase on the original native graph42 and whole source chart. Phase costs precede every history and source label; no doubled carrier, shifted Fourier phase, new threshold or phase-profile premise (main:eq:primary-strain; app:ch_regular:eq:source-tail)."
private def publish (mode : Nat) : MetaM Unit := withPhase fun c => do
  let d := c.parent
  let p := d.params52
  let native := p[:51].toArray
  let cp := c.op33
  if mode == 0 then
    let hop ← mkAppM ``le_trans #[c.hc,← mkAppM ``le_trans #[c.hr,← mkAppM ``le_trans #[c.hi,d.full60[45]!]]]
    let target ← mkAppM ``LE.le #[app (op ++ `S) cp,p[44]!]
    save `operator_reached native hop target
    return
  let hop := app (ns ++ `operator_reached) native
  let ca := c.radial11
  let n := ca[0]!
  let f := c.fixed23
  let hn := p[1]!
  let F := (← bodyAt (app (quad ++ `Q) c.graph42)).appArg!
  let T := app `JanetCartan.currentCoefficientScale #[p[44]!,p[46]!]
  let hT := app (fr ++ `current_scale_one) #[app (op ++ `S) cp,p[44]!,app (op ++ `fact0) cp,hop,p[46]!]
  let AQ := app (op ++ `AQ) cp
  let hAQ := app (op ++ `fact1) cp
  let inputs := cp ++ #[p[44]!,hop] ++ p[46:50].toArray
  let cont := app (op ++ `continuation) inputs
  let ct ← whnfR (← resultAt (op ++ `continuation) inputs)
  unless ct.isAppOfArity ``And 2 do
    throwError "ordinary phase: coefficient continuation head changed to {ct.getAppFn.constName!}"
  let tailType ← whnfR ct.appArg!
  unless tailType.isAppOfArity ``And 2 do
    throwError "ordinary phase: coefficient continuation second head changed to {tailType.getAppFn.constName!}"
  let profileType := tailType.appArg!
  let pe ← forallBoundedTelescope profileType (some 2) fun K _ => do
    mkLambdaFVars K (.proj ``And 0 (mkAppN (.proj ``And 1 (.proj ``And 1 cont)) K))
  let low := app `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder #[p[0]!]
  let dim := app ``Nat.add #[p[0]!,mkNatLit 2]
  let hreserve ← mkAppM ``Nat.le_trans #[app (fr ++ `enough) #[p[0]!],← mkAppM ``Nat.le_add_right #[low,dim]]
  let args := #[n,hn,f[4]!,f[5]!,f[6]!,F,ca[5]!,ca[6]!,cp[28]!,hreserve,T,hT,AQ,hAQ,pe]
  let frame := app (fr ++ `at_history) args
  save `frame_profile native frame (← resultAt (fr ++ `at_history) args)
end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Template
end
run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Template.publish 0
run_meta JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Template.publish 1
