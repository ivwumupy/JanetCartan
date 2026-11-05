module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.History
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.Quadratures
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.DataTemplate
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.ObservedLabelsTemplate
public import JanetCartan.Iteration.PhysicalPairs.OriginalMaskRows
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMomentAdmissionTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-! # One fixed-data family of the actual complete primary source

Every localization constant is chosen over this entire family before the
history, target, smoothing, outer sample, or quadrature is supplied. The
original full-forcing Picard count is fixed; its actual raw source and exact
uncut inverse input are retained (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate

open Lean Meta Elab Command

def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Family
def phase := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Native
def coeff := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.CoefficientProfiles.Native
def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
def source := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceData
def raw := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.RawProfiles
def regular := `JanetCartan.PhysicalInitialization.OriginalRegular
def world := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

def resultAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let mut type := (← getConstInfo key).type
  for _ in p do
    let .forallE _ _ body _ := type.consumeMData |
      throwError "actual primary family: original telescope changed for {key}"
    type := body
  return type.instantiateRev p

private def body (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let some value := ci.value? (allowOpaque := true) |
    throwError "actual primary family: original body unavailable for {ci.name}"
  return ((value.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta

def part (e : Expr) (k : Nat) : Expr := Expr.proj ``And 0
  (Nat.rec (motive := fun _ => Expr) e (fun _ v => Expr.proj ``And 1 v) k)

structure Context where
  fixed : Array Expr
  labels : Expr
  label : Expr
  data : RawProfilesTemplate.Data
  imaginary : Expr
  operatorReached : Expr
  native : Array Expr
  graph : Array Expr
  graphStatic : Array Expr
  masksStatic : Array Expr
  chart : Expr
  domain : Expr
  domain_measurable : Expr
  R : Expr
  rho : Expr

def Context.sourceArgs (c : Context) := c.data.sourceArgs.push c.imaginary
def Context.family (c : Context) (e : Expr) := mkLambdaFVars #[c.label] e
def Context.field (c : Context) (key : Name) := app (root ++ key) c.fixed
def Context.at (c : Context) (key : Name) := mkApp (c.field key) c.label

/-- Read the original graph from the unchanged ordinary phase; the label
projection never selects another history or source. -/
def withFamily (next : Context → MetaM Unit) : MetaM Unit :=
  ObservedLabelsTemplate.withLabels fun fixed labels t d imaginary operatorReached => do
    let native := d.native.push d.baselineArgs[50]!
    let rawPhase ← body (app (phase ++ `phase) native)
    unless rawPhase.isAppOfArity `JanetCartan.PhysicalPairs.SampledQuadrature.group_phase 42 do
      throwError "actual primary family: not the original graph42 phase"
    let gp := rawPhase.getAppArgs
    let reached ← inferType gp[37]!
    unless reached.isAppOfArity ``LE.le 4 && reached.getAppArgs[2]!.isAppOfArity
        (regular ++ `Graph.S) 34 do
      throwError "actual primary family: original graph reach changed"
    let graphStatic := reached.getAppArgs[2]!.getAppArgs
    let masksStatic := graphStatic[:23].toArray
    let R := app ``JanetCartan.historyScale
      #[d.native[44]!,mkConst ``JanetCartan.growthExponent,d.native[46]!]
    let rho ← mkAppM ``HPow.hPow #[R,mkConst ``JanetCartan.carrierExponent]
    next {
      fixed := fixed, labels := labels, label := t, data := d, imaginary := imaginary,
      operatorReached := operatorReached,
      native := native, graph := gp, graphStatic := graphStatic, masksStatic := masksStatic,
      chart := app (masks ++ `chart) masksStatic,
      domain := app (world ++ `W) masksStatic,
      domain_measurable := app (world ++ `W_measurable) masksStatic,
      R := R, rho := rho }

/-- The node subtype is admitted by the original nonzero outer weight; there
is no inner annular nonzero gate or replacement sample. -/
def phaseArgs (c : Context) : MetaM (Array Expr) := do
  let group ← mkAppM ``Prod.mk #[c.data.baselineArgs[50]!,c.data.baselineArgs[51]!]
  let indexType ← inferType c.data.sample
  unless indexType.isAppOfArity ``JanetCartan.CanonicalRowComparison.SampleIndex 7 do
    throwError "actual primary family: original sample type changed"
  let a := indexType.getAppArgs
  let hp := app ``JanetCartan.PhysicalPairs.OriginalMaskRows.node_cube
    #[a[0]!,a[1]!,a[2]!,a[5]!,a[3]!,a[4]!,a[6]!,
      app `JanetCartan.PhysicalSampling.OriginalOuterWeights.parameterRadius c.graph[:22].toArray,
      app `JanetCartan.PhysicalSampling.OriginalOuterWeights.nonzero_parameter c.graph[:22].toArray,
      c.data.sample]
  let membership ← inferType hp
  unless membership.isAppOfArity ``Membership.mem 5 do
    throwError "actual primary family: original outer parameter admission changed"
  let z := membership.getAppArgs[4]!
  let next ← resultAt (phase ++ `representative) (c.native.push group)
  let subtype ← whnf next.bindingDomain!
  unless subtype.isAppOfArity ``Subtype 2 do
    throwError "actual primary family: original colored node subtype changed"
  let node := mkAppN (mkConst ``Subtype.mk subtype.getAppFn.constLevels!)
    (subtype.getAppArgs ++ #[z,hp])
  return c.native ++ #[group,node]

def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual primary family: a late or unresolved input escaped {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking complete original primary family {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The full selected33+N family of SAME actual complete primary source quadratures, before all history, target, sample and smoothing choices. The original full-forcing source, ordinary carrier, current graph and uncut input are retained; no localization or residual success is assumed (main:eq:primary-strain)."
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "actual primary family: nonstandard axioms {name}: {ax}"
  logInfo m!"PASS complete original primary family {key}/{p.size}: {ax}"

elab "publish_actual_primary_source_family " mode:num : command => liftTermElabM do
  unless mode.getNat ≤ 11 do throwError "actual primary family: unknown field"
  withFamily fun c => do
    if mode.getNat == 0 then
      let reached := c.operatorReached
      let Sop := app `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Sop
        c.data.selected[:33].toArray
      let hR₀ ← mkAppM ``le_trans
        #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS c.data.native[:44].toArray,
          c.data.native[45]!]
      let Sgraph := app (regular ++ `Graph.S) c.graphStatic
      let index := app ``primaryHistory
        #[c.data.native[0]!,c.data.native[29]!,c.data.native[32]!,Sgraph,Sop,c.data.native[44]!,
          hR₀,c.graph[37]!,reached,c.data.native[46]!,c.data.native[47]!,c.data.native[48]!,c.data.native[49]!]
      let value ← c.family index
      let target ← mkForallFVars #[c.label]
        (app `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial.GraphFamily c.graphStatic)
      save `historyMap c.fixed value target true
      return
    if mode.getNat == 10 then
      let proof ← c.family (app (source ++ `input_support) c.sourceArgs)
      let localInput ← mkAppM ``Subtype.val #[app (source ++ `input) c.sourceArgs]
      let target := (← inferType proof).replace fun e => if e == localInput then some (c.at `input) else none
      save `support c.fixed proof target
      return
    let (key,value) ←
      if mode.getNat == 1 then pure (`frequency,c.rho)
      else if mode.getNat == 2 then pure (`fine,c.R)
      else if mode.getNat == 3 then do
        let u ← mkAppM ``Subtype.val #[app (source ++ `input) c.sourceArgs]
        pure (`input,u)
      else if mode.getNat == 4 then pure (`discrepancy,app (source ++ `discrepancy) c.sourceArgs)
      else if mode.getNat == 5 then pure (`phase,app (phase ++ `representative) (← phaseArgs c))
      else if mode.getNat == 6 then do
        let u := c.at `input
        pure (`complexSource,app `JanetCartan.PhysicalInitialization.OriginalSampledObserved.complexSource
          #[c.data.native[0]!,c.domain,c.domain_measurable,u])
      else if mode.getNat == 7 then pure (`Q,app (coeff ++ `Q) c.native)
      else if mode.getNat == 8 then pure (`A,app (coeff ++ `A) c.data.native)
      else if mode.getNat == 11 then pure (`smoothInput,app (source ++ `input) c.sourceArgs)
      else do
        let B := app (raw ++ `amplitude) c.data.args
        let rotated ← mkAppM ``HSMul.hSMul #[app ``quadratureScalar #[c.imaginary],B]
        pure (`B,rotated)
    let family ← c.family value
    save key c.fixed family (← inferType family) true

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.FamilyTemplate
end
