module

public import JanetCartan.Iteration.PhysicalPairs.OriginalCompleteAmplitude
public import JanetCartan.Iteration.PhysicalPairs.SampledQuadrature
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalProfiles
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianSupportTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication

/-!
# The original primary angle at the ordinary history frequency

The graph, group and node are read from the actual complete source wave before
using any strain or amplitude estimate.  The original quotient angle is the
history frequency times the same undoubled radial `group_phase`.  Only the
original sample-coordinate equality and inverse-rate arithmetic are used
(`main:eq:primary-strain`, `app:ch_regular:eq:source-tail`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] noncomputable section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.PhaseTemplate

private theorem original_rate (a r l : ℝ) : a / (r*l)⁻¹ = l*(r*a) := by
  rw [div_inv_eq_mul]
  ring

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.PhaseTemplate
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.PhaseTemplate

open Lean Meta Elab Command

private def app (key : Name) (p : Array Expr) : Expr := mkAppN (mkConst key) p

private def bodyAt (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let some body := ci.value? (allowOpaque := true) |
    throwError "ordinary source phase: missing original body {ci.name}"
  return ((body.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta

private def sourceTelescope (type : Expr)
    (next : Array Expr → Expr → MetaM Unit) : MetaM Unit := loop 53 type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0, type, p => next p (type.instantiateRev p)
    | k+1, type, p => do
      let .forallE key domain body bi := type.consumeMData |
        throwError "ordinary source phase: original source53 ended at {p.size}"
      let domain := domain.instantiateRev p
      if bi == .instImplicit then
        withLocalDecl key bi domain fun x => loop k body (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate key bi domain fun x => loop k body (p.push x)

elab "check_original_primary_carrier " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "ordinary source phase: unknown proof stage"
  let wave := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourceCombinedWave
  sourceTelescope (← getConstInfo wave).type fun p _ => do
    let whole ← bodyAt (app wave p)
    unless whole.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalLocalWaves.Combined.field 69 do
      throwError "ordinary source phase: actual whole69 field changed"
    let graph := whole.getAppArgs[:42].toArray
    unless graph[36]! == p[44]! && graph[38]! == p[46]! do
      throwError "ordinary source phase: source graph changed its original history scale"
    let sum ← bodyAt whole
    unless sum.isAppOfArity ``HAdd.hAdd 6 do
      throwError "ordinary source phase: actual baseline-plus-angular sum changed"
    let angular := sum.getAppArgs[5]!
    unless angular.isAppOfArity
        `JanetCartan.PhysicalPrimary.OriginalLocalWaves.Whole.full_angular.corrected 66 do
      throwError "ordinary source phase: actual angular parameter spine changed"
    unless angular.getAppArgs[:42].toArray == graph do
      throwError "ordinary source phase: the complete and angular graphs differ"
    let node := angular.getAppArgs[64]!
    let i := p[52]!
    let index ← inferType i
    unless index.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
      throwError "ordinary source phase: original sample type changed"
    let row := Expr.proj ``Sigma 0 i
    let sample := Expr.proj ``Subtype 0 (Expr.proj ``Sigma 1 i)
    let color := app `JanetCartan.SeparatedSampling.color
      #[index.getAppArgs[1]!,Expr.proj ``Prod 0 sample]
    let group ← mkAppM ``Prod.mk #[row,color]
    let hcoord := app
      ``PhysicalMean.OriginalBackgroundHermitianSupportTemplate.outer_sampling_node #[node]
    let hct ← inferType hcoord
    unless hct.isAppOfArity ``Eq 3 do
      throwError "ordinary source phase: original sample coordinates changed"
    let z := hct.getAppArgs[2]!
    let nativePhase := app `JanetCartan.PhysicalPairs.SampledQuadrature.group_phase graph
    let radial ← bodyAt nativePhase
    unless radial.isAppOfArity `JanetCartan.PhysicalPairs.SampledQuadrature.radialCarrier 11 do
      throwError "ordinary source phase: original radial carrier changed"
    let r := mkApp radial.getAppArgs[7]! group
    let R := app `JanetCartan.historyScale #[p[44]!,mkConst `JanetCartan.growthExponent,p[46]!]
    let rho ← mkAppM ``HPow.hPow #[R,mkConst `JanetCartan.carrierExponent]
    let phase := app `JanetCartan.PhysicalPairs.OriginalCompleteAmplitude.phase p
    withLocalDeclD `x (← inferType phase).bindingDomain! fun x => do
      let angle := (mkApp (← bodyAt phase) x).headBeta
      unless angle.isAppOfArity ``HDiv.hDiv 6 do
        throwError "ordinary source phase: original inverse-rate angle changed"
      let hcarrier ← mkAppM ``congrArg #[angle.getAppArgs[4]!.appFn!,hcoord]
      let a := (← inferType hcarrier).getAppArgs[2]!
      let algebra := app ``original_rate #[a,r,rho]
      let quotient ← withLocalDeclD `t (mkConst ``Real) fun t =>
        mkLambdaFVars #[t] (mkAppN angle.getAppFn (angle.getAppArgs.set! 4 t))
      let first ← mkAppM ``congrArg #[quotient,hcarrier]
      let ft ← inferType first
      let algebraType ← inferType algebra
      unless ft.isAppOfArity ``Eq 3 && algebraType.isAppOfArity ``Eq 3 do
        throwError "ordinary source phase: rate arithmetic changed"
      let f := ft.getAppArgs
      let proof := mkAppN (mkConst ``Eq.trans ft.getAppFn.constLevels!)
        #[f[0]!,f[1]!,f[2]!,algebraType.getAppArgs[2]!,first,algebra]
      let ordinary := mkAppN nativePhase #[group,z,x]
      let target ← mkEq (mkApp phase x) (← mkAppM ``HMul.hMul #[rho,ordinary])
      let params := p.push x
      let root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization
      let isStatement := mode.getNat == 0
      let key := if isStatement then `phase_statement else `phase_eq_original_carrier
      let declarationTarget := if isStatement then mkSort .zero else app (root ++ `phase_statement) params
      let declarationValue := if isStatement then target else proof
      let type ← instantiateMVars (← mkForallFVars params declarationTarget)
      let value ← instantiateMVars (← mkLambdaFVars params declarationValue)
      let env ← getEnv
      for e in #[type,value] do
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
          throwError "ordinary source phase: extra or unresolved input"
        unless (e.getUsedConstants.filter (fun c => (env.find? c).isNone)).isEmpty do
          throwError "ordinary source phase: missing original metadata"
      let (type,value) := Lean.ShareCommon.shareCommon (type,value)
      let name := root ++ key
      IO.println s!"Kernel checking SAME original source angle and graph42 {key}/54"
      (← IO.getStdout).flush
      if isStatement then
        addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
      else
        addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
      addDocStringCore name "The actual complete source wave's angle equals its original history frequency times the literal ordinary group_phase on the SAME graph42, group, outer node and source. Only original sample-coordinate transport and inverse-rate arithmetic are used, without a strain/profile premise or a doubled phase (main:eq:primary-strain)."
      let ax ← collectAxioms name
      unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
        throwError "ordinary source phase: nonstandard axioms {ax}"
      logInfo m!"PASS original source angle {key}/54: {ax}"

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.PhaseTemplate
end

