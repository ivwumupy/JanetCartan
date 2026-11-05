module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceAmplitude
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourcePlateau
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.Measure
/-! # Remove the original source observation on the whole pair chart

The existing original23 chart is not shrunk. The actual source-observation
plateau and original half-cell bound identify the complete physical angular
amplitude with the canonical source derivative at the quotient point.
Consumer: `main:eq:mean-final-amplitude` and the genuine pair node profile.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Set Metric
namespace JanetCartan.PhysicalPairs.OriginalSourceChartTemplate
/-- The pre-existing observation support and its actual one-value put a point
inside the original periodization cell; no new support is selected. -/
theorem representative_of_observation_one {n : ℕ} {μ : ℝ}
    {ψ : Euclidean n → ℝ}
    (hsupport : tsupport ψ ⊆ closedBall 0 (4*μ)) (hcell : 4*μ < 1/2)
    {x : Euclidean n} (hone : ψ x = 1) :
    AmplitudeBound.centeredTorusRepresentative (torusQuotient x) = x :=
  PeriodicLocalL2.centeredTorusRepresentative_quotient
    (ContinuumRow.FixedCutoffs.closedBall_four_subset_cell hcell
      (hsupport (subset_tsupport ψ (hone.trans_ne one_ne_zero))))

/-- Remove only the same observation and representative from an exact matrix
identity. This avoids re-elaborating the original native wave's type. -/
theorem remove_observation {n N : ℕ} {ψ : Euclidean n → ℝ}
    {A : Euclidean n → Matrix (Fin N) (Fin n) ℂ} {a : Matrix (Fin N) (Fin n) ℂ}
    {x y : Euclidean n} (h : a = ψ x • A x) (hxy : x = y) (hone : ψ y = 1) :
    a = A y := by
  rw [h,hxy,hone,one_smul]
end JanetCartan.PhysicalPairs.OriginalSourceChartTemplate
end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSourceChartTemplate
open Lean Meta Elab Command
open PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSourceAmplitude
private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args
private def termWith (vars : List (Name × Expr)) (code : String)
    (goal : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code goal)
private def save (key : Name) (params : Array Expr) (value : Expr) (data : Bool)
    (target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "original source chart: unresolved {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  liftM <| IO.eprintln s!"original source chart: kernel checking {name}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  liftM <| IO.eprintln s!"original source chart: kernel passed {name}"

elab "identify_original_source_angular_on_chart " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "original source chart: unknown publication mode"
  withActualSelectedSourceWave fun params _ input _ _ _ _ => do
    liftM <| IO.eprintln "original source chart: actual source callback ready"
    let n := input.getAppArgs[0]!
    let space := app `JanetCartan.Euclidean #[n]
    let statement := ns ++ `observed_angular_statement
    let info ← getConstInfo statement
    let .some body := info.value? (allowOpaque := true) |
      throwError "original source chart: unavailable checked observation statement"
    let result ← withLocalDeclD `x space fun x => do
      let quotient := app `JanetCartan.torusQuotient #[n,x]
      let eq := (body.beta (params.push quotient)).headBeta
      unless eq.isAppOfArity ``Eq 3 do throwError "original source chart: changed exact observed matrix equality"
      let rhs := eq.getAppArgs[2]!
      unless rhs.isAppOfArity ``HSMul.hSMul 6 do throwError "original source chart: lost original observation"
      let obsPoint := rhs.getAppArgs[4]!
      let obs := obsPoint.appFn!
      unless obs.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.observationFunction 22 do
        throwError "original source chart: not the SAME original common observation22"
      let representative := obsPoint.appArg!
      let some wave := rhs.find? (·.isAppOfArity `JanetCartan.CanonicalAtomRealization.wholeSourceCorrectedWave 20) |
        throwError "original source chart: lost complete original source wave"
      let T := wave.getAppArgs[6]!
      unless T.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalLocalWaves.T 53 do
        throwError "original source chart: missing native original source53"
      let source := T.getAppArgs
      liftM <| IO.eprintln "original source chart: exact observed equality and source53 ready"
      let chart := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart source[:23].toArray
      withLocalDeclD `hx (← mkAppM `Membership.mem #[chart,x]) fun hx => do
        let germ := app `JanetCartan.PhysicalPairs.OriginalSourcePlateau.germ_on_original_chart
          (source[:23].toArray ++ #[x,hx])
        liftM <| IO.eprintln "original source chart: original23 germ applied"
        let hone ← mkAppM ``Filter.EventuallyEq.eq_of_nhds #[germ]
        liftM <| IO.eprintln "original source chart: observation is one"
        let hsupport := app `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.observation_support obs.getAppArgs
        let hcell := app `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.observation_cell obs.getAppArgs
        let cutoffInfo ← getConstInfo `JanetCartan.PhysicalMean.OriginalCanonicalDerivative.observationCutoff
        let cutoff := (cutoffInfo.value! (allowOpaque := true)).beta obs.getAppArgs
        unless cutoff.isAppOfArity `JanetCartan.ContinuumRow.FixedCutoffs.physical 4 do
          throwError "original source chart: original observation cutoff shape changed"
        let μ := cutoff.getAppArgs[1]!
        let hre := app ``representative_of_observation_one #[n,μ,obs,hsupport,hcell,x,hone]
        liftM <| IO.eprintln "original source chart: centered representative removed on original cell"
        let angular := rhs.getAppArgs[5]!.replace fun e => if e == representative then some x else none
        let target ← mkEq eq.getAppArgs[1]! angular
        let hnative := app (ns ++ `observed_angular_amplitude) (params.push quotient)
        let matrixField := rhs.getAppArgs[5]!.appFn!
        let N := wave.getAppArgs[1]!
        let proof := app ``remove_observation #[n,N,obs,matrixField,eq.getAppArgs[1]!,representative,x,hnative,hre,hone]
        return (← mkLambdaFVars #[x,hx] proof, ← mkForallFVars #[x,hx] target)
    if mode.getNat == 0 then
      save `angular_on_original_statement params result.2 true (mkSort .zero)
    else
      save `angular_on_original_chart params result.1 false (app (ns ++ `angular_on_original_statement) params)
end JanetCartan.PhysicalPairs.OriginalSourceChartTemplate
end
