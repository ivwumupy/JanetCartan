module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawCombinedNative

public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawGroupedRealization
import all JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticPrimitives
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActual
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate

/-!
# The actual raw angular differential on the original source input

The whole annular differential is evaluated at the original component adjoint
of the same inverse and source, with the same fixed prefix.  The previously
proved grouped raw identity then gives the actual raw source field.  This is
the angular summand of `main:eq:primary-strain`; no corrected derivative is
identified with its pre-response counterpart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section

namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceTemplate

open Lean Meta Elab Command
open PhysicalMean.OriginalCanonicalQuadraticSourceProfilesTemplate (getField)

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization
private def raw := `JanetCartan.PhysicalPrimary.OriginalRawSourceField
private def angular := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryRealization.Actual
private def source := `JanetCartan.PhysicalPrimary.OriginalRawSourceProfile

def app (key : Name) (p : Array Expr) : Expr := mkAppN (mkConst key) p

def bodyAt (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let some body := ci.value? (allowOpaque := true) |
    throwError "raw source factorization: missing original body {ci.name}"
  return ((body.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta

/-- Read the exact type of a constant application with one final substitution.
All original binders are retained; no remaining large type is repeatedly expanded. -/
def typeAt (e : Expr) : MetaM Expr := do
  let ci ← getConstInfo e.getAppFn.constName!
  let args := e.getAppArgs
  let rec remaining (count : Nat) (type : Expr) : MetaM Expr := do
    match count with
    | 0 => pure (type.instantiateRev args)
    | k+1 =>
      let .forallE _ _ body _ := type.consumeMData |
        throwError "raw source factorization: original constant application arity changed"
      remaining k body
  remaining args.size (ci.type.instantiateLevelParams ci.levelParams e.getAppFn.constLevels!)

def save (key : Name) (p : Array Expr) (proof target : Expr)
    (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "raw source factorization: unresolved field {key}"
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do
      throwError "raw source factorization: missing original metadata {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking original raw source factorization {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  let documentation := if key == `raw_factor_statement || key == `raw_factor_on_source_chart then
      "Exact factorization of the SAME complete pre-response primary derivative on its original source chart: the undoubled history carrier times the unscaled raw baseline plus the whole raw source amplitude. Original graph42, group, outer node, source, inverse, adjoint and prefix are retained. No analytic, residual, strain, or response success premise (main:eq:primary-strain; main:eq:lag-strain)."
    else if key == `raw_angular_smooth then
      "The SAME whole raw angular summand on the original unweighted adjoint input is smooth on the unchanged source chart, including zero angular labels (main:eq:primary-strain)."
    else
      "The SAME actual whole raw angular field at the original prefixed component adjoint has its exact observed demodulated derivative equal to the genuine raw native source field. Original source, global inverse, adjoint, phase, mask, sample and prefix are retained; no corrected-G identification or analytic success premise (main:eq:primary-strain)."
  addDocStringCore name documentation
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "raw source factorization: nonstandard axioms {ax}"
  logInfo m!"PASS original raw source factorization {key}/{p.size}: {ax}"

structure Data where
  primitive : Array Expr
  sourceArgs : Array Expr
  actualArgs : Array Expr
  input : Expr
  sourceData : Expr
  sample : Expr
  n : Expr
  N : Expr
  J : Expr
  refinedInput : Expr
  rawField : Expr
  baseline : Expr
  angularField : Expr
  chart : Expr

def Data.params (d : Data) : Array Expr := d.primitive ++ #[d.sourceData,d.sample]

/-- Decode only the original source and sample data; the actual input is the
unweighted component adjoint, before the unchanged fixed wide prefix. -/
def withSource (next : Data → MetaM Unit) : MetaM Unit := do
  PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun p fields => do
    unless p.size == 53 do throwError "raw source factorization: primitive53 changed"
    let n ← getField fields `n
    let N ← getField fields `N
    let J ← getField fields `J
    let ν ← getField fields `ν
    let sourceType ← mkAppM ``CoeSort.coe #[app `JanetCartan.CurrentMean.SmoothResidual #[n]]
    withLocalDeclD `source sourceType fun u => do
      withLocalDeclD `sample ν fun i => do
        let sourceArgs := p[:50].toArray ++ #[p[52]!,u,i]
        let rawField := app (raw ++ `raw) sourceArgs
        let native ← bodyAt rawField
        unless native.isAppOfArity (raw ++ `Native.raw) 69 do
          throwError "raw source factorization: original raw69 specialization changed"
        let sum ← bodyAt native
        unless sum.isAppOfArity ``HAdd.hAdd 6 do
          throwError "raw source factorization: original raw sum changed"
        let angularField := sum.getAppArgs[5]!
        unless angularField.isAppOfArity
            `JanetCartan.PhysicalPrimary.OriginalLocalWaves.Whole.full_angular.raw 66 do
          throwError "raw source factorization: original full angular summand changed"
        let input := angularField.getAppArgs.back!
        unless input.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalInput.wideInput 8 do
          throwError "raw source factorization: not the original unweighted wide input"
        let actualArgs ← PhysicalMean.OriginalMeanQuadraticPrimitives.Core.actualAtSample
          (← getField fields `G) i
        let refinedInput := mkAppN
          (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalInput.rawInput [.zero])
          #[n,J,ν,← getField fields `A,← getField fields `Q₀,u,i]
        let smooth ← typeAt (app (raw ++ `raw_smooth) sourceArgs)
        unless smooth.isAppOfArity ``ContDiffOn 11 do
          throwError "raw source factorization: same raw source smoothness changed"
        let originalChart := smooth.getAppArgs[10]!
        let some family := sum.getAppArgs[4]!.find? (·.isAppOfArity
            `JanetCartan.PhysicalPrimary.OriginalLocalWaves.T 53) |
          throwError "raw source factorization: original baseline T53 disappeared"
        let chart := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart
          family.getAppArgs[:23].toArray
        unless ← withTransparency .all (isDefEq originalChart chart) do
          throwError "raw source factorization: not the SAME original baseline source chart"
        next { primitive := p
               sourceArgs := sourceArgs
               actualArgs := actualArgs
               input := input
               sourceData := u
               sample := i
               n := n
               N := N
               J := J
               refinedInput := refinedInput
               rawField := rawField
               baseline := sum.getAppArgs[4]!
               angularField := angularField
               chart := chart }

private def renameDerivative (lhs field : Expr) : MetaM Expr := do
  let lhs := lhs.headBeta
  unless lhs.isAppOfArity ``HSMul.hSMul 6 do
    throwError "raw source factorization: original observation changed"
  let phase := lhs.getAppArgs[5]!
  unless phase.isAppOfArity ``HSMul.hSMul 6 do
    throwError "raw source factorization: original carrier demodulation changed"
  let matrix := phase.getAppArgs[5]!
  let m := matrix.getAppArgs
  unless m.size == 6 && m[4]!.isAppOfArity
      `JanetCartan.RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix 2 &&
      m[5]!.isAppOf ``fderiv do
    throwError "raw source factorization: original raw differential disappeared"
  let derivative := m[5]!
  let a := derivative.getAppArgs
  unless a[a.size-2]!.isAppOfArity (angular ++ `raw_angular) 54 do
    throwError "raw source factorization: forward theorem is not the actual raw angular field"
  let renamed := mkAppN derivative.getAppFn (a.set! (a.size-2) field)
  let matrix := mkAppN matrix.getAppFn (m.set! 5 renamed)
  let phase := mkAppN phase.getAppFn (phase.getAppArgs.set! 5 matrix)
  return mkAppN lhs.getAppFn (lhs.getAppArgs.set! 5 phase)

elab "identify_original_raw_source_derivative " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "raw source factorization: unknown mode"
  withSource fun d => do
    if mode.getNat == 0 then
      let proof := app (angular ++ `raw_angular_smooth_on_source) (d.actualArgs.push d.input)
      let t ← typeAt proof
      unless t.isAppOfArity ``ContDiffOn 11 do
        throwError "raw source factorization: raw angular smoothness changed"
      let target := mkAppN t.getAppFn (t.getAppArgs.set! 9 d.angularField)
      save `raw_angular_smooth d.params proof target
      return
    let stem := app (angular ++ `prefixed_forward)
      (d.actualArgs ++ #[d.primitive[52]!,d.refinedInput])
    forallBoundedTelescope (← typeAt stem) (some 2) fun point _ => do
      unless point.size == 2 do throwError "raw source factorization: original point/chart tail changed"
      let forward := mkAppN stem point
      let grouped := app `JanetCartan.PhysicalPrimary.OriginalRawGroupedRealization.raw_annular_sum_eq_field
        (d.params.push point[0]!)
      let ft ← bodyAt (app (angular ++ `prefixed_forward_statement)
        (d.actualArgs ++ #[d.primitive[52]!,d.refinedInput] ++ point))
      let gt ← typeAt grouped
      unless ft.isAppOfArity ``Eq 3 && gt.isAppOfArity ``Eq 3 do
        throwError "raw source factorization: original forward/grouped identities changed"
      let a := ft.getAppArgs
      let b := gt.getAppArgs
      let proof := mkAppN (mkConst ``Eq.trans ft.getAppFn.constLevels!)
        #[a[0]!,a[1]!,a[2]!,b[2]!,forward,grouped]
      let lhs ← renameDerivative a[1]! d.angularField
      let rhs := mkApp (app (source ++ `field) d.params) point[0]!
      let all := d.params ++ point
      let target ← mkEq lhs rhs
      if mode.getNat == 1 then
        save `observed_raw_angular_statement all target (mkSort .zero) true
      else
        save `observed_raw_angular_eq_source all proof
          (app (root ++ `observed_raw_angular_statement) all)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Factorization.SourceTemplate
end
