module
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourceQuadratic
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSelection
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampleBudgets
import all JanetCartan.Iteration.PhysicalSampling.OriginalWeights
import all JanetCartan.Iteration.PhysicalSampling.OriginalOuterWeights
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Uniform original total sample weight for the full Hermitian mean tensor

The SAME unnormalized μ already has an O(1) total mass. Apply the original
window/outer patch mass theorem, not the coefficientMass or squared-sqrtμ
budget. The constant is fixed BEFORE scale/history/shift/prefix/source.
Consumer: the complete baseline-plus-source Hermitian tensor's true-R profile
(`main:eq:mean-equation`, `main:prop:mean`). No sample-count loss, lower weight
bound, new event or field-profile premise is introduced.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped BigOperators
@[expose] noncomputable section
namespace JanetCartan.PhysicalMean.OriginalCanonicalWeightMass
private theorem cost_nonneg {J : Type} [Fintype J] (p : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    0 ≤ SeparatedSampling.countConstant p B * ((∑ _a : J, (1 : ℝ)) * (1 : ℝ)^3) := by
  unfold SeparatedSampling.countConstant SeparatedSampling.blockCountConstant
  positivity
end JanetCartan.PhysicalMean.OriginalCanonicalWeightMass
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalWeightMass
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalCanonicalWeightMass
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "actual total weight: unavailable {key}"
  return (value.beta p).headBeta
private def save (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual total weight: missing {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual total weight: later scale/history/sample/source escaped {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME original unnormalized sample weights have O(1) total mass, with a fixed before-history Cweight44. Uses actual window and outer patch bounds, not coefficientMass or squared sqrt weights; no h^-3/sample-count loss (main:eq:mean-equation; main:prop:mean)."
  logInfo m!"actual total original weight {key}/{p.size}: no sample-count or sqrt-weight-square loss"

elab "prove_original_total_weight " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "actual total weight: unknown mode"
  OriginalCanonicalSourceApplication.withActualQuadratic fun p _ _ fields _ => do
    withTransparency .default do
      let weight := fields[0]!
      let index := (← inferType weight).bindingDomain!
      unless index.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
        throwError "actual total weight: changed SAME sample type"
      let s := index.getAppArgs
      unless s[0]!.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.Index 22 &&
          s[2]!.isAppOfArity `JanetCartan.PhysicalSampling.OriginalOuterWeights.B 22 do
        throwError "actual total weight: changed fixed original rows/outer patch"
      let cube ← bodyAt `JanetCartan.PhysicalSampling.OriginalWeights.exists_cube s[0]!.getAppArgs
      unless cube.isAppOfArity `JanetCartan.PhysicalSampling.exists_finite_original_carrier_weight_bounds 5 do
        throwError "actual total weight: changed original row Fintype"
      let finite := cube.getAppArgs[1]!
      let dm ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalRow.D p[:50].toArray
      unless dm.isAppOfArity `JanetCartan.PhysicalSampling.OriginalJointEvent.measured_kernel 60 do
        throwError "actual total weight: changed original measured kernel60"
      let m := dm.getAppArgs
      let fixed := m[:46].toArray
      let rates := app `JanetCartan.PhysicalSampling.OriginalCommonStage.stage_rates
        (fixed ++ #[m[47]!,m[48]!,m[49]!])
      let h0 := app `JanetCartan.PhysicalSampling.OriginalCommonThreshold.T₀_ge_one fixed
      let hR ← mkAppM ``le_trans #[h0,Expr.proj ``And 0 rates]
      let R := (← inferType hR).getAppArgs[3]!
      let hw ← mkAppM `JanetCartan.PhysicalSampling.OriginalWindow.window_bounds #[m[45]!]
      let hweights := app `JanetCartan.PhysicalSampling.OriginalOuterWeights.patchBounds s[2]!.getAppArgs
      let one ← Term.TermElabM.run'
        (PhysicalBackground.NativeReferenceSourceTemplate.termWith [] "(1 : ℝ)")
      let unitProfile ← withLocalDeclNoLocalInstanceUpdate `row .default s[0]! fun row => mkLambdaFVars #[row] one
      let bound := mkAppN (mkConst `JanetCartan.UniformStep.sampleWeight_mass_le_originalScale [.zero])
        #[s[0]!,finite,s[1]!,s[2]!,one,unitProfile,s[3]!,s[4]!,hw,hweights,R,hR,s[6]!]
      let t ← inferType bound
      unless t.isAppOfArity ``LE.le 4 do throwError "actual total weight: changed mass inequality"
      let cost := t.getAppArgs[3]!
      let early := p[:44].toArray
      let C := app (root ++ `Cweight) early
      if mode.getNat == 0 then
        save `Cweight early cost (mkConst ``Real) true
      else if mode.getNat == 1 then
        let hB ← mkAppM ``le_of_lt #[app `JanetCartan.PhysicalSampling.OriginalOuterWeights.hB s[2]!.getAppArgs]
        let proof := app ``cost_nonneg #[s[0]!,finite,s[1]!,s[2]!,hB]
        let target := (← inferType proof).replace fun e => if e == cost then some C else none
        unless (target.find? (· == C)).isSome do throwError "actual total weight: changed exact fixed cost"
        save `Cweight_nonneg early proof target
      else
        let lhs := t.getAppArgs[2]!
        unless lhs.isAppOf ``Finset.sum do throwError "actual total weight: changed finite weight sum"
        let a := lhs.getAppArgs
        let sum := mkAppN lhs.getAppFn (a.set! (a.size-1) weight)
        let target := t.replace fun e => if e == lhs then some sum else if e == cost then some C else none
        save `weight_mass_le p[:51].toArray bound target

elab "prove_original_selected_total_weight" : command => liftTermElabM do
  let name := root ++ `weight_mass_le
  forallBoundedTelescope (← getConstInfo name).type (some 50) fun p _ => do
    unless p.size == 50 do throwError "actual total weight: changed selected native50"
    let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift p
    let proof := app name (p.push shift)
    save `selected_weight_mass_le p proof (← inferType proof)
end JanetCartan.PhysicalMean.OriginalCanonicalWeightMass
end

prove_original_total_weight 0
prove_original_total_weight 1
prove_original_total_weight 2
prove_original_selected_total_weight
