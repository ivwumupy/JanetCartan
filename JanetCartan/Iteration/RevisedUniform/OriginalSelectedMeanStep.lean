module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedPhysicalMeanPrecision
public import JanetCartan.Iteration.RevisedUniform.OriginalSelectedMeanNormalization
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean
/-!
# The actual mean error in the literal revised finite-step equation

Apply the exact selected52 normalization to the already proved requested
physical mean precision. The SAME actual Schwartz mean and full sampled self
remain, with the SAME finite Picard count for accuracy+1, fixed sample, core,
initial Saux/Serror gates and current-stage reaches. Only the normalized target
is rewritten as b^-2 times the SAME finite-moment smoothed metric defect.
Consumer: hmeanBound of `RevisedStage.increment_estimates_of_physicalSobolev_profiles`;
with this literal error, hmean is reflexivity (`main:eq:mean-equation`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
@[expose] noncomputable section
namespace JanetCartan.RevisedUniform.OriginalSelectedMeanStepTemplate
private theorem norm_error_after_normalization {n : ℕ}
    (A T S : MetricTensor n) (r : ℝ) (h : T = S) (hb : ‖A-T‖ ≤ r) : ‖A-S‖ ≤ r := by
  rw [← h]
  exact hb
end JanetCartan.RevisedUniform.OriginalSelectedMeanStepTemplate
end
public meta section
namespace JanetCartan.RevisedUniform.OriginalSelectedMeanStepTemplate
open Lean Meta Elab Command
private def fields := `JanetCartan.PhysicalMean.OriginalSelectedMeanData
private def source := fields ++ `physicalMean_error_le_requested_precision_on_common_core
private def normalization := `JanetCartan.RevisedUniform.OriginalSelectedMeanNormalization.normalizedTarget_eq_smoothedDefect
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
run_cmd liftTermElabM do
  forallBoundedTelescope (← getConstInfo source).type (some 60) fun p target => do
    unless p.size == 60 && target.isAppOfArity ``LE.le 4 do
      throwError "actual mean step: genuine requested precision60 changed"
    let selected := p[:33].toArray ++ p[34:53].toArray
    let x := p[57]!
    let norm := target.getAppArgs[2]!
    unless norm.isAppOfArity ``Norm.norm 3 do throwError "actual mean step: not the original physical error norm"
    let error := norm.getAppArgs[2]!
    unless error.isAppOfArity ``HSub.hSub 6 do throwError "actual mean step: original residual subtraction changed"
    let T := error.getAppArgs[5]!
    unless T == mkApp (app (fields ++ `normalizedTarget) selected) x do
      throwError "actual mean step: target is not the SAME selected52 at the original point"
    let eqProof := app normalization selected
    let eqType ← inferType eqProof
    unless eqType.isAppOfArity ``Eq 3 do throwError "actual mean step: normalization52 changed"
    let S := mkApp eqType.getAppArgs[2]! x
    unless (S.find? (·.isAppOf `JanetCartan.PhysicalSmoothing.smoothedDefect)).isSome do
      throwError "actual mean step: normalized right side lost the SAME smoothedDefect"
    let pointEq ← mkAppM ``congrFun #[eqProof,x]
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let proof := app ``norm_error_after_normalization
      #[n,error.getAppArgs[4]!,T,S,target.getAppArgs[3]!,pointEq,app source p]
    let type ← instantiateMVars (← mkForallFVars p (← inferType proof))
    let value ← instantiateMVars (← mkLambdaFVars p proof)
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
        throwError "actual mean step: added analytic input or unresolved field"
    unless value.getUsedConstants.contains source && value.getUsedConstants.contains normalization do
      throwError "actual mean step: genuine precision or exact normalization not consumed"
    let (type,value) := Lean.ShareCommon.shareCommon (type,value)
    let name := `JanetCartan.RevisedUniform.OriginalSelectedMeanStep.mean_error_le_requested_precision
    IO.println "Checking actual selected mean step precision60"
    (← IO.getStdout).flush
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
    addDocStringCore name "The actual SAME Schwartz mean, full sampled self and revised b^-2 smoothedDefect satisfy requested precision on the original final core. Genuine physical mean precision and exact selected normalization are applied internally; every unchanged remaining gate is numerical. No field replacement or analytic success premise (main:eq:mean-equation; RevisedStage.hmeanBound)."
    let ax ← collectAxioms name
    unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "actual mean step: nonstandard axioms {ax}"
    logInfo m!"PASS actual mean step precision60: SAME physical fields/Picard count/core/smoothedDefect, {ax}"
end JanetCartan.RevisedUniform.OriginalSelectedMeanStepTemplate
end
#print axioms JanetCartan.RevisedUniform.OriginalSelectedMeanStep.mean_error_le_requested_precision
