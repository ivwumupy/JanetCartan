module

public import JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEvent
public import JanetCartan.Iteration.PhysicalSampling.OriginalSobolevTest
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredMeanBudgetsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgetsApplication
public meta import Lean.Elab.Command

/-!
# Add the physical amplitude test to the very same original event

Open exactly one existential from the actual positive-density joint event.
Keep its entire measured/scalar, count, mass, geometry and quadrature statement.
For THIS shift family, and for every admissible prefix, apply the original
physical matrix Sobolev test using its native scalar operator norm. This adds
no hypotheses to the three genuinely needed high-profile producer conclusions
(`new:eq:amplitude-test`, `app:ch_waves:thm:sampling`).
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalSobolevEventApplication
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalSampling
private def upstream := root ++ `OriginalPositiveEvent.exists_of_high_initial_and_response_profiles
private def resultName := root ++ `OriginalPositiveEvent.exists_with_physical_amplitude_test

elab "attach_original_physical_sobolev_test" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo upstream).type (some 57) fun x ex => do
    let ex ← whnf ex
    unless x.size == 57 && ex.isAppOfArity ``Exists 2 do
      throwError "physical amplitude event: missing original positive57 and its SINGLE shift family"
    let prior := mkAppN (mkConst upstream) x
    let a := ex.getAppArgs
    let proof ← withLocalDeclD `ξ a[0]! fun ξ => do
      withLocalDeclD `sameEvent ((mkApp a[1]! ξ).headBeta) fun same => do
        let mut tail := same
        for _ in [:4] do tail := .proj ``And 1 tail
        let normBound := Expr.proj ``And 0 tail
        let amp ← forallBoundedTelescope (← inferType normBound) (some 2) fun rowArgs t => do
          unless rowArgs.size == 2 && t.isAppOfArity ``LE.le 4 do
            throwError "physical amplitude event: missing one native norm for every original prefix"
          let some T := t.getAppArgs[2]!.find? (·.isAppOf ``PhysicalSamplingShells.nativeScalarOperator)
            | throwError "physical amplitude event: not the norm of the original scalar operator"
          let args := T.getAppArgs
          let native := args.extract (args.size - 8) args.size
          unless native.size == 8 && native[7]! == rowArgs[0]! do
            throwError "physical amplitude event: changed mesh/extended shifts/kernel/prefix"
          let S ← mkAppOptM ``OriginalSobolevTest.native_physical_amplitude_test
            (args.map some ++ #[some t.getAppArgs[3]!,some (mkAppN normBound rowArgs)])
          mkLambdaFVars rowArgs S
        let both ← mkAppM ``And.intro #[same,amp]
        let result ← inferType both
        let predicate ← mkLambdaFVars #[ξ] result
        let one ← mkAppOptM ``Exists.intro #[none,some predicate,some ξ,some both]
        let branch ← mkLambdaFVars #[ξ,same] one
        mkAppM ``Exists.elim #[prior,branch]
    let type ← instantiateMVars (← mkForallFVars x (← inferType proof))
    let value ← instantiateMVars (← mkLambdaFVars x proof)
    if type.hasMVar || value.hasMVar || type.hasLevelMVar || value.hasLevelMVar ||
        type.hasFVar || value.hasFVar || type.hasSorry || value.hasSorry then
      throwError "physical amplitude event: an event-dependent or free assumption escaped"
    addDecl (.thmDecl {name := resultName, levelParams := [], type, value}) (forceExpose := true)
    logInfo "one original positive57 witness, all prior fields AND true physical H^ell matrix amplitude action on the same native shell measure"

end JanetCartan.PhysicalSampling.OriginalSobolevEventApplication
end

@[expose] public noncomputable section
set_option maxRecDepth 32000
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
attach_original_physical_sobolev_test
