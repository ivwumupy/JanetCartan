module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalInitialSourceApplication
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialData
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceScalar
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceProfiles
public meta import Lean

/-!
# The genuine native initial field in the unchanged original Source53

Apply the actual higher-reserve native density profile to Source53 input 52,
then apply the original full source constructor. Both declarations retain the
same source39 row, reached original native/source thresholds, physical history,
coefficient scale and positive source rate. The unscaled initial budget is
shifted by 16, the size is exactly σ, and the scalar is the sole canonical
`OriginalNativeSourceScalar.scalar`. No profile-success premise, new scalar,
row maximum, threshold, sample, cutoff or current is chosen here.

The source52/source53 split only resets elaboration work; the second theorem
uses the first by name. Consumers: the actual graded response and original
uncut source application (`app:ch_response:eq:response-graded-source`,
`app:ch_response:cor:current-atoms`). The frozen after16 and local-wave leaves
are not changed by publishing this independent application.
-/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalActualInitialSource
open Lean Meta Elab Command
open JanetCartan.PhysicalSampling.OriginalNativeSourceRowsApplication

private def root := `JanetCartan.PhysicalPrimary.OriginalActualInitialSource
private def native := `JanetCartan.PhysicalSampling.OriginalNativeInitialEvent
private def source := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
private def scalar := `JanetCartan.PhysicalSampling.OriginalNativeSourceScalar.scalar

private def save (field : Name) (xs : Array Expr) (proof target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars xs target)
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  if type.hasFVar || type.hasMVar || type.hasLevelMVar || type.hasSorry ||
      value.hasFVar || value.hasMVar || value.hasLevelMVar || value.hasSorry then
    throwError "actual original initial source: open declaration {field}"
  addDecl (.thmDecl {name := root ++ field, levelParams := [], type, value})
    (forceExpose := true)

/-- Open the existing static source39 row and the native profile's unchanged
physical history. `xs` is fixed44, response-budget3, native-history6, then
`i`, reached-source-row, rate and rate-positivity. There is no new selection. -/
private def withActual (next : Data → Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit :=
  withTransparency .reducible <| withSourceData fun d => do
    let pre := mkAppN (mkConst (native ++ `S)) d.initial44
    forallBoundedTelescope (← inferType pre) (some 3) fun resp _ => do
      let high := d.initial44 ++ resp
      let profile := mkAppN (mkConst (native ++ `native_initial_profile)) high
      forallBoundedTelescope (← inferType profile) (some 6) fun history _ => do
        unless history.size == 6 do throwError "actual original initial source: changed native history"
        let R := history[0]!
        let hHigh := history[1]!
        let hist := history[2:6].toArray
        let sourceS := mkAppN (mkConst (source ++ `S)) d.source39
        withLocalDeclD `hRow (← mkAppM ``LE.le #[sourceS,R]) fun hRow => do
          withLocalDeclD `rate (mkConst ``Real) fun rate => do
            let zero ← mkNumeral (mkConst ``Real) 0
            withLocalDeclD `hRate (← mkAppM ``LT.lt #[zero,rate]) fun hRate => do
              let hn ← mkAppM `le_trans #[mkAppN (mkConst (native ++ `native_le)) high,hHigh]
              let actualScalar := mkAppN (mkConst scalar) (d.native33 ++ #[R,hn] ++ hist ++ #[d.i])
              let K := mkAppN (mkConst `JanetCartan.currentCoefficientScale) #[R,hist[0]!]
              let σ := d.native33[21]!
              let sign ← mkAppM `le_of_lt #[Expr.proj ``And 0 d.native33[23]!]
              let s52 := d.source39 ++ #[R,hRow] ++ hist ++
                #[K,← mkAppM `le_refl #[K],rate,hRate,actualScalar,σ,sign]
              unless s52.size == 52 do throwError "actual original initial source: changed Source53 spine"
              let xs := d.fixed ++ resp ++ history ++ #[d.i,hRow,rate,hRate]
              next d high history xs s52

/-- Construct the genuine source52 inequality, then the same full-source
consequent using that checked named inequality. No analytic field is assumed. -/
elab "construct_original_actual_initial_source " which:num : command => liftTermElabM do
  withActual fun d high history xs s52 => do
    match which.getNat with
    | 0 =>
      let sourceApp := mkAppN (mkConst (source ++ `full_source_profiles)) s52
      let needed := (← whnf (← inferType sourceApp)).bindingDomain!
      let bound ← forallBoundedTelescope needed (some 1) fun _ t => do
        unless t.isAppOfArity ``LE.le 4 do
          throwError "actual original initial source: source52 target changed"
        let args := t.getAppArgs[2]!.getAppArgs
        let A := mkAppN (mkConst (native ++ `initialC)) (d.initial44.push d.i)
        let actual := mkAppN (mkConst (native ++ `native_initial_profile)) (high ++ history ++ #[d.i])
        JanetCartan.PhysicalPrimary.OriginalInitialSourceApplication.apply_source53_after16
          args[args.size-3]! args.back! s52[45]! s52[50]! A d.source39[37]! actual
      save `source52 xs bound needed
      logInfo "checked actual native54 → source52: sole scalar, unscaled initialC(k+16), one sigma, same original row/history"
    | 1 =>
      let bound := mkAppN (mkConst (root ++ `source52)) xs
      let full := mkAppN (mkConst (source ++ `full_source_profiles)) (s52.push bound)
      save `source53 xs full (← inferType full)
      logInfo "checked actual original Source53 consequent using the canonical source52; no new selection or high-profile premise"
    | _ => throwError "actual original initial source: unknown construction stage"

end JanetCartan.PhysicalPrimary.OriginalActualInitialSource
end

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 2800000
set_option backward.isDefEq.respectTransparency false

construct_original_actual_initial_source 0
construct_original_actual_initial_source 1
