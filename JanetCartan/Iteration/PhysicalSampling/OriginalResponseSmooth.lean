module

public import JanetCartan.Iteration.PhysicalSampling.OriginalResponseWindow
public import JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularity
public meta import Lean

/-!
# The original uncut source response on the sampler's actual open working region

The qualitative row obligation in the measured Berry/Bernstein kernel uses
joint `(x,c,z)` smoothness on the root-centered sampling ball. Specialize the
actual ordinary source53/weak38 uncut solver at that same selected, capped
family and restrict its checked full response from `univ × V`. No separate
response smoothness or domain-containment hypothesis is added. The physical
source admission itself (in particular the scalar is in the native span and
meets its high size profile) remains explicit until the actual initial density
is substituted (`app:ch_response:cor:current-atoms`, `app:ch_waves:thm:sampling`).
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalResponseSmoothApplication
open Lean Meta Elab Command

elab "restrict_actual_uncut_response_to_sampling_ball" : command => liftTermElabM do
  let ps := `JanetCartan.PhysicalSampling
  let source := `JanetCartan.PhysicalPrimary.OriginalJointResponseRegularity.full_response_smooth
  forallBoundedTelescope (← getConstInfo (ps ++ `OriginalMargins.δ)).type (some 22) fun fixed _ => do
    let cap := mkAppN (mkConst (ps ++ `samplingCappedExtra)) #[fixed[0]!,fixed[1]!,fixed[2]!,fixed[21]!]
    let ordinary21 := (fixed[:2].toArray ++ fixed[3:22].toArray).set! 20 cap
    let sourcePrefix := mkAppN (mkConst source) ordinary21
    forallBoundedTelescope (← inferType sourcePrefix) (some 36) fun rest t => do
      let s := ordinary21 ++ rest
      let x := fixed ++ rest
      unless s.size == 57 && t.isAppOf ``ContDiffOn do throwError "uncut sampler response: changed source57 joint profile"
      let hsub := mkAppN (mkConst (ps ++ `OriginalResponseWindow.working_open_in_source_window)) (fixed.push s[34]!)
      let subType ← inferType hsub
      let sub := subType.getAppArgs
      let O := sub[sub.size-2]!
      let a := t.getAppArgs
      unless a.size == 11 && O.isAppOf ``Metric.ball do throwError "uncut sampler response: lost actual open working ball"
      let h := mkAppN (mkConst ``ContDiffOn.mono t.getAppFn.constLevels!)
        (a[:8].toArray ++ #[a[10]!,a[9]!,a[8]!,mkAppN sourcePrefix rest,O,hsub])
      let g := mkAppN t.getAppFn (a.set! 10 O)
      logInfo "recovered original whole-working-region proof and the literal source57 uncut response"
      let type ← instantiateMVars (← mkForallFVars x g)
      let value ← instantiateMVars (← mkLambdaFVars x h)
      if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar || type.hasLevelMVar ||
          value.hasLevelMVar || type.hasSorry || value.hasSorry then throwError "uncut sampler response: open actual source application"
      let declName := ps ++ `OriginalResponseWindow.full_response_smooth_on_working_ball
      addDecl (.thmDecl {name := declName, levelParams := [],type,value}) (forceExpose := true)
      logInfo "checked the actual uncut ordinary source57 response on its SAME capped root-centered sampling ball; no response smoothness or domain premise"

end JanetCartan.PhysicalSampling.OriginalResponseSmoothApplication
end

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 2400000

restrict_actual_uncut_response_to_sampling_ball
