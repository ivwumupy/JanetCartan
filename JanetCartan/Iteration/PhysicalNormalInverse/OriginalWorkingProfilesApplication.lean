module

public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalRetainedProfiles
public import JanetCartan.Iteration.PhysicalNormalInverse.WorkingBallProfiles
public import JanetCartan.Iteration.PhysicalSampling.OriginalWorkingRadius
public meta import Lean

/-!
# The actual retained fields on the literal original sampling radius

Read the selected cell from the identical current getter. Its original root
certificate supplies the one already-named working radius. Restrict all five
profiles and the free-covector jets, retaining the SAME budgets and current
coefficient functions. No geometric or analytic witness is reselected.
-/

public meta section
namespace JanetCartan.PhysicalNormalInverse.OriginalWorkingProfilesApplication
open Lean Meta Elab Command

private def save (name : Name) (params : Array Expr) (proof : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params (← inferType proof))
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  if value.hasFVar || value.hasMVar || value.hasSorry || type.hasFVar || type.hasMVar || type.hasSorry then
    throwError "original working profiles: incomplete theorem {name}"
  addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)

private def component (proof : Expr) (index : Nat) : MetaM Expr := do
  let mut proof := proof
  for _ in [:index] do
    proof ← mkAppM ``And.right #[proof]
  let type ← whnf (← inferType proof)
  if type.isAppOfArity ``And 2 then mkAppM ``And.left #[proof] else pure proof

private def conjunction (parts : Array Expr) : MetaM Expr := do
  let mut proof := parts.back!
  for i in (List.range (parts.size - 1)).reverse do
    proof ← mkAppM ``And.intro #[parts[i]!, proof]
  return proof

private def retainedArgs (params : Array Expr) : MetaM (Array Expr) := do
  let mut value := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalCurrent.current) params
  for _ in [:4] do
    if value.getAppFn.isConstOf `JanetCartan.PhysicalPrimary.LeadingCell.current then break
    let some body := (← getConstInfo value.getAppFn.constName!).value?
      | throwError "original working profiles: current alias has no body"
    value := body.beta value.getAppArgs
  unless value.getAppFn.isConstOf `JanetCartan.PhysicalPrimary.LeadingCell.current && value.getAppArgs.size == 36 do
    throwError "original working profiles: expected actual retained36"
  return value.getAppArgs

/-- Supply the actual original root and restrict the closed same-cap positive
coefficient profiles, without adding any geometric admission hypothesis. -/
elab "apply_profiles_on_original_working_radius" : command => liftTermElabM do
  let root := `JanetCartan.PhysicalNormalInverse.OriginalRetained
  let producer := root ++ `positive_continuation
  let info ← getConstInfo producer
  forallTelescopeReducing info.type fun all _ => do
    unless all.size == 51 do throwError "original working profiles: expected actual positive51"
    let fixed := all[:31].toArray
    let profileParams := all[:34].toArray
    let n := fixed[0]!
    let hn := fixed[1]!
    let i := all[31]!
    let hNative ← mkAppM `le_trans
      #[mkAppN (mkConst (root ++ `S_native)) profileParams, all[35]!]
    let native := fixed ++ #[all[34]!, hNative] ++ all[36:40].toArray ++ #[i]
    let args ← retainedArgs native
    let q ← mkAppM ``Subtype.val #[← mkAppM ``Sigma.fst #[i]]
    let l ← mkAppM ``Sigma.snd #[i]
    let cell := args[35]!
    let patch := args[4]!.getAppArgs.back!
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[n, hn, fixed[20]!]
    let selected := fixed[:21].toArray.set! 20 capped
    let hroot ← mkAppM ``And.right
      #[mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.fact1) (selected ++ #[q, l])]
    let radius := mkAppN (mkConst `JanetCartan.PhysicalSampling.originalSamplingRadius)
      #[n, hn, q, l, cell]
    let hRadius ← mkAppM ``Subtype.property #[radius]
    let spec := mkAppN (mkConst `JanetCartan.PhysicalSampling.originalSamplingRadius_spec)
      #[n, hn, q, l, cell, hroot]
    let hcontain ← component spec 0
    let hphaseClosed ← component spec 1
    let hSigma ← component
      (mkAppN (mkConst `JanetCartan.PhysicalSeed.OriginalBoundary.comparison_pos)
        #[n, hn, patch, cell]) 8
    let original := mkAppN (mkConst producer) all
    let Q := mkAppN (mkConst `JanetCartan.PhysicalPrimary.LeadingData.Q) args[:35].toArray
    let phaseSmooth ← mkAppM ``JanetCartan.LeadingWave.FullModulation.phaseGradient_joint_smooth
      #[args[4]!, Q]
    let oldPhaseSmooth ← mkAppM ``ContDiffOn.mono #[phaseSmooth, ← component original 3]
    let phaseRestriction ← mkAppM ``JanetCartan.PhysicalNormalInverse.retained_profile_on_working_ball
      #[hSigma, hRadius, hcontain, oldPhaseSmooth, ← component original 8]
    let mut smooth : Array Expr := #[]
    let mut profiles : Array Expr := #[← mkAppM ``And.right #[phaseRestriction]]
    for k in [:4] do
      let restriction ← mkAppM ``JanetCartan.PhysicalNormalInverse.retained_profile_on_working_ball
        #[hSigma, hRadius, hcontain, ← component original (k + 4), ← component original (k + 9)]
      smooth := smooth.push (← mkAppM ``And.left #[restriction])
      profiles := profiles.push (← mkAppM ``And.right #[restriction])
    let hsmall ← mkAppM ``JanetCartan.PhysicalNormalInverse.working_ball_subset_retained_ball
      #[hRadius, hcontain]
    let oldJets ← component original 13
    let jets ← forallBoundedTelescope (← inferType oldJets) (some 2) fun jw _ => do
      unless jw.size == 2 do throwError "original working profiles: expected jet order and point"
      let membership := (← inferType (mkApp hsmall jw[1]!)).bindingDomain!
      withLocalDeclD `hw membership fun hw => do
        mkLambdaFVars (jw.push hw)
          (mkAppN oldJets #[jw[0]!, jw[1]!, mkAppN hsmall #[jw[1]!, hw]])
    let proof ← conjunction
      (#[← component original 0, ← component original 1, ← component original 2, hphaseClosed] ++
        smooth ++ profiles ++ #[jets])
    save (root ++ `on_original_sampling_radius) all proof
    logInfo "kernel-checked actual positive51 on ONE named originalSamplingRadius; all five budgets and coefficient functions unchanged"

end JanetCartan.PhysicalNormalInverse.OriginalWorkingProfilesApplication
