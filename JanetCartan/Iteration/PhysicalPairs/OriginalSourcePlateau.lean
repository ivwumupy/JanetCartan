module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceMasks
/-! # The original pair chart lies on the common observation plateau

The chart is the original inverse-mask chart, not a newly selected smaller
support. Its entire radius is bounded by the original screened mask family,
so the common measured source observation equals one in a neighborhood of
every point. Consumer: removal of observation from the actual source-data
amplitude identity in `main:eq:mean-final-amplitude` and `main:prop:pairs`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Metric Filter
open scoped Topology
namespace JanetCartan.PhysicalPairs.OriginalSourcePlateau
open PhysicalInitialization RegularSector.FiniteMasks.ActualFamily

/-- The original chart lies strictly inside the pre-existing common source
plateau; no additional cutoff or smaller pair window is chosen. -/
theorem original_chart_germ {d : ℕ} (hn : 5 ≤ d+1) {r μ : ℝ}
    (hr : 0 < r) (hμ : 0 < μ) {Ω K : Set (Euclidean (d+1))} {M : ℝ}
    (f : ActualMaskFamily Ω 0 (OriginalRegular.coreRadius hn
      (OriginalRegular.screenedRadius hn r μ)) (cubeStress (d+1)) K M)
    (t : ℝ) (x : Euclidean (d+1)) (hx : x ∈ ball 0 (min t f.physicalRadius)) :
    OriginalRegular.measuredSourceCutoff hμ =ᶠ[𝓝 x] (fun _ ↦ 1) := by
  have hρ := f.physicalRadius_pos
  have hsmall := (OriginalRegular.core_inside_native_cutoffs hn hr hμ).2.1
  have hxρ : x ∈ closedBall 0 f.physicalRadius :=
    ball_subset_closedBall ((ball_subset_ball (min_le_right _ _)) hx)
  have hxcore := f.physicalBall_coefficientDomain
    (closedBall_subset_closedBall (by linarith only [hρ] : f.physicalRadius ≤ 4*f.physicalRadius) hxρ)
  have hxμ : x ∈ closedBall (0 : Euclidean (d+1)) (((2 : Fin 3).val+1 : ℝ)*μ) := by
    apply closedBall_subset_closedBall _ hxcore
    change OriginalRegular.coreRadius hn (OriginalRegular.screenedRadius hn r μ) ≤ (2+1)*μ
    linarith only [hsmall,hμ]
  exact mem_interior_iff_mem_nhds.mp (ContinuumRow.FixedCutoffs.physical_plateau hμ 2 hxμ)

end JanetCartan.PhysicalPairs.OriginalSourcePlateau
end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSourcePlateau
open Lean Meta Elab Command
private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args
run_cmd liftTermElabM do
  let src := `JanetCartan.PhysicalInitialization.OriginalRegular
  let chart := `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart
  forallBoundedTelescope (← getConstInfo chart).type (some 23) fun xs _ => do
    unless xs.size == 23 do throwError "original observation plateau: source23 changed"
    let n := mkApp (mkConst ``Nat.succ) xs[0]!
    let original := #[n] ++ xs[1:21].toArray
    let capped := app `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,xs[1]!,original[20]!]
    let selected := original.set! 20 capped
    let hμ := app `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure selected
    let hr := app `JanetCartan.PhysicalInitialization.OriginalProtected.fact2 original
    let f := app (src ++ `f) xs
    let t := app (src ++ `r) xs
    let proof ← mkAppM ``original_chart_germ #[xs[1]!,hr,hμ,f,t]
    let type ← instantiateMVars (← mkForallFVars xs (← inferType proof))
    let value ← instantiateMVars (← mkLambdaFVars xs proof)
    for e in #[type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
        throwError "original observation plateau: unresolved native source parameter"
    let pair := Lean.ShareCommon.shareCommon (type,value)
    let name := `JanetCartan.PhysicalPairs.OriginalSourcePlateau.germ_on_original_chart
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
    logInfo "checked common source-observation germ on the entire unchanged original23 pair chart"
end JanetCartan.PhysicalPairs.OriginalSourcePlateau
end
