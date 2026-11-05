module

public import JanetCartan.Iteration.PhysicalSampling.OriginalResponseWindow
public import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometry
public import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutSourceApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
public meta import Lean

/-!
# Actual sampling K lies in the native open current / parameter comparison region

No second, smaller sampling radius is selected. The original doubled joint
working ball lies in the parent σcover ball; the actual uncut current already
contains that parent's closed doubled ball, while its parameter projection
lies in the *closed, single* parent parameter cell inside the θ comparison
germ. The displacement/derivative estimates from the original solver's true
uniform output support extend from the Xsrc rectangle to THIS region, not by
an arbitrary recut of B (`app:ch_response:eq:response-reconstruction-grading`,
`app:ch_waves:eq:sampling-operator-bounds`).
-/

@[expose] public section
namespace JanetCartan.PhysicalSampling.OriginalResponseWindow
open Set Metric

private theorem root_buffers_in_current {E P : Type} [PseudoMetricSpace E] [PseudoMetricSpace P]
    {x : E} {root cell : P} {ρ σ : ℝ} {O : Set (E × P)} {W : Set P}
    (hρ : 0 < ρ) (hparent : closedBall (x,root) (2*ρ) ⊆ ball (x,cell) σ)
    (hcurrent : closedBall (x,cell) (2*σ) ⊆ O) (hwindow : closedBall cell σ ⊆ W) :
    closedBall (x,root) ρ ⊆ O ∩ (univ ×ˢ W) ∧
    closedBall (x,root) (2*ρ) ⊆ O ∩ (univ ×ˢ W) := by
  have hd : closedBall (x,root) (2*ρ) ⊆ O ∩ (univ ×ˢ W) := by
    intro v hv
    have hc := hparent hv
    have hs : 0 < σ := (dist_nonneg (x := v) (y := (x,cell))).trans_lt hc
    have hO : v ∈ O := hcurrent (closedBall_subset_closedBall (show σ ≤ 2*σ by linarith only [hs])
      (ball_subset_closedBall hc))
    rw [mem_ball, Prod.dist_eq,max_lt_iff] at hc
    exact ⟨hO,mem_univ _,hwindow hc.2.le⟩
  exact ⟨(closedBall_subset_closedBall (show ρ ≤ 2*ρ by linarith only [hρ])).trans hd,hd⟩

end JanetCartan.PhysicalSampling.OriginalResponseWindow
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalGradedResponseWindowApplication
open Lean Meta Elab Command
private def ps := `JanetCartan.PhysicalSampling
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def comp := `JanetCartan.PhysicalPrimary.OriginalUncutSource
private def tail (h : Expr) (j : Nat) := Nat.repeat (fun e => Expr.proj ``And 1 e) j h
private def save (field : Name) (v : Array Expr) (e : Expr) : MetaM Unit := do
  let t ← instantiateMVars (← mkForallFVars v (← inferType e))
  let value ← instantiateMVars (← mkLambdaFVars v e)
  if t.hasMVar || t.hasFVar || t.hasLevelMVar || value.hasLevelMVar || value.hasMVar || value.hasFVar || t.hasSorry || value.hasSorry then throwError "native graded window: open {field}"
  let name := ps ++ `OriginalResponseWindow ++ field
  addDecl (.thmDecl {name,levelParams := [],type := t,value}) (forceExpose := true)
  logInfo m!"checked original sampled working compact in current/parameter-comparison region: {field} at {v.size} inputs"

elab "retain_actual_graded_working_region" : command => liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (ps ++ `OriginalMargins.δ)).type (some 22) fun fixed _ => do
    let cap := mkAppN (mkConst (ps ++ `samplingCappedExtra)) #[fixed[0]!,fixed[1]!,fixed[2]!,fixed[21]!]
    let ordinary := (fixed[:2].toArray ++ fixed[3:22].toArray).set! 20 cap
    let current := mkAppN (mkConst (geo ++ `current_cell)) ordinary
    forallBoundedTelescope (← inferType current) (some 32) fun rest _ => do
      let s := ordinary ++ rest
      let x := fixed ++ rest
      let n := mkApp (mkConst ``Nat.succ) s[0]!
      let key := geo ++ `parameter_window
      let some body := (← getConstInfo key).value? | throwError "native graded window: missing original current parameter window"
      let V := (body.beta s).headBeta
      unless V.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.V 25 do throwError "native graded window: lost literal chosen cell"
      let a := V.getAppArgs[23]!
      let cell := V.getAppArgs[24]!
      unless cell.isAppOfArity `JanetCartan.PhysicalSeed.SelectedBoundary.cell 23 do throwError "native graded window: selected source cell has changed"
      let i := cell.getAppArgs[21]!
      let l := cell.getAppArgs[22]!
      let hroot := mkAppN (mkConst (ps ++ `OriginalAdmission.root_mem)) (fixed ++ #[i,l])
      let radiusArgs := #[n,s[1]!,i,l,cell]
      let radius := mkAppN (mkConst (ps ++ `originalSamplingRadius)) radiusArgs
      let hparent := mkAppN (mkConst (ps ++ `originalSamplingRadius_spec)) (radiusArgs.push hroot)
      let hW := mkAppN (mkConst (comp ++ `parameterComparisonWindow_spec)) #[n,s[1]!,a,cell]
      let h ← mkAppM ``OriginalResponseWindow.root_buffers_in_current
        #[.proj ``Subtype 1 radius,.proj ``And 0 hparent,mkAppN current rest,tail hW 3]
      save `working_in_native_graded_domain x (.proj ``And 0 h)
      save `doubled_in_native_graded_domain x (.proj ``And 1 h)

end JanetCartan.PhysicalSampling.OriginalGradedResponseWindowApplication
end

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxRecDepth 32000
set_option maxHeartbeats 2000000
retain_actual_graded_working_region
