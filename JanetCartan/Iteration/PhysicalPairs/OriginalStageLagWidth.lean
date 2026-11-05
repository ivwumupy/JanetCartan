module
public import JanetCartan.Iteration.PhysicalPairs.OriginalStageLag

/-! # Select the common graph width before σ for the pair strain

Take the minimum with the actual positive frame threshold at the free graph
width binder. All later source/reference-scale and history arguments specialize
to this choice. There is no quantitative frame premise after the history.
`app:ch_pairs:eq:pairs-lag-sum-error`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalStageLagWidth
variable {n : ℕ}
def width (hn : 5 ≤ n) (ζ : ℝ) : ℝ := min ζ (RawPrimary.ambientStrainFrameThreshold hn)
theorem width_pos (hn : 5 ≤ n) {ζ : ℝ} (hz : 0 < ζ) : 0 < width hn ζ := lt_min hz (RawPrimary.ambientStrainFrameThreshold_pos hn)
theorem width_le_parent (hn : 5 ≤ n) (ζ : ℝ) : width hn ζ ≤ ζ := min_le_left _ _
theorem width_le_frame (hn : 5 ≤ n) (ζ : ℝ) : width hn ζ ≤ RawPrimary.ambientStrainFrameThreshold hn := min_le_right _ _
end JanetCartan.PhysicalPairs.OriginalStageLagWidth
end
public meta section
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option warningAsError true
namespace JanetCartan.PhysicalPairs.OriginalStageLagWidth
open Lean Meta Elab Command PhysicalInitialization.OriginalProtectedTemplate
private def here := `JanetCartan.PhysicalPairs.OriginalStageLagWidth
private def a (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
run_cmd liftTermElabM do
  let lag := `JanetCartan.PhysicalPairs.OriginalStageLag.lag
  forallBoundedTelescope (← getConstInfo lag).type (some 24) fun p _ => do
    let n := mkApp (mkConst ``Nat.succ) p[0]!
    let hn := p[1]!
    withLocalDeclD `parentWidth (mkConst ``Real) fun ζ => do
      let D := a (here ++ `width) #[n,hn,ζ]
      let pre := a lag (p.push D)
      let ht := (← inferType pre).bindingDomain!.replace fun e => if e == D then some ζ else none
      withLocalDeclD `parentWidth_pos ht fun hζ => do
        let after := mkApp pre (a (here ++ `width_pos) #[n,hn,ζ,hζ])
        forallBoundedTelescope (← inferType after) (some 11) fun later _ => do
          let native := mkApp (mkAppN after later) (a (here ++ `width_le_frame) #[n,hn,ζ])
          discard <| store (here ++ `lag) (p ++ #[ζ,hζ] ++ later) native
end JanetCartan.PhysicalPairs.OriginalStageLagWidth
end
