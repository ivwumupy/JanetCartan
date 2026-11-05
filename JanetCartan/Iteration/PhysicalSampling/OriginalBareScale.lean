module

public import JanetCartan.Iteration.PhysicalSampling.OriginalBareEventBudget
public import JanetCartan.Iteration.PhysicalSampling.OriginalSourceGraphCaps
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalSourceGraphCaps
public meta import Lean

/-!
# A single pre-source scale ceiling for the actual bare family and full inverse

Before σ, `Cresp`, an inverse accuracy, or R₀, use the actual chosen bare
frame and capped original geometry. The minimum of the genuine signed row's
tolerance and the sampler tolerance keeps the sampling graph admissible. A
single positive scale ceiling pays that graph, the canonical signed graph for
the full physical inverse, both sources and the native protected density.
No post-source frame, rate or cap is changed (`new:sec:order-of-choices`).
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalBareScaleApplication
open Lean Meta Elab Command
private def ps := `JanetCartan.PhysicalSampling
private def ns := ps ++ `OriginalBareScale
private def bare := ps ++ `OriginalBare
private def positive := ps ++ `OriginalPositiveEvent
private def admission := ps ++ `OriginalSourceGraphAdmission
private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs

/-- The fixed original22 spine, built from bare24 without a new selection. -/
def originalSampler (p : Array Expr) : MetaM (Array Expr) := do
  let f ← mkAppM (bare ++ `exists_frame) #[p[1]!,p[4]!]
  let chosen ← mkAppM ``Classical.choose #[f]
  let spec ← mkAppM ``Classical.choose_spec #[f]
  let cap := app (bare ++ `userCap) #[p[0]!,p[1]!,p[21]!]
  pure (p[:3].toArray ++ #[chosen,Expr.proj ``And 0 spec] ++ p[5:21].toArray ++ #[cap])

private def save (n : Name) (p : Array Expr) (e : Expr) (data := false) (g : Option Expr := none) : MetaM Expr := do
  let t ← match g with | none => inferType e | some t => pure t
  let type ← instantiateMVars (← mkForallFVars p t)
  let value ← instantiateMVars (← mkLambdaFVars p e)
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar || type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then throwError "original bare scale: open {n}"
  if data then addDecl (.defnDecl {name := ns ++ n,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name := ns ++ n,levelParams := [],type,value}) (forceExpose := true)
  return app (ns ++ n) p

elab "fix_original_bare_scale_before_source" : command => liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (ps ++ `OriginalBareEvent.S)).type (some 24) fun p _ => do
    let w ← originalSampler p
    let stat := w ++ p[22:24].toArray
    let graph := app (admission ++ `graphTolerance) stat
    let ambient ← mkAppM `JanetCartan.RawPrimary.ambientStrainFrameThreshold #[p[1]!]
    let earlyBound ← mkAppM ``Min.min #[ambient,p[3]!]
    let γ ← save `γ p (← mkAppM ``Min.min #[graph,earlyBound]) true
    let hmin ← mkAppM `lt_min #[← mkAppM `JanetCartan.RawPrimary.ambientStrainFrameThreshold_pos #[p[1]!],p[4]!]
    let hγ ← save `γ_pos p (← mkAppM `lt_min #[app (admission ++ `graphTolerance_pos) stat,hmin]) false (some (← mkAppM ``LT.lt #[← mkNumeral (mkConst ``Real) 0,γ]))
    let hg ← save `γ_le_joint_graph p (← mkAppM `min_le_left #[graph,earlyBound]) false (some (← mkAppM ``LE.le #[γ,graph]))
    discard <| save `γ_le_sampler p (← mkAppM `le_trans #[hg,app (admission ++ `graphTolerance_le_sampler) stat])
    let hb ← mkAppM `min_le_right #[graph,earlyBound]
    discard <| save `γ_le_ambient p (← mkAppM `le_trans #[hb,← mkAppM `min_le_left #[ambient,p[3]!]]) false (some (← mkAppM ``LE.le #[γ,ambient]))
    discard <| save `γ_le_extra p (← mkAppM `le_trans #[hb,← mkAppM `min_le_right #[ambient,p[3]!]]) false (some (← mkAppM ``LE.le #[γ,p[3]!]))
    let g := stat ++ #[γ,hγ]
    let cap ← save `ceiling p (app (positive ++ `scaleCeiling) g) true
    discard <| save `ceiling_pos p (app (positive ++ `scaleCeiling_pos) g) false (some (← mkAppM ``LT.lt #[← mkNumeral (mkConst ``Real) 0,cap]))
    withLocalDeclD `σ (mkConst ``Real) fun σ => do
      let capI ← mkAppM ``Set.Ioc #[← mkNumeral (mkConst ``Real) 0,cap]
      withLocalDeclD `hσ (← mkAppM ``Membership.mem #[capI,σ]) fun hσ => do
        let both := app (positive ++ `scale_admissions) (g ++ #[σ,hσ])
        discard <| save `scale_admissions (p ++ #[σ,hσ]) both
  logInfo "checked a single original bare frame's scale ceiling, genuine graph tolerance and five actual source/graph/nativity admissions; no R₀ or Cresp used"

end JanetCartan.PhysicalSampling.OriginalBareScaleApplication
end

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
set_option maxRecDepth 32000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
fix_original_bare_scale_before_source
