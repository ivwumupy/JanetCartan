module

public meta import Lean
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate

/-! Actual original-map and qext buffers for the cutoff-one current source.
The existing native geometryIndex is reused; no carrier or row is reselected.
Consumer: the physical map/frame inputs of `app:ch_background:eq:bg-current-profile`.
-/

public meta section
namespace JanetCartan.PhysicalBackground.NativeSourceGeometryTemplate
open Lean Meta Elab Command Term
open NativeReferenceSourceTemplate (termWith)

private def targetNS := `JanetCartan.PhysicalBackground.NativeSourceGeometry

private def store (name : Name) (params : Array Expr) (value : Expr) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars params (← inferType value))
  let value ← instantiateMVars (← mkLambdaFVars params value)
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar ||
      type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then
    throwError "native source geometry: open or future-dependent buffer {name}"
  let name := targetNS ++ name
  addDecl (.thmDecl { name, type, value, levelParams := [] }) (forceExpose := true)
  pure (mkAppN (mkConst name) params)

elab "realize_native_source_buffers" : command => liftTermElabM do
  let density := `JanetCartan.PhysicalBackground.NativeDensity
  let source := `JanetCartan.PhysicalBackground.NativeReferenceSource
  let boundary := `JanetCartan.PhysicalSeed.OriginalBoundary
  let indexInfo ← getConstInfo (density ++ `geometryIndex)
  forallBoundedTelescope indexInfo.type (some 21) fun fixed _ => do
    unless fixed.size == 21 do throwError "native source geometry: expected raw original21"
    let index := mkAppN (mkConst (density ++ `geometryIndex)) fixed
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[fixed[0]!, fixed[1]!, fixed[20]!]
    let selected := fixed.set! 20 capped
    let src (name : Name) := mkAppN (mkConst (source ++ name)) selected
    let original (name : Name) := mkAppN (mkConst (boundary ++ name)) fixed[:2].toArray
    let T := mkApp (src `T) index
    let mut t := T
    for _ in [:16] do
      if t.isAppOfArity (boundary ++ `T) 3 then break
      let some name := t.getAppFn.constName? |
        throwError "native source geometry: nonconstant original T alias"
      let some body := (← getConstInfo name).value? (allowOpaque := true) |
        throwError "native source geometry: original T alias body unavailable {name}"
      t ← Core.betaReduce (← zetaReduce (body.beta t.getAppArgs))
    unless t.isAppOfArity (boundary ++ `T) 3 do
      throwError "native source geometry: lost the actual original parent patch"
    let args := t.getAppArgs
    unless (← isDefEq args[0]! fixed[0]!) && (← isDefEq args[1]! fixed[1]!) do
      throwError "native source geometry: original T changed dimension/data"
    let state := mkAppN (mkConst (boundary ++ `stateDomain_subset_ball)) args
    let hFrame ← store `frameBall_subset_original fixed (← termWith [(`T, T), (`state, state)]
      "frameBall_subset_of_stateDomain T.data.localReference state")
    let bindings := [(`n, fixed[0]!), (`mu, src `r), (`hr, src `hr), (`T, T),
      (`root, mkApp (src `root) index), (`am, mkApp (src `am) index),
      (`ham, mkApp (src `am_pos) index), (`hMeasure, mkApp (src `measure_lt_carrier) index),
      (`hInner, mkApp (src `inner_support_product) index),
      (`hRadius, mkApp (src `product_radius_le_physical) index),
      (`hP, mkApp (src `hP) index), (`hFrame, hFrame), (`b, original `b),
      (`R, original `R), (`hbR, original `b_lt_R), (`ext, fixed[4]!),
      (`hcenter, fixed[5]!), (`hradius, fixed[6]!)]
    let buffer ← store `measurement_buffer fixed (← termWith bindings
      ("(by\n" ++
       "  intro x hx\n" ++
       "  let p0 : CarrierParameter := (root 0, FullPhaseCharts.ActualComparison.spectatorCenter root)\n" ++
       "  have hp0 : p0 ∈ CanonicalConic.carrierSupport root (r := am) :=\n" ++
       "    ⟨mem_closedBall_self (half_pos ham).le, mem_closedBall_self (half_pos ham).le⟩\n" ++
       "  have ham' : 0 < am := ham\n" ++
       "  have hMeasure' : 6 * mu < am := hMeasure\n" ++
       "  have hx' : x ∈ closedBall (0 : Euclidean n) (4 * am) :=\n" ++
       "    closedBall_subset_closedBall (by linarith only [hMeasure', ham']) hx\n" ++
       "  have hp := (hInner (q := (x, p0)) ⟨hx', hp0⟩).1\n" ++
       "  exact hFrame ((T.physicalBall_subset_frameBall hP) (ball_subset_ball hRadius hp))\n" ++
       "  : closedBall (0 : Euclidean n) (6 * mu) ⊆ ball 0 b)"))
    let bindings := bindings ++ [(`buffer, buffer)]
    discard <| store `measurement_buffer_chart fixed (← termWith bindings
      "(Set.Subset.trans buffer (ball_subset_ball hbR.le) : closedBall (0 : Euclidean n) (6 * mu) ⊆ ball 0 R)")
    discard <| store `measurement_buffer_qext fixed (← termWith bindings
      ("(by\n" ++
       "  rw [hcenter, hradius]\n" ++
       "  exact Set.Subset.trans buffer ball_subset_closedBall\n" ++
       "  : closedBall (0 : Euclidean n) (6 * mu) ⊆ closedBall ext.center ext.radius)"))
    discard <| store `measurement_four_buffer fixed (← termWith bindings
      "((closedBall_subset_closedBall (show 4 * mu ≤ 6 * mu by linarith only [(show 0 < mu from hr)])).trans buffer : closedBall (0 : Euclidean n) (4 * mu) ⊆ ball 0 b)")
    discard <| store `measurement_five_chart fixed (← termWith bindings
      "(by intro x hx; exact ball_subset_ball hbR.le (buffer (closedBall_subset_closedBall (show 5 * mu ≤ 6 * mu by linarith only [(show 0 < mu from hr)]) (ball_subset_closedBall hx))) : ball (0 : Euclidean n) (5 * mu) ⊆ ball 0 R)")
  logInfo "same native measurement six-buffer lies in ORIGINAL b/qext before sigma; no selected measurement-b substitution"

end JanetCartan.PhysicalBackground.NativeSourceGeometryTemplate
end
