module

public meta import Lean

/-!
# Cache one original scalar/corrected/comparison geometry witness

Only the finite geometric prefixes are selected. Their complete analytic
continuations remain attached to those SAME named witnesses. In particular the
normal-comparison consumer must use these comparison radii, not choose them
again. The actual candidate inputs precede reference and source scale.
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalChoicesApplication
open Lean Meta Elab Command

private def store (name : Name) (params : Array Expr) (type value : Expr) : MetaM Expr := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  if type.hasMVar || value.hasMVar || type.hasSorry || value.hasSorry then
    throwError "original sampling choices: open or recovered declaration {name}"
  let fullType ← mkForallFVars params type
  let fullValue ← mkLambdaFVars params value
  if fullType.hasFVar || fullValue.hasFVar then
    throwError "original sampling choices: escaping source parameter {name}"
  if ← isProp type then
    addDecl (.thmDecl { name, levelParams := [], type := fullType, value := fullValue })
      (forceExpose := true)
  else
    addDecl (.defnDecl {
      name, levelParams := [], type := fullType, value := fullValue,
      hints := .abbrev, safety := .safe }) (forceExpose := true)
  return mkAppN (mkConst name) params

private def retainPrefix (ns : Name) (params : Array Expr) (initial : Expr)
    (names : Array Name) : MetaM Unit := do
  let mut proof := initial
  for index in [:names.size] do
    let type ← whnf (← inferType proof)
    if type.isAppOfArity ``Exists 2 then
      let predicate := type.appArg!
      let witness ← mkAppM ``Classical.choose #[proof]
      let selected ← store (ns ++ names[index]!) params (← inferType witness) witness
      let spec ← mkAppM ``Classical.choose_spec #[proof]
      proof ← store (ns.str s!"spec{index + 1}") params (predicate.beta #[selected]) spec
    else if type.isAppOfArity ``And 2 then
      let fields := type.getAppArgs
      let fact ← mkAppM ``And.left #[proof]
      let _ ← store (ns ++ names[index]!) params fields[0]! fact
      let tail ← mkAppM ``And.right #[proof]
      proof ← store (ns.str s!"spec{index + 1}") params fields[1]! tail
    else
      throwError "original sampling choices: {ns} prefix ended at {index}, before {names[index]!}"
  let type ← whnf (← inferType proof)
  unless type.isForall do
    throwError "original sampling choices: {ns} did not end at its analytic continuation"
  let _ ← store (ns ++ `continuation) params type proof
  logInfo m!"retained SAME {ns} witness: {names.size} static fields and full analytic continuation"

/-- Choose each actual static factory's witness once, before source scale, and
retain all later bounds for exactly its named radii and auxiliary cutoffs. -/
elab "cache_original_sampling_candidate_geometry" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalSampling.OriginalScalar.exists_geometry
  let info ← getConstInfo source
  forallBoundedTelescope info.type (some 6) fun original _ => do
    unless original.size == 6 do
      throwError "original sampling choices: expected m, hn, q, l, j and root membership"
    withLocalDecl `p .implicit (mkConst ``Nat) fun p => do
      let params := #[original[0]!, p] ++ original[1:]
      let base := `JanetCartan.PhysicalSampling.OriginalChoices
      retainPrefix (base ++ `Scalar) params (mkAppN (mkConst source) original)
        #[`δ, `ε, `cap, `hδ, `hδ_threshold, `hε, `hε_max, `hε_radius, `hcap,
          `χstar, `hcap_χstar, `hχstar_outer, `hχstar_radius,
          `β, `hβ, `hβ_one, `hβ_geometry]
      let geometricNames := #[`radius, `s, `e, `δ, `hradius, `hradius_max, `hs, `hs_radius,
        `he, `he_max, `he_one, `he_radius, `hδ, `hδ_threshold]
      retainPrefix (base ++ `Mean) params
        (mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalMeasured.exists_mean_geometry) params)
        geometricNames
      let bandName := `JanetCartan.PhysicalSampling.OriginalMeasured.exists_band_geometry
      let bandInfo ← getConstInfo bandName
      let band := mkConst bandName (bandInfo.levelParams.map fun _ ↦ .zero)
      retainPrefix (base ++ `Band) params (mkAppN band original[:5])
        #[`a, `b, `e, `δ, `ha, `hb, `he, `hδ, `ha_radius, `hb_radius, `he_b, `hδ_threshold,
          `θ, `hθ, `hθ_compact, `hθ_one, `hθ_support]
      retainPrefix (base ++ `Comparison) params
        (mkAppN
          (mkConst `JanetCartan.PhysicalNormalInverse.OriginalTransport.geometry_on_originalSamplingRadius)
          params) geometricNames

/-- Retain the single joint cutoff and sharp-band carrier cap after the
already-fixed scalar/mean/band/comparison candidate geometry. -/
elab "cache_original_sampling_cutoff_geometry" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalSampling.OriginalCutoffs.exists_joint_cutoff_geometry
  let info ← getConstInfo source
  forallBoundedTelescope info.type (some 7) fun params _ => do
    unless params.size == 7 do
      throwError "original sampling cutoffs: expected m, p, hn, q, l, j and root membership"
    let base := `JanetCartan.PhysicalSampling.OriginalChoices
    retainPrefix (base ++ `Cutoff) params (mkAppN (mkConst source) params)
      #[`κ, `ψ, `Bψ, `hBψ, `cap, `hcap, `hκ, `hκ_compact, `hκ_bounds,
        `hκ_support, `hκ_radius, `hκ_s, `hψ, `hψ_compact, `hψ_bounds, `hψ_support]
    retainPrefix (base ++ `Label) params
      (mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalCutoffs.exists_original_label_geometry)
        params)
      #[`cap, `hcap]

end JanetCartan.PhysicalSampling.OriginalChoicesApplication
