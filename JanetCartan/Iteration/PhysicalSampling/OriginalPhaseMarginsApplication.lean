module

public meta import Lean

/-!
# Actual same-source current-frame margin applications

Specialize the original regular producer with the sampler's merged callback,
then use its proved current-frame bound. The source dilation and all current
histories are the actual original ones. Kernel-checked applications reject all
metavariables and recovery proofs; no current phase estimate is assumed.
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalPhaseMarginsApplication
open Lean Meta Elab Command

private def publish (short : Name) (params : Array Expr) (proof : Expr) : MetaM Expr := do
  let name := `JanetCartan.PhysicalSampling.OriginalPhaseMargins ++ short
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  let type ← instantiateMVars (← mkForallFVars params (← inferType proof))
  if value.hasMVar || type.hasMVar || value.hasSorry || type.hasSorry ||
      value.hasFVar || type.hasFVar then
    throwError "original current margin: open or recovered proof {short}"
  addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  logInfo m!"checked SAME original physical current margin {short}"
  return mkAppN (mkConst name) params

private def field (proof : Expr) (index : Nat) : MetaM Expr := do
  let mut proof := proof
  for _ in [:index] do proof ← mkAppM ``And.right #[proof]
  if (← whnf (← inferType proof)).isAppOfArity ``And 2 then
    mkAppM ``And.left #[proof]
  else pure proof

/-- No current-frame bound is a premise: it is supplied by the original
`Graph.current_frame_margin` on the SAME merged/once-capped parent. -/
elab "realize_original_current_sampling_phase_margins" : command => liftTermElabM <| withTransparency .reducible do
  let source := `JanetCartan.PhysicalInitialization.OriginalRegular.Graph.current_frame_margin
  let info ← getConstInfo source
  forallBoundedTelescope info.type (some 23) fun fixed _ => do
    unless fixed.size == 23 do throwError "original current margin: expected original23"
    withLocalDeclD `pOrder (mkConst ``Nat) fun pOrder => do
      let d := fixed[0]!
      let hn := fixed[1]!
      let weightsArgs := fixed[:2].toArray ++ #[pOrder] ++ fixed[2:21].toArray
      let merged := mkAppN (mkConst `JanetCartan.PhysicalSampling.samplingCappedExtra)
        #[d, hn, pOrder, fixed[20]!]
      let original := fixed.set! 20 merged
      let margin := mkAppN (mkConst source) original
      let δ := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalMargins.δ) weightsArgs
      forallBoundedTelescope (← inferType margin) (some 2) fun tolerance _ => do
        unless tolerance.size == 2 do throwError "original current margin: missing fixed graph tolerance"
        withLocalDeclD `hγδ (← mkAppM ``LE.le #[tolerance[0]!, δ]) fun hγδ => do
          let margin := mkAppN margin tolerance
          forallBoundedTelescope (← inferType margin) (some 15) fun current _ => do
            unless current.size == 15 do throwError "original current margin: missing actual history arguments"
            let params := weightsArgs ++ fixed[21:].toArray ++ tolerance ++ #[hγδ] ++ current
            let bound := mkAppN margin current
            let raw ← mkAppM `JanetCartan.PhysicalSampling.original_raw_frame_margin_of_extended
              #[hn, fixed[4]!, fixed[5]!, fixed[6]!, bound]
            let raw ← publish `raw_frame_margin params raw
            let index := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalWeights.Index) weightsArgs
            withLocalDeclD `i index fun i => do
              let q ← mkAppM ``Subtype.val #[← mkAppM ``Sigma.fst #[i]]
              let qv ← mkAppM ``Subtype.val #[q]
              let chart ← mkAppM ``Prod.fst #[qv]
              let patchNumber ← mkAppM ``Sigma.snd #[i]
              let rawType ← whnf (← inferType raw)
              let patchType ← whnf rawType.bindingDomain!
              unless patchType.isAppOfArity ``Sigma 2 do
                throwError "original current margin: expected original patch sigma type"
              let patch := mkAppN (mkConst ``Sigma.mk [.zero, .zero])
                (patchType.getAppArgs ++ #[chart, patchNumber])
              let hsmall ← mkAppM `lt_of_lt_of_le #[mkApp raw patch, hγδ]
              let caps := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalMargins.δ_caps)
                (weightsArgs.push i)
              let bounds ← (#[0, 1, 2, 3] : Array Nat).mapM fun k => do
                mkAppM `lt_of_lt_of_le #[hsmall, ← field caps k]
              let proof ← mkAppM ``And.intro #[bounds[0]!, ← mkAppM ``And.intro
                #[bounds[1]!, ← mkAppM ``And.intro #[bounds[2]!, bounds[3]!]]]
              discard <| publish `all_four_phase_margins (params.push i) proof

end JanetCartan.PhysicalSampling.OriginalPhaseMarginsApplication
