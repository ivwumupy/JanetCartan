module

public meta import Lean

/-!
# Kernel-checked actual original sampler admissions

Apply the existing selected-row certificates to the one merged/strong-capped
callback without unfolding that callback's classical geometric witnesses.
Every result is inferred from an actual proof term and checked by `addDecl`;
no declaration type is assumed, no analytic premise is introduced, and every
open metavariable or recovery proof is rejected.
-/

public meta section
namespace JanetCartan.PhysicalSampling.OriginalAdmissionApplication
open Lean Meta Elab Command

private def store (short : Name) (params : Array Expr) (proof : Expr) : MetaM Expr := do
  let name := `JanetCartan.PhysicalSampling.OriginalAdmission ++ short
  let proof ← instantiateMVars proof
  let type ← instantiateMVars (← inferType proof)
  if type.hasMVar || proof.hasMVar || type.hasSorry || proof.hasSorry then
    throwError "original admission: open or recovered proof {short}"
  let type ← mkForallFVars params type
  let value ← mkLambdaFVars params proof
  if type.hasFVar || value.hasFVar then
    throwError "original admission: escaping source parameter {short}"
  addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  logInfo m!"kernel-checked actual once-capped admission {short}"
  return mkAppN (mkConst name) params

private def conjunctionField (proof : Expr) (index : Nat) : MetaM Expr := do
  let mut proof := proof
  for _ in [:index] do proof ← mkAppM ``And.right #[proof]
  let type ← whnf (← inferType proof)
  if type.isAppOfArity ``And 2 then mkAppM ``And.left #[proof] else pure proof

private def conjunction (proofs : Array Expr) : MetaM Expr := do
  if proofs.size < 2 then throwError "original admission: expected at least two conjuncts"
  let mut proof := proofs.back!
  for i in (List.range (proofs.size - 1)).reverse do
    proof ← mkAppM ``And.intro #[proofs[i]!, proof]
  return proof

/-- Close all actual selected root/spatial/angular inputs, then apply the
retained scalar, κ and carrier-label continuations to those SAME masks. -/
elab "realize_original_sampling_admission" : command => liftTermElabM <| withTransparency .reducible do
  let selected := `JanetCartan.PhysicalSeed.SelectedBoundary
  let source := selected ++ `fact1
  let info ← getConstInfo source
  forallBoundedTelescope info.type (some 21) fun sourceArgs body => do
    forallBoundedTelescope body (some 2) fun indices _ => do
      let proof ← mkAppM ``And.right #[mkAppN (mkConst source) (sourceArgs ++ indices)]
      discard <| store `root_in_original_product (sourceArgs ++ indices) proof
  let .forallE _ _ body _ := info.type | throwError "original admission: missing dimension"
  withLocalDecl `m .implicit (mkConst ``Nat) fun m => do
    let samplingInfo ← getConstInfo `JanetCartan.PhysicalSampling.samplingCappedExtra
    let samplingTail := samplingInfo.type.bindingBody!.instantiate1 m
    let n := samplingTail.bindingDomain!.appArg!
    forallBoundedTelescope (body.instantiate1 n) (some 20) fun fixed _ => do
      unless fixed.size == 20 do throwError "original admission: expected original20 after dimension"
      withLocalDeclD `pOrder (mkConst ``Nat) fun pOrder => do
        let hn := fixed[0]!
        let userExtra := fixed[19]!
        let all := #[m, hn, pOrder] ++ fixed[1:]
        let merged := mkAppN (mkConst `JanetCartan.PhysicalSampling.samplingCappedExtra)
          #[m, hn, pOrder, userExtra]
        let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
          #[n, hn, merged]
        let actualArgs := (#[n] ++ fixed).set! 20 capped
        let field (name : Name) := mkAppN (mkConst (selected ++ name)) actualArgs
        let rootFact := field `fact1
        forallBoundedTelescope (← inferType rootFact) (some 2) fun indices _ => do
          unless indices.size == 2 do throwError "original admission: missing original incidence/patch"
          let proof := mkAppN
            (mkConst `JanetCartan.PhysicalSampling.OriginalAdmission.root_in_original_product)
            (actualArgs ++ indices)
          discard <| store `root_mem (all ++ indices) proof
        let spatialFact := field `fact22
        forallBoundedTelescope (← inferType spatialFact) (some 1) fun indices _ => do
          unless indices.size == 1 do throwError "original admission: missing actual selected row"
          let i := indices[0]!
          let q ← mkAppM ``Subtype.val #[← mkAppM ``Sigma.fst #[i]]
          let l ← mkAppM ``Sigma.snd #[i]
          let j := mkAppN (field `cell) #[q, l]
          let params := all ++ indices
          let radiusArgs := #[m, hn, pOrder, q, l, j]
          let hstrong := mkAppN
            (mkConst `JanetCartan.PhysicalNormalInverse.h_cappedExtra_le_userExtra)
            #[n, hn, merged, q, l, j]
          let hsampling := mkAppN
            (mkConst `JanetCartan.PhysicalSampling.samplingCappedExtra_le_sampling)
            (radiusArgs.push userExtra)
          let hcap ← mkAppM `le_trans #[hstrong, hsampling]
          let hspatial ← store `spatial_le_sampling params
            (← mkAppM `le_trans #[mkApp spatialFact i, hcap])
          let hangular ← store `angular_le_sampling params
            (← mkAppM `le_trans #[mkApp (field `angularWidth_le_aExtra) i, hcap])
          let hroot := mkAppN
            (mkConst `JanetCartan.PhysicalSampling.OriginalAdmission.root_mem) (all ++ #[q, l])
          let capSpec := mkAppN
            (mkConst `JanetCartan.PhysicalSampling.originalSamplingExtraCap_spec)
            (radiusArgs.push hroot)
          let spatialBounds ← (#[0, 1, 2] : Array Nat).mapM fun k => do
            mkAppM `le_trans #[hspatial, ← conjunctionField capSpec k]
          let angularBounds ← (#[0, 3, 4] : Array Nat).mapM fun k => do
            mkAppM `le_trans #[hangular, ← conjunctionField capSpec k]
          discard <| store `spatial_caps params (← conjunction spatialBounds)
          discard <| store `angular_caps params (← conjunction angularBounds)
          let retained := #[m, pOrder, hn, q, l, j, hroot]
          let hη := mkApp (field `hηb) i
          let hr := mkApp (field `hr') i
          let ha := mkApp (field `ha') i
          let r := (← inferType hr).appArg!
          let a := (← inferType ha).appArg!
          let hηeq := mkAppN
            (mkConst `JanetCartan.PhysicalSampling.selected_tangential_covector_eq_quarter)
            (actualArgs.push i)
          let ηeqType ← whnf (← inferType hηeq)
          unless ηeqType.isAppOfArity ``Eq 3 do
            throwError "original admission: expected exact selected quarter equality"
          let η := ηeqType.getAppArgs[1]!
          let normalize ← withLocalDeclD `η (← inferType η) fun v => do
            mkLambdaFVars #[v] (← mkAppM `NormedSpace.normalize #[v])
          let hdir ← mkAppM ``congrArg #[normalize, hηeq]
          let ηbase := ηeqType.getAppArgs[2]!
          for (part, name, index) in [
            (`Mean, `mean_detector_support, 1),
            (`Comparison, `comparison_detector_support, 2)] do
            let radius := mkAppN
              (mkConst (`JanetCartan.PhysicalSampling.OriginalChoices ++ part ++ `radius)) retained
            let hwidth := angularBounds[index]!
            let width := (← inferType hwidth).appArg!
            let hwidthRefl ← mkAppM `le_refl #[width]
            let proof := mkAppN
              (mkConst `JanetCartan.PhysicalSampling.originalConicDetector_support_of_angular_cap)
              #[n, η, ηbase, r, radius, width, hη, hr, hdir, hwidth, hwidthRefl]
            discard <| store name params proof
          let scalar := mkAppN
            (mkConst `JanetCartan.PhysicalSampling.OriginalChoices.Scalar.continuation)
            (retained ++ #[η, r, a, hη, hr, ha, hdir, angularBounds[0]!, spatialBounds[0]!])
          discard <| store `scalar_on_actual_selected_row params scalar
          for (part, name, bound) in [
            (`Cutoff, `cutoff_on_actual_selected_row, spatialBounds[1]!),
            (`Label, `label_on_actual_selected_row, spatialBounds[2]!)] do
            let proof := mkAppN
              (mkConst (`JanetCartan.PhysicalSampling.OriginalChoices ++ part ++ `continuation))
              (retained ++ #[a, ha, bound])
            discard <| store name params proof
          let plateau := mkAppN
            (mkConst `JanetCartan.PhysicalSampling.originalSamplingExtraCap_scalar_cutoffs)
            (radiusArgs ++ #[hroot, a, ha, hspatial])
          discard <| store `scalar_cutoff_on_actual_selected_row params plateau

end JanetCartan.PhysicalSampling.OriginalAdmissionApplication
