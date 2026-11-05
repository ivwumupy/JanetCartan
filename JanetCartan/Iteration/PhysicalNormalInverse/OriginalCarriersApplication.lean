module

public import JanetCartan.Iteration.PhysicalInitialization.CurrentInverse
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedMeasurement.Restriction
public meta import Lean

/-!
# The identical actual carriers on the common measurement chart

Apply the released common-measurement theorem to the actual original current
inverse's carriers and its exact selected measurement radius. The individual
carrier radius and angular/label weight are NOT changed to the common radius.
The entire native inverse predicate is retained on the SAME carrier witness.
Consumer: the original rounded-prefix identity in the corrected normal mean
comparison (`app:ch_waves:eq:sampling-prefix-normal`).
-/

public meta section
namespace JanetCartan.PhysicalNormalInverse.OriginalCarriersApplication
open Lean Meta Elab Command

private def save (name : Name) (params : Array Expr) (proof : Expr) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars params (← inferType proof))
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  if value.hasFVar || value.hasMVar || value.hasSorry || type.hasFVar || type.hasMVar || type.hasSorry then
    throwError "original common carriers: incomplete theorem {name}"
  addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
  return mkAppN (mkConst name) params

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

/-- Restrict the SAME native carrier witness, preserving its full specification
and every original label/angular and transport function. -/
elab "apply_actual_carriers_common_measurement" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalInitialization.OriginalCurrent.continuation
  let root := `JanetCartan.PhysicalNormalInverse.OriginalCarriers
  let selectedNS := `JanetCartan.PhysicalSeed.SelectedBoundary
  let info ← getConstInfo source
  forallBoundedTelescope info.type (some 44) fun all _ => do
    unless all.size == 44 do throwError "original common carriers: expected native44"
    let native := mkAppN (mkConst source) all
    let nativeType ← whnf (← inferType native)
    unless nativeType.isAppOfArity ``Exists 2 do
      throwError "original common carriers: native carrier existential missing"
    let carrierType := nativeType.getAppArgs[0]!
    let nativePredicate := nativeType.appArg!
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[all[0]!, all[1]!, all[20]!]
    let selected := all[:21].toArray.set! 20 capped
    let selectedField (name : Name) := mkAppN (mkConst (selectedNS ++ name)) selected
    let mu := selectedField `rMeasure
    let hMu := selectedField `hrMeasure
    let hMuCell := selectedField `hMeasureCell
    let construction ← withLocalDeclD `Vop carrierType fun Vop => do
      withLocalDeclD `hNative (nativePredicate.beta #[Vop]) fun hNative => do
        let representations ← mkAppM ``And.left #[hNative]
        let measured ← forallBoundedTelescope (← inferType representations) (some 1) fun indices _ => do
          unless indices.size == 1 do throwError "original common carriers: expected selected carrier index"
          let i := indices[0]!
          let representation := mkApp representations i
          let tests ← mkAppM ``And.left #[representation]
          let adjoint ← mkAppM ``And.right #[representation]
          let d ← forallBoundedTelescope (← inferType adjoint) (some 1) fun _ result => do
            let some integral := result.find? (fun e =>
                e.isAppOf `JanetCartan.ContinuumRow.carrierAdjointIntegral && e.getAppArgs.size ≥ 3)
              | throwError "original common carriers: literal original adjoint integral missing"
            Core.betaReduce (← zetaReduce integral.getAppArgs[2]!)
          unless d.getAppFn.isConstOf `JanetCartan.ContinuumRow.CanonicalCarrier.data && d.getAppArgs.size == 18 do
            throwError "original common carriers: expected literal canonical data18, got {d.getAppFn} / {d.getAppArgs.size}"
          let da := d.getAppArgs
          let outputChart ← mkAppM ``JanetCartan.ContinuumRow.CarrierData.outputChart #[d]
          let hchart ← mkEqRefl outputChart
          let base := mkAppN
            (mkConst `JanetCartan.ContinuumRow.NormalizedMeasurement.supplied_carrier_common_measurement)
            #[all[0]!, da[6]!, d, mu, da[13]!, hMu, da[14]!, hMuCell, da[15]!,
              mkApp (selectedField `fact60) i, hchart]
          let pointType := (← inferType base).bindingDomain!
          let hpoint ← forallBoundedTelescope pointType (some 2) fun point result => do
            unless point.size == 2 do throwError "original common carriers: expected chart point and membership"
            let result ← whnf result
            unless result.isAppOfArity ``Eq 3 do throwError "original common carriers: expected chart point equality"
            mkLambdaFVars point (← mkEqRefl result.getAppArgs[1]!)
          let measurement ← mkAppM ``JanetCartan.ContinuumRow.CarrierData.measurementCutoff #[d]
          let common := mkAppN base #[hpoint, ← mkEqRefl measurement]
          let operators := mkApp (← component common 8) (mkApp Vop i)
          let bounded ← component operators 0
          let testAndSupport := mkApp (← component operators 1) tests
          let commonAdjoint := mkApp (← component operators 2) adjoint
          let static ← (List.range 8).toArray.mapM fun k => do
            return ← component common k
          let bundle ← conjunction (static ++ #[bounded, ← mkAppM ``And.left #[testAndSupport],
            ← mkAppM ``And.right #[testAndSupport], commonAdjoint])
          mkLambdaFVars indices bundle
        let helper ← save (root ++ `common_measurement_of_native) (all ++ #[Vop, hNative]) measured
        let bundle ← mkAppM ``And.intro #[hNative, helper]
        let predicate ← mkLambdaFVars #[Vop] (← inferType bundle)
        let existsProof ← mkAppOptM ``Exists.intro #[none, some predicate, some Vop, some bundle]
        mkLambdaFVars #[Vop, hNative] existsProof
    let result ← mkAppM ``Exists.elim #[native, construction]
    discard <| save (root ++ `exists_common_measured_carriers) all result
    logInfo "kernel-checked actual native44 plus common test/adjoint on SAME carrier witness; ENTIRE inverse predicate and individual masks retained"

/-- Admit the whole common source ball and the FULL original carrier support
into the actual current compatibility domain, without shrinking label weights. -/
elab "apply_actual_carriers_common_coordinates" : command => liftTermElabM do
  let currentNS := `JanetCartan.PhysicalInitialization.OriginalCurrent
  let selectedNS := `JanetCartan.PhysicalSeed.SelectedBoundary
  let info ← getConstInfo (currentNS ++ `current)
  forallTelescope info.type fun all _ => do
    unless all.size == 38 do throwError "original common coordinates: expected native38"
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[all[0]!, all[1]!, all[20]!]
    let selected := all[:21].toArray.set! 20 capped
    let selectedField (name : Name) := mkAppN (mkConst (selectedNS ++ name)) selected
    let i := all[37]!
    let outer := mkApp (selectedField `fact23) i
    let hOuter ← component outer 1
    let hrr ← component outer 2
    let haa ← component outer 3
    let har' ← component outer 4
    let har ← mkAppM `le_trans #[har', hrr]
    let hSource ← mkAppOptM
      `JanetCartan.ContinuumRow.NormalizedMeasurement.source_product_subset_retained_cell
      #[some all[0]!, none, none, none, none, none,
        some (selectedField `hrMeasure), some (mkApp (selectedField `fact60) i),
        some haa, some har, none, some hOuter]
    let geometry := mkAppN (mkConst (currentNS ++ `geometry)) all
    let hCoordinates ← component geometry 6
    let result ← mkAppM `Set.MapsTo.mono_left #[hCoordinates, hSource]
    discard <| save `JanetCartan.PhysicalNormalInverse.OriginalCarriers.common_measurement_coordinates
      all result
    logInfo "kernel-checked actual native38 common source coordinates with FULL original label support and original compatibility domain"

end JanetCartan.PhysicalNormalInverse.OriginalCarriersApplication
