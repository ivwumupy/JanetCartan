module

public meta import Lean

/-!
# Apply the full source producer to the one actual original current

The ordinary generated proof closes all reference, leading-data, geometric
and current-history inputs of the native full-strain source constructor.
Prescribed mask/scalar inputs remain explicit until the original signed mask
specialization; they are not claimed to be actual response or Main producers.
-/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSourceProfilesTemplate
open Lean Meta Elab Command

private def lead : Name := `JanetCartan.PhysicalInitialization.CurrentLeading
private def current : Name := `JanetCartan.PhysicalInitialization.OriginalCurrent
private def original : Name := `JanetCartan.PhysicalSeed.OriginalBoundary
private def selected : Name := `JanetCartan.PhysicalSeed.SelectedBoundary
private def cap : Name := `JanetCartan.PhysicalNormalInverse.StrongCurrent.Cap
private def root : Name := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Prescribed

private def save (name : Name) (params : Array Expr) (proof : Expr) (isDef := false) : MetaM Expr := do
  let type ← instantiateMVars (← mkForallFVars params (← inferType proof))
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  if type.hasMVar || value.hasMVar || type.hasFVar || value.hasFVar ||
      type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then
    throwError "original source: unfinished or extra argument in {name}"
  if isDef then
    addDecl (.defnDecl {
      name, levelParams := [], type, value,
      hints := .abbrev, safety := .safe }) (forceExpose := true)
  else
    addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
  return mkAppN (mkConst name) params

private def component (proof : Expr) (index : Nat) : MetaM Expr := do
  let mut proof := proof
  for _ in [:index] do proof := .proj ``And 1 proof
  if (← whnf (← inferType proof)).isAppOfArity ``And 2 then
    return .proj ``And 0 proof
  return proof

private partial def cache (ns : Name) (params : Array Expr) (proof : Expr)
    (index : Nat := 0) : MetaM Unit := do
  let type ← whnf (← inferType proof)
  if type.isAppOfArity ``Exists 2 then
    let .lam name _ _ _ := type.appArg! | throwError "original source: expected witness"
    discard <| save (ns ++ name) params (← mkAppM ``Classical.choose #[proof]) true
    let next ← save (ns ++ Name.mkSimple s!"afterChoice_{name}") params
      (← mkAppM ``Classical.choose_spec #[proof])
    cache ns params next index
  else if type.isAppOfArity ``And 2 then
    discard <| save (ns ++ Name.mkSimple s!"fact{index}") params (.proj ``And 0 proof)
    let next ← save (ns ++ Name.mkSimple s!"afterFact{index}") params (.proj ``And 1 proof)
    cache ns params next (index+1)
  else
    discard <| save (ns ++ `continuation) params proof

private def sourcePatch (fixed : Array Expr) (i : Expr) : MetaM (Expr × Expr) := do
  let center ← mkAppM ``Sigma.fst #[i]
  let incidence ← mkAppM ``Subtype.val #[center]
  let pair ← mkAppM ``Subtype.val #[incidence]
  let chart ← mkAppM ``Prod.fst #[pair]
  let patchNumber ← mkAppM ``Sigma.snd #[i]
  let E := mkAppN (mkConst (lead ++ `E)) fixed
  let .forallE _ patchType _ _ ← whnf (← inferType E) | throwError "original source: missing patch"
  let patchType ← whnf patchType
  let patch ← mkAppOptM ``Sigma.mk
    #[some patchType.appFn!.appArg!, some patchType.appArg!, some chart, some patchNumber]
  let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
    #[fixed[0]!, fixed[1]!, fixed[20]!]
  let originalPrefix := fixed[:21].toArray.set! 20 capped
  let cell := mkAppN (mkConst (selected ++ `cell)) (originalPrefix ++ #[incidence, patchNumber])
  return (patch, cell)

/-- Close the full source's actual original reference/leading/history inputs.
The remaining prescribed masks and scalar reserve are exactly the inputs of
its subsequent original signed-cutoff specialization. -/
elab "apply_original_current_reduced_source" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalPrimary.exists_history_leading_reducedSource_reserved_fourier_profiles
  let strong := `JanetCartan.PhysicalNormalInverse.StrongCurrent.initialized
  let strongInfo ← getConstInfo strong
  let some strongBody := strongInfo.value? (allowOpaque := true)
    | throwError "original source: strong constructor proof is not exposed"
  forallBoundedTelescope (← getConstInfo (current ++ `S)).type (some 31) fun fixed _ => do
    unless fixed.size == 31 do throwError "original source: expected original31"
    let orig := fixed[:21].toArray
    let native ← withTransparency .reducible <| whnf (strongBody.beta orig)
    unless native.isAppOfArity
        `JanetCartan.PhysicalNormalInverse.exists_capped_source_history_inverse_with_scalar_admission 121 do
      throwError "original source: strong constructor lost exact121 static application"
    let na := native.getAppArgs
    let hSigma := .proj ``And 0 fixed[22]!
    let hSigmaOne ← mkAppM `le_trans
      #[.proj ``And 1 fixed[22]!, mkAppN (mkConst (cap ++ `fact2)) orig]
    let G ← mkAppM `JanetCartan.sourceDilationReference #[na[4]!, hSigma, hSigmaOne]
    let sourceRef := mkAppN (mkConst source)
      #[fixed[0]!, fixed[1]!, G, na[5]!, na[6]!, na[7]!, na[8]!, na[9]!]
    let .forallE _ referenceType _ _ ← whnf (← inferType sourceRef)
      | throwError "original source: missing reference tolerance"
    let marginType ← forallTelescope referenceType fun _ bound =>
      mkAppM ``LE.le #[fixed[2]!, bound.appArg!]
    withLocalDeclD `hstrain marginType fun hstrain => do
      let hframe := mkAppN
        (mkConst `JanetCartan.PhysicalInitialization.supplied_original_source_frame)
        (fixed[:18].toArray ++ #[fixed[21]!, hSigma, hSigmaOne])
      let href ← forallTelescope referenceType fun index _ => do
        mkLambdaFVars index (← mkAppM `lt_of_lt_of_le #[mkAppN hframe index, hstrain])
      let nativePrefix := mkAppN
        (mkConst `JanetCartan.PhysicalNormalInverse.StrongCurrent.source_continuation) fixed[:30].toArray
      let .forallE _ budgetType _ _ ← whnf (← inferType nativePrefix)
        | throwError "original source: missing selected index budget"
      forallBoundedTelescope budgetType (some 1) fun indices _ => do
        let i := indices[0]!
        let (patch, cell) ← sourcePatch fixed i
        let atPatch := mkAppN (mkConst (lead ++ `AtPatch.fact0)) fixed
        let dataArgs ← forallBoundedTelescope (← inferType atPatch) (some 6) fun history _ => do
          let type ← inferType (mkAppN atPatch (history.push patch))
          unless type.isAppOfArity `JanetCartan.PhysicalPrimary.RetainedLeadingData 34 do
            throwError "original source: actual leading datum changed"
          let args := type.getAppArgs[:30].toArray
          for arg in args do
            if (arg.find? fun e ↦ history.contains e).isSome then
              throwError "original source: static source budgets depend on history"
          return args
        let atCell (name : Name) := mkAppN (mkConst (original ++ name))
          #[fixed[0]!, fixed[1]!, patch, cell]
        let positive := atCell `comparison_pos
        let cover := atCell `comparison_cover
        let hLower ← mkAppM `JanetCartan.PhysicalInitialization.positive_leading_scalar_lower_bound #[hSigma]
        let hm ← mkAppM `le_of_lt #[hLower]
        let hgap ← mkAppM `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.scalar_budget_gap
          #[hSigma, mkAppN (mkConst (cap ++ `fact5)) orig]
        let hc := mkAppN (mkConst (lead ++ `fact2)) (fixed.push patch)
        let hball := mkApp na[15]! i
        let sourceArgs := #[href, dataArgs[1]!, dataArgs[4]!, hball] ++
          dataArgs[6:23].toArray ++
          #[dataArgs[23]!, dataArgs[24]!, dataArgs[25]!, hm, hgap, hc,
            dataArgs[26]!, dataArgs[27]!, dataArgs[28]!, dataArgs[29]!, cell,
            ← component positive 0, ← component positive 1, ← component positive 2,
            ← component positive 8, ← component cover 0, ← component cover 1]
        let sourceGeometry := mkAppN sourceRef sourceArgs
        forallBoundedTelescope (← inferType sourceGeometry) (some 18) fun masks _ => do
          unless masks.size == 18 do throwError "original source: prescribed scalar/mask telescope changed"
          let full := mkAppN sourceGeometry (masks ++ #[fixed[24]!, fixed[25]!, fixed[26]!])
          forallBoundedTelescope (← inferType full) (some 1) fun reserve _ => do
            let full := mkAppN full (reserve.push fixed[27]!)
            forallBoundedTelescope (← inferType full) (some 1) fun hreserve _ => do
              let params := fixed ++ #[hstrain] ++ indices ++ masks ++ reserve ++ hreserve
              let proof := mkAppN full (hreserve.push fixed[29]!)
              let proof ← save (root ++ `initialized) params proof
              cache (root ++ `Native) params proof
              let nativeS := mkAppN (mkConst (root ++ `Native.threshold)) params
              let currentS := mkAppN (mkConst (current ++ `S)) fixed
              let S ← save (root ++ `S) params (← mkAppM ``Max.max #[currentS, nativeS]) true
              let hCurrent ← mkAppM `le_max_left #[currentS, nativeS]
              let hSource ← mkAppM `le_max_right #[currentS, nativeS]
              discard <| save (root ++ `hS) params (← mkAppM `le_trans
                #[mkAppN (mkConst (current ++ `hS)) fixed, hCurrent])
              let continuation := mkAppN (mkConst (root ++ `Native.continuation)) params
              let .forallE name realType _ _ ← whnf (← inferType continuation)
                | throwError "original source: missing physical frequency"
              withLocalDeclD name realType fun R => do
                withLocalDeclD `hR (← mkAppM ``LE.le #[S,R]) fun hR => do
                  let hRi ← mkAppM `le_trans #[hCurrent,hR]
                  let hRs ← mkAppM `le_trans #[hSource,hR]
                  let afterR := mkAppN continuation #[R,hRs]
                  forallBoundedTelescope (← inferType afterR) (some 4) fun history _ => do
                    let afterHistory := mkAppN afterR history
                    forallBoundedTelescope (← inferType afterHistory) (some 2) fun K _ => do
                      let hLeading ← mkAppM `le_trans
                        #[mkAppN (mkConst (current ++ `leading_threshold_le)) fixed,hRi]
                      let leadingPrefix := fixed ++ #[R,hLeading] ++ history
                      let data := mkAppN (mkConst (lead ++ `AtPatch.fact0)) (leadingPrefix.push patch)
                      let da := (← inferType data).getAppArgs
                      let proof := mkAppN afterHistory
                        (K ++ #[da[31]!,da[32]!,da[33]!,data])
                      let publicPrefix := fixed ++ #[R,hRi] ++ history
                      for field in #[`current, `Φ, `Y] do
                        let actual := mkAppN (mkConst (current ++ field)) (publicPrefix.push i)
                        let retained := mkAppN (mkConst (`JanetCartan.PhysicalPrimary.LeadingCell ++ field))
                          (da ++ #[data,cell])
                        unless ← isDefEq actual retained do
                          throwError "original source: mismatch with SAME actual current {field}"
                      discard <| save (root ++ `continuation)
                        (params ++ #[R,hR] ++ history ++ K) proof
  logInfo "kernel-checked full source on SAME original current: no reference, leading datum, chart, rank or coefficient geometry premise; prescribed masks/scalar remain explicit"

/-- Substitute the actual original23 inverse masks, core, chart and selected
cell parameter cutoff into the already checked original-current source proof.
All constants are aliases of the SAME prescribed source choice, not reselected. -/
elab "apply_actual_original_source_masks" : command => liftTermElabM do
  let regular := `JanetCartan.PhysicalInitialization.OriginalRegular
  let masksNS := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
  let actualNS := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
  forallBoundedTelescope (← getConstInfo (regular ++ `f)).type (some 23) fun family _ => do
    let n := (← inferType family[1]!).appArg!
    let originalPrefix := #[n] ++ family[1:21].toArray
    let currentPrefix := mkAppN (mkConst (current ++ `S)) originalPrefix
    forallBoundedTelescope (← inferType currentPrefix) (some 10) fun tail _ => do
      let fixed := originalPrefix ++ tail
      let initialized := mkAppN (mkConst (root ++ `initialized)) fixed
      forallBoundedTelescope (← inferType initialized) (some 4) fun scalar _ => do
        let i := scalar[1]!
        let (patch, cell) ← sourcePatch fixed i
        let masks (field : Name) := mkAppN (mkConst (masksNS ++ field)) family
        let cellMasks (field : Name) := mkAppN (mkConst (masksNS ++ field))
          (family ++ #[patch,cell])
        let core := mkAppN (mkConst `JanetCartan.RevisedUniform.OriginalCore.D) family
        let χsrc := mkAppN (mkConst (regular ++ `χsrc)) family[:21].toArray
        let χ₂ := mkAppN (mkConst (regular ++ `χ₂)) family
        let η ← mkAppM `ContDiffBump.toFun #[χ₂]
        let bump := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.parameterCutoff)
          #[n, family[1]!, patch,cell]
        let θ ← mkAppM `ContDiffBump.toFun #[bump]
        let thetaSpec := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.parameterCutoff_spec)
          #[n, family[1]!, patch,cell]
        let concreteMasks := #[core, masks `chart, masks `χenv, masks `chart_open,
          cellMasks `V, cellMasks `V_open, cellMasks `product_in_comparison_cell,
          masks `χenv_support_coefficient_ball, χsrc, η, masks `χsrc_smooth, masks `χ₂_smooth,
          θ, ← component thetaSpec 0, ← component thetaSpec 1, ← component thetaSpec 2]
        let source := mkAppN initialized (scalar ++ concreteMasks)
        forallBoundedTelescope (← inferType source) (some 2) fun reserve _ => do
          let closed := fixed ++ scalar ++ concreteMasks ++ reserve
          let params := family ++ tail ++ scalar ++ reserve
          unless closed.size == 53 && params.size == 39 do
            throwError "actual source masks: changed fixed input spine"
          for field in #[`S, `hS] do
            discard <| save (actualNS ++ field) params
              (mkAppN (mkConst (root ++ field)) closed) (field == `S)
          discard <| save (actualNS ++ `Csource) params
            (mkAppN (mkConst (root ++ `Native.Csource)) closed) true
          discard <| save (actualNS ++ `Csource_nonneg) params
            (mkAppN (mkConst (root ++ `Native.fact1)) closed)
          let continuation := mkAppN (mkConst (root ++ `continuation)) closed
          discard <| save (actualNS ++ `continuation) params continuation
          forallBoundedTelescope (← inferType continuation) (some 14) fun physical _ => do
            unless physical.size == 14 do
              throwError "actual source masks: changed history/frequency/scalar spine"
            let bounds := mkAppN continuation physical
            let normalizer :=
              `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.normalize_full_source_fourier
            let hproduct ← mkAppM ``congrFun #[masks `source_product]
            let normalized ← forallBoundedTelescope (← getConstInfo normalizer).type
                (some 27) fun arguments _ => do
              unless arguments.size == 27 do
                throwError "actual source masks: changed normalization input spine"
              let mut inputs : Array (Option Expr) := #[]
              for argument in arguments do
                let name ← argument.fvarId!.getUserName
                inputs := inputs.push <| if name == `χenv then some (masks `χenv)
                  else if name == `hsource then some hproduct
                  else if name == `henv then some (masks `χ₃_on_χ₂)
                  else if name == `hbound then some bounds
                  else none
              mkAppOptM normalizer inputs
            discard <| save (actualNS ++ `full_source_profiles) (params ++ physical) normalized
  logInfo "kernel-checked actual original39 full source: SAME chi2/chi3/measured mask, exact coreD, selected-cell parameter mask, no geometric/mask inputs and no new choice; scalar profile remains its explicit positive-density consumer"

/-- The actual original masks normalize the literal source globally. Therefore
all jets use the small chi2 source, not the broad measured mask or chi3 alone. -/
elab "prove_actual_original_source_normalization" : command => liftTermElabM do
  let regular := `JanetCartan.PhysicalInitialization.OriginalRegular
  let masksNS := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
  let sourceNS := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles
  forallBoundedTelescope (← getConstInfo (masksNS ++ `V)).type (some 25) fun fixed _ => do
    let family := fixed[:23].toArray
    let n := (← inferType fixed[1]!).appArg!
    let primitive := mkApp (mkConst (sourceNS ++ `reducedSource_mask_normalization)) n
    forallBoundedTelescope (← inferType primitive) (some 2) fun raw _ => do
      let masks (field : Name) := mkAppN (mkConst (masksNS ++ field)) family
      let χsrc := mkAppN (mkConst (regular ++ `χsrc)) family[:21].toArray
      let η ← mkAppM `ContDiffBump.toFun #[mkAppN (mkConst (regular ++ `χ₂)) family]
      let χenv ← mkAppM `JanetCartan.ResponseSourceExtension.OutputCutoff.toFun #[masks `χenv]
      let θ ← mkAppM `ContDiffBump.toFun
        #[mkAppN (mkConst (sourceNS ++ `parameterCutoff)) #[n,fixed[1]!,fixed[23]!,fixed[24]!]]
      let proof := mkAppN primitive
        (raw ++ #[χsrc,η,χenv,θ,← mkAppM ``congrFun #[masks `source_product],masks `χ₃_on_χ₂])
      discard <| save (sourceNS ++ `original_mask_normalization) (fixed ++ raw) proof
  logInfo "kernel-checked global original27 mask normalization: theta chiSrc chi2 halfQ(chi3 rawstrain) = theta chi2 halfQ(rawstrain), including all jets by equality"

end JanetCartan.PhysicalPrimary.OriginalSourceProfilesTemplate
