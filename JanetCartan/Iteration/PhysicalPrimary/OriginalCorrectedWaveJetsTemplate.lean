module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate

/-!
# Original-data specialization for sharp physical-wave constants

The radial data below are the existing once-capped original colored packet.
Only their finite upper sum is taken; neither a new packet nor a rate, event,
shift, cutoff or inverse is selected. The costs precede all histories.
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPrimary.OriginalCorrectedWaveJetsTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveJets
private def color := `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication
private def app (name : Name) (args : Array Expr) : Expr := mkAppN (mkConst name) args

private def emit (key : Name) (params : Array Expr) (value : Expr)
    (data := false) (target : Option Expr := none) : MetaM Expr := do
  let result ← store (ns ++ key) params value data target
  addDocStringCore (ns ++ key) "Original-data prerequisite for sharp fixed-scale physical jets (main:eq:primary-fixed-scales), preserving the native colored packet, source/current, smoothing chart, outer labels and shifted parameters. No new radial packet, event, sample, cutoff or response is chosen."
  return result

/-- The existing original22 colored menu supplies both radial comparisons
needed for sharp displacement remodulation, with constant one on the inverse
carrier side. The full spatial-wave profile is a separate construction. -/
elab "construct_original_sharp_radial_comparisons" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (color ++ `Rcolor)).type (some 22) fun fixed _ => do
    unless fixed.size == 22 do throwError "sharp original jets: changed original22 colored prefix"
    let radial := app (color ++ `Rcolor) fixed
    let hradial := app (color ++ `radial_ge_one) fixed
    let groups := (← inferType radial).bindingDomain!
    let native ← withTransparency .all <| whnf groups
    unless native.isAppOfArity ``Prod 2 do throwError "sharp original jets: colored product index changed"
    let index ← withTransparency .all <| whnf native.getAppArgs[0]!
    let colors ← withTransparency .all <| whnf native.getAppArgs[1]!
    let concrete ← mkAppM ``Prod #[index,colors]
    let finite ← synthInstance (← mkAppM `Finite #[concrete])
    let rawCost ← mkAppOptM (ns ++ `finiteRadialCost) #[some groups,some finite,some radial]
    let C ← emit `Cfrequency fixed rawCost true
    let hb ← mkAppOptM (ns ++ `finiteRadialCost_bounds) #[some groups,some finite,some radial,some hradial]
    let hC : Expr := .proj ``And 0 hb
    let hu : Expr := .proj ``And 1 hb
    let substitute (t : Expr) := t.replace fun e => if e == rawCost then some C else none
    discard <| emit `Cfrequency_ge_one fixed hC false (some (substitute (← inferType hC)))
    let hupper ← emit `radial_le_Cfrequency fixed hu false (some (substitute (← inferType hu)))
    withLocalDeclD `Rinit (mkConst `Real) fun R => do
      let one ← mkNumeral (mkConst `Real) 1
      withLocalDeclD `hRinit (← mkAppM ``LE.le #[one,R]) fun hR => do
        withLocalDeclD `stage (mkConst ``Nat) fun stage => do
          forallBoundedTelescope (← inferType hradial) (some 1) fun label _ => do
            unless label.size == 1 do throwError "sharp original jets: missing SAME colored label"
            let proof ← mkAppM (ns ++ `radial_rate_bounds)
              #[hR,mkAppN hradial label,mkAppN hupper label,stage]
            discard <| emit `rate_comparisons (fixed ++ #[R,hR,stage] ++ label) proof
  logInfo "actual original22 colored packet: fixed Cfrequency and BOTH reciprocal-carrier comparisons before every history, stage and label; no choice of labels or sample"

/-- The already fixed smoothing chart is an open subset of every original
protected spatial source. Hence its entire cutoff support lies inside the
interior region on which the physical response profile is valid. -/
elab "retain_original_sharp_cutoff_interior" : command => liftTermElabM do
  let source := `JanetCartan.PhysicalPrimary.OriginalUncutSource.Actual
  let geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
  forallBoundedTelescope (← getConstInfo (source ++ `chart_in_source)).type (some 24) fun x _ => do
    unless x.size == 24 do throwError "sharp cutoff geometry: expected fixed23 and original patch"
    let hcut := app (geo ++ `smoothing_chart_in_source_chart) x[:23].toArray
    let hs := app (source ++ `chart_in_source) x
    let hsub ← mkAppM `Set.Subset.trans #[hcut,hs]
    let subArgs := (← inferType hsub).getAppArgs
    let O := subArgs[subArgs.size-2]!
    let hO ← mkFreshExprMVar (← mkAppM `IsOpen #[O])
    unless (← hO.mvarId!.apply (← mkConstWithFreshMVarLevels `Metric.isOpen_ball)).isEmpty do
      throwError "sharp cutoff geometry: actual smoothing chart ceased to be the native ball"
    let hO ← instantiateMVars hO
    let hi ← mkAppM `interior_maximal #[hsub,hO]
    discard <| emit `cutoff_chart_in_source_interior x hi
  logInfo "actual fixed23 smoothing chart lies inside the SAME protected source interior for every original patch"

/-- Every nonzero ORIGINAL outer-weight label belongs to the unchanged open
comparison window. The positive baseline needs no inner angular factor. The
same source/current geometry then admits every point of Dsmooth.chart. -/
elab "retain_original_sharp_active_comparison_region" : command => liftTermElabM do
  let geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
  let comparison := `JanetCartan.PhysicalPrimary.OriginalUncutSource
  OriginalLocalWaveGeometryTemplate.withSourcePrefix 53 fun s => do
    let a ← OriginalLocalWaveGeometryTemplate.sourceCurrent s
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let cn := #[n,s[1]!,a.patch,a.cell]
    let ws := app (comparison ++ `parameterComparisonWindow_spec) cn
    let closedToComparison : Expr := .proj ``And 1 (.proj ``And 1 (.proj ``And 1 ws))
    let V := app (comparison ++ `parameterComparisonWindow) cn
    let hX := app (ns ++ `cutoff_chart_in_source_interior) (s[:23].toArray.push a.patch)
    let hcut := app (geo ++ `smoothing_chart_in_source_chart) s[:23].toArray
    let X := (← inferType hX).getAppArgs.back!
    let O := (← inferType (app (geo ++ `current_open) s)).appArg!
    let region ← emit `comparison_region s (← mkAppM `Set.inter #[O,← mkAppM `Set.prod #[X,V]]) true
    let hclosed := app (geo ++ `outer_weight_closed_cell) s
    let hbig := app (geo ++ `outer_weight_parameter) s
    forallBoundedTelescope (← inferType hclosed) (some 5) fun sample _ => do
      unless sample.size == 5 do throwError "sharp outer admission: changed original sample/node/weight prefix"
      let hc := mkAppN hclosed sample
      let tc ← Core.betaReduce (← zetaReduce (← inferType hc))
      unless tc.isAppOfArity `Membership.mem 5 do
        throwError "sharp outer admission: expected the original closed-cell membership"
      let c := tc.getAppArgs[4]!
      let hv ← emit `outer_active_comparison_parameter (s ++ sample) (mkAppN closedToComparison #[c,hc])
      let result ← forallBoundedTelescope (← inferType hcut) (some 2) fun xx _ => do
        unless xx.size == 2 do throwError "sharp cutoff inclusion: missing point and chart membership"
        let pair ← mkAppM ``Prod.mk #[xx[0]!,c]
        let hprod ← mkAppM ``And.intro #[mkAppN hcut xx,mkAppN hbig sample]
        let ho := mkAppN (app (geo ++ `source_product_in_current) s) #[pair,hprod]
        let hs ← mkAppM ``And.intro #[mkAppN hX xx,hv]
        let h ← mkAppM ``And.intro #[ho,hs]
        let target ← mkAppM `Membership.mem #[region,pair]
        let target ← mkForallFVars xx target
        let h ← mkLambdaFVars xx h
        return (h,target)
      discard <| emit `outer_active_cutoff_region (s ++ sample) result.1 false (some result.2)
  logInfo "actual nonzero outer labels: SAME closed carrier cell and Dsmooth chart admitted into the physical response comparison region; original positive baseline retained"

/-- The whole-wave frequency shifts already lie in the SAME closed small
cell, by the original finite-band rate margin. Apply the existing comparison
window certificate without replacing a scalar, a shift, or the full response. -/
elab "retain_original_sharp_shifted_comparison_region" : command => liftTermElabM do
  let wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
  let geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
  let comparison := `JanetCartan.PhysicalPrimary.OriginalUncutSource
  let closedName := wave ++ `Whole.shifted_parameter_in_closed_cell
  forallTelescope (← getConstInfo closedName).type fun xs target => do
    let some value := (← getConstInfo closedName).value? (allowOpaque := true)
      | throwError "sharp shifted admission: unavailable original closed-cell proof"
    let original ← Core.betaReduce (value.beta xs)
    let some rawT := original.find? (·.isAppOfArity (wave ++ `T) 53)
      | throwError "sharp shifted admission: lost the SAME original Source53 patch family"
    let s := rawT.getAppArgs
    unless s.all (fun e => !e.hasLooseBVars) do
      throwError "sharp shifted admission: source data unexpectedly depends on a bound variable"
    let a ← OriginalLocalWaveGeometryTemplate.sourceCurrent s
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let cn := #[n,s[1]!,a.patch,a.cell]
    let ws := app (comparison ++ `parameterComparisonWindow_spec) cn
    let closedToComparison : Expr := .proj ``And 1 (.proj ``And 1 (.proj ``And 1 ws))
    let comparisonToWindow : Expr := .proj ``And 0 (.proj ``And 1 ws)
    let mem ← Core.betaReduce (← zetaReduce target)
    unless mem.isAppOfArity `Membership.mem 5 do
      throwError "sharp shifted admission: expected exact closed-cell membership"
    let c := mem.getAppArgs[4]!
    let hv ← emit `whole_shifted_comparison_parameter xs
      (mkAppN closedToComparison #[c,app closedName xs])
    let hbig := mkAppN comparisonToWindow #[c,hv]
    let hX := app (ns ++ `cutoff_chart_in_source_interior) (s[:23].toArray.push a.patch)
    let hcut := app (geo ++ `smoothing_chart_in_source_chart) s[:23].toArray
    let region := app (ns ++ `comparison_region) s
    let result ← forallBoundedTelescope (← inferType hcut) (some 2) fun xx _ => do
      unless xx.size == 2 do throwError "sharp shifted cutoff inclusion: missing physical point"
      let pair ← mkAppM ``Prod.mk #[xx[0]!,c]
      let hprod ← mkAppM ``And.intro #[mkAppN hcut xx,hbig]
      let ho := mkAppN (app (geo ++ `source_product_in_current) s) #[pair,hprod]
      let hs ← mkAppM ``And.intro #[mkAppN hX xx,hv]
      let h ← mkAppM ``And.intro #[ho,hs]
      let target ← mkForallFVars xx (← mkAppM `Membership.mem #[region,pair])
      return (← mkLambdaFVars xx h,target)
    discard <| emit `whole_shifted_cutoff_region xs result.1 false (some result.2)
  logInfo "actual whole-wave shifted parameters and Dsmooth chart lie in the SAME physical response comparison region, using only the native finite-band margin"

end JanetCartan.PhysicalPrimary.OriginalCorrectedWaveJetsTemplate
end
