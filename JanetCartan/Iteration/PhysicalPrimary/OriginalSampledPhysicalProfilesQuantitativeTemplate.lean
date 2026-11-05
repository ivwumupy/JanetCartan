module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalProfilesWhole
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPdoProfiles
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalSourceTemplate

/-!
# Quantitative deductions for the frozen original physical field

Keep the independent whole-field data and detector callback frozen. These
commands apply the actual parent sharp jets to the unchanged selected component
adjoint input of supplied smooth source DATA, then use only its literal Fourier
mass. The frozen background-only iterate is a checked special data case, not
the final paper forcing. These commands do not assert the still-pending uniform
fixed-K mass or the final Sobolev profile (`main:eq:primary-fixed-scales`).
-/

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
open Lean Meta Elab Command
open OriginalCorrectedWaveEnvelopeTemplate
open OriginalSampledPhysicalProfilesTemplate
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
private def envelope := `JanetCartan.PhysicalPrimary.OriginalCorrectedWaveEnvelope
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def termWith (vars : List (Name × Expr)) (code : String)
    (goal : Option Expr := none) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith vars code goal)
private def tail (h : Expr) (j : Nat) := Nat.repeat (fun e => Expr.proj ``And 1 e) j h
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (tail h j)
private def nativeType (value : Expr) : MetaM Expr := do
  let info ← getConstInfo value.getAppFn.constName!
  let mut type := info.type.instantiateLevelParams info.levelParams value.getAppFn.constLevels!
  for arg in value.getAppArgs do
    let .forallE _ _ rest _ := type.consumeMData |
      throwError "actual primary integral: changed published declaration arity"
    type := rest.instantiate1 arg
  return type

private def smoothAtUsing (smooth type order x neighborhood : Expr) : MetaM Expr := do
  unless type.isAppOfArity ``ContDiffOn 11 do
    throwError "pointwise smoothness: original ContDiffOn signature changed"
  let a := type.getAppArgs
  let levels := type.getAppFn.constLevels!
  let atPoint := mkAppN (mkConst ``ContDiffOn.contDiffAt levels)
    (a[:8].toArray ++ #[a[10]!,a[9]!,x,a[8]!,smooth,neighborhood])
  let orderLe ← termWith [] "(by simp)" (some (← mkAppM ``LE.le #[order,a[8]!]))
  return mkAppN (mkConst ``ContDiffAt.of_le levels)
    (a[:8].toArray ++ #[a[9]!,x,order,a[8]!,atPoint,orderLe])

private def emit (field : Name) (xs : Array Expr) (proof : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType proof
  let type ← instantiateMVars (← mkForallFVars xs target)
  let value ← instantiateMVars (← mkLambdaFVars xs proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual sampled primary: unresolved declaration {field}"
  let name := ns ++ field
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  liftM <| IO.eprintln s!"actual sampled primary: checking {field}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual original native stage and unchanged whole response on the old Dsmooth chart, with original scalar, source, cutoff, sample and rates (main:eq:primary-fixed-scales). Quantitative completion still requires the actual fixed-K Picard mass bound."
  logInfo m!"actual original physical wave: checked {field} / {xs.size}"

/-- Uniformize only over the fixed original ROW labels. The actual published
Index22 supplies its own Fintype through the unchanged original weight cube;
no sample, band or Picard count is inserted (`main:eq:primary-fixed-scales`). -/
private def withOriginalRowPhysicalCost
    (next : Array Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  let name := envelope ++ `Cphysical
  let info ← getConstInfo name
  bindNative 45 info.type #[] fun xs => do
    let fixed := xs[:44].toArray
    let actualRow ← inferType xs[44]!
    let .forallE _ rowType _ _ := (← nativeType (app (envelope ++ `Pξ) fixed)).consumeMData |
      throwError "uniform physical cost: original Pξ row domain disappeared"
    unless rowType.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.Index 22 do
      throwError "uniform physical cost: changed original Pξ row index"
    let index ← getConstInfo rowType.getAppFn.constName!
    let some body := index.value? (allowOpaque := true) |
      throwError "uniform physical cost: original row index body unavailable"
    let originalRow := (body.beta rowType.getAppArgs).headBeta
    unless originalRow == actualRow do
      unless ← isDefEq originalRow actualRow do
        throwError "uniform physical cost: Cphysical and its original Pξ do not share the same row"
    let cube ← getConstInfo `JanetCartan.PhysicalSampling.OriginalWeights.exists_cube
    let some proof := cube.value? (allowOpaque := true) |
      throwError "uniform physical cost: original cube proof requires its private import"
    let original := (proof.beta rowType.getAppArgs).headBeta
    unless original.isAppOfArity `JanetCartan.PhysicalSampling.exists_finite_original_carrier_weight_bounds 5 do
      throwError "uniform physical cost: changed original finite cube producer"
    let args := original.getAppArgs
    unless args[0]! == rowType do
      throwError "uniform physical cost: original row domain was changed"
    next fixed rowType args[1]! (app name fixed)
where
  bindNative : Nat → Expr → Array Expr → (Array Expr → MetaM Unit) → MetaM Unit
    | 0,_,xs,next => next xs
    | remaining+1,type,xs,next => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "uniform physical cost: original static45 ended at {xs.size}"
      withLocalDeclNoLocalInstanceUpdate name bi domain fun x =>
        bindNative remaining (body.instantiate1 x) (xs.push x) next

/-- Retain the actual fixed-row physical profile and its two elementary finite
majorant consequences before R/history. Each declaration has ordinary defaults;
no norm or Fourier-mass bound is an input. -/
elab "publish_quantitative_original_uniform_cost " mode:num : command => liftTermElabM do
  withOriginalRowPhysicalCost fun fixed rowType finite family => do
    let majorant := `JanetCartan.PhysicalPrimary.OriginalPdoProfiles
    let args := #[rowType,finite,family]
    let value := mkAppN (mkConst (majorant ++ `finite_profile_majorant) [.zero]) args
    let named := app (ns ++ `uniformPhysicalCost) fixed
    if mode.getNat == 0 then
      emit `uniformPhysicalCost fixed value true
        (some (← mkArrow (mkConst ``Nat) (mkConst ``Real)))
    else if mode.getNat == 1 || mode.getNat == 2 then
      let theoremName := if mode.getNat == 1 then `finite_profile_majorant_nonneg
        else `le_finite_profile_majorant
      let field := if mode.getNat == 1 then `uniformPhysicalCost_nonneg else `physicalCost_le_uniform
      let proof := mkAppN (mkConst (majorant ++ theoremName) [.zero]) args
      let target := (← nativeType proof).replace fun e => if e == value then some named else none
      unless target.getUsedConstantsAsSet.contains (ns ++ `uniformPhysicalCost) do
        throwError "uniform physical cost: exact retained majorant alias disappeared"
      emit field fixed proof false (some target)
    else throwError "uniform physical cost: unknown consequence"

elab "publish_quantitative_original_baseline_sharp_jets" : command => liftTermElabM do
  withPublishedNativeStage fun g => withNativeResponseColor g fun color => do
    let closed := app (geo ++ `outer_weight_closed_cell) color.source53
    forallBoundedTelescope (← nativeType closed) (some 5) fun sample _ => do
      unless sample.size == 5 do throwError "actual baseline sharp: original window/mesh/shift/node/weight changed"
      let hc := mkAppN closed sample
      let membership ← Core.betaReduce (← zetaReduce (← nativeType hc))
      unless membership.isAppOfArity `Membership.mem 5 do
        throwError "actual baseline sharp: lost SAME closed parent cell"
      let parameter := membership.getAppArgs[4]!
      let h := app (envelope ++ `atom_sharp_spatial_jets)
        (g.args50 ++ #[g.data.i,color.color,parameter,hc])
      emit `baseline_sharp_spatial_jets (g.args50 ++ #[g.data.i,color.color] ++ sample) h false (some (← nativeType h))

elab "publish_quantitative_original_shifted_sharp_jets" : command => liftTermElabM do
  withPublishedNativeStage fun g => withNativeResponseColor g fun color => do
    let family := originalWaveFamily color
    unless family.size == 61 do throwError "actual shifted sharp: original source/graph61 changed"
    let rates := app (envelope ++ `stage_rates) g.args50
    let hΛ := part rates 1
    let Λ := (← inferType hΛ).appArg!
    let byColor := mkAppN (tail rates 6) #[g.data.i,color.color]
    let margin := tail byColor 3
    let closed := app (wave ++ `Whole.shifted_parameter_in_closed_cell)
      (family ++ #[Λ,hΛ,margin])
    forallBoundedTelescope (← nativeType closed) (some 4) fun shifted _ => do
      unless shifted.size == 4 do throwError "actual shifted sharp: carrier/frequency admission changed"
      let hc := mkAppN closed shifted
      let membership ← Core.betaReduce (← zetaReduce (← nativeType hc))
      unless membership.isAppOfArity `Membership.mem 5 do
        throwError "actual shifted sharp: lost original shifted closed-cell parameter"
      let parameter := membership.getAppArgs[4]!
      let h := app (envelope ++ `atom_sharp_spatial_jets)
        (g.args50 ++ #[g.data.i,color.color,parameter,hc])
      emit `shifted_sharp_spatial_jets (g.args50 ++ #[g.data.i,color.color] ++ shifted) h false (some (← nativeType h))

private abbrev NativeArgs := Array (Name × Expr)

private def nativeAt (xs : NativeArgs) (key : Name) : MetaM Expr := do
  let some (_,value) := xs.find? (·.1 == key) |
    throwError "actual primary integral: missing native operand {key}"
  return value

private def nativeArguments (name : Name) (value : Expr) : MetaM NativeArgs := do
  let value := value.headBeta
  unless value.isAppOf name do
    throwError "actual primary integral: expected producer {name}, found {value.getAppFn}"
  let mut type := (← getConstInfo name).type
  let mut xs := #[]
  for value in value.getAppArgs do
    let .forallE key _ rest _ := type.consumeMData |
      throwError "actual primary integral: changed producer telescope {name}"
    xs := xs.push (key,value)
    type := rest
  return xs

private def applyNativeThrough (name last : Name) (xs : NativeArgs) : MetaM Expr := do
  let mut type := (← getConstInfo name).type
  let mut value := mkConst name
  while let .forallE key _ rest _ := type.consumeMData do
    value := mkApp value (← nativeAt xs key)
    if key == last then return value
    type := rest
  throwError "actual primary integral: missing final native operand {last}"

private def originalBodyAt (name : Name) (args : Array Expr)
    (levels : List Level := []) : MetaM Expr := do
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true) |
    throwError "actual primary field: unavailable original producer {name}"
  unless info.levelParams.length == levels.length do
    throwError "actual primary field: native producer universe arguments changed"
  return ((body.instantiateLevelParams info.levelParams levels).beta args).headBeta

/-- On14's one selected shift, integrate86's unchanged sharp corrected atoms,
then add the unscaled positive baseline and the original zero-safe angular
factor. The right side is the L¹ mass of the original unweighted component
input of supplied source DATA, not a free WideInput or a claimed Picard bound.
The complete-source run is substituted by its actual producer. External sqrtμ
is still absent here. -/
elab "publish_quantitative_original_selected_mass_jets " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "unknown actual source mass-jet publication"
  withActualSelectedSourceWave fun params _ input literal _ native64 detector => do
    let field := app (ns ++ `selectedSourceCombinedWave) params
    let combinedArgs := literal.getAppArgs
    let combined ← originalBodyAt (wave ++ `Combined.field) combinedArgs
    unless combined.isAppOfArity ``HAdd.hAdd 6 do
      throwError "actual final physical jets: changed baseline-plus-full-angular sum"
    let base := combined.getAppArgs[4]!
    let sample := combinedArgs[64:68].toArray
    let i := params[52]!
    let index ← inferType i
    unless index.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do
      throwError "actual final physical jets: original outer sample changed"
    let sa := index.getAppArgs
    let row := Expr.proj ``Sigma 0 i
    let sampleValue := Expr.proj ``Subtype 0 (Expr.proj ``Sigma 1 i)
    let color := app `JanetCartan.SeparatedSampling.color #[sa[1]!,Expr.proj ``Prod 0 sampleValue]
    let hweight := mkAppN (mkConst (ns ++ `original_sample_weight_ne_zero) [.zero]) (sa.push i)
    let atomic := params[:50].toArray ++ #[row,color]
    let baseline := app (ns ++ `baseline_sharp_spatial_jets) (atomic ++ sample.push hweight)
    let baselineType ← nativeType baseline
    unless baselineType.isAppOfArity ``And 2 do
      throwError "actual final physical jets: baseline sharp conjunction changed"
    let smoothType := baselineType.getAppArgs[0]!
    let X := smoothType.getAppArgs[10]!
    let hX ← termWith [] "(Metric.isOpen_ball)" (some (← mkAppM `IsOpen #[X]))
    let node := app `JanetCartan.SeparatedSampling.node sample[1:4].toArray
    let factorEq := app (wave ++ `Whole.full_angular_factor.corrected) (native64 ++ #[node,input])
    let factorType ← nativeType factorEq
    unless factorType.isAppOfArity ``Eq 3 && factorType.appArg!.isAppOfArity ``HSMul.hSMul 6 do
      throwError "actual final physical jets: full-angular factor identity changed"
    let b := factorType.appArg!.getAppArgs[4]!
    let W := factorType.appArg!.getAppArgs[5]!
    unless b.isAppOfArity `JanetCartan.PhysicalMean.OriginalWeightBridge.Original.factor 24 do
      throwError "actual final physical jets: not the original zero-safe angular factor"
    let hb := app `JanetCartan.PhysicalMean.OriginalWeightBridge.Original.factor_range b.getAppArgs
    let d ← nativeAt detector `d
    let mass ← termWith [(`d,d),(`v,input)]
      "(∫ η, ‖JanetCartan.RawInputPartition.weightedWideDensity d v η‖)" (some (mkConst ``Real))
    let zero ← mkNumeral (mkConst ``Real) 0
    let hmass ← termWith [] "(by exact MeasureTheory.integral_nonneg (fun _ => norm_nonneg _))"
      (some (← mkAppM ``LE.le #[zero,mass]))
    let rawBody ← originalBodyAt (wave ++ `Whole.raw_on_selected_cell) native64
    let rawName := `JanetCartan.RawPrimary.contDiffOn_fullPrimaryWave
    let some raw := rawBody.find? (·.isAppOf rawName) |
      throwError "actual final physical jets: native source admission disappeared"
    let rawKnown ← nativeArguments rawName raw
    let T ← nativeAt rawKnown `T
    unless T.isAppOfArity (wave ++ `T) 53 do
      throwError "actual final physical jets: original source53 changed"
    let source := T.getAppArgs
    let hcut := app (geo ++ `smoothing_chart_in_source_chart) source[:23].toArray
    let support := app (wave ++ `Whole.inner_factor_support) (native64[:61].toArray.push node)
    let supportType ← nativeType support
    let .forallE supportLabel supportDomain _ supportBi := supportType.consumeMData |
      throwError "actual final physical jets: original factor support implication missing"
    let withSupport (next : Expr → Array Expr → MetaM Expr) : MetaM Expr := do
      withLocalDeclNoLocalInstanceUpdate supportLabel supportBi supportDomain fun nonzero => do
        let hp := mkApp support nonzero
        let hpType ← nativeType hp
        unless hpType.isAppOfArity ``Membership.mem 5 do
          throwError "actual final physical jets: native inner carrier support changed"
        let carrier := hpType.getAppArgs[4]!
        let whole := native64 ++ #[carrier,hp,input]
        mkLambdaFVars #[nonzero] (← next nonzero whole)
    let jetsType := baselineType.getAppArgs[1]!
    forallBoundedTelescope jetsType (some 3) fun point result => do
      unless point.size == 3 && result.isAppOfArity ``LE.le 4 do
        throwError "actual final physical jets: original jet/point/chart tail changed"
      let q := point[0]!
      let x := point[1]!
      let hx := point[2]!
      let C := result.getAppArgs[3]!
      let hbase := mkAppN (tail baseline 1) point
      let hC ← termWith [(`h,hbase)] "(by exact (norm_nonneg _).trans h)"
        (some (← mkAppM ``LE.le #[zero,C]))
      let known := #[(`n,← nativeAt rawKnown `n),(`N,← nativeAt rawKnown `N),
        (`Z₀,base),(`W,W),(`b,b),(`C,C),(`mass,mass),(`hb,hb),(`hC,hC),(`hmass,hmass),(`q,q),(`x,x)]
      let partialProof ← applyNativeThrough (ns ++ `baseline_add_whole_angular_physical_jet) `x known
      let .forallE _ hBaseType _ _ := (← nativeType partialProof).consumeMData |
        throwError "actual final physical jets: zero-safe baseline smoothness input changed"
      unless hBaseType.isAppOfArity ``ContDiffAt 11 do
        throwError "actual pointwise smoothness order changed"
      let order := hBaseType.getAppArgs[8]!
      let neighborhood ← termWith [(`hX,hX),(`hx,hx)] "(hX.mem_nhds hx)"
      let hbaseSmooth ← smoothAtUsing (part baseline 0) smoothType order x neighborhood
      let afterBase := mkApp partialProof hbaseSmooth
      let .forallE _ _hWholeType _ _ := (← nativeType afterBase).consumeMData |
        throwError "actual final physical jets: zero-safe whole smoothness input changed"
      let hwholeSmooth ← withSupport fun _ whole => do
        let smooth := app (wave ++ `Whole.corrected_on_cutoff_chart) whole
        smoothAtUsing smooth (← nativeType smooth) order x neighborhood
      let afterSmooth := mkAppN afterBase #[hwholeSmooth,hbase]
      let hwhole ← withSupport fun _ whole => do
        let sourceSmooth ← originalBodyAt (wave ++ `Whole.corrected_on_source_chart) whole
        unless sourceSmooth.isAppOf ``ContDiffOn.mono do
          throwError "actual final physical jets: original source-chart inclusion changed"
        let inCell := sourceSmooth.getAppArgs.back!
        let hxCell := mkAppN inCell #[x,mkAppN hcut #[x,hx]]
        let massProof := app (ns ++ `Whole.physical_jet_mass) (whole ++ #[q,x,hxCell,C])
        let .forallE _ boundType _ _ := (← nativeType massProof).consumeMData |
          throwError "actual final physical jets: actual atomic-integral bound changed"
        let bound ← forallBoundedTelescope boundType (some 2) fun freq _ => do
          unless freq.size == 2 do throwError "actual final physical jets: original Fourier ceiling changed"
          let inWindow := mkAppN (← nativeAt rawKnown `hVceil) freq
          let closed := app (wave ++ `Whole.shifted_parameter_in_closed_cell)
            (whole[:66].toArray ++ #[freq[0]!,inWindow])
          let membership ← Core.betaReduce (← zetaReduce (← nativeType closed))
          let shifted := app (envelope ++ `atom_sharp_spatial_jets)
            (atomic ++ #[membership.getAppArgs[4]!,closed])
          mkLambdaFVars freq (mkAppN (tail shifted 1) point)
        return mkApp massProof bound
      let proof := mkApp afterSmooth hwhole
      let resultType ← nativeType proof
      let summed := factorType.appArg!
      let combinedTarget ← mkAppM ``HAdd.hAdd #[base,summed]
      let target := resultType.replace fun e => if e == combinedTarget then some field else none
      unless (target.find? (· == field)).isSome do
        throwError "actual final physical jets: result did not retain the literal selected final field"
      let waveType := factorType.getAppArgs[0]!
      let angular := factorType.getAppArgs[1]!
      let predicate ← withLocalDeclNoLocalInstanceUpdate `angularField .default waveType fun angularField => do
        let statement := resultType.replace fun e => if e == summed then some angularField else none
        mkLambdaFVars #[angularField] statement
      let equality := mkAppN (mkConst ``congrArg
          [factorType.getAppFn.constLevels!.head!,.succ .zero])
        #[waveType,mkSort .zero,angular,summed,predicate,factorEq]
      let actual := mkAppN (mkConst ``Eq.mpr [.zero])
        #[mkApp predicate angular,mkApp predicate summed,equality,proof]
      for e in #[actual,target] do
        if e.hasMVar || e.hasLevelMVar || e.hasSorry then
          throwError "unexpected unresolved actual mass-jet proof"
      let all := params ++ point
      if mode.getNat == 0 then
        emit `selectedSourceCombinedWave_mass_statement all target true (some (mkSort .zero))
      else
        emit `selectedSourceCombinedWave_mass_jets all actual false
          (some (app (ns ++ `selectedSourceCombinedWave_mass_statement) all))


end JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
end
