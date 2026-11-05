module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate

/-!
# Apply the actual original leading and uncut response producers

The raw telescope is exactly source53. Corrected atoms add only the original
Graph42 admissions, sharing its source family and its literal four history
arguments. In particular Source53 is NOT claimed to imply the graph cap,
sector order or graph reached threshold. The existing adapter owns that map.
-/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalLocalWavesTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate
open OriginalLocalWaveGeometryTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def sources := `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.Actual
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def cells := `JanetCartan.PhysicalPrimary.LeadingCell
private def graph := `JanetCartan.PhysicalSampling.OriginalGraphResponse

private def byName (name : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let rec options (type : Expr) : Array (Option Expr) :=
    match type with
    | .forallE n _ body _ =>
      #[(known.find? (fun entry => entry.1 == n)).map Prod.snd] ++ options body
    | .mdata _ body => options body
    | _ => #[]
  mkAppOptM name (options (← getConstInfo name).type)

/-- The already admitted real field itself, including its actual χ₂. -/
private def sourceSubtype (h : Expr) : MetaM Expr := do
  let t ← inferType h
  unless t.isAppOfArity ``Membership.mem 5 do throwError "original wave: missing literal real source membership"
  mkAppM ``Subtype.mk #[t.getAppArgs[4]!,h]

private def functionOfSmooth (h : Expr) : MetaM Expr := do
  let type ← inferType h
  unless type.isAppOf `ContDiffOn do
    throwError "original local wave: expected a literal local smoothness conclusion"
  let args := type.getAppArgs
  return args[args.size-2]!

/-- Apply the retained primitive scalar theorem, not a scalar-success premise.
The positive lower CONSTANT proves nonvanishing; the actual arbitrary span
scalar is used only after the published linear-span extension. -/
elab "construct_original_local_raw_atoms" : command => liftTermElabM do
  withSourcePrefix 53 fun s => do
    let a ← sourceCurrent s
    let da := a.dataArgs
    let all := da ++ #[a.datum,a.cell]
    let cell (field : Name) := mkAppN (mkConst (cells ++ field)) all
    let Q ← store (ns ++ `Q) s (mkAppN (mkConst `JanetCartan.PhysicalPrimary.LeadingData.Q) (da.push a.datum)) true
    let T ← store (ns ++ `T) s da[4]! true
    let F ← store (ns ++ `F) s da[30]! true
    let row ← store (ns ++ `row) s (mkApp da[7]! a.cell) true
    let col ← store (ns ++ `col) s (mkApp da[8]! a.cell) true
    let Φ ← store (ns ++ `Φ) s (cell `Φ) true
    let Y ← store (ns ++ `Y) s (cell `Y) true
    let r ← store (ns ++ `scalar) s (← mkAppM ``Subtype.val #[s[49]!]) true
    let fields ← #[(`current_map_smooth,da[31]!),(`current_immersion,da[32]!),(`current_full_rank,da[33]!)].mapM fun (field,h) => do
      let t := (← inferType h).replace fun e => if e == da[30]! then some F else none
      store (ns ++ field) s h false (some t)
    let hr ← mkAppM ``Subtype.property #[s[49]!]
    let z₀ ← mkAppM ``Subtype.val #[← mkAppM ``Subtype.val #[a.cell]]
    let R := mkApp da[10]! a.cell
    let M := da[23]!
    let m := da[24]!
    let hσ := .proj ``And 0 s[24]!
    let hm ← mkAppM `le_of_lt
      #[← mkAppM `JanetCartan.PhysicalInitialization.positive_leading_scalar_lower_bound #[hσ]]
    let hgap ← mkAppM `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.scalar_budget_gap
      #[hσ,mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.StrongCurrent.Cap.fact5)
        a.fixed[:21].toArray]
    let hmM ← mkAppM `le_of_lt #[hgap]
    let hconst := mkAppN (mkConst `JanetCartan.CorrectedAtoms.lowerConstant_mem_primitiveInitialScalars)
      #[da[0]!,z₀,R,M,m,hm,hmM]
    let .forallE rname rdom _ rbi ← whnf (← inferType r)
      | throwError "original local wave: scalar is not on the original initial chart"
    let lower := mkLambda rname rbi rdom m
    let hnonzero := mkAppN (cell `scalar_nonzero)
      #[lower,component hconst 0,component hconst 1,.proj ``And 1 (.proj ``And 1 hconst)]
    let primitive := mkAppN (mkConst `JanetCartan.PrimarySourceAdmission.primitiveInitialScalars)
      #[da[0]!,z₀,R,M,m]
    let hαprimitive ← withLocalDeclD `r (← inferType r) fun rgen => do
      withLocalDeclD `hr (← mkAppM `Membership.mem #[primitive,rgen]) fun hgen => do
        let h := mkAppN (cell `scalar_regular)
          #[rgen,component hgen 0,component hgen 1,.proj ``And 1 (.proj ``And 1 hgen)]
        mkLambdaFVars #[rgen,hgen] h
    let hα ← mkAppM `JanetCartan.PrimarySourceAdmission.contDiffOn_scalarAmplitude_of_mem_initialScalarSpan
      #[T,Q,F,row,col,Φ,Y,hαprimitive,hr]
    let geometry (field : Name) := mkAppN (mkConst (geo ++ field)) s
    let hΩ := geometry `current_open
    let hspace := geometry `current_space
    let hphase := geometry `current_phase
    let hα ← store (ns ++ `scalar_smooth) s hα
    let hnonzero ← store (ns ++ `nullvectors_nonzero) s hnonzero
    let hraw ← mkAppM `JanetCartan.RawPrimary.contDiffOn_fullPrimaryAtom_of_leading_outputs
      #[T,Q,F,row,col,Φ,Y,r,s[47]!,hΩ,hspace,hphase,fields[0]!,fields[1]!,fields[2]!,hα,hnonzero]
    let hraw ← store (ns ++ `joint_raw_smooth) s hraw
    let joint ← store (ns ++ `raw) s (← functionOfSmooth hraw) true
    let V := geometry `parameter_window
    let .app _ parameterType ← inferType V
      | throwError "original local wave: missing original parameter window type"
    withLocalDeclD `c parameterType fun c => do
      withLocalDeclD `hc (← mkAppM `Membership.mem #[V,c]) fun hc => do
        let params := s ++ #[c,hc]
        let hproduct := geometry `source_product_in_current
        let onSource ← mkAppM (geo ++ `contDiffOn_slice) #[hraw,hproduct,hc]
        let W ← functionOfSmooth onSource
        discard <| store (ns ++ `raw_on_source_chart) params onSource
        let hcut := mkAppN (mkConst (geo ++ `smoothing_chart_in_source_chart)) s[:23].toArray
        discard <| store (ns ++ `raw_on_cutoff_chart) params
          (← mkAppM `ContDiffOn.mono #[onSource,hcut])
        let mask (field : Name) := mkAppN (mkConst (masks ++ field)) s[:23].toArray
        let hχ := mask `χ₂_smooth
        let χ := (← inferType hχ).appArg!
        let hs ← mkAppM (geo ++ `source_slice_mem) #[hproduct,mask `χ₂_support_chart,hc]
        let z ← mkAppM ``Prod.fst #[c]
        let ξ ← mkAppM ``Prod.snd #[c]
        let admitted ← mkAppM `JanetCartan.PrimarySourceAdmission.fullPrimaryAtom_source_mem
          #[T,Q,F,row,col,Φ,Y,r,hΩ,hspace,da[31]!,s[47]!,hraw,z,ξ,χ,hχ,mask `χ₂_compact,hs]
        discard <| store (ns ++ `source_quadratures) params admitted
        discard <| store (ns ++ `source) params
          (← mkAppM `JanetCartan.CorrectedAtoms.complexAtomicSource #[F,χ,W]) true
        discard <| store (ns ++ `source_chart_in_current_space) params
          (← mkAppM (ns ++ `slice_in_space) #[hproduct,hspace,hc])
        let literal ← mkAppM `JanetCartan.RawPrimary.fullPrimaryAtom
          #[T,Q,F,row,col,Φ,Y,s[47]!,r,z]
        let .forallE xname xdomain _ xbi ← whnf (← inferType W)
          | throwError "original local wave: raw slice lost its spatial argument"
        let native ← withLocalDecl xname xbi xdomain fun x => do
          let p ← mkAppM ``Prod.mk #[x,ξ]
          mkLambdaFVars #[x] (mkApp literal p)
        unless ← isDefEq W native do
          throwError "original local wave: actual raw slice is not SAME native fullPrimaryAtom"
        discard <| store (ns ++ `same_native_raw) params (← mkEqRefl W)
          false (some (← mkEq W native))
        let _ := joint
    let outer := geometry `outer_weight_parameter
    forallBoundedTelescope (← inferType outer) (some 5) fun sample _ => do
      unless sample.size == 5 do throwError "original raw wave: changed outer weight/node ABI"
      let admitted := mkAppN outer sample
      let membership ← Core.betaReduce (← zetaReduce (← inferType admitted))
      unless membership.isAppOfArity ``Membership.mem 5 do
        throwError "original raw wave: outer support did not produce original parameter membership"
      let c := membership.getAppArgs[4]!
      let atPoint := s ++ #[c,admitted]
      let hraw := mkAppN (mkConst (ns ++ `raw_on_cutoff_chart)) atPoint
      discard <| store (ns ++ `outer_active_raw) (s ++ sample) (← functionOfSmooth hraw) true
      discard <| store (ns ++ `outer_active_raw_smooth) (s ++ sample) hraw
      discard <| store (ns ++ `outer_active_source_quadratures) (s ++ sample)
        (mkAppN (mkConst (ns ++ `source_quadratures)) atPoint)
  logInfo "actual source53 raw atoms: SAME selected current/flow/footpoint, positive LOWER CONSTANT for nullvectors, linear-span scalar smoothness, BOTH actual chi2 source quadratures; active OUTER nodes use actual74 product/parameter support, no inner-b baseline zero claim or global Schwartz premise"

/-- The same single capped callback, with the *literal source* binder type.
This is definitional naming only: no source cap, buffer, or function is changed. -/
elab "name_original_local_source_callback" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (graph ++ `B)).type (some 42) fun x _ => do
    let g := (← inferType x[37]!).getAppArgs[2]!.getAppArgs
    let cb := g[20]!
    let original := mkAppN (mkConst `JanetCartan.PhysicalSampling.samplingCappedExtra)
      #[x[0]!,x[1]!,x[2]!,x[21]!]
    unless cb == original do throwError "original source/graph: changed literal capped callback"
    let source20 := mkAppN (mkConst (sources ++ `full_source_profiles)) g[:20].toArray
    let d := (← whnf (← inferType source20)).bindingDomain!
    discard <| store (ns ++ `source_extra_on_graph) x[:22].toArray cb true (some d)

/-- Merge source53 with task26's exact graph42, without duplicating its weak38
adapter. Only already-existing Source53 admissions remain as added binders.
All four history entries and the actual source scale/family are shared. -/
private partial def sourceOnGraph (x g : Array Expr)
    (finish : Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let cb := mkAppN (mkConst (ns ++ `source_extra_on_graph)) x[:22].toArray
  let g := g.set! 20 cb
  let known : Array (Nat × Expr) :=
    (g[:23].toArray.mapIdx fun i v => (i,v)) ++
      #[(23,x[27]!),(26,x[29]!),(27,x[30]!),(28,x[31]!),(29,x[32]!),
        (31,x[35]!),(39,x[36]!),(41,x[38]!),(42,x[39]!),(43,x[40]!),(44,x[41]!)]
  let rec go (type : Expr) (sourceArgs extra : Array Expr) : MetaM Unit := do
    if sourceArgs.size == 53 then
      finish sourceArgs extra
    else
      let .forallE name dom body bi ← whnf type
        | throwError "original corrected wave: source53 ended before its exact dynamic tail"
      if let some (_,value) := known.find? (fun entry => entry.1 == sourceArgs.size) then
        if sourceArgs.size == 20 then
          unless (← inferType value) == dom do throwError "original corrected wave: changed source callback domain"
        else
          unless ← isDefEq (← inferType value) dom do
            throwError "original corrected wave: shared source/history input mismatch {name}"
        go (body.instantiate1 value) (sourceArgs.push value) extra
      else
        let d ← sourceInputDomain sourceArgs dom
        withLocalDecl name bi d fun value =>
          go (body.instantiate1 value) (sourceArgs.push value) (extra.push value)
  go (← getConstInfo (sources ++ `full_source_profiles)).type #[] #[]

/-- Instantiate only a fixed native geometry lemma, without re-inferring a
large selected cell from its membership proof. The stored theorem still checks
all arguments with the kernel; no cast or additional hypothesis is introduced. -/
private def nativeGeometry (name : Name) (values : Array (Name × Expr)) : MetaM Expr := do
  let mut type := (← getConstInfo name).type
  let mut args := #[]
  while type.isForall do
    let key := type.bindingName!.eraseMacroScopes
    let some (_,value) := values.find? (fun p => p.1 == key)
      | throwError "original shifted geometry: missing explicit field {key} of {name}"
    args := args.push value
    if key == `hshift then return mkAppN (mkConst name) args
    type := type.bindingBody!.instantiate1 value
  throwError "original shifted geometry: missing final displacement bound in {name}"

/-- Whole inputs use the literal selected detector and its proved continuous
unit bound. Only a numerical original-rate margin and membership in the SAME
inner carrier support are added. All shifted-domain and source smoothness
premises are actually derived here; the response acts AFTER synthesis. -/
private def constructWhole (mode : Nat) (x s family : Array Expr) : MetaM Unit := do
  let keep (stage : Nat) (field : Name) (params : Array Expr) (proof : Expr) (isDef := false) : MetaM Expr := do
    if mode == stage then store (ns ++ field) params proof isDef
    else pure (mkAppN (mkConst (ns ++ field)) params)
  let a ← sourceCurrent s
  let n := a.dataArgs[0]!
  let transverse := mkApp2 (mkConst ``Nat.sub) n (mkNatLit 1)
  -- The sampler and its WeightBridge use this exact original22 spine. In
  -- particular do not reconstruct its curvature/detector data by unfolding
  -- the equivalent source53 callback, whose native binder spelling differs.
  let sampleType := (← getConstInfo `JanetCartan.PhysicalSampling.OriginalWeights.Index).type
  let nsample := (sampleType.bindingBody!.instantiate1 x[0]!).bindingDomain!.appArg!
  let merged := mkAppN (mkConst `JanetCartan.PhysicalSampling.samplingCappedExtra)
    #[x[0]!,x[1]!,x[2]!,x[21]!]
  let cap := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[nsample,x[1]!,merged]
  let native := (#[nsample,x[1]!] ++ x[3:22].toArray).set! 20 cap
  let iSample := mkAppN (mkConst (ns ++ `original_sample_row)) family
  let selected (field : Name) := mkAppN
    (mkConst (`JanetCartan.PhysicalSeed.SelectedBoundary ++ field)) (native.push iSample)
  let raw (field : Name) := mkAppN (mkConst (ns ++ field)) s
  let geometry (field : Name) := mkAppN (mkConst (geo ++ field)) s
  let mask (field : Name) := mkAppN (mkConst (masks ++ field)) s[:23].toArray
  let original22 := x[:22].toArray
  let q ← mkAppM ``Subtype.val #[← mkAppM ``Sigma.fst #[iSample]]
  let l ← mkAppM ``Sigma.snd #[iSample]
  let hroot := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalAdmission.root_mem)
    (original22 ++ #[q,l])
  let actualCell := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.cell) (native ++ #[q,l])
  let radius := mkAppN (mkConst `JanetCartan.PhysicalSampling.originalSamplingRadius)
    #[nsample,s[1]!,q,l,actualCell]
  let hρ ← mkAppM ``Subtype.property #[radius]
  let ρ ← mkAppM ``Subtype.val #[radius]
  let working := mkAppN (mkConst `JanetCartan.PhysicalSampling.originalSamplingRadius_spec)
    #[nsample,s[1]!,q,l,actualCell,hroot]
  let hworking ← keep 0 `Whole.working_radius_in_cell family (component working 0)
  let cutoff := mkAppN
    (mkConst `JanetCartan.PhysicalSampling.OriginalAdmission.cutoff_on_actual_selected_row)
    (original22.push iSample)
  let carrierGraph := component cutoff 3
  let caps := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalMargins.ε_caps)
    (original22.push iSample)
  let hεPhase := Nat.repeat (fun p => Expr.proj ``And 1 p) 4 caps
  let phaseType ← inferType hεPhase
  let phaseRadius := phaseType.appArg!
  unless phaseRadius.isAppOf `JanetCartan.Sampling.MeasuredAmplitude.measuredPhaseRadius do
    throwError "original whole wave: changed SAME original phase-rate margin"
  let phaseMinimum ← bodyAt `JanetCartan.Sampling.MeasuredAmplitude.measuredPhaseRadius
    phaseRadius.getAppArgs
  unless phaseMinimum.isAppOfArity ``Min.min 4 do
    throwError "original whole wave: measured phase radius lost original eighth margin"
  let pm := phaseMinimum.getAppArgs
  let hε8 ← mkAppM `le_trans #[hεPhase,← mkAppM `min_le_right #[pm[2]!,pm[3]!]]
  let ε := (← inferType hε8).getAppArgs[2]!
  let hτ ← mkAppM `le_of_lt #[s[48]!]
  let hη := selected `hηb
  let hr := selected `hr'
  let ηtype ← Core.betaReduce (← zetaReduce (← inferType hη))
  unless ηtype.isAppOfArity ``Ne 3 do throwError "original whole wave: missing nonzero original direction"
  let detArgs := #[nsample,ηtype.getAppArgs[1]!, (← inferType hr).appArg!,hη,hr]
  let hdetector := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.OriginalPrefix.sampling_detector_continuous) detArgs
  let hd ← mkAppM `Continuous.measurable #[hdetector]
  let hb := mkAppN (mkConst `JanetCartan.Sampling.norm_originalConicDetectorMask_le_one) detArgs
  let detector := (← inferType hdetector).appArg!
  let bridge (field : Name) := mkAppN
    (mkConst (`JanetCartan.PhysicalMean.OriginalWeightBridge.Original ++ field))
    (original22.push iSample)
  let root := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalOuterWeights.root)
    (original22.push iSample)
  let innerSupport ← if mode == 0 then do
      let h ← mkAppM (ns ++ `inner_factor_mem_carrier) #[root,selected `ha',bridge `factor_sq_eq_inner]
      store (ns ++ `Whole.inner_factor_support) family h
    else pure (mkAppN (mkConst (ns ++ `Whole.inner_factor_support)) family)
  discard <| keep 0 `Whole.inner_factor family (bridge `factor) true
  if mode == 0 then return
  let hM ← mkAppOptM `zero_le_one #[some (mkConst `Real),none,none,none,none]
  let one := (← inferType hM).appArg!
  let B := mkAppN (mkConst (graph ++ `B)) x
  let F := raw `F
  let hχ := mask `χ₂_smooth
  let χ := (← inferType hχ).appArg!
  let base := #[raw `T,raw `Q,F,raw `row,raw `col,raw `Φ,raw `Y,raw `scalar,
    geometry `current_open,geometry `current_space,geometry `current_phase,
    raw `current_map_smooth,raw `current_immersion,raw `current_full_rank,
    raw `scalar_smooth,raw `nullvectors_nonzero]
  withLocalDeclD `Λ (mkConst `Real) fun Λ => do
    withLocalDeclD `hΛ (← mkAppM ``LE.le #[one,Λ]) fun hΛ => do
      let band := mkAppN (mkConst (geo ++ `original_finite_band_open_buffer))
        #[transverse,Λ,s[47]!,ε,ρ,hΛ,hτ,hε8]
      forallBoundedTelescope (← inferType band) (some 1) fun numerical _ => do
        unless numerical.size == 1 do throwError "original whole wave: expected original finite-band rate bound"
        let rateParams := family ++ #[Λ,hΛ] ++ numerical
        let buffer := mkAppN band numerical
        let hceil := component buffer 0
        let hshiftNorm := .proj ``And 1 buffer
        let V := (← inferType hceil).appArg!
        unless V.isAppOfArity `Metric.ball 4 do throwError "original whole wave: changed native frequency ball"
        let hV ← mkAppOptM `Metric.isOpen_ball (V.getAppArgs.map some)
        let hcell := mkAppN (mkConst (masks ++ `chart_in_cell)) (s[:23].toArray ++ #[a.patch,a.cell])
        let cellX := (← inferType hcell).appArg!
        unless cellX.isAppOfArity `Metric.ball 4 do throwError "original whole wave: changed native spatial cell"
        let hcellOpen ← mkAppOptM `Metric.isOpen_ball (cellX.getAppArgs.map some)
        let hself ← forallBoundedTelescope (← mkAppM `Set.Subset #[cellX,cellX]) (some 2) fun y _ => do
          mkLambdaFVars y y[1]!
        let hcut := mkAppN (mkConst (geo ++ `smoothing_chart_in_source_chart)) s[:23].toArray
        let hceil ← keep 1 `Whole.ceiling_buffer rateParams hceil
        forallBoundedTelescope (← inferType carrierGraph) (some 2) fun carrier _ => do
          if mode != 1 && mode != 2 && mode != 5 then return
          unless carrier.size == 2 do throwError "original whole wave: missing actual inner carrier support"
          let hgraph := mkAppN carrierGraph carrier
          let graphMembership ← Core.betaReduce (← zetaReduce (← inferType hgraph))
          unless graphMembership.isAppOfArity ``Membership.mem 5 do
            throwError "original whole wave: missing native quarter-radius graph membership"
          let z ← mkAppM ``Prod.fst #[graphMembership.getAppArgs[4]!]
          let wholeParams := rateParams ++ carrier
          let tt := (← inferType (raw `T)).getAppArgs
          unless tt.size == 4 do throwError "original shifted geometry: changed current T type"
          let parentType ← Core.betaReduce (← zetaReduce (← inferType hworking))
          let currentCell := geometry `current_cell
          let currentType ← Core.betaReduce (← zetaReduce (← inferType currentCell))
          let pa := parentType.getAppArgs
          let ca := currentType.getAppArgs
          unless pa.size ≥ 2 && ca.size ≥ 2 &&
              pa[pa.size-2]!.isAppOfArity `Metric.closedBall 4 && ca[ca.size-2]!.isAppOfArity `Metric.closedBall 4 do
            throwError "original shifted geometry: lost literal ball inclusions {parentType.getAppFn}/{currentType.getAppFn}"
          let getCenter (ball : Expr) : MetaM Expr := do
            unless ball.getAppNumArgs == 4 do throwError "original shifted geometry: expected native ball"
            let center := ball.getAppArgs[2]!
            unless center.isAppOfArity ``Prod.mk 4 && center.getAppArgs[3]!.isAppOfArity ``Prod.mk 4 do
              throwError "original shifted geometry: expected physical/carrier/parameter center"
            return center.getAppArgs[3]!.getAppArgs[2]!
          let zRoot ← getCenter pa[pa.size-2]!
          let zCell ← getCenter ca[ca.size-2]!
          let Ω := ca.back!
          let σ := cellX.getAppArgs[3]!
          let values := #[(`d,s[0]!),(`P,tt[1]!),(`U,tt[2]!),(`hU,tt[3]!),(`T,raw `T),
            (`zRoot,zRoot),(`zCell,zCell),(`z,z),(`ρ,ρ),(`σ,σ),(`hρ,hρ),(`Ω,Ω),
            (`hparent,hworking),(`hcell,currentCell),(`hz,hgraph),(`V,V),(`τ,s[47]!),(`hshift,hshiftNorm)]
          let entire ← if mode == 1 then do
              store (ns ++ `Whole.shifted_selected_cell) wholeParams (← nativeGeometry (geo ++ `shifted_source_product)
                (values ++ #[(`X,cellX),(`hX,hself)]))
            else pure (mkAppN (mkConst (ns ++ `Whole.shifted_selected_cell)) wholeParams)
          let _shifted ← if mode == 1 then do
              let xa := (← inferType hcell).getAppArgs
              let X := xa[xa.size-2]!
              let goal ← inferType (← nativeGeometry (geo ++ `shifted_source_product)
                (values ++ #[(`X,X),(`hX,hcell)]))
              let proof ← forallBoundedTelescope goal (some 2) fun p _ => do
                let first ← mkAppM ``Prod.fst #[p[0]!]
                let hx := mkAppN hcell #[first,.proj ``And 0 p[1]!]
                let hp ← mkAppM ``And.intro #[hx,.proj ``And 1 p[1]!]
                mkLambdaFVars p (mkAppN entire #[p[0]!,hp])
              store (ns ++ `Whole.shifted_domain) wholeParams proof false (some goal)
            else pure (mkAppN (mkConst (ns ++ `Whole.shifted_domain)) wholeParams)
          if mode == 1 then return
          if mode == 5 then
            let hpar ← nativeGeometry (geo ++ `shifted_parameter_in_cell) values
            discard <| store (ns ++ `Whole.shifted_parameter_in_cell) wholeParams hpar
            let hclosed ← forallBoundedTelescope (← inferType hpar) (some 2) fun η _ => do
              let hp := mkAppN hpar η
              let mem ← Core.betaReduce (← zetaReduce (← inferType hp))
              unless mem.isAppOfArity ``Membership.mem 5 do
                throwError "shifted parameter: missing native ball membership"
              let ball := mem.getAppArgs[3]!
              let cl ← mkAppOptM `Metric.ball_subset_closedBall (ball.getAppArgs.map some)
              let point := mem.getAppArgs[4]!
              mkLambdaFVars η (mkAppN cl #[point,hp])
            discard <| store (ns ++ `Whole.shifted_parameter_in_closed_cell) wholeParams hclosed
            let θspec := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalSourceProfiles.parameterCutoff_spec)
              #[n,s[1]!,a.patch,a.cell]
            let germ : Expr := .proj ``And 1 (.proj ``And 1 (.proj ``And 1 θspec))
            let hgerm ← forallBoundedTelescope (← inferType hpar) (some 2) fun η _ => do
              let hp := mkAppN hpar η
              let mem ← Core.betaReduce (← zetaReduce (← inferType hp))
              unless mem.isAppOfArity ``Membership.mem 5 do throwError "shifted parameter not in original small cell"
              let ball := mem.getAppArgs[3]!
              unless ball.isAppOfArity `Metric.ball 4 do throwError "shifted parameter cell is not the original ball"
              let cl ← mkAppOptM `Metric.ball_subset_closedBall (ball.getAppArgs.map some)
              let point := mem.getAppArgs[4]!
              mkLambdaFVars η (mkAppN germ #[point,mkAppN cl #[point,hp]])
            discard <| store (ns ++ `Whole.shifted_θ_germ) wholeParams hgerm
            return
          let c ← forallBoundedTelescope (← inferType entire) (some 2) fun p target => do
            let mem ← Core.betaReduce (← zetaReduce target)
            unless mem.isAppOfArity ``Membership.mem 5 do throwError "original whole source: missing shifted membership"
            let point := mem.getAppArgs[4]!
            unless point.isAppOfArity ``Prod.mk 4 do throwError "original whole source: missing physical/carrier pair"
            let pt := (← inferType p[0]!).getAppArgs
            withLocalDeclD `η pt[1]! fun η => do
              let pair ← mkAppM ``Prod.mk #[cellX.getAppArgs[2]!,η]
              let body := point.getAppArgs[3]!.replace fun e => if e == p[0]! then some pair else none
              mkLambdaFVars #[η] body
          let hspace := mkAppN (mkConst (ns ++ `shifted_slice_in_space))
            #[n,mkApp (mkConst `JanetCartan.RawInputPartition.cutoffCount) Λ,cellX,tt[2]!,V,Ω,c,
              entire,geometry `current_space,hceil]
          let hspace ← store (ns ++ `Whole.selected_cell_in_current_space) wholeParams hspace
          let hFcell ← store (ns ++ `Whole.current_map_on_selected_cell) wholeParams
            (← mkAppM `ContDiffOn.mono #[raw `current_map_smooth,hspace])
          let hsrc := mask `χ₂_support_chart
          let hsrcCell ← forallBoundedTelescope (← inferType hsrc) (some 2) fun y _ => do
            mkLambdaFVars y (mkAppN hcell #[y[0]!,mkAppN hsrc y])
          let J := mkApp (mkConst `JanetCartan.RawInputPartition.cutoffCount) Λ
          let input := mkAppN (mkConst `JanetCartan.RawInputPartition.WideInput) #[n,J]
          withLocalDeclD `v input fun v => do
            let all := wholeParams.push v
            let bigArgs := base ++ #[s[47]!,z,entire,hcellOpen,hV,hceil,hd,hM,hb]
            let hraw ← store (ns ++ `Whole.raw_on_selected_cell) all
              (← mkAppM `JanetCartan.RawPrimary.contDiffOn_fullPrimaryWave (bigArgs.push v))
            let W ← functionOfSmooth hraw
            let admitted ← mkAppM `JanetCartan.PrimarySourceAdmission.cutoff_strain_quadratures_mem
              #[hχ,mask `χ₂_compact,hcellOpen,hFcell,hraw,hsrcCell]
            let admitted ← store (ns ++ `Whole.source_quadratures) all admitted
            let src ← mkAppM `JanetCartan.CorrectedAtoms.complexAtomicSource #[F,χ,W]
            let reSource ← sourceSubtype (component admitted 0)
            let imSource ← sourceSubtype (.proj ``And 1 admitted)
            let smooth := mkAppN (mkConst (graph ++ `smoothOn)) x
            let hre ← mkAppM `ContDiffOn.mono #[mkApp smooth reSource,hspace]
            let him ← mkAppM `ContDiffOn.mono #[mkApp smooth imSource,hspace]
            let hresponse ← store (ns ++ `Whole.response_on_selected_cell) all
              (← mkAppM (ns ++ `contDiffOn_complexifyResponse) #[B,src,hre,him])
            let hcorrected ← mkAppM `ContDiffOn.sub #[hraw,hresponse]
            let corrected ← functionOfSmooth hcorrected
            let native ← mkAppM `JanetCartan.CanonicalAtomRealization.wholeSourceCorrectedWave
              #[raw `T,raw `Q,F,raw `row,raw `col,raw `Φ,raw `Y,raw `scalar,χ,B,s[47]!,z,detector,v]
            unless ← isDefEq corrected native do
              throwError "original whole wave: changed wholeSourceCorrectedWave or response after synthesis"
            discard <| store (ns ++ `Whole.raw) all W true
            discard <| store (ns ++ `Whole.source) all src true
            discard <| store (ns ++ `Whole.corrected) all native true
            let hcorrected ← store (ns ++ `Whole.corrected_on_selected_cell) all hcorrected
            let hraw ← store (ns ++ `Whole.raw_on_source_chart) all (← mkAppM `ContDiffOn.mono #[hraw,hcell])
            let hcorrected ← store (ns ++ `Whole.corrected_on_source_chart) all
              (← mkAppM `ContDiffOn.mono #[hcorrected,hcell])
            discard <| store (ns ++ `Whole.raw_on_cutoff_chart) all
              (← mkAppM `ContDiffOn.mono #[hraw,hcut])
            discard <| store (ns ++ `Whole.corrected_on_cutoff_chart) all
              (← mkAppM `ContDiffOn.mono #[hcorrected,hcut])
            discard <| store (ns ++ `Whole.same_native_wave) all (← mkEqRefl corrected)
              false (some (← mkEq corrected native))
        -- This is a proof on the ACTUAL native mask, not a reusable weighted API:
        -- b=0 only kills b*whole, while the separate positive baseline is untouched.
        withLocalDeclD `node (mkConst `JanetCartan.SeparatedSampling.Point) fun node => do
          if mode != 3 then return
          let b := mkApp (bridge `factor) node
          let innerAt := mkApp innerSupport node
          let .forallE _ nonzeroType membership _ ← whnf (← inferType innerAt)
            | throwError "original angular wave: missing actual factor support implication"
          unless !membership.hasLooseBVars && membership.isAppOfArity ``Membership.mem 5 do
            throwError "original angular wave: changed SAME carrier node membership"
          let p := membership.getAppArgs[4]!
          let z := mkApp (← mkAppM `DFunLike.coe
            #[mkConst `JanetCartan.ContinuumRow.CanonicalCarrier.parameter]) p
          let highPass := detector.appArg!
          let hi ← withLocalDeclD `η (mkApp (mkConst `JanetCartan.Euclidean) transverse) fun η => do
            mkLambdaFVars #[η] (mkApp (mkConst `Complex.ofReal) (mkApp highPass η))
          let J := mkApp (mkConst `JanetCartan.RawInputPartition.cutoffCount) Λ
          let input := mkAppN (mkConst `JanetCartan.RawInputPartition.WideInput) #[n,J]
          withLocalDeclD `v input fun v => do
            let all := rateParams ++ #[node,v]
            let physical := #[raw `T,raw `Q,F,raw `row,raw `col,raw `Φ,raw `Y,raw `scalar,s[47]!]
            let bareRaw ← mkAppM `JanetCartan.RawPrimary.fullPrimaryWave
              #[raw `T,raw `Q,F,raw `row,raw `col,raw `Φ,raw `Y,s[47]!,raw `scalar,z,detector,v]
            let bareCorrected ← mkAppM `JanetCartan.CanonicalAtomRealization.wholeSourceCorrectedWave
              #[raw `T,raw `Q,F,raw `row,raw `col,raw `Φ,raw `Y,raw `scalar,χ,B,s[47]!,z,detector,v]
            let rawFactor ← withLocalDeclD `y (mkApp (mkConst `JanetCartan.Euclidean) n) fun y => do
              mkLambdaFVars #[y] (← mkAppM
                `JanetCartan.PhysicalMean.OriginalWeightBridge.originalAngular_fullPrimaryWave
                (physical ++ #[root,selected `ha',selected `hηb,selected `hr',p,hi,v,y]))
            let rawFactor ← mkAppM ``funext #[rawFactor]
            let angularEq ← mkAppM
              `JanetCartan.PhysicalMean.OriginalWeightBridge.originalAngular_correctedWave
              (physical ++ #[χ,B,root,selected `ha',selected `hηb,selected `hr',p,hi,hd,hb,v])
            let inputEq ← mkAppM
              `JanetCartan.PhysicalMean.OriginalWeightBridge.wholeSourceCorrectedWave_carrierFactor
              (physical ++ #[z,χ,B,b,hd,hb,v])
            let smulEq ← mkAppM
              `JanetCartan.PhysicalMean.OriginalWeightBridge.wholeSourceCorrectedWave_carrierFactor_smul
              (physical ++ #[z,χ,B,b,detector,v])
            let correctedFactor ← mkAppM ``Eq.trans
              #[angularEq,← mkAppM ``Eq.trans #[← mkAppM ``Eq.symm #[inputEq],smulEq]]
            for (label,W,identity,localSmooth) in
                #[(`raw,bareRaw,rawFactor,`raw_on_selected_cell),
                  (`corrected,bareCorrected,correctedFactor,`corrected_on_selected_cell)] do
              unless ← isDefEq (← inferType identity).appArg! (← mkAppM `HSMul.hSMul #[b,W]) do
                throwError "original full-angular identity changed its native whole wave"
              let onNonzero ← withLocalDeclD `hb nonzeroType fun hbNode => do
                let hp := mkApp innerAt hbNode
                mkLambdaFVars #[hbNode] (mkAppN (mkConst (ns ++ `Whole ++ localSmooth))
                  (rateParams ++ #[p,hp,v]))
              let hfull ← mkAppM (ns ++ `contDiffOn_full_angular_of_native_factor) #[identity,onNonzero]
              let allCell ← store (ns ++ `Whole.full_angular_smooth_on_selected_cell ++ label) all hfull
              let sourceChart ← mkAppM `ContDiffOn.mono #[allCell,hcell]
              let full := (← inferType identity).getAppArgs[1]!
              discard <| store (ns ++ `Whole.full_angular ++ label) all full true
              discard <| store (ns ++ `Whole.full_angular_smooth ++ label) all
                (← mkAppM `ContDiffOn.mono #[sourceChart,hcut])
              discard <| store (ns ++ `Whole.full_angular_factor ++ label) all identity
        let outer := geometry `outer_weight_parameter
        forallBoundedTelescope (← inferType outer) (some 5) fun sample _ => do
          if mode != 4 then return
          unless sample.size == 5 do throwError "original combined wave: changed actual outer node ABI"
          let admitted := mkAppN outer sample
          let membership ← Core.betaReduce (← zetaReduce (← inferType admitted))
          unless membership.isAppOfArity ``Membership.mem 5 do
            throwError "original combined wave: lost actual outer baseline parameter geometry"
          let c := membership.getAppArgs[4]!
          let baseline := mkAppN (mkConst (ns ++ `Corrected.unrestricted_atom)) (family ++ #[c])
          let hbaseline := mkAppN (mkConst (ns ++ `Corrected.on_cutoff_chart))
            (family ++ #[c,admitted])
          let node := mkAppN (mkConst `JanetCartan.SeparatedSampling.node)
            #[sample[1]!,sample[2]!,sample[3]!]
          let J := mkApp (mkConst `JanetCartan.RawInputPartition.cutoffCount) Λ
          let input := mkAppN (mkConst `JanetCartan.RawInputPartition.WideInput) #[n,J]
          withLocalDeclD `v input fun v => do
            let all := rateParams ++ sample ++ #[v]
            let angular := mkAppN (mkConst (ns ++ `Whole.full_angular.corrected))
              (rateParams ++ #[node,v])
            let hangular := mkAppN (mkConst (ns ++ `Whole.full_angular_smooth.corrected))
              (rateParams ++ #[node,v])
            let combined ← mkAppM `HAdd.hAdd #[baseline,angular]
            let hsmooth ← mkAppM `ContDiffOn.add #[hbaseline,hangular]
            unless ← isDefEq (← functionOfSmooth hsmooth) combined do
              throwError "original combined wave: changed unscaled zero atom plus fullangular whole wave"
            -- The FIELD has no nonzero-weight premise; only its local proof does.
            -- The store guard rejects any accidental occurrence of sample[4].
            discard <| store (ns ++ `Combined.field) (rateParams ++ sample[:4].toArray ++ #[v]) combined true
            discard <| store (ns ++ `Combined.active_smooth) all hsmooth

/-- The three costly graph-admission binder types, never additional inputs.
The native tolerance domain at position 26 alone costs 329,786 heartbeats for
one kernel check; it must not be expanded in every corrected-wave getter. -/
private def graphInputName : Nat → Option Name
  | 26 => some `graphToleranceAdmission
  | 28 => some `graphScaleAdmission
  | 37 => some `graphReached
  | _ => none

/-- Open the unchanged measured graph42 with its exact original admission types
shared by definition. This also avoids recomputing the native margin. -/
partial def withGraphPrefix (limit : Nat) (finish : Array Expr → MetaM Unit) : MetaM Unit := do
  let rec go (type : Expr) (xs : Array Expr) : MetaM Unit := do
    if xs.size == limit then finish xs
    else
      let .forallE n d b bi ← whnf type | throwError "original graph telescope ended at {xs.size}"
      let d ← match graphInputName xs.size with
        | none => pure d
        | some key => do
          let key := `JanetCartan.PhysicalPrimary.OriginalLocalWaveInputs ++ key
          if (← getEnv).contains key then pure (mkAppN (mkConst key) xs)
          else store key xs d true
      withLocalDecl n bi d fun v => go (b.instantiate1 v) (xs.push v)
  go (← getConstInfo (graph ++ `B)).type #[]

elab "abbreviate_original_local_graph_inputs_through " k:num : command => liftTermElabM do
  withGraphPrefix (k.getNat+1) fun _ => pure ()

/-- Join the two original telescopes, with the exact graph34 and its history. -/
private def withGraphSource (k : Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  withGraphPrefix 42 fun x => do
    let hT ← inferType x[37]!
    let key := `JanetCartan.PhysicalPrimary.OriginalLocalWaveInputs.graphReached
    unless hT.isAppOfArity key 37 do throwError "original corrected wave: changed graph37 domain"
    let reached := (← getConstInfo key).value!.beta hT.getAppArgs
    unless reached.isAppOfArity ``LE.le 4 do
      throwError "original corrected wave: missing graph reached threshold"
    let S := reached.getAppArgs[2]!
    unless S.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalRegular.Graph.S 34 do
      throwError "original corrected wave: graph34 spine changed"
    let g := S.getAppArgs
    sourceOnGraph x g fun s extra => k x s (x ++ extra)

/-- Type the literal original source row once at the original sampler's index.
Its value is the old row itself, not another selection or label. -/
elab "name_original_local_sample_row" : command => liftTermElabM do
  withGraphSource fun x s family => do
    let I := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalWeights.Index) x[:22].toArray
    discard <| store (ns ++ `original_sample_row) family s[34]! true (some I)

/-- Correct the admitted actual atom by the SAME frozen full response. The only
new proof is local complexification of its TWO existing real smooth outputs. -/
elab "construct_original_local_corrected_atoms" : command => liftTermElabM do
  withGraphSource fun x s family => do
      let raw (field : Name) := mkAppN (mkConst (ns ++ field)) s
      let B := mkAppN (mkConst (graph ++ `B)) x
      let F := raw `F
      let same := mkAppN (mkConst (graph ++ `same_finite_map)) x
      let sameType ← inferType same
      unless sameType.isAppOfArity ``Eq 3 && (← isDefEq sameType.appArg! F) do
        throwError "original corrected wave: response is not on SAME literal finiteMap"
      discard <| store (ns ++ `Corrected.B) family B true
      discard <| store (ns ++ `Corrected.same_finite_map) family same
      let onSource := raw `raw_on_source_chart
      forallBoundedTelescope (← inferType onSource) (some 1) fun parameter _ => do
        unless parameter.size == 1 do throwError "original corrected wave: missing unrestricted native parameter"
        let hχ := mkAppN (mkConst (masks ++ `χ₂_smooth)) s[:23].toArray
        let χ := (← inferType hχ).appArg!
        let native ← mkAppM `JanetCartan.CorrectedAtoms.fullCorrectedPrimaryAtom
          #[raw `T,raw `Q,F,raw `row,raw `col,raw `Φ,raw `Y,χ,B,s[47]!,raw `scalar,parameter[0]!]
        discard <| store (ns ++ `Corrected.unrestricted_atom) (family ++ parameter) native true
      forallBoundedTelescope (← inferType onSource) (some 2) fun parameter _ => do
        unless parameter.size == 2 do throwError "original corrected wave: expected parameter and cell admission"
        let all := family ++ parameter
        let hraw := mkAppN onSource parameter
        let W ← functionOfSmooth hraw
        let admitted := mkAppN (raw `source_quadratures) parameter
        let src := mkAppN (raw `source) parameter
        let hre := component admitted 0
        let him := .proj ``And 1 admitted
        let reSource ← sourceSubtype hre
        let imSource ← sourceSubtype him
        let smooth := mkAppN (mkConst (graph ++ `smoothOn)) x
        let hspace := mkAppN (raw `source_chart_in_current_space) parameter
        let hre ← mkAppM `ContDiffOn.mono #[mkApp smooth reSource,hspace]
        let him ← mkAppM `ContDiffOn.mono #[mkApp smooth imSource,hspace]
        let hχ := mkAppN (mkConst (masks ++ `χ₂_smooth)) s[:23].toArray
        let χ := (← inferType hχ).appArg!
        let hresponse ← store (ns ++ `Corrected.response_on_source_chart) all
          (← mkAppM (ns ++ `contDiffOn_complexifyResponse) #[B,src,hre,him])
        let shape ← mkAppM (ns ++ `contDiffOn_complexCorrectedAtom)
          #[F,χ,B,W,hraw,hre,him]
        let hcorrected ← store (ns ++ `Corrected.on_source_chart) all
          (← mkAppM `ContDiffOn.sub #[hraw,hresponse]) false (some (← inferType shape))
        let corrected ← functionOfSmooth hcorrected
        let native ← mkAppM `JanetCartan.CorrectedAtoms.fullCorrectedPrimaryAtom
          #[raw `T,raw `Q,F,raw `row,raw `col,raw `Φ,raw `Y,χ,B,s[47]!,raw `scalar,parameter[0]!]
        unless ← isDefEq corrected native do
          throwError "original corrected wave: changed native fullCorrectedPrimaryAtom"
        discard <| store (ns ++ `Corrected.atom) all native true
        let hcut := mkAppN (mkConst (geo ++ `smoothing_chart_in_source_chart)) s[:23].toArray
        discard <| store (ns ++ `Corrected.on_cutoff_chart) all
          (← mkAppM `ContDiffOn.mono #[hcorrected,hcut])
        discard <| store (ns ++ `Corrected.same_native_atom) all (← mkEqRefl corrected)
          false (some (← mkEq corrected native))
  logInfo "native corrected positive baseline: SAME graph and finite map, both admitted quadratures, unchanged positive whole atom"

/-- The true outer weight uses the same square of the retained cutoff at the
actual original22 samples (`app:ch_mean_pairs:eq:mean-current-canonical`). -/
elab "construct_original_local_corrected_sample" : command => liftTermElabM do
  withGraphSource fun x s family => do
      let iSample := mkAppN (mkConst (ns ++ `original_sample_row)) family
      let rawχ ← bodyAt (geo ++ `outer_cutoff) s
      let out := `JanetCartan.PhysicalSampling.OriginalOuterWeights
      let actualχ := mkApp (← bodyAt (out ++ `χ) x[:22].toArray) iSample
      unless rawχ.getAppFn == actualχ.getAppFn do throwError "original wave: different native cutoff family"
      let eqχ ← store (ns ++ `Corrected.same_outer_cutoff) family (← mkEqRefl rawχ)
        false (some (← mkEq rawχ actualχ))
      let square := mkConst `JanetCartan.PhysicalSampling.OriginalOuterWeightsTemplate.outerSquare
      let composed ← mkAppM ``congrArg #[square,eqχ]
      let outer := mkAppN (mkConst (geo ++ `outer_weight_parameter)) s
      forallBoundedTelescope (← inferType outer) (some 5) fun sample _ => do
        unless sample.size == 5 do throwError "original corrected wave: changed outer sample ABI"
        let admitted := mkAppN outer sample
        let membership ← Core.betaReduce (← zetaReduce (← inferType admitted))
        unless membership.isAppOfArity ``Membership.mem 5 do
          throwError "original corrected wave: lost actual outer parameter admission"
        let c := membership.getAppArgs[4]!
        let atPoint := family ++ #[c,admitted]
        let hcorrected := mkAppN (mkConst (ns ++ `Corrected.on_cutoff_chart)) atPoint
        let weightType ← inferType sample[4]!
        let some weight := weightType.find? (·.isAppOf `JanetCartan.SeparatedSampling.weight)
          | throwError "original corrected wave: changed literal outer sample weight"
        let ψ := weight.getAppArgs[0]!
        let actualψ := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalOuterWeights.ψ)
          (x[:22].toArray.push iSample)
        -- `same_outer_weight` below is the typed kernel equality of the actual
        -- functions. Do not first normalize their dependent arguments twice.
        discard <| store (ns ++ `Corrected.outer_active_atom) (family ++ sample)
          (← functionOfSmooth hcorrected) true
        discard <| store (ns ++ `Corrected.outer_active_smooth) (family ++ sample) hcorrected
        discard <| store (ns ++ `Corrected.same_outer_weight) (family ++ sample)
          composed false (some (← mkEq ψ actualψ))
  logInfo "native corrected baseline: original graph42/source53, both real quadratures on the same B and positive whole atom at active outer labels"

/-- Build the complete angular response, retaining the positive baseline even
when the inner detector factor vanishes. -/
elab "construct_original_local_whole_waves " k:num : command => liftTermElabM do
  unless k.getNat < 6 do throwError "original wave: expected one of six concrete construction stages"
  withGraphSource (constructWhole k.getNat)
  logInfo m!"checked actual original whole-wave stage {k.getNat}: 0 static sampler, 1 shifted cells, 2 raw/corrected source, 3 full angular factor, 4 combined field, 5 shifted θ germ"
  if k.getNat == 4 then logInfo "actual graph42/source53 corrected atoms AND whole-input waves: SAME literal source/history finiteMap and selected detector, existing task26 B adapter, BOTH quadratures admitted BEFORE response; native atom/whole field locally smooth on SAME Dsmooth; full J ceiling joined through J-1 and original sampling radius without hshift; active original71 outer atoms use actual74 support"

end JanetCartan.PhysicalPrimary.OriginalLocalWavesTemplate
end
