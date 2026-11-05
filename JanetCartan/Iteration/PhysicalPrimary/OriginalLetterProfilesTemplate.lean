module

public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-! Close the remaining actual coefficient, phase and mask arguments after
OriginalLetterCurrent. Only the primitive Fourier-source continuation remains;
no response estimate is assumed. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalLetterProfilesTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private def ns := `JanetCartan.PhysicalPrimary.OriginalLetterProfiles
private def family := `JanetCartan.PhysicalPrimary.OriginalLetterCurrent
private def cur := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
private def wp := `JanetCartan.PhysicalPrimary.OriginalWordProfiles
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def pdo := `JanetCartan.PhysicalPrimary.OriginalPdoProfiles
private def sy := `JanetCartan.PhysicalPrimary.OriginalRetardedSymbols
private def gradient := `JanetCartan.PhysicalPrimary.OriginalWordGradient
private def geom := `JanetCartan.PhysicalPrimary.OriginalRetardedGeometry
private def whole := `JanetCartan.PhysicalPrimary.OriginalIncidence.Whole

private def part (h : Expr) : Nat → Expr
  | 0 => .proj ``And 0 h
  | j+1 => part (.proj ``And 1 h) j
private def tail (h : Expr) : Nat → Expr
  | 0 => h
  | j+1 => tail (.proj ``And 1 h) j

private def normalize (type : Expr) : MetaM Expr := do
  let type ← Core.betaReduce type
  transform type (post := fun expr => do
    let args := expr.getAppArgs
    if args.size ≥ 38 && (expr.isAppOf (reg ++ `Current.W₁) || expr.isAppOf (cur ++ `W₁)) then
      let some value := (← getConstInfo expr.getAppFn.constName!).value? (allowOpaque := true)
        | throwError "native actual profiles: missing literal W1 alias body"
      return .visit (value.beta args)
    let nativeNat := args.size > 0 && args[0]! == mkConst ``Nat
    if (nativeNat && (expr.isAppOf ``HAdd.hAdd || expr.isAppOf ``HSub.hSub ||
        expr.isAppOf ``OfNat.ofNat)) || (args.size ≥ 2 && (expr.isAppOf ``Nat.add || expr.isAppOf ``Nat.sub)) then
      let value ← whnf expr
      if value != expr then return .visit value
    return .continue)

private partial def binder (type : Expr) : MetaM Expr := do
  match type with
  | .mdata _ body => binder body
  | .letE _ _ value body _ => binder (body.instantiate1 value)
  | _ => return type

/-- The closed declaration written by `store` kernel-checks each argument against
its exact native binder, including the frame coercions. Only inspect the outer
spine here: unfolding the entire history at every argument duplicates that work. -/
private def applyOne (label : Name) (proof value : Expr) : MetaM Expr := do
  let .forallE _ _ _ _ ← binder (← inferType proof)
    | throwError "native actual profiles {label}: no remaining binder"
  return mkApp proof value

/-- Restrict smoothness without reselecting a norm on the physical coefficient space. -/
private def onDomain (h domain : Expr) : MetaM Expr := do
  let t ← inferType h
  unless t.isAppOfArity `ContDiff 10 do
    throwError "native coefficient smoothness has changed: {t}"
  let a := t.getAppArgs
  return mkAppN (mkConst `ContDiff.contDiffOn t.getAppFn.constLevels!)
    (a[:8].toArray ++ #[domain,a[9]!,a[8]!,h])

/-- Actual source-admitted native steps. Thresholds and profiles are the
already selected original ones; the full source amplitude itself is supplied
by OriginalSourceProfiles, not by a response-estimate hypothesis. -/
elab "apply_original_native_letter_profiles" : command => liftTermElabM do
  let some currentBody := (← getConstInfo (cur ++ `normalized_solver)).value? (allowOpaque := true)
    | throwError "native actual profiles: original normalized current body missing"
  for label in [`residual,`solver] do
    let receiver := family ++ label ++ `geometric_family
    forallBoundedTelescope (← getConstInfo receiver).type (some 63) fun all _ => do
      unless all.size == 63 do throwError "native actual profiles: actual56 plus numeric7 changed"
      let static := all[:50].toArray
      let fixed := all[:23].toArray
      let get (name : Name) := mkAppN (mkConst (reg ++ name)) fixed
      let mask (name : Name) := mkAppN (mkConst (masks ++ name)) fixed
      let reserve ← mkAppM (family ++ `native_profile_reserves) #[all[49]!,all[43]!,all[41]!]
      let profile := all[:32].toArray ++ #[all[32]!,all[37]!,all[49]!,all[38]!,
        .proj ``And 0 reserve,.proj ``And 1 reserve]
      let pg (name : Name) := mkAppN (mkConst (wp ++ name)) profile
      let phistory := mkAppN (mkConst (family ++ `profile_threshold)) static
      let chistory := mkAppN (mkConst (family ++ `current_threshold)) static
      let f := get `f
      let fa := (← inferType f).getAppArgs
      unless fa.size == 7 do throwError "native actual profiles: finite mask family spine changed"
      let K ← mkAppM `Metric.closedBall #[fa[2]!,fa[3]!]
      let hcK ← mkAppM `ProperSpace.isCompact_closedBall #[fa[2]!,fa[3]!]
      let hχ₂ := mask `χ₂_smooth
      let hχ₃ := mask `χ₃_smooth
      let χ₂ := (← inferType hχ₂).appArg!
      let χ₃ := (← inferType hχ₃).appArg!
      let hχ₃continuous ← mkAppM `ContDiff.continuous #[hχ₃]
      let hbχ₂ ← mkAppM `JanetCartan.SmallSupport.bump_norm_le_one #[get `χ₂]
      let hbχ₃ ← mkAppM `JanetCartan.SmallSupport.bump_norm_le_one #[get `χ₃]
      let hsWord ← mkAppM (family ++ `native_word_source_support)
        #[← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.physicalRadius_pos #[f],
          χ₂,mask `χ₂_support_chart]
      let n := mkApp (mkConst ``Nat.succ) all[0]!
      let original := #[n] ++ all[1:21].toArray
      let hK₀ := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalProtected.fact14) original
      let input ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.inputMask #[f]
      let hinput ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.ActualMaskFamily.inputMask_range #[f]
      let hib ← mkAppM `JanetCartan.PhysicalPrimary.OriginalLetterGeometry.original_output_norm_bound #[input,hinput]
      let hc := mkAppN (mkConst (reg ++ `Sector.rootBuffer)) fixed
      let hdom ← mkAppM `JanetCartan.ArbitraryAccuracy.SelectedResidualInputs.selected_constant_complement_domain_of_supplied_collar
        #[f,get `fact6]
      let cap := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra) #[n,all[1]!,original[20]!]
      let hμ := mkAppN (mkConst `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure) (original.set! 20 cap)
      let hr := mkAppN (mkConst `JanetCartan.PhysicalInitialization.OriginalProtected.fact2) original
      let hscreen ← mkAppM (reg ++ `screened_pos) #[all[1]!,hr,hμ]
      let core ← mkAppM (reg ++ `core_spec) #[all[1]!,hscreen]
      let hRQ ← mkAppM `le_of_lt #[part core 0]
      let hball := part core 2
      let scalarProfiles : Array Expr := if label == `residual then
        #[pg `AQ,pg `AB,pg `Aphase,mkAppN (mkConst (pdo ++ `Dendpoint)) fixed,
          mkAppN (mkConst (pdo ++ `Dalgebraic)) fixed,get `amplitudeCost,
          pg `AQ_nonneg,pg `AB_nonneg,pg `Aphase_nonneg,
          mkAppN (mkConst (pdo ++ `Dendpoint_nonneg)) fixed,
          mkAppN (mkConst (pdo ++ `Dalgebraic_nonneg)) fixed,
          mkAppN (mkConst (sy ++ `amplitude_cost_nonneg)) fixed]
        else #[pg `AQ,pg `AB,pg `Aphase,mkAppN (mkConst (pdo ++ `Dalgebraic)) fixed,
          pg `AQ_nonneg,pg `AB_nonneg,pg `Aphase_nonneg,
          mkAppN (mkConst (pdo ++ `Dalgebraic_nonneg)) fixed]
      let sectorType := (← inferType (get `fact11)).bindingDomain!
      withLocalDeclD `i all[34]! fun i => do
        let history := #[mkApp all[51]! i,mkApp all[52]! i,mkApp all[53]! i,mkApp all[55]! i]
        let wpArgs := profile ++ #[mkApp all[50]! i,← mkAppM `le_trans #[phistory,mkApp all[54]! i]] ++ history
        let now := all[:32].toArray ++ #[mkApp all[50]! i,
          ← mkAppM `le_trans #[chistory,mkApp all[54]! i]] ++ history
        let weak := currentBody.beta now
        unless weak.isAppOfArity (reg ++ `Current.normalized_solver) 38 do
          throwError "native actual profiles: original weak current38 disappeared"
        let wa := weak.getAppArgs
        let current (name : Name) := mkAppN (mkConst (cur ++ name)) now
        let actualProfile (name : Name) := mkAppN (mkConst (wp ++ name)) wpArgs
        let each (value : Expr) := mkLambdaFVars #[i] value
        let phase ← mkAppM ``Function.curry #[actualProfile `φ]
        let mut proof := mkAppN (mkConst receiver) all
        proof ← applyOne (label ++ `phase) proof (← each phase)
        proof := mkApp proof (← each (actualProfile `phase_smooth))
        let .forallE _ eqType _ _ ← binder (← inferType proof)
          | throwError "native actual profiles: missing literal phase pullback"
        let eqProof ← forallBoundedTelescope eqType (some 4) fun q goal => do
          unless q.size == 4 && goal.isAppOfArity ``Eq 3 do
            throwError "native actual profiles: phase pullback shape changed"
          mkLambdaFVars q (← mkEqRefl goal.getAppArgs[1]!)
        proof := mkApp proof eqProof
        let mut known : Array Expr := if label == `residual then
          #[χ₂,χ₃,hχ₂,mask `χ₂_compact,hχ₃continuous,hbχ₂,hbχ₃,mask `χ₃_on_χ₂]
          else #[χ₂,χ₃,mask `χ₂_compact,hχ₃continuous,hbχ₃,mask `χ₃_on_χ₂]
        known := known ++ #[mkAppN (mkConst (geom ++ `source_in_box)) fixed,hsWord,hK₀,hib]
        if label == `residual then
          let one ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 1
          let retarded ← withLocalDeclD `p sectorType fun p =>
            mkLambdaFVars #[i,p] (mkApp (mkApp (current `Op) one) p)
          known := known ++ #[← each (current `W₁),retarded]
        for j in [:known.size] do
           proof ← applyOne (label ++ `source_masks) proof known[j]!
        if label == `residual then
          let .forallE _ eqType _ _ ← binder (← inferType proof)
            | throwError "native actual profiles: missing same retarded operator equality"
          let eqProof ← forallBoundedTelescope eqType (some 2) fun q goal => do
            unless goal.isAppOfArity ``Eq 3 do throwError "native actual profiles: retained operator equality changed"
            mkLambdaFVars q (← mkEqRefl goal.getAppArgs[1]!)
          proof ← applyOne (label ++ `same_operator) proof eqProof
        let some uqBody := (← getConstInfo (reg ++ `Current.uQ)).value? (allowOpaque := true)
          | throwError "native actual profiles: missing original coefficient realization"
        let hΩ := (uqBody.beta wa).getAppArgs[7]!
        for value in #[hΩ,hRQ,hball,get `hL,hc,hdom] do
          proof ← applyOne (label ++ `static_profiles) proof value
        for value in scalarProfiles do
          proof ← applyOne (label ++ `static_profiles) proof value
        let hQon ← onDomain (current `hQ) fa[1]!
        let hBon ← onDomain (current `hB) fa[1]!
        let hmap ← mkAppM `Set.MapsTo.mono_left #[current `fact0,← mkAppM `Set.subset_univ #[fa[1]!]]
        let low := mkAppN (current `fact2) #[K,hcK]
        let nativeLow ← mkAppM (family ++ `native_low_coefficient_bounds)
          #[K,current `Q,current `B,part low 0,part low 1]
        let coefficients := mkAppN (tail (actualProfile `coefficient_profiles) 2) #[K,hcK]
        for value in #[hQon,hBon,hmap,.proj ``And 0 nativeLow,.proj ``And 1 nativeLow,
            .proj ``And 0 coefficients,.proj ``And 1 coefficients] do
          proof := mkApp proof (← each value)
        let sectorType := (← inferType (get `fact11)).bindingDomain!
        withLocalDeclD `p sectorType fun p => do
          let mut proof := proof
          let point (value : Expr) := mkLambdaFVars #[p,i] value
          let symbol (name : Name) := mkAppN (mkConst (sy ++ name)) (wa.push p)
          if label == `residual then
            proof ← applyOne (label ++ `W1_smooth) proof (← mkLambdaFVars #[i,p] (symbol `W1_joint_smooth))
            proof ← applyOne (label ++ `W1_budget) proof (← mkLambdaFVars #[i,p] (symbol `W1_seminorms))
            let endpoint := mkAppN (mkConst (pdo ++ `endpoint)) (wa.push p)
            let ea := (← inferType endpoint).getAppArgs
            for value in #[ea[ea.size-5]!,ea[ea.size-2]!,ea[ea.size-1]!] do
              proof ← applyOne (label ++ `endpoint_data) proof (← point value)
            proof ← applyOne (label ++ `endpoint) proof (← point endpoint)
          proof ← applyOne (label ++ `algebraic) proof
            (← point (mkAppN (mkConst (pdo ++ `algebraic)) (wa.push p)))
          let patch := #[all[0]!,all[1]!,all[32]!]
          let lo := mkAppN (mkConst (whole ++ `wholeLo)) patch
          let hi := mkAppN (mkConst (whole ++ `wholeHi)) patch
          let hlo := mkAppN (mkConst (whole ++ `fact0)) patch
          let hhi ← mkAppM `lt_trans #[hlo,mkAppN (mkConst (whole ++ `fact1)) patch]
          for value in #[lo,hi,hlo,hhi] do proof ← applyOne (label ++ `phase_band) proof value
          let chart := mkAppN (mkConst (reg ++ `Sector.chart)) (fixed.push p)
          let index ← mkAppM `JanetCartan.RegularSector.FiniteMasks.ActualFamily.LocalChart.index #[chart]
          let coordinate := mkAppN (mkConst (wp ++ `coordinate_word_profiles)) (wpArgs.push index)
          let physical := actualProfile `word_profiles
          let coordinateGradient := mkAppN (mkConst (gradient ++ `coordinate_gradient_range)) (now ++ #[all[32]!,index])
          let physicalGradient := mkAppN (mkConst (gradient ++ `physical_gradient_range)) (now.push all[32]!)
          for value in #[← point (part coordinate 0),← point (tail coordinate 2),← point coordinateGradient,
              ← each (part physical 0),← each (tail physical 2),← each physicalGradient] do
            proof ← applyOne (label ++ `word_phase_profiles) proof value
          discard <| store (ns ++ label ++ `source_admitted_step) all proof
  logInfo "actual native53/50 coefficient, phase and mask continuations closed on SAME histories; only primitive actual Fourier source admission remains, never a response estimate"

end JanetCartan.PhysicalPrimary.OriginalLetterProfilesTemplate
