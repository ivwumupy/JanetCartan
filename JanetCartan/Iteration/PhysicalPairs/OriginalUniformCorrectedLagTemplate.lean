module
public import JanetCartan.Iteration.PhysicalPairs.OriginalUniformTail
public import JanetCartan.Iteration.PhysicalPairs.OriginalCorrectedLag
/-! # Corrected-source decay uniform before all later source data

Instantiate the original normalized corrected-source theorem on the universal
bounded-wave labels. Its single rapid-decay constant covers every later
history, shift, target and smoothing datum at the fixed derivative price. The
pointwise error is the existing literal smooth-right minus original signed
stress, not a new corrector (`main:prop:pairs`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalUniformCorrectedLagTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalUniformCorrectedLag
private def waves := `JanetCartan.PhysicalPairs.OriginalUniformWaveData
private def uf := `JanetCartan.PhysicalPairs.OriginalUniformFirstMask
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def world := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def err := `JanetCartan.PhysicalPairs.OriginalResidualEmbedding
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def down (e : Expr) : Nat → Expr | 0 => e | k+1 => down (.proj ``And 1 e) k
private def part (e : Expr) (k : Nat) := Expr.proj ``And 0 (down e k)
private def beforeLets : Expr → Array Name
  | .forallE n _ body _ => #[n] ++ beforeLets body
  | .mdata _ e => beforeLets e
  | _ => #[]
private def save (key : Name) (p : Array Expr) (proof : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p (← inferType proof))
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "uniform corrected source: later input escaped fixed budget {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking universal actual corrected lag {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The actual original normalized smooth correction minus its SAME signed stress decays uniformly before all histories, shifts, targets and smoothing inputs, over all complete Schwartz source waves of one fixed derivative price (main:prop:pairs; app:ch_pairs:eq:pairs-lag-one-error)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "uniform actual corrected lag: nonstandard axioms {axioms}"
  logInfo m!"universal actual corrected lag {key}/{p.size}: {axioms}"
elab "prove_original_uniform_corrected_lag " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "uniform actual corrected lag: unknown mode"
  forallBoundedTelescope (← getConstInfo (uf ++ `first_mask)).type (some 39) fun p _ => do
    let b := p[:37].toArray
    let fixed := p[:38].toArray
    let d := b[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let β := app (waves ++ `Labels) fixed
    let ρ := app (waves ++ `frequency) fixed
    let gf := (← inferType (app (hist ++ `historyMap) b)).bindingBody!
    let fix := gf.getAppArgs[:23].toArray
    let stat (key : Name) := app (reg ++ key) fix
    let f := stat `f
    let fa := (← inferType f).getAppArgs
    let W := app (world ++ `W) fix
    let hW := app (world ++ `W_measurable) fix
    let E ← inferType fa[2]!
    let χ := stat `χ₂
    let ψ := stat `χ₃
    let measured := ((← getConstInfo (waves ++ `measured)).value! (allowOpaque := true)).beta fixed
    lambdaBoundedTelescope measured 1 fun label row => do
      unless row.isAppOfArity `JanetCartan.PhysicalPairs.OriginalSignedData.measured 50 do
        throwError "uniform actual corrected lag: changed original measured source"
      let t := label[0]!
      let rv := row.getAppArgs
      let pt := rv[:49].toArray
      let fam (e : Expr) := mkLambdaFVars label e
      if mode.getNat == 0 then
        let r ← mkAppM `ContDiffBump.rIn #[χ]
        let V ← mkAppM `Metric.ball #[fa[2]!,r]
        let hV := app `JanetCartan.PhysicalInitialization.OriginalSampledObserved.native_norm_ball #[n,r]
        let hψW ← mkAppM `Set.Subset.trans #[app (masks ++ `χ₃_support_chart) fix,stat `hUW]
        let hχW ← mkAppM `Set.Subset.trans #[app (masks ++ `χ₂_support_chart) fix,stat `hUW]
        let χVW ← mkAppM `JanetCartan.PhysicalPairs.OriginalPacketEquation.inner_subset #[χ,hχW]
        let hχobsCore := app `JanetCartan.PhysicalPairs.OriginalCorrectedPairs.inner_plateau #[n,fa[2]!,χ,ψ,app (masks ++ `χ₃_on_χ₂) fix]
        let hob := app `JanetCartan.PhysicalInitialization.OriginalSampledObserved.bounded_mask #[E,stat `output,stat `fact18]
        let hi := app (hist ++ `measured_history) pt
        let now := pt[:36].toArray ++ #[pt[37]!,part hi 0] ++ pt[39:43].toArray
        let current := ((← getConstInfo `JanetCartan.PhysicalInitialization.OriginalSampledPairs.projected).value! (allowOpaque := true)).beta now
        unless current.isAppOfArity (reg ++ `Current.projected) 38 do throwError "uniform corrected lag: original current changed"
        let cur (key : Name) := app (reg ++ `Current ++ key) current.getAppArgs
        let unc ← mkAppM ``Subtype.val #[app `JanetCartan.PhysicalPairs.OriginalSignedData.uncut rv]
        let coeff := #[n] ++ fix[1:21].toArray
        let window := part (app (hist ++ `native_window) pt) 0
        let one ← mkNumeral (mkConst ``Real) 1
        let hA ← mkAppOptM `zero_le_one #[some (mkConst ``Real),none,none,none,none]
        let plus ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 1
        withLocalDeclD `observationOrder (mkConst ``Nat) fun s => do
          let args : Array (Name × Expr) := #[(`d,d),(`ι,β),(`Ω,fa[1]!),(`center,fa[2]!),(`RQ,fa[3]!),(`A₀,fa[4]!),(`K,fa[5]!),(`M,fa[6]!),
            (`f,f),(`hK,app `JanetCartan.PhysicalInitialization.OriginalProtected.fact14 coeff),(`L₀,stat `L),(`hL₀,stat `hL),
            (`Q,← fam (cur `Q)),(`B,← fam (cur `B)),(`W₁,← fam (cur `W₁)),(`retarded,← fam (mkApp (cur `retarded) plus)),
            (`output,stat `output),(`ho,stat `fact17),(`hoc,stat `fact19),(`hob,hob),(`D,W),(`hD,hW),(`rLp,(← inferType (stat `hrU)).appArg!),
            (`hrLp,stat `hrU),(`hball,stat `hUW),(`hmem,← fam (cur `hmem)),(`budget,(← inferType (stat `hbudget)).appArg!),(`hbudget,stat `hbudget),(`hbound,← fam (cur `hbound)),
            (`χ₂,χ),(`χ₃,ψ),(`χobs,ψ),(`hχ₂ball,stat `fact42),(`hnest,app (masks ++ `χ₃_on_χ₂) fix),(`hχ₃D,hψW),(`Vobs,W),(`Wcore,V),(`hVobs,hW),(`hWcore,hV),
            (`hχobsV,hψW),(`hWV,χVW),(`hχobsCore,hχobsCore),(`ρ,ρ),(`A,← fam one),(`hρ,← fam (app (fm ++ `one_of_two) #[mkApp ρ t,part window 2])),(`hA,← fam hA),(`s,s),(`h,← fam unc)]
          let key := `JanetCartan.ArbitraryAccuracy.SelectedLocalization.normalized_correctedSource_angular_rapidDecayAt_of_original_remainder
          let info ← getConstInfo key
          let names := beforeLets info.type
          unless names.back! == `h do throwError "uniform corrected lag: original remainder telescope changed"
          let fields ← names.mapM fun name => do
            let some (_,value) := args.find? (·.1 == name) | throwError "uniform corrected lag: unsupplied original field {name}"
            pure value
          let hK ← fam (← mkAppM `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.lt_one_of_half_bound #[cur `fact6])
          let chains := mkApp (app (uf ++ `observed_powers) (p ++ #[W,hW])) s
          let remainder := app `JanetCartan.PhysicalPairs.OriginalUniformTail.unobserved_remainder (p.push s)
          let proof := mkAppN (mkConst key (info.levelParams.map fun _ => .zero)) (fields ++ #[hK,chains,remainder])
          save `corrected_rapid (p.push s) proof
        return
      let error ← fam (app (err ++ `error) rv)
      let smooth ← fam (app (err ++ `error_smooth) rv)
      let ae := app (err ++ `actual_observation_ae) rv
      let rhs := (← inferType ae).appArg!
      unless rhs.isAppOfArity `MeasureTheory.AEEqFun.cast 6 && rhs.appArg!.isAppOfArity ``Subtype.val 3 do
        throwError "uniform corrected lag: original angular observation class changed"
      let u ← fam rhs.appArg!.appArg!
      let some V := (← inferType ae).getAppArgs[2]!.find? (·.isAppOf `Metric.ball)
        | throwError "uniform corrected lag: original inner ball missing"
      let va := V.getAppArgs
      let c := va[va.size-2]!
      let r := va.back!
      let hr ← mkAppM `ContDiffBump.rIn_pos #[r.appArg!]
      withLocalDeclD `jetOrder (mkConst ``Nat) fun s => withLocalDeclD `accuracy (mkConst ``Real) fun q => do
        if mode.getNat == 1 then
          let level := mkApp2 (mkConst ``Nat.add) (mkApp2 (mkConst ``Nat.add) s n) (mkNatLit 1)
          let h := app (root ++ `corrected_rapid) (p.push level)
          let proof := mkAppN (mkConst (err ++ `on_inner_ball) [.zero]) #[n,β,c,r,hr,ρ,error,u,smooth,← fam ae,s,h,q]
          save `smooth_right_cnorm (p ++ #[s,q]) proof
        else
          let h := app (root ++ `smooth_right_cnorm) (p ++ #[mkNatLit 0,q])
          let some D := (← inferType h).find? (·.isAppOf `Metric.closedBall)
            | throwError "uniform corrected lag: original closed stage ball missing"
          let proof := mkAppN (mkConst `JanetCartan.PhysicalPairs.OriginalCorrectedLag.point_of_cnorm [.zero])
            #[n,β,c,D.appArg!,ρ,error,smooth,q,h]
          save `pointwise (p.push q) proof
end JanetCartan.PhysicalPairs.OriginalUniformCorrectedLagTemplate
end
