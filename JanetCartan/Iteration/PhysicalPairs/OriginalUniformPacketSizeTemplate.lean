module
public import JanetCartan.Iteration.PhysicalPairs.OriginalUniformFirstMask
public import JanetCartan.Iteration.PhysicalPairs.OriginalPacketSize
public import JanetCartan.Iteration.PhysicalPairs.OriginalUniformSizeSelection
/-! # Original packet size from its actual pair jets only

The original size threshold and all-order constants are already fixed before
waves. Apply that SAME continuation to one later complete Schwartz family and
the genuine derivative bounds at its two original nodes. No history-wide wave
family, target-dependent constant, or replacement normalized solver is selected
(`main:prop:pairs`, `app:ch_pairs:eq:pairs-lag-sum-size`).
-/
public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalUniformPacketSizeTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalPairs.OriginalUniformPacketSize
private def original := `JanetCartan.PhysicalPairs.OriginalPacketSize
private def sel := `JanetCartan.PhysicalPairs.OriginalUniformSizeSelection
private def hist := `JanetCartan.PhysicalPairs.SampledHistory
private def fm := `JanetCartan.PhysicalPairs.OriginalFirstMask
private def rows := `JanetCartan.PhysicalPairs.OriginalMaskRows
private def sup := `JanetCartan.PhysicalPairs.OriginalSizeSupport
private def fq := `JanetCartan.PhysicalPairs.OriginalSizeFrequency
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def data := `JanetCartan.PhysicalPairs.OriginalSignedData
private def pkt := `JanetCartan.PhysicalPairs.OriginalSignedPackets
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def down (e : Expr) : Nat → Expr | 0 => e | k+1 => down (.proj ``And 1 e) k
private def part (e : Expr) (k : Nat) := Expr.proj ``And 0 (down e k)
private def save (key : Name) (p : Array Expr) (proof : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p (← inferType proof))
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "uniform original packet size: unresolved or misplaced source {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  IO.println s!"Kernel checking actual local signed packet size {key}/{p.size}"
  (← IO.getStdout).flush
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME original signed packet obeys the SAME physical-size continuation fixed before all source waves, using only its two actual complete derivative profiles; actual current, input measurement and normalized solver retained (main:prop:pairs; app:ch_pairs:eq:pairs-lag-sum-size)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "uniform original packet size: nonstandard axioms {axioms}"
  logInfo m!"actual local signed packet size {key}/{p.size}: {axioms}"
elab "prove_original_uniform_packet_size " mode:num : command => liftTermElabM do
  unless mode.getNat < 3 do throwError "uniform original packet size: unknown mode"
  forallBoundedTelescope (← getConstInfo (hist ++ `index)).type (some 49) fun pt gf => do
    let b := pt[:37].toArray
    let fix := gf.getAppArgs[:23].toArray
    let d := b[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let N := app `JanetCartan.embeddingDimension #[n]
    let m (key : Name) := app (masks ++ key) fix
    let stat (key : Name) := app (reg ++ key) fix
    let t := app (hist ++ `label) pt
    let reached := part (app (hist ++ `measured_history) pt) 0
    let current := ((← getConstInfo `JanetCartan.PhysicalInitialization.OriginalSampledPairs.projected).value! (allowOpaque := true)).beta
      (b[:36].toArray ++ #[pt[37]!,reached] ++ pt[39:43].toArray)
    let weak := current.getAppArgs
    let cur (key : Name) := app (reg ++ `Current ++ key) weak
    let F := Expr.proj ``Subtype 0 current
    let χ₂ := stat `χ₂
    let α := app (sup ++ `factor) fix
    let η := app (original ++ `unitFactor) #[n]
    let hcapType := (← inferType (app (sel ++ `native_budget) b)).bindingDomain!
    withLocalDeclD `historyCapForSize hcapType fun hcap => do
      forallBoundedTelescope (← inferType (app `JanetCartan.PhysicalPairs.OriginalUniformFirstMask.first_mask b)) (some 2) fun prices _ => do
        let C := prices[0]!
        let hC := prices[1]!
        let selP := b ++ #[hcap,C,hC]
        let named (key : Name) := app (sel ++ key) selP
        let wt := (← inferType (app (data ++ `uncut) pt)).bindingDomain!
        withLocalDeclD `completePrimaryWaves wt fun Z => do
          let ptZ := pt.push Z
          let profileArgs := b ++ #[C,t,Z]
          let profileName := `JanetCartan.PhysicalPairs.OriginalUniformWaveData.DerivativeProfile
          let profileType := app profileName profileArgs
          withLocalDeclD `truePairJets profileType fun hPair => do
            let θ := app (data ++ `angles) pt
            let oldη := (← inferType (m `χsrc_smooth)).appArg!
            let H ← mkAppM `JanetCartan.PhysicalPairs.SampledInput.tensor #[Z,θ,pt[45]!,pt[46]!,pt[47]!]
            let htType ← mkAppM ``LE.le #[named `threshold,pt[37]!]
            withLocalDeclD `reachedPhysicalSize htType fun hr => do
              let all := selP ++ pt[37:39].toArray ++ #[hr] ++ pt[39:].toArray ++ #[Z,hPair]
              if mode.getNat == 0 then
                let start := mkAppN (named `continuation) (#[pt[37]!,hr] ++ pt[39:43].toArray)
                let qsol ← mkAppM ``Classical.choose_spec #[start]
                let core ← mkAppM ``Classical.choose_spec #[qsol]
                let ret ← mkAppM (original ++ `cacheSlots) #[cur `retarded]
                let norm := mkAppN core #[cur `W₁,ret,app `JanetCartan.PhysicalPairs.OriginalInverse.response_tame weak]
                let window := part (app (hist ++ `native_window) pt) 0
                let lc := part window 0
                let le := part window 1
                let fine := (← inferType le).appArg!
                let hlam := app (fq ++ `fine_le_lam) pt
                let lam := (← whnf (← inferType hlam)).appArg!
                let rho := (← inferType (part window 2)).appArg!
                let specs := mkAppN norm #[fine,lam,rho,le,hlam,← mkAppM (original ++ `strictly_positive) #[part window 2],app (fq ++ `rho_le_carrier) pt]
                let angles ← mkAppM (original ++ `pairSlots) #[mkApp θ pt[46]!,mkApp θ pt[47]!]
                let amp ← mkAppM (original ++ `pairSlots) #[app (rows ++ `leftAmplitude) ptZ,app (rows ++ `rightAmplitude) ptZ]
                let V := m `chart
                let hVB := m `chart_in_coefficient_ball
                let hV ← mkAppM `JanetCartan.PhysicalPairs.OriginalSizeSelection.in_profile #[stat `normRadius,hVB]
                let zero ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 0
                let one ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 1
                let fbase := mkAppN specs #[V,m `chart_open,hV,α,η,angles,amp,pt[45]!,zero,one,app (original ++ `different) #[pt[45]!]]
                let hL ← mkAppM ``le_trans #[lc,le]
                let jets (f hf : Expr) := mkAppM (sup ++ `jet_bound) #[hVB,f,hf,hL]
                let localLedger := ((← getConstInfo profileName).value! (allowOpaque := true)).beta profileArgs
                unless localLedger.isAppOfArity (fm ++ `FullDerivativeProfile) 8 do
                  throwError "uniform packet size: original two-node ledger changed"
                let ledgerArgs := localLedger.getAppArgs.push hPair
                let left := mkApp (app (fm ++ `left_bound) ledgerArgs) (mkConst ``Unit.unit)
                let right := mkApp (app (fm ++ `right_bound) ledgerArgs) (mkConst ``Unit.unit)
                let proof := mkAppN fbase #[app (sup ++ `smooth) fix,app (fm ++ `support_refl) #[d,α],app (sup ++ `support_chart) fix,app (original ++ `unit_on) #[n,V],
                  app (fq ++ `angle_smooth) pt,app (rows ++ `left_smooth) ptZ,app (rows ++ `right_smooth) ptZ,app (fq ++ `angle_jets) pt,
                  ← jets α (app (sup ++ `smooth) fix),← jets η (app (original ++ `unit_smooth) #[n]),left,right]
                save `localized_response all proof
                return
              let priced := app (root ++ `localized_response) all
              IO.eprintln "uniform packet size: choose source integrability"
              let hf ← mkAppM ``Classical.choose #[priced]
              let start ← mkAppM ``Classical.choose_spec #[priced]
              IO.eprintln "uniform packet size: project SAME uncut source"
              let v ← mkAppM ``Subtype.val #[app (data ++ `uncut) ptZ]
              let hχball ← mkAppM ``Set.Subset.trans #[m `χ₂_support_chart,m `chart_in_coefficient_ball]
              IO.eprintln "uniform packet size: apply exact measurement identity"
              let W := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source.W fix
              let center := (← inferType χ₂).appArg!
              let radius := (← inferType fix[6]!).appArg!
              let exactInput := app (original ++ `measured_extended)
                #[n,N,W,center,χ₂,fix[4]!,F,radius,fix[5]!,fix[6]!,hχball,H,oldη,α,
                  app (sup ++ `same_input) fix,v,app (sup ++ `original_input_ae) ptZ]
              let same := mkApp exactInput hf
              IO.eprintln "uniform packet size: measurement identity assembled"
              if mode.getNat == 1 then
                save `same_measurement all same
                return
              let same := app (root ++ `same_measurement) all
              let ae := app (data ++ `solver_representation) ptZ
              let old := app (data ++ `measured) ptZ
              let predicate ← withLocalDeclD `originalMeasured (← inferType old) fun u => do
                mkLambdaFVars #[u] ((← inferType ae).replace fun e => if e == old then some u else none)
              let trans ← mkAppM ``congrArg #[predicate,← mkAppM ``Eq.symm #[same]]
              let hsol ← mkAppM ``Eq.mp #[trans,ae]
              let solver := app (pkt ++ `solved) ptZ
              let field := app (pkt ++ `packet) ptZ
              let form := app (pkt ++ `formula) ptZ
              let ψ := (← inferType (m `χ₃_smooth)).appArg!
              let eq ← withLocalDeclD `x (app `JanetCartan.Euclidean #[n]) fun x => do
                let atX ← mkAppM ``congrFun #[form,x]
                let some cv := (← inferType atX).find? (·.isAppOfArity `JanetCartan.AmbientResponse.completedVariation 6)
                  | throwError "uniform packet size: actual completion changed"
                let physicalF := cv.getAppArgs[2]!
                let more := app (sup ++ `same_field) #[n,N,ψ,oldη,α,app (sup ++ `same_output) fix,physicalF,solver,H,x]
                mkLambdaFVars #[x] (← mkAppM ``Eq.trans #[atX,more])
              let result := mkAppN start #[solver,app (pkt ++ `solved_smooth) ptZ,hsol,field,eq]
              save `size all result
end JanetCartan.PhysicalPairs.OriginalUniformPacketSizeTemplate
end
