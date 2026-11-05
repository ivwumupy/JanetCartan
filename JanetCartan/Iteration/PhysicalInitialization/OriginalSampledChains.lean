module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledFactors
public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledChainInputs
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedObservedResidual.FiniteMaskReindexing
public meta import Lean

/-!
# Original observed powers on the admitted signed-history family

The finite-chain consumer keeps the physical coefficient domain and the
native norm ball. The original terminal and all signed operator estimates
are pulled back along an arbitrary map of source labels into the admitted
history family. Only the actual source's support, norm and first-mask input
are supplied by `PhysicalPairs.LocalCorrectedApplication`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalInitialization.OriginalSampledChains
open Lean Meta Elab Command OriginalProtectedTemplate
open scoped Matrix.Norms.Frobenius
private def root := `JanetCartan.PhysicalInitialization.OriginalSampledChains
private def obs := `JanetCartan.PhysicalInitialization.OriginalSampledObserved
private def poly := `JanetCartan.PhysicalInitialization.OriginalSampledPolynomial
private def reindex := `JanetCartan.PhysicalInitialization.OriginalSampledReindexing
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def op := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
private def termNS := `JanetCartan.PhysicalInitialization.OriginalSampledTerminal
private def fac := `JanetCartan.PhysicalInitialization.OriginalSampledFactors
private def a (k : Name) (x : Array Expr) := mkAppN (mkConst k) x
private def down (h : Expr) : Nat → Expr
  | 0 => h
  | k+1 => down (.proj ``And 1 h) k
private def field (h : Expr) (j : Nat) := Expr.proj ``And 0 (down h j)
private def spine (label : String) (h : Expr) : MetaM Unit := do
  forallBoundedTelescope (← whnf (← inferType h)) (some 20) fun xs _ => do
    let names ← xs.mapM fun x => return (← x.fvarId!.getDecl).userName
    logInfo m!"{label}: {names}"
private def storeExplicit (name : Name) (params : Array Expr) (value type : Expr) : MetaM Unit := do
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← mkForallFVars params type)
  if type.hasFVar || type.hasMVar || type.hasSorry || value.hasFVar || value.hasMVar || value.hasSorry then
    throwError "open or incomplete observed-chain declaration {name}"
  logInfo "Closed observation proof and conclusion ready for kernel checking."
  addDecl (.thmDecl { name, levelParams := [], type, value }) (forceExpose := true)
  logInfo "Observation application kernel checked."
private def next (h : Expr) (prove : Expr → MetaM Expr) : MetaM Expr := do
  let .forallE _ t _ _ ← whnf (← inferType h) | throwError "expected the next observed-power premise"
  return mkApp h (← prove t)
private def nextTyped (h : Expr) (prove : Expr → MetaM Expr) : MetaM (Expr × Expr) := do
  let .forallE _ t body _ ← whnf (← inferType h) | throwError "expected the next observed-power premise"
  let proof ← prove t
  return (mkApp h proof, body.instantiate1 proof)
private def witness (goal value : Expr) (prove : Expr → MetaM Expr) : MetaM Expr := do
  let t ← whnf goal
  unless t.isAppOfArity ``Exists 2 do throwError "expected a finite-chain existential"
  let pred := t.appArg!
  let rest := (mkApp pred value).headBeta
  let proof ← prove rest
  return mkAppN (mkConst ``Exists.intro [.one]) #[t.getAppArgs[0]!,pred,value,proof]
private def byName (key : Name) (known : Array (Name × Expr)) : MetaM Expr := do
  let rec opts : Expr → Array (Option Expr)
    | .forallE n _ body _ => #[(known.find? (·.1 == n)).map (·.2)] ++ opts body
    | .mdata _ e => opts e
    | _ => #[]
  mkAppOptM key (opts (← getConstInfo key).type)
private def localLinear (hU U T : Expr) : MetaM Expr := do
  let h ← mkAppM `JanetCartan.RegularSector.Characteristic.RetardedLocalization.localRetardedOperator #[hU,U,T]
  mkAppM `ContinuousLinearMap.toLinearMap #[h]
/- Read only the three scalar factors of the proved estimate. The resulting
   expression keeps the selected loss before accuracy and cost before history. -/
private def decayScalars (h : Expr) : MetaM (Expr × Expr × Expr) := do
  let bound := Expr.proj ``And 1 h
  let rhs := (← inferType bound).appArg!
  let left (e : Expr) := e.getAppArgs[e.getAppArgs.size-2]!
  let base := left (left (left rhs))
  let c := base.appArg!.appArg!
  let b := (left (left rhs)).appArg!.appArg!
  return (c,b,left base)
private def uniformDecay (goal β : Expr)
    (make : Expr → Expr → MetaM Expr) (positive : Expr → Expr) : MetaM Expr := do
  withLocalDeclD `sample β fun sample => do
    withLocalDeclD `accuracy (mkConst ``Nat) fun accuracy => do
      -- The sample is used only to read the fixed exponents, not to select
      -- a history-dependent constant.
      let probe ← make sample accuracy
      let .forallE _ vtype _ _ ← whnf (← inferType probe) | throwError "missing the localized test vector"
      withLocalDeclD `v vtype fun v => do
        let sampleBound := mkApp probe v
        let (c,b,_) ← decayScalars sampleBound
        if c.containsFVar sample.fvarId! || b.containsFVar sample.fvarId! ||
            c.containsFVar accuracy.fvarId! || b.containsFVar accuracy.fvarId! then
          throwError "native finite-chain loss depends on the sample or accuracy"
        witness goal c fun g => witness g b fun g =>
          forallBoundedTelescope g (some 1) fun q t => do
            let probe ← make sample q[0]!
            let (_,_,C) ← decayScalars (mkApp probe v)
            if C.containsFVar sample.fvarId! then
              throwError "native finite-chain constant depends on the sampled history"
            let result ← witness t C fun t => do
              let t ← whnf t
              let body := t.getAppArgs[1]!
              let all ← forallBoundedTelescope body (some 2) fun iv _ => do
                let h ← make iv[0]! q[0]!
                mkLambdaFVars iv (mkApp h iv[1]!)
              mkAppM ``And.intro #[positive q[0]!,all]
            mkLambdaFVars q result

run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (root ++ `after_individual_bounds)).type (some 43) fun p _ => do
    let x := p[:36].toArray
    let β := p[36]!
    let e := p[37]!
    let u := p[38]!
    let d := x[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let args ← OriginalSampledTerminal.actualTerminalArguments x[:22].toArray x[22:24].toArray
    let fixed := args[26]!.getAppArgs
    let g := fixed ++ x[24:26].toArray ++ x[27:36].toArray
    let fa := (← inferType args[26]!).getAppArgs
    let E ← inferType fa[2]!
    let univ := mkApp (mkConst `Set.univ [.zero]) E
    let meas ← synthInstance (mkApp (mkConst `MeasurableSpace [.zero]) E)
    let hUniv ← byName `MeasurableSet.univ #[(`α,E),(`m,meas)]
    let CV ← mkAppM `EuclideanSpace #[mkConst ``Complex,mkApp (mkConst ``Fin) n]
    let G ← mkAppM `JanetCartan.LocalSobolev.restrictionSobolevScale #[univ,CV,hUniv]
    let stat (k : Name) := a (termNS ++ `Static ++ k) args
    let native (k : Name) := a (reg ++ k) fixed
    let D ← mkAppM `Metric.ball #[fa[2]!,native `normRadius]
    let hD := a (obs ++ `native_norm_ball) #[n,native `normRadius]
    let hs := a `JanetCartan.PhysicalPrimary.OriginalSourceMasks.χ₂_smooth fixed
    let χ₂ := (← inferType hs).appArg!
    let S ← mkAppM `Set.prod #[← mkAppM `tsupport #[χ₂],args[36]!]
    withLocalDeclD `j β fun j => do
      let i := mkApp e j
      let raw ← mkAppM ``Subtype.val #[i]
      let idx (k : Name) := a (`JanetCartan.PhysicalPrimary.OriginalHistoryFamily.RawIndex ++ k) #[d,mkConst ``Unit,raw]
      let prop ← mkAppM ``Subtype.property #[i]
      let family (z : Expr) := mkLambdaFVars #[j] z
      let ρ ← family (idx `lam)
      let L ← family (idx `K)
      let A ← family (← mkNumeral (mkConst ``Real) 1)
      let source ← family (a (obs ++ `complexSource) #[d,D,hD,mkApp u j])
      let r ← mkAppM ``Subtype.mk #[idx `lam,field prop 2]
      let terminal ← family (← localLinear hUniv univ (mkApp (stat `Mterminal) r))
      let firstType := a (obs ++ `FirstMaskInput) #[d,β,ρ,source,S]
      withLocalDeclD `hfirst firstType fun hfirst => do
        let (final,finalType) ← nextTyped (a (root ++ `after_individual_bounds) p) fun hproofType =>
          forallBoundedTelescope hproofType (some 1) fun depth _ => do
            let xp := x.push depth[0]!
            let chain := (← inferType (a (termNS ++ `before_history) xp)).getAppArgs
            let c (k : Name) := a (termNS ++ `Chain ++ k) chain
            let f (k : Name) (j : Expr) := a (fac ++ k) (xp.push (mkApp e j))
            let right := f `actual_right j
            let left := f `actual_left j
            let kType := (← inferType right).bindingDomain!
            let zero ← mkNumeral kType 0
            let Rfin ← forallBoundedTelescope (← inferType right) (some 1) fun k _ => do
              mkLambdaFVars k (← family (← localLinear hUniv univ (mkApp right k[0]!)))
            let Lfin ← forallBoundedTelescope (← inferType left) (some 1) fun k _ => do
              mkLambdaFVars k (← family (← localLinear hUniv univ (mkApp left k[0]!)))
            let first := f `actual_first_buffer j
            let msmooth ← family (← mkAppM `JanetCartan.FiniteChain.Graph.IsBufferedLocalizer.smooth #[first])
            let mcompact ← family (← mkAppM `JanetCartan.FiniteChain.Graph.IsBufferedLocalizer.compactSupport #[first])
            let mrange ← family (← mkAppM `JanetCartan.FiniteChain.Graph.IsBufferedLocalizer.range #[first])
            let firstActual := mkAppN hfirst #[c `θ,c `fact0,c `H,c `fact2,
              ← family (mkApp (f `actual_masks j) zero),msmooth,mcompact,mrange,
              ← family (mkApp (f `actual_mask_jets j) zero),← family (mkApp (f `actual_even j) zero),
              ← family (f `actual_first_plateau j),← family (mkApp right zero),
              ← family (field (mkApp (f `actual_realization j) zero) 1)]
            let letters := a (root ++ `letters) (x ++ #[β,e])
            let target := `JanetCartan.ArbitraryAccuracy.SelectedLocalization.exists_observedChain_localizers_of_finite_terminal_masks
            let scaleArgs := (← inferType G).getAppArgs
            unless scaleArgs.size == 3 do throwError "changed actual restriction scale signature"
            let .forallE _ alpha _ _ ← whnf (← inferType letters) | throwError "missing actual signed alphabet"
            let h := mkAppN (mkConst target [.zero,.zero,.zero])
              (#[β,alpha] ++ scaleArgs ++ #[G,depth[0]!,letters,source,ρ,L,A,terminal,Rfin,Lfin,firstActual])
            logInfo "Actual finite masks and first-source input prepared."
            let h ← next h fun dom => forallBoundedTelescope dom (some 2) fun ka _ => do
              let l := Expr.proj ``Prod 0 ka[1]!
              let reflected := Expr.proj ``Prod 1 ka[1]!
              let rp := g ++ #[β,e,l,mkConst ``Bool.false,reflected]
              let T := a (reindex ++ `operator) rp
              let hT := a (reindex ++ `raw_bound) rp
              let hR := field (mkApp (f `actual_realization j) ka[0]!) 3
              let hC := mkApp (a `JanetCartan.PhysicalInitialization.OriginalSampledOperatorBounds.Low.fact0 fixed) l
              let C := (← inferType hC).appArg!
              let D := (← inferType (c `fact12)).appArg!
              let bound := a (obs ++ `uniform_near_cost) #[d,n,β,C,D,hC,c `fact12,ρ,T,
                ← family (mkApp right ka[0]!),hT,← family hR]
              mkLambdaFVars ka bound
            logInfo "Native signed near bound supplied."
            let h ← next h fun dom => forallBoundedTelescope dom (some 1) fun k _ => do
              let hL := down (mkApp (f `actual_realization j) k[0]!) 4
              let C := (← inferType (c `fact12)).appArg!
              let bound := a (obs ++ `uniform_low_cost) #[d,n,β,C,c `fact12,ρ,← family (mkApp left k[0]!),← family hL]
              mkLambdaFVars k bound
            logInfo "Native left localizer low bound supplied."
            let factors := (← inferType (a (fac ++ `fixed_before_current) xp)).getAppArgs
            let h ← next h fun dom => forallBoundedTelescope dom (some 3) fun kas t => do
              let k := kas[0]!
              let l := Expr.proj ``Prod 0 kas[1]!
              let reflected := Expr.proj ``Prod 1 kas[1]!
              let s := kas[2]!
              let make (j q : Expr) := pure (a (fac ++ `actual_between_masks)
                (xp ++ #[s,mkApp e j,k,l,reflected,mkConst ``Bool.false,q]))
              let positive (q : Expr) := a (fac ++ `Signed.fact0) (factors ++ #[s,l,mkConst ``Bool.false,q])
              let bound ← uniformDecay t β make positive
              mkLambdaFVars kas bound
            logInfo "Every actual reflected signed factor supplied."
            let makeQuant (which : Nat) (k s j q : Expr) : MetaM Expr := do
              let all := mkAppN (f `actual_adjacent_and_terminal j) #[k,s,q,mkConst ``Bool.false]
              forallBoundedTelescope (← inferType all) (some 1) fun v _ => do
                let raw := if which == 0 then Expr.proj ``And 0 (mkAppN all v) else Expr.proj ``And 1 (mkAppN all v)
                let result ← byName (obs ++ `nat_frequency_power) #[(`h,raw)]
                mkLambdaFVars v result
            let h ← next h fun dom => forallBoundedTelescope dom (some 2) fun ks t => do
              let bound ← uniformDecay t β (makeQuant 0 ks[0]! ks[1]!)
                (fun q => mkAppN (c `fact13) #[ks[1]!,q])
              mkLambdaFVars ks bound
            logInfo "Actual adjacent cross-localizer estimate supplied."
            let h ← next h fun dom => forallBoundedTelescope dom (some 2) fun ks t => do
              let bound ← uniformDecay t β (makeQuant 1 ks[0]! ks[1]!)
                (fun q => mkAppN (c `fact14) #[ks[1]!,q])
              mkLambdaFVars ks bound
            logInfo "All six finite-mask inputs constructed at native depth 2*n+1."
            mkLambdaFVars depth h
        storeExplicit (root ++ `observed_residual_powers) (p.push hfirst) final finalType
end JanetCartan.PhysicalInitialization.OriginalSampledChains
end
