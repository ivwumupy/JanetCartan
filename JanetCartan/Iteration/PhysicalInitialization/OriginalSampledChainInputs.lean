module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledTerminalFlow
public import JanetCartan.Iteration.PhysicalInitialization.OriginalSampledReindexing
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedObservedResidual.FiniteMaskReindexing
public meta import Lean

/-!
# Original source and individual estimates for observed powers

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
@[expose] public noncomputable section
namespace JanetCartan.PhysicalInitialization.OriginalSampledChains
open Set Metric FiniteChain.Graph ArbitraryAccuracy.ProtectedMasks
/-- The actual terminal support has the same strict inner frequency shell. -/
theorem terminal_lower_bound {n : ℕ} {m : LocalizerSymbol n} {R a b : ℝ}
    (h : tsupport m ⊆ closedBall 0 R ×ˢ PhysicalShells.frequencyAnnulus a b) :
    ∀ z ∈ tsupport m, a ≤ ‖z.2‖ := fun _ hz ↦ (h hz).2.1
/-- The native protected terminal remains in the original cone, not a larger
    replacement cone (`app:ch_regular:lem:finite-chain`). -/
theorem terminal_in_cone {d : ℕ} {m : LocalizerSymbol (d+1)}
    {S : Set (Euclidean (d+1) × Euclidean (d+1))} {K : Set (Euclidean (d+1))}
    (h : IsBufferedLocalizer m S (physicalProtectedRegion K)) :
    ∀ z ∈ tsupport m, NormedSpace.normalize z.2 ∈ K :=
  fun _ hz ↦ interior_subset (h.support_subset hz).2
end JanetCartan.PhysicalInitialization.OriginalSampledChains
end
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
  return mkAppN (mkConst ``Exists.intro [.zero]) #[t.getAppArgs[0]!,pred,value,proof]
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
        witness goal c fun g => witness g b fun g =>
          forallBoundedTelescope g (some 1) fun q t => do
            let probe ← make sample q[0]!
            let (_,_,C) ← decayScalars (mkApp probe v)
            let result ← witness t C fun t => do
              let t ← whnf t
              let body := t.getAppArgs[1]!
              let all ← forallBoundedTelescope body (some 2) fun iv _ => do
                let h ← make iv[0]! q[0]!
                mkLambdaFVars iv (mkApp h iv[1]!)
              mkAppM ``And.intro #[positive q[0]!,all]
            mkLambdaFVars q result

/- Supply the scale window, terminal observation, and actual signed low and
   polynomial costs. The actual finite-chain input is discharged in OriginalSampledChains. -/
run_cmd liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (termNS ++ `before_history)).type (some 36) fun x _ => do
    let args ← OriginalSampledTerminal.actualTerminalArguments x[:22].toArray x[22:24].toArray
    let fixed := args[26]!.getAppArgs
    let g := fixed ++ x[24:26].toArray ++ x[27:36].toArray
    let weak := fixed ++ #[g[25]!,a (reg ++ `Graph.regular_scale) g[:27].toArray] ++ g[27:34].toArray
    let d := x[0]!
    let reserve := a `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder #[d]
    let coeff := weak[:28].toArray ++ #[reserve,weak[28]!,weak[29]!,a (poly ++ `coefficient_reserve) #[d,weak[27]!,weak[30]!],weak[31]!]
    let hargs := #[d,weak[25]!,weak[28]!,a (reg ++ `Graph.S) g,a (op ++ `S) coeff]
    let I := a (poly ++ `GraphFamily) g
    let stat (k : Name) := a (termNS ++ `Static ++ k) args
    let buf := stat `fact4
    let smooth ← mkAppM `JanetCartan.FiniteChain.Graph.IsBufferedLocalizer.smooth #[buf]
    let compact ← mkAppM `JanetCartan.FiniteChain.Graph.IsBufferedLocalizer.compactSupport #[buf]
    let hann ← mkAppM ``terminal_lower_bound #[stat `fact9]
    let hterminal ← mkAppM ``terminal_in_cone #[buf]
    withLocalDeclD `β (mkSort .one) fun β => do
     withLocalDeclD `indices (← mkArrow β I) fun e => do
      let initial := a (obs ++ `for_reindexed_sources) (g ++ #[β,e])
      forallBoundedTelescope (← withTransparency .all <| whnf (← inferType initial)) (some 2) fun us _ => do
       withLocalDeclD `j β fun j => do
        let i := mkApp e j
        let raw ← mkAppM ``Subtype.val #[i]
        let idx (k : Name) := a (`JanetCartan.PhysicalPrimary.OriginalHistoryFamily.RawIndex ++ k) #[d,mkConst ``Unit,raw]
        let prop ← mkAppM ``Subtype.property #[i]
        let data := a (poly ++ `admitted_data) (hargs ++ #[a (op ++ `fact0) coeff,i])
        let family (v : Expr) := mkLambdaFVars #[j] v
        let ρ ← family (idx `lam)
        let L ← family (idx `K)
        let hρ ← family (field prop 2)
        let hL ← family (field data 3)
        let hLρ ← family (field data 4)
        let hscale ← family (field prop 4)
        let one ← mkNumeral (mkConst ``Real) 1
        let A ← family one
        let hA ← family (← byName `zero_le_one #[(`α,mkConst ``Real)])
        let hσ := mkConst (obs ++ `signed_gap_positive)
        let σ := (← inferType hσ).appArg!
        let r ← mkAppM ``Subtype.mk #[idx `lam,field prop 2]
        let Mt ← family (mkApp (stat `Mterminal) r)
        let hMt ← family (mkApp (stat `fact12) r)
        let withScale := mkAppN initial (us ++ #[ρ,L,A,σ,hρ,hL,hLρ,hσ,hscale,hA])
        forallBoundedTelescope (← inferType withScale) (some 1) fun hu _ => do
          let h := mkAppN withScale hu
          let h := mkAppN h #[stat `mi,smooth,compact,stat `a,stat `fact6,hann,hterminal,Mt,hMt]
          forallBoundedTelescope (← inferType h) (some 2) fun W _ => do
            let h := mkAppN h W
            withLetDecl `nativeObservation (← inferType h) h fun cached => do
              let h := cached
              logInfo "Original source, scale and terminal inputs fixed."
              let h ← next h fun dom => forallBoundedTelescope dom (some 1) fun letter _ => do
                unless letter.size == 1 do throwError "the signed-cost premise has {letter.size} binders: {dom}"
                let l := Expr.proj ``Prod 0 letter[0]!
                let reflected := Expr.proj ``Prod 1 letter[0]!
                mkLambdaFVars letter (a (reindex ++ `low) (g ++ #[β,e,l,mkConst ``Bool.false,reflected]))
              logInfo "Actual signed low costs supplied."
              let (h,resultType) ← nextTyped h fun dom => forallBoundedTelescope dom (some 1) fun letter _ => do
                unless letter.size == 1 do throwError "the signed-cost premise has {letter.size} binders: {dom}"
                let l := Expr.proj ``Prod 0 letter[0]!
                let reflected := Expr.proj ``Prod 1 letter[0]!
                let params := g ++ #[β,e,l,mkConst ``Bool.false,reflected]
                discard <| store (root ++ `letters) (x ++ #[β,e,letter[0]!]) (a (reindex ++ `local_operator) params) true
                mkLambdaFVars letter (a (reindex ++ `costs) params)
              logInfo "Actual polynomial costs supplied; checking the whole observation application."
              logInfo "Exact observation conclusion retained."
              let result ← mkLetFVars #[cached] h
              logInfo "Original observation proof shared and closed."
              storeExplicit (root ++ `after_individual_bounds) (x ++ #[β,e] ++ us ++ hu ++ W) result resultType

end JanetCartan.PhysicalInitialization.OriginalSampledChains
end
