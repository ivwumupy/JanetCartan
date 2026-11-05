module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.GraphRemainder
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.UncutObservation
public import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometry

/-!
# Original uncut angular source decay on arbitrary primary labels

Apply the actual original observed chain and the native inverse remainder to
one family of already localized real sources. All geometric, coefficient,
contraction and gain inputs are supplied by the existing graph. The only
source assumptions are its actual support, low norm, first-mask estimate and
negative moments, all produced from the raw primary profiles in the parent
construction. The final observation uses `χ₃ * Current.Inv(u)` without another
`χ₂` and is on the original open core (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

@[expose] noncomputable section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual

private theorem contractive_after_eq {E : Type*} [Norm E] {a b : E}
    (h : a = b) (hb : ‖a‖ ≤ (1/2 : ℝ)) : ‖b‖ < 1 := by
  rw [← h]
  exact hb.trans_lt (by norm_num)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.Template

open Lean Meta Elab Command

private def beforeLets : Expr → Array Name
  | .forallE n _ body _ => #[n] ++ beforeLets body
  | .mdata _ e => beforeLets e
  | _ => #[]

private def withNext (name : Name) (f : Expr) (go : Expr → Expr → MetaM Unit) : MetaM Unit := do
  let type ← inferType f
  unless type.isForall do throwError "primary source observation: missing original input {name}"
  withLocalDeclD name type.bindingDomain! fun x => go x (mkApp f x)

/-- The actual native inverse is the SAME Neumann inverse of the measured
operator occurring in the observed chains, by the existing exact identity. -/
elab "identify_original_primary_graph_inverse" : command => liftTermElabM do
  withGraph fun x g weak coeff graph =>
    withLocalDeclD `originalHistory graph fun i => do
      let (w,_,_,_,_) ← currentAt g weak coeff i
      let cur (key : Name) := app (regular ++ `Current ++ key) w
      let eqK := app `JanetCartan.PhysicalInitialization.OriginalSampledObserved.native_residual_identity w
      let rawInv := ((← getConstInfo (regular ++ `Current.Inv)).value! (allowOpaque := true)).beta w
      unless rawInv.isAppOfArity ``JanetCartan.neumannInverse 4 do
        throwError "primary source observation: original Inv is not its literal Neumann series"
      let inverseMap := mkAppN rawInv.getAppFn rawInv.getAppArgs[:3].toArray
      let proof ← mkAppM ``congrArg #[inverseMap,eqK]
      let target ← mkEq (cur `Inv) (← inferType proof).getAppArgs[2]!
      discard <| save `inverse_eq_measured (x.push i) proof false (some target)

identify_original_primary_graph_inverse

elab "observe_original_primary_graph_source" : command => liftTermElabM do
  withSource fun p g weak coeff _ => do
    let x := p[:36].toArray
    let fixed := g[:23].toArray
    let β := p[36]!
    let indices := p[37]!
    let u := p[38]!
    let d := x[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let stat (key : Name) := app (regular ++ key) fixed
    let f := stat `f
    let fa := (← inferType f).getAppArgs
    let E ← inferType fa[2]!
    let W := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source.W fixed
    let hW := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source.W_measurable fixed
    let χ := stat `χ₂
    let ψ := stat `χ₃
    let r ← mkAppM ``ContDiffBump.rIn #[χ]
    let V ← mkAppM ``Metric.ball #[fa[2]!,r]
    let hV := app `JanetCartan.PhysicalInitialization.OriginalSampledObserved.native_norm_ball #[n,r]
    let hψW ← mkAppM ``Set.Subset.trans
      #[app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.χ₃_support_chart fixed,stat `hUW]
    let hχW ← mkAppM ``Set.Subset.trans
      #[app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.χ₂_support_chart fixed,stat `hUW]
    let hInner := app `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry.inner_ball_subset_tsupport #[n,χ]
    let hVW ← mkAppM ``Set.Subset.trans #[hInner,hχW]
    let hnest := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.χ₃_on_χ₂ fixed
    let plateau ← forallBoundedTelescope (← inferType hInner) (some 2) fun y _ =>
      mkLambdaFVars y (mkAppN hnest #[y[0]!,mkAppN hInner y])
    let hob := app `JanetCartan.PhysicalInitialization.OriginalSampledObserved.bounded_mask
      #[E,stat `output,stat `fact18]
    withNext `hsupport (app observed p) fun hsupport supp =>
      withNext `hSourceNorm supp fun hlow low => do
        let onW := mkAppN low #[W,hW]
        withNext `hfirst onW fun hfirst chain => do
          let rem := app (root ++ `unobserved_remainder) p
          forallBoundedTelescope (← inferType rem) (some 4) fun sourceData _ => do
            unless sourceData.size == 4 do
              throwError "primary source observation: moment/count interface changed"
            let s := sourceData[3]!
            let known ← withLocalDeclD `i β fun i => do
              let (w,_,rho,_,window) ← currentAt g weak coeff (mkApp indices i)
              let cur (key : Name) := app (regular ++ `Current ++ key) w
              let fam (value : Expr) := mkLambdaFVars #[i] value
              let one ← mkNumeral (mkConst ``Real) 1
              let hA ← mkAppOptM ``zero_le_one #[some (mkConst ``Real),none,none,none,none]
              let plus ← mkNumeral (mkApp (mkConst ``Fin) (mkNatLit 2)) 1
              let eqK := app `JanetCartan.PhysicalInitialization.OriginalSampledObserved.native_residual_identity w
              let hk ← mkAppM ``contractive_after_eq #[eqK,cur `fact6]
              let values : Array (Name × Expr) := #[
                (`d,d),(`ι,β),(`Ω,fa[1]!),(`center,fa[2]!),(`RQ,fa[3]!),(`A₀,fa[4]!),(`K,fa[5]!),(`M,fa[6]!),
                (`f,f),(`hK,app `JanetCartan.PhysicalInitialization.OriginalProtected.fact14 (#[n] ++ fixed[1:21].toArray)),
                (`L₀,stat `L),(`hL₀,stat `hL),(`Q,← fam (cur `Q)),(`B,← fam (cur `B)),
                (`W₁,← fam (cur `W₁)),(`retarded,← fam (mkApp (cur `retarded) plus)),
                (`output,stat `output),(`ho,stat `fact17),(`hoc,stat `fact19),(`hob,hob),(`D,W),(`hD,hW),
                (`χ₂,χ),(`χ₃,ψ),(`χobs,ψ),(`hnest,hnest),(`hχ₃D,hψW),(`Vobs,W),(`Wcore,V),
                (`hVobs,hW),(`hWcore,hV),(`hχobsV,hψW),(`hWV,hVW),(`hχobsCore,plateau),
                (`ρ,← fam rho),(`A,← fam one),(`hρ,← fam (part window 1)),(`hA,← fam hA),
                (`s,s),(`u,u),(`hsupport,hsupport),(`hKrecut,← fam hk)]
              pure values
            let key := root ++ `uncut_angular_rapidDecayAt_of_original_remainder
            let info ← getConstInfo key
            let names := beforeLets info.type
            unless names.back! == `hsupport do
              throwError "primary source observation: genuine uncut theorem telescope changed"
            let args ← names.mapM fun name => do
              let some (_,value) := known.find? (·.1 == name)
                | throwError "primary source observation: unsupplied native coordinate {name}"
              pure value
            let some (_,hK) := known.find? (·.1 == `hKrecut)
              | throwError "primary source observation: missing actual contraction"
            let proof := mkAppN (mkConst key (info.levelParams.map fun _ => .zero))
              (args ++ #[hK,mkApp chain s,mkAppN rem sourceData])
            let all := p ++ #[hsupport,hlow,hfirst] ++ sourceData
            discard <| save `neumann_rapid all proof

observe_original_primary_graph_source

elab "retain_original_primary_uncut_inverse" : command => liftTermElabM do
  forallBoundedTelescope (← getConstInfo (root ++ `neumann_rapid)).type (some 46) fun p target => do
    unless p.size == 46 && target.isAppOf ``JanetCartan.ArbitraryAccuracy.RapidDecayAt do
      throwError "primary source observation: full source46 rapid-decay interface changed"
    let oldField := target.appArg!
    let indices := p[37]!
    let graph := (← inferType indices).bindingBody!
    let g := graph.getAppArgs
    let fixed := g[:23].toArray
    let weak := fixed ++ #[g[25]!,app (regular ++ `Graph.regular_scale) g[:27].toArray] ++ g[27:34].toArray
    let reserve := app `JanetCartan.RegularSector.FiniteEvolution.sectorLowOrder #[g[0]!]
    let coeff := weak[:28].toArray ++ #[reserve,weak[28]!,weak[29]!,
      app (polynomial ++ `coefficient_reserve) #[g[0]!,weak[27]!,weak[30]!],weak[31]!]
    let whole ← lambdaBoundedTelescope oldField 1 fun i value => do
      let some inverse := value.find? (·.isAppOfArity ``JanetCartan.neumannInverse 4)
        | throwError "primary source observation: uncut Neumann inverse disappeared"
      let (w,_,_,_,_) ← currentAt g weak coeff (mkApp indices i[0]!)
      let expectedInv := app (regular ++ `Current.Inv) w
      let hInv := app (root ++ `inverse_eq_measured) (p[:36].toArray.push (mkApp indices i[0]!))
      let lift ← withLocalDeclD `inverse (← inferType inverse) fun inv =>
        mkLambdaFVars #[inv] (value.replace fun e => if e == inverse then some inv else none)
      let equality ← mkAppM ``congrArg #[lift,hInv]
      let eqType ← inferType equality
      unless (eqType.getAppArgs[1]!.find? (· == expectedInv)).isSome do
        throwError "primary source observation: actual current inverse was not retained"
      mkLambdaFVars i equality
    let fieldEq ← mkAppM ``funext #[whole]
    let newField := (← inferType fieldEq).getAppArgs[1]!
    let predicate ← withLocalDeclD `field (← inferType oldField) fun field =>
      mkLambdaFVars #[field] (mkApp target.appFn! field)
    let targetEq ← mkAppM ``congrArg #[predicate,fieldEq]
    let proof ← mkAppM ``Eq.mpr #[targetEq,app (root ++ `neumann_rapid) p]
    discard <| save `uncut_corrected_rapid p proof false (some (mkApp target.appFn! newField))

retain_original_primary_uncut_inverse

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.SourceResidual.Template
end
