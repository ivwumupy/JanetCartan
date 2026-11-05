module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Frame
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Frame
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean
/-!
# Checked applications of the original finite-menu phase estimates

This command applies the retained original frame profiles to the same finite
radial menu and transfers its joint representative to the literal ordinary
`group_phase`. It creates no new phase and adds no phase-profile hypothesis
(`main:eq:primary-strain`, `app:ch_regular:eq:source-tail`). The generated proof
terms are checked by Lean and their closed dependency graphs are audited.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Template
open Lean Meta Elab
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def ob := `JanetCartan.PhysicalSeed.OriginalBoundary
private def col := `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def math := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles
private def chooseSpec (h : Expr) : MetaM Expr := mkAppM ``Classical.choose_spec #[h]
private def choose (h : Expr) : MetaM Expr := mkAppM ``Classical.choose #[h]

private structure CostContext where
  native51 : Array Expr
  graph42 : Array Expr
  fixed23 : Array Expr
  radial11 : Array Expr
  op33 : Array Expr

private def costTelescope (type : Expr) (go : Array Expr → Expr → MetaM Unit) : MetaM Unit :=
  loop 51 type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0, type, p => go p (type.instantiateRev p)
    | k + 1, type, p => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "ordinary phase: published native telescope ended at {p.size}"
      let domain := domain.instantiateRev p
      if bi == .instImplicit then
        withLocalDecl name bi domain fun x => loop k body (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi domain fun x => loop k body (p.push x)

/-- Read only the already published original frame types. The graph is the
literal native response target's graph, independent of its later jet order;
the operator data are the literal left side of `operator_reached`. -/
private def withCostPhase (next : CostContext → MetaM Unit) : MetaM Unit := do
  let info ← getConstInfo (ns ++ `operator_reached)
  costTelescope info.type fun p reached => do
    let source ← resultAt `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.uncut_response_jets p
    let some graph := source.find? (·.isAppOfArity
        `JanetCartan.PhysicalSampling.OriginalGraphResponse.B 42) |
      throwError "ordinary phase: published native target lost the original graph42"
    if graph.hasLooseBVars then
      throwError "ordinary phase: original graph depends on a later derivative order"
    unless reached.isAppOfArity ``LE.le 4 do
      throwError "ordinary phase: original reached operator bound changed"
    let S := reached.getAppArgs[2]!
    unless S.isAppOfArity (op ++ `S) 33 do
      throwError "ordinary phase: original operator33 changed"
    let gp := graph.getAppArgs
    let stage := (← resultAt (quad ++ `group_phase) gp[:37].toArray).bindingDomain!.getAppArgs[2]!
    unless stage.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalRegular.Graph.S 34 do
      throwError "ordinary phase: original source chart23 changed"
    let radial ← bodyAt (app (quad ++ `group_phase) gp)
    unless radial.isAppOfArity (quad ++ `radialCarrier) 11 do
      throwError "ordinary phase: original radial scalar changed"
    next ⟨p, gp, stage.getAppArgs[:23].toArray, radial.getAppArgs, S.getAppArgs⟩

private def ordinaryData (c : CostContext) : MetaM (Expr × Expr × Array Expr) := do
  let f := c.fixed23
  let n := c.radial11[0]!
  let hn := c.native51[1]!
  let original := #[n] ++ f[1:21].toArray
  let cap := app `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,hn,original[20]!]
  let selected := original.set! 20 cap
  let hr := app (reg ++ `screened_pos) #[n,hn,
    app `JanetCartan.PhysicalInitialization.OriginalProtected.r original,
    app `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure selected,
    app `JanetCartan.PhysicalInitialization.OriginalProtected.fact2 original,
    app `JanetCartan.PhysicalSeed.SelectedBoundary.hrMeasure selected]
  let r := (← resultAt hr.getAppFn.constName! hr.getAppArgs).appArg!
  return (r,hr,original)
private def publishCost (mode : Nat) : MetaM Unit := withCostPhase fun c => do
  let p := c.native51
  let fixed := p[:44].toArray
  let native := p[:51].toArray
  let phaseParams := native
  let ca := c.radial11
  let n := ca[0]!
  let G := ca[5]!
  let phase := app (quad ++ `group_phase) c.graph42
  let namedPhase := app (ns ++ `phase) phaseParams
  if mode == 0 then
    let (r,hr,_) ← ordinaryData c
    let hD := app (ob ++ `hD) #[n,p[1]!]
    let ht ← resultAt (ob ++ `hD) #[n,p[1]!]
    let actualGroups ← bodyAt G
    let fin ← synthInstance (mkApp (mkConst ``Fintype [.zero]) actualGroups)
    let args := #[n,p[1]!,ht.getAppArgs[ht.getAppNumArgs-2]!,ht.appArg!,hD,G,fin,
      ca[6]!,ca[7]!,r,hr,app (op ++ `AQ) c.op33,app (op ++ `fact1) c.op33]
    save `joint_cost fixed (app (fr ++ `menu_cost) args) (← resultAt (fr ++ `menu_cost) args)
    return
  let cost := app (ns ++ `joint_cost) fixed
  let D := app (ns ++ `jointProfile) fixed
  let P := app (ns ++ `P) fixed
  if mode == 1 then
    save `jointProfile fixed (← choose cost) (← mkArrow (mkConst ``Nat) (mkConst ``Real)) true
    return
  if mode == 2 then
    let value ← withLocalDeclD `q (mkConst ``Nat) fun q =>
      mkLambdaFVars #[q] (mkApp D (app ``Nat.add #[q,mkNatLit 1]))
    save `P fixed value (← mkArrow (mkConst ``Nat) (mkConst ``Real)) true
    return
  if mode == 3 then
    let nonneg := Expr.proj ``And 0 (← chooseSpec cost)
    let zero ← mkNumeral (mkConst ``Real) 0
    withLocalDeclD `q (mkConst ``Nat) fun q => do
      let proof := mkApp nonneg (app ``Nat.add #[q,mkNatLit 1])
      let target ← mkAppM ``LE.le #[zero,mkApp P q]
      save `P_nonneg fixed (← mkLambdaFVars #[q] proof) (← mkForallFVars #[q] target)
    return
  if mode == 4 then
    save `phase phaseParams phase (← resultAt (quad ++ `group_phase) c.graph42) true
    return
  if mode == 5 then
    save `phase_eq_group_phase phaseParams (← mkEqRefl phase) (← mkEq namedPhase phase)
    return
  let T := app `JanetCartan.currentCoefficientScale #[p[44]!,p[46]!]
  let hT := app (fr ++ `current_scale_one) #[app (op ++ `S) c.op33,p[44]!,
    app (op ++ `fact0) c.op33,app (ns ++ `operator_reached) native,p[46]!]
  let f := c.fixed23
  let U := app (masks ++ `chart) f
  let Z := app (col ++ `Scolor) c.graph42[:22].toArray
  if mode == 6 then
    let spec ← chooseSpec cost
    let draw ← choose cost
    let low ← withLocalDeclD `g G fun g =>
      mkLambdaFVars #[g] (mkApp (app (quad ++ `Q_low) c.graph42) (mkApp ca[6]! g))
    let ready := mkAppN (.proj ``And 1 spec) #[app (quad ++ `Q) c.graph42,
      app (quad ++ `Q_smooth) c.graph42,low,T,hT,app (ns ++ `frame_profile) native]
    let Φ ← choose ready
    let facts ← chooseSpec ready
    let hΦ := Expr.proj ``And 0 facts
    let hg := Expr.proj ``And 0 (.proj ``And 1 facts)
    let hj := Expr.proj ``And 1 (.proj ``And 1 facts)
    let (_,_,original) ← ordinaryData c
    let cap := app `JanetCartan.PhysicalNormalInverse.strongCappedExtra #[n,p[1]!,original[20]!]
    let family := app (reg ++ `f) f
    let ft ← resultAt (reg ++ `f) f
    let a := ft.getAppArgs
    let bufferArgs := #[p[0]!,p[1]!,app `JanetCartan.PhysicalInitialization.OriginalProtected.r original,
      app `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure (original.set! 20 cap),
      a[a.size-2]!,a.back!,family,app (reg ++ `r) f]
    let buffer := app `JanetCartan.PhysicalPairs.OriginalMaskGeometry.chart_buffer bufferArgs
    let bt ← resultAt `JanetCartan.PhysicalPairs.OriginalMaskGeometry.chart_buffer bufferArgs
    let S := bt.appArg!
    withLocalDeclD `g G fun g => do
      let zType ← mkAppM ``Subtype #[mkApp Z g]
      withLocalDeclD `z zType fun z => do
        let args := #[n,G,Z,Φ,hΦ,phase,U,S,buffer,hg,T,hT,draw,.proj ``And 0 spec,hj,g,z]
        let theoremName := math ++ `ordinary_phase_of_joint_germ
        let target := (← resultAt theoremName args).replace fun e =>
          if e == draw then some D else if e == phase then some namedPhase else none
        save `ordinary_spec native (← mkLambdaFVars #[g,z] (app theoremName args))
          (← mkForallFVars #[g,z] target)
    return
  let spec := app (ns ++ `ordinary_spec) native
  let st ← resultAt (ns ++ `ordinary_spec) native
  forallBoundedTelescope st (some 2) fun gz result => do
    let all := native ++ gz
    let atGroup := mkAppN spec gz
    let result ← whnfR result
    unless result.isAppOfArity ``And 2 do throwError "ordinary phase: native specification changed"
    if mode == 7 then
      save `smooth all (.proj ``And 0 atGroup) result.getAppArgs[0]!
      return
    if mode == 10 then
      withLocalDeclD `R (mkConst ``Real) fun R => do
        let htrType ← mkAppM ``LE.le #[T,R]
        withLocalDeclD `hTR htrType fun hTR => do
          let hz ← Term.TermElabM.run' <|
            PhysicalBackground.NativeReferenceSourceTemplate.termWith [(`hT,hT)] "(zero_le_one.trans hT)"
          let args := #[n,mkAppN namedPhase #[gz[0]!,Expr.proj ``Subtype 0 gz[1]!],U,P,T,R,
            app (ns ++ `P_nonneg) fixed,hz,hTR,app (ns ++ `jets) all]
          let lemmaName := math ++ `ordinary_phase_jets_mono
          save `jets_of_le (all ++ #[R,hTR]) (app lemmaName args) (← resultAt lemmaName args)
      return
    forallBoundedTelescope result.appArg! (some 2) fun point target => do
      let target ← whnfR target
      unless target.isAppOfArity ``And 2 do throwError "ordinary phase: native pointwise specification changed"
      let hp := mkAppN (.proj ``And 1 atGroup) point
      if mode == 8 then
        let t := target.getAppArgs[0]!
        unless t.isAppOfArity ``LE.le 4 do throwError "ordinary phase: first derivative norm changed"
        let wanted := mkAppN t.getAppFn (t.getAppArgs.set! 3 (mkApp P (mkNatLit 0)))
        save `gradient_upper all (← mkLambdaFVars point (.proj ``And 0 hp)) (← mkForallFVars point wanted)
        return
      forallBoundedTelescope target.appArg! (some 1) fun q t => do
        unless t.isAppOfArity ``LE.le 4 do throwError "ordinary phase: higher derivative norm changed"
        let rhs ← mkAppM ``HMul.hMul #[mkApp P q[0]!,← mkAppM ``HPow.hPow #[T,q[0]!]]
        let wanted := mkAppN t.getAppFn (t.getAppArgs.set! 3 rhs)
        save `jets all (← mkLambdaFVars (point ++ q) (mkAppN (.proj ``And 1 hp) q))
          (← mkForallFVars (point ++ q) wanted)
end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Template
end
