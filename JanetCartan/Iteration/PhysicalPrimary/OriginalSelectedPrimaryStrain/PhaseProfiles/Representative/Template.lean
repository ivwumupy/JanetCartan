module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.HistoryScale
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Representative.Basic
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Representative.Basic
import all JanetCartan.Iteration.PhysicalPrimary.OriginalPrimarySourcePhaseGeometry
import all JanetCartan.Iteration.PhysicalPairs.OriginalMaskGeometry
import all JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean

/-!
# The original finite-menu representative in the primary source estimates

Read the already published literal phase and reached operator data. The
representative is exactly the choice from the same finite-menu cost and
same current frame, followed by a spatial slice. Its global smoothness and
source-chart germ are produced internally; the original phase estimates and
gradient compact transfer across that germ (`main:eq:primary-strain`,
`app:ch_regular:eq:source-tail` in paper-v2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.RepresentativeTemplate

open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Native
private def math := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles
private def op := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
private def quad := `JanetCartan.PhysicalPairs.SampledQuadrature
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

private def bodyAt (e : Expr) : MetaM Expr := do
  let info ← getConstInfo e.getAppFn.constName!
  return ((info.value! (allowOpaque := true)).instantiateLevelParams
    info.levelParams e.getAppFn.constLevels!).beta e.getAppArgs |>.headBeta

private def resultAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let mut type := (← getConstInfo key).type
  for _ in p do
    let .forallE _ _ body _ := type |
      throwError "primary representative: changed original telescope {key}"
    type := body
  return type.instantiateRev p

private def choose (h : Expr) : MetaM Expr := mkAppM ``Classical.choose #[h]
private def chooseSpec (h : Expr) : MetaM Expr := mkAppM ``Classical.choose_spec #[h]

private def originalTelescope (type : Expr) (go : Array Expr → Expr → MetaM Unit) : MetaM Unit :=
  loop 51 type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0, type, p => go p (type.instantiateRev p)
    | k + 1, type, p => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "primary representative: native telescope ended at {p.size}"
      let domain := domain.instantiateRev p
      if bi == .instImplicit then
        withLocalDecl name bi domain fun x => loop k body (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi domain fun x => loop k body (p.push x)

private structure Input where
  native51 : Array Expr
  graph42 : Array Expr
  n : Expr
  groups : Expr
  cubes : Expr
  chart : Expr
  buffer : Expr
  chart_in_buffer : Expr
  joint : Expr
  joint_smooth : Expr
  joint_germ : Expr

private def withInput (next : Input → MetaM Unit) : MetaM Unit := do
  let phaseInfo ← getConstInfo (root ++ `phase)
  originalTelescope phaseInfo.type fun p _ => do
    unless p.size == 51 do
      throwError "primary representative: actual native51 changed"
    let saved := ((phaseInfo.value! (allowOpaque := true)).beta p).headBeta
    unless saved.isAppOfArity (quad ++ `group_phase) 42 do
      throwError "primary representative: literal original graph42 phase changed"
    let gp := saved.getAppArgs
    let radial ← bodyAt saved
    unless radial.isAppOfArity (quad ++ `radialCarrier) 11 do
      throwError "primary representative: original radial carrier changed"
    let ca := radial.getAppArgs
    let n := ca[0]!
    let G := ca[5]!
    let thresholdType := (← resultAt (quad ++ `group_phase) gp[:37].toArray).bindingDomain!
    let stage := thresholdType.getAppArgs[2]!
    unless stage.isAppOfArity `JanetCartan.PhysicalInitialization.OriginalRegular.Graph.S 34 do
      throwError "primary representative: original source chart changed"
    let f := stage.getAppArgs[:23].toArray
    let U := app (masks ++ `chart) f
    let Z := app `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication.Scolor
      gp[:22].toArray
    let reached := app (root ++ `operator_reached) p
    let reachedType ← resultAt (root ++ `operator_reached) p
    let operatorThreshold := reachedType.getAppArgs[2]!
    unless operatorThreshold.isAppOfArity (op ++ `S) 33 do
      throwError "primary representative: original reached operator changed"
    let cp := operatorThreshold.getAppArgs
    let T := app ``JanetCartan.currentCoefficientScale #[p[44]!, p[46]!]
    let hT := app ``JanetCartan.PhysicalPairs.OriginalSignedFrames.current_scale_one
      #[operatorThreshold, p[44]!, app (op ++ `fact0) cp, reached, p[46]!]
    let cost := app (root ++ `joint_cost) p[:44].toArray
    let spec ← chooseSpec cost
    let low ← withLocalDeclD `group G fun g =>
      mkLambdaFVars #[g] (mkApp (app (quad ++ `Q_low) gp) (mkApp ca[6]! g))
    let ready := mkAppN (.proj ``And 1 spec)
      #[app (quad ++ `Q) gp, app (quad ++ `Q_smooth) gp, low, T, hT,
        app (root ++ `frame_profile) p]
    let joint ← choose ready
    let facts ← chooseSpec ready
    let original := #[n] ++ f[1:21].toArray
    let cap := app `JanetCartan.PhysicalNormalInverse.strongCappedExtra
      #[n, p[1]!, original[20]!]
    let family := app (reg ++ `f) f
    let a := (← resultAt (reg ++ `f) f).getAppArgs
    let bufferArgs := #[p[0]!, p[1]!,
      app `JanetCartan.PhysicalInitialization.OriginalProtected.r original,
      app `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure (original.set! 20 cap),
      a[a.size - 2]!, a.back!, family, app (reg ++ `r) f]
    let bufferProof := app ``JanetCartan.PhysicalPairs.OriginalMaskGeometry.chart_buffer bufferArgs
    let S := (← resultAt ``JanetCartan.PhysicalPairs.OriginalMaskGeometry.chart_buffer bufferArgs).appArg!
    next {
      native51 := p
      graph42 := gp
      n := n
      groups := G
      cubes := Z
      chart := U
      buffer := S
      chart_in_buffer := bufferProof
      joint := joint
      joint_smooth := .proj ``And 0 facts
      joint_germ := .proj ``And 0 (.proj ``And 1 facts) }

private def save (key : Name) (p : Array Expr) (proof target : Expr)
    (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  for e in #[type, value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "primary representative: unresolved original input in {key}"
  let (type, value) := Lean.ShareCommon.shareCommon (type, value)
  let name := root ++ key
  IO.println s!"Kernel checking actual ordinary primary representative {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {
      name := name
      levelParams := []
      type := type
      value := value
      hints := .regular 0
      safety := .safe }) (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  addDocStringCore name "The SAME finite-menu joint representative at the actual original current frame, spatially sliced at the unchanged colored node. Global smoothness, the original group_phase germ on the entire source chart, the original Ksource22 and fixed-price history-scale jets are produced from the existing original construction; no global smoothness of the raw phase, new source, cutoff, scale gate or analytic success premise is assumed (main:eq:primary-strain; app:ch_regular:eq:source-tail)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "primary representative: nonstandard axioms {name}: {axioms}"
  logInfo m!"PASS actual ordinary primary representative {key}/{p.size}: {axioms}"

private def publish (mode : Nat) : MetaM Unit := do
  unless mode ≤ 8 do throwError "primary representative: unknown field"
  withInput fun c => do
    let p := c.native51
    let joint := app (root ++ `jointRepresentative) p
    if mode == 0 then
      save `jointRepresentative p c.joint (← inferType c.joint) true
      return
    if mode == 1 then
      let target := (← inferType c.joint_smooth).replace fun e =>
        if e == c.joint then some joint else none
      save `jointRepresentative_smooth p c.joint_smooth target
      return
    forallBoundedTelescope (← resultAt (root ++ `smooth) p) (some 2) fun gz _ => do
      unless gz.size == 2 do throwError "primary representative: original group/node changed"
      let all := p ++ gz
      let raw := mkAppN (app (root ++ `phase) p)
        #[gz[0]!, .proj ``Subtype 0 gz[1]!]
      let rep := app (root ++ `representative) all
      if mode == 2 then
        let value ← withLocalDeclD `x (mkApp (mkConst ``JanetCartan.Euclidean) c.n) fun x => do
          let pair ← mkAppM ``Prod.mk #[x, Expr.proj ``Subtype 0 gz[1]!]
          mkLambdaFVars #[x] (mkApp (mkApp joint gz[0]!) pair)
        save `representative all value (← inferType value) true
        return
      if mode == 3 then
        let args := #[c.n, c.groups, c.cubes, joint, c.joint_smooth,
          app (root ++ `phase) p, c.chart, c.buffer, c.chart_in_buffer,
          c.joint_germ, gz[0]!, gz[1]!]
        let proof := app ``spatial_representative_spec args
        let target ← resultAt ``spatial_representative_spec args
        unless target.isAppOfArity ``And 2 do
          throwError "primary representative: global smooth/germ specification changed"
        let literalSlice := target.getAppArgs[0]!.appArg!
        let target := target.replace fun e => if e == literalSlice then some rep else none
        save `representative_spec all proof target
        return
      let spec := app (root ++ `representative_spec) all
      let specType ← resultAt (root ++ `representative_spec) all
      if mode == 4 then
        save `representative_smooth all (.proj ``And 0 spec) specType.getAppArgs[0]!
        return
      if mode == 5 then
        save `representative_germ all (.proj ``And 1 spec) specType.appArg!
        return
      let germ := app (root ++ `representative_germ) all
      let P := app (root ++ `P) p[:44].toArray
      if mode == 6 then
        let args := #[c.n, raw, rep, c.chart, mkApp P (mkNatLit 0), germ,
          app (root ++ `gradient_upper) all]
        let proof := app ``representative_upper_of_germ args
        save `representative_gradient_upper all proof (← resultAt ``representative_upper_of_germ args)
        return
      if mode == 7 then
        let R := app ``JanetCartan.historyScale
          #[p[44]!, mkConst ``JanetCartan.growthExponent, p[46]!]
        let args := #[c.n, raw, rep, c.chart, P, R, germ,
          app (root ++ `jets_at_historyScale) all]
        let proof := app ``representative_jets_of_germ args
        save `representative_jets_at_historyScale all proof
          (← resultAt ``representative_jets_of_germ args)
        return
      let K := app `JanetCartan.PhysicalInitialization.OriginalColoredProtectionApplication.Ksource
        c.graph42[:22].toArray
      let gradient ← withLocalDeclD `x (mkApp (mkConst ``JanetCartan.Euclidean) c.n) fun x => do
        withLocalDeclD `hx (← mkAppM ``Membership.mem #[c.chart, x]) fun hx => do
          let original := app `JanetCartan.PhysicalPrimary.OriginalPrimarySourcePhaseGeometry.gradient_mem_source
            (c.graph42 ++ #[x, hx] ++ gz)
          mkLambdaFVars #[x, hx] original
      let args := #[c.n, raw, rep, c.chart, K, germ, gradient]
      let proof := app ``representative_gradient_of_germ args
      save `representative_gradient_mem_source all proof
        (← resultAt ``representative_gradient_of_germ args)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.RepresentativeTemplate
end
