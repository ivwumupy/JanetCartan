module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.CoefficientProfiles.Basic
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Frame
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalPrimarySourcePhaseGeometry
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Frame
import all JanetCartan.Iteration.PhysicalPrimary.OriginalPrimaryStrainMaskData
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEvent
import all JanetCartan.Iteration.PhysicalSampling.OriginalGraphResponse
import all JanetCartan.Iteration.PhysicalPrimary.OriginalFullResponse
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean

/-!
# Applications of the actual full coefficient producers

The native telescope and reached operator threshold are read from the checked
phase-frame leaf. `OriginalGraphResponse.B` identifies the SAME weak current,
so the row retained here is literally `OriginalRegular.Current.Q`, with its
prescribed affine extension. `OriginalPrimaryStrainMaskData.Native` supplies
the actual twice-Jacobian. The fixed cutoffs and their compact buffer are the
original ones, before any history. The resulting history-scale estimates are
inputs to the primary first mask and negative moments in
`main:eq:primary-strain` and `app:ch_regular:eq:source-tail` of paper-v2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.CoefficientProfiles.Template

open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.CoefficientProfiles.Native
private def math := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.CoefficientProfiles
private def phase := `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Native
private def op := `JanetCartan.PhysicalPrimary.OriginalOperatorProfiles
private def sourceA := `JanetCartan.PhysicalPrimary.OriginalPrimaryStrainMaskData.Native
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def rows := `JanetCartan.PhysicalPairs.OriginalMaskRows
private def regular := `JanetCartan.PhysicalInitialization.OriginalRegular

private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p

private def resultAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let mut type := (← getConstInfo key).type
  for _ in p do
    let .forallE _ _ body _ := type |
      throwError "primary coefficient profiles: changed telescope {key}"
    type := body
  return type.instantiateRev p

private def bodyAt (e : Expr) : MetaM Expr := do
  let info ← getConstInfo e.getAppFn.constName!
  let some value := info.value? (allowOpaque := true) |
    throwError "primary coefficient profiles: unavailable original body {info.name}"
  return ((value.instantiateLevelParams info.levelParams e.getAppFn.constLevels!).beta
    e.getAppArgs).headBeta

private def termWith (p : List (Name × Expr)) (code : String) : MetaM Expr :=
  Term.TermElabM.run' (PhysicalBackground.NativeReferenceSourceTemplate.termWith p code)

/-- Apply the ordinary smoothness restriction with its already known normed
spaces. Re-inferring these spaces would unfold the entire native input type. -/
private def restrictSmooth (type U h : Expr) : MetaM (Expr × Expr) := do
  unless type.isAppOfArity ``ContDiff 10 do
    throwError "primary coefficient profiles: global smoothness signature changed"
  let a := type.getAppArgs
  let levels := type.getAppFn.constLevels!
  let proof := mkAppN (mkConst ``ContDiff.contDiffOn levels)
    (a[:8].toArray ++ #[U, a[9]!, a[8]!, h])
  let target := mkAppN (mkConst ``ContDiffOn levels) (a.push U)
  return (proof, target)

private def nativeTelescope (type : Expr)
    (go : Array Expr → Expr → MetaM Unit) : MetaM Unit := loop 51 type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0, type, p => go p (type.instantiateRev p)
    | k + 1, type, p => do
      let .forallE name domain body bi := type.consumeMData |
        throwError "primary coefficient profiles: native telescope ended at {p.size}"
      let domain := domain.instantiateRev p
      if bi == .instImplicit then
        withLocalDecl name bi domain fun x => loop k body (p.push x)
      else
        withLocalDeclNoLocalInstanceUpdate name bi domain fun x => loop k body (p.push x)

private structure Context where
  native51 : Array Expr
  weak38 : Array Expr
  operator33 : Array Expr

/-- Read the actual graph/current solely from the published native types;
no raw-source or response proof is unfolded to recover an analytic premise. -/
private def withContext (go : Context → MetaM Unit) : MetaM Unit := do
  nativeTelescope (← getConstInfo (phase ++ `operator_reached)).type fun p reached => do
    let source ← resultAt
      `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.uncut_response_jets p
    let some graph := source.find? (·.isAppOfArity
        `JanetCartan.PhysicalSampling.OriginalGraphResponse.B 42) |
      throwError "primary coefficient profiles: original graph42 is missing"
    if graph.hasLooseBVars then
      throwError "primary coefficient profiles: graph depends on a later derivative order"
    let full ← bodyAt graph
    unless full.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalFullResponse.B 38 do
      throwError "primary coefficient profiles: original weak current38 changed"
    unless reached.isAppOfArity ``LE.le 4 do
      throwError "primary coefficient profiles: original threshold bound changed"
    let S := reached.getAppArgs[2]!
    unless S.isAppOfArity (op ++ `S) 33 do
      throwError "primary coefficient profiles: original operator33 changed"
    go ⟨p, full.getAppArgs, S.getAppArgs⟩

private def save (key : Name) (p : Array Expr) (proof target : Expr)
    (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type, value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam ||
        e.hasLooseBVars || e.hasSorry then
      throwError "primary coefficient profiles: unresolved or later input in {key}"
    let missing := e.getUsedConstants.filter fun n => (env.find? n).isNone
    unless missing.isEmpty do
      throwError "primary coefficient profiles: missing original metadata in {key}: {missing}"
  let (type, value) := Lean.ShareCommon.shareCommon (type, value)
  let name := root ++ key
  IO.println s!"Kernel checking original primary coefficient {key}/{p.size}"
  (← IO.getStdout).flush
  if data then
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  addDocStringCore name "The SAME full Current.Q, actual twice-Jacobian, and original fixed source cutoffs on the entire original source chart. All prices precede the history; every jet uses the true historyScale R and the original coefficient producer (main:eq:primary-strain; app:ch_regular:eq:source-tail)."
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
    throwError "primary coefficient profiles: nonstandard axioms in {name}: {axioms}"
  logInfo m!"PASS original primary coefficient {key}/{p.size}: {axioms}"

private def compactBuffer (c : Context) : MetaM (Expr × Expr × Expr) := do
  let p := c.native51
  let fixed := c.weak38[:23].toArray
  let n := app ``Nat.add #[p[0]!, mkNatLit 1]
  let original := #[n] ++ fixed[1:21].toArray
  let cap := app `JanetCartan.PhysicalNormalInverse.strongCappedExtra
    #[n, p[1]!, original[20]!]
  let f := app (regular ++ `f) fixed
  let ft ← resultAt (regular ++ `f) fixed
  let fa := ft.getAppArgs
  let args := #[p[0]!, p[1]!,
    app `JanetCartan.PhysicalInitialization.OriginalProtected.r original,
    app `JanetCartan.PhysicalSeed.SelectedBoundary.rMeasure (original.set! 20 cap),
    fa[fa.size - 2]!, fa.back!, f, app (regular ++ `r) fixed]
  let hUS := app `JanetCartan.PhysicalPairs.OriginalMaskGeometry.chart_buffer args
  let bt ← resultAt `JanetCartan.PhysicalPairs.OriginalMaskGeometry.chart_buffer args
  let S := bt.appArg!
  let sa := S.getAppArgs
  let hS ← mkAppM ``isCompact_closedBall #[sa[sa.size - 2]!, sa.back!]
  return (S, hS, hUS)

private def scales (c : Context) : MetaM (Expr × Expr × Expr) := do
  let p := c.native51
  let hInitial ← mkAppM ``le_trans
    #[app (op ++ `fact0) c.operator33, app (phase ++ `operator_reached) p]
  let facts ← mkAppM ``JanetCartan.PhysicalMean.fixedPicard_history_scale_facts
    #[hInitial, p[46]!]
  return (.proj ``And 0 facts, .proj ``And 0 (.proj ``And 1 facts),
    .proj ``And 0 (.proj ``And 1 (.proj ``And 1 facts)))

elab "publish_original_primary_coefficient_profiles " mode:num : command => liftTermElabM do
  unless mode.getNat < 10 do throwError "primary coefficient profiles: unknown mode"
  withContext fun c => do
    let p := c.native51
    let fixed := p[:44].toArray
    let native50 := p[:50].toArray
    let original23 := c.weak38[:23].toArray
    let chart := app (masks ++ `chart) original23
    let n := app ``Nat.add #[p[0]!, mkNatLit 1]
    let N := app ``JanetCartan.embeddingDimension #[n]
    if mode.getNat == 0 then
      for (key, smooth) in [(`χ₂, `χ₂_smooth), (`χsrc, `χsrc_smooth)] do
        let hs := app (masks ++ smooth) original23
        let st ← resultAt (masks ++ smooth) original23
        let χ := st.appArg!
        let named := app (root ++ key) fixed
        save key fixed χ (← mkArrow st.getAppArgs[2]! st.getAppArgs[5]!) true
        let target := st.replace fun e => if e == χ then some named else none
        save (key.appendAfter "_global_smooth") fixed hs target
        let hs := app (root ++ key.appendAfter "_global_smooth") fixed
        let (hsOn, targetOn) ← restrictSmooth target chart hs
        save (key.appendAfter "_smooth") fixed hsOn targetOn
      return
    if mode.getNat == 1 then
      for (key, value, positive) in [
          (`CQ, app (op ++ `AQ) c.operator33, app (op ++ `fact1) c.operator33),
          (`CA, app (sourceA ++ `C) fixed, app (sourceA ++ `C_nonneg) fixed)] do
        save key fixed value (← mkArrow (mkConst ``Nat) (mkConst ``Real)) true
        let named := app (root ++ key) fixed
        save (key.appendAfter "_nonneg") fixed positive
          ((← resultAt positive.getAppFn.constName! positive.getAppArgs).replace
            fun e => if e == value then some named else none)
      return
    if mode.getNat == 2 then
      let (S, _, _) ← compactBuffer c
      for (key, mask) in [(`X, `χ₂), (`Y, `χsrc)] do
        let χ := app (root ++ mask) fixed
        let price := app (rows ++ `cutoffPrice) #[n, S, χ]
        let positive := app (rows ++ `cutoffPrice_nonneg) #[n, S, χ]
        save key fixed price (← mkArrow (mkConst ``Nat) (mkConst ``Real)) true
        let named := app (root ++ key) fixed
        save (key.appendAfter "_nonneg") fixed positive
          ((← resultAt (rows ++ `cutoffPrice_nonneg) #[n, S, χ]).replace
            fun e => if e == price then some named else none)
      return
    if mode.getNat == 3 then
      let Q := app (regular ++ `Current.Q) c.weak38
      let named := app (root ++ `Q) p
      let type ← resultAt (regular ++ `Current.Q) c.weak38
      save `Q p Q type true
      save `Q_eq_current p (mkAppN (mkConst ``Eq.refl [.succ .zero]) #[type, Q])
        (mkAppN (mkConst ``Eq [.succ .zero]) #[type, named, Q])
      return
    if mode.getNat == 4 then
      let A := app (sourceA ++ `A) native50
      let named := app (root ++ `A) native50
      let type ← resultAt (sourceA ++ `A) native50
      save `A native50 A type true
      save `A_eq_original native50 (mkAppN (mkConst ``Eq.refl [.succ .zero]) #[type, A])
        (mkAppN (mkConst ``Eq [.succ .zero]) #[type, named, A])
      return
    if mode.getNat == 5 then
      let args := c.operator33 ++ #[p[44]!, app (phase ++ `operator_reached) p] ++ p[46:50].toArray
      let cont := app (op ++ `continuation) args
      let ct ← whnfR (← resultAt (op ++ `continuation) args)
      let qt := ct.getAppArgs[0]!
      let rawQ := qt.appArg!
      let Q := app (root ++ `Q) p
      let target := qt.replace fun e => if e == rawQ then some Q else none
      save `Q_global_smooth p (.proj ``And 0 cont) target
      let hs := app (root ++ `Q_global_smooth) p
      let (hsOn, targetOn) ← restrictSmooth target chart hs
      save `Q_smooth p hsOn targetOn
      return
    if mode.getNat == 6 then
      let A := app (sourceA ++ `A) native50
      let named := app (root ++ `A) native50
      let hs := app (sourceA ++ `smooth) native50
      let target := (← resultAt (sourceA ++ `smooth) native50).replace
        fun e => if e == A then some named else none
      save `A_global_smooth native50 hs target
      let hs := app (root ++ `A_global_smooth) native50
      let (hsOn, targetOn) ← restrictSmooth target chart hs
      save `A_smooth p hsOn targetOn
      return
    let (hR, hT, hTR) ← scales c
    let T := app ``JanetCartan.currentCoefficientScale #[p[44]!, p[46]!]
    let R := app ``JanetCartan.historyScale
      #[p[44]!, mkConst ``JanetCartan.growthExponent, p[46]!]
    if mode.getNat == 7 then
      let (S, hS, hUS) ← compactBuffer c
      let args := c.operator33 ++ #[p[44]!, app (phase ++ `operator_reached) p] ++ p[46:50].toArray
      let cont := app (op ++ `continuation) args
      let hp := Expr.proj ``And 0 (mkAppN (.proj ``And 1 (.proj ``And 1 cont)) #[S, hS])
      let args := #[n, app (root ++ `Q) p, chart, S, hS, hUS,
        app (root ++ `Q_global_smooth) p, c.operator33[28]!, T, R,
        app (root ++ `CQ) fixed, hT, hTR, app (root ++ `CQ_nonneg) fixed, hp]
      let key := math ++ `stress_jets_on_chart
      save `Q_jets p (app key args) (← resultAt key args)
      return
    if mode.getNat == 8 then
      let hTzero ← termWith [(`hT, hT)] "zero_le_one.trans hT"
      let args := #[n, N, app (root ++ `A) native50, chart, T, R,
        app (root ++ `CA) fixed, hTzero, hTR, app (root ++ `CA_nonneg) fixed,
        app (sourceA ++ `jets) native50]
      let key := math ++ `matrix_coefficient_jets_mono
      save `A_jets p (app key args) (← resultAt key args)
      return
    let (S, hS, hUS) ← compactBuffer c
    for (mask, cost) in [(`χ₂, `X), (`χsrc, `Y)] do
      let χ := app (root ++ mask) fixed
      let hs := app (root ++ mask.appendAfter "_global_smooth") fixed
      let args := #[n, S, chart, hS, hUS, χ, hs, R, hR]
      let price := app (rows ++ `cutoffPrice) #[n, S, χ]
      let named := app (root ++ cost) fixed
      let target := (← resultAt (rows ++ `cutoff_jets) args).replace fun e =>
        if e == price then some named else none
      save (mask.appendAfter "_jets") p (app (rows ++ `cutoff_jets) args) target

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.CoefficientProfiles.Template
end
