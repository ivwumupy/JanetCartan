module

public meta import Lean
public meta import JanetCartan.Iteration.PhysicalNormalInverse.StrongToleranceApplication

/-!
# Actual PhysicalSeed source-family application with the protected outer weight

Consumer: `NativeRawSeedBudget`, and then the SAME current raw correction in
`NativeDensity` (`app:ch_background:prop:bg-current`,
`app:ch_background:eq:bg-Hsigma`, `new:sec:order-of-choices`).

The actualSource29 application supplies the existing c_sigma, not a newly
chosen source family. Only chi-independent seed/product geometry is extracted
from the old full source producer's INPUTS; its old chi, weighted limiting mean,
source cap and continuation are not used. The new chi is task74's ONE protected
cutoff on the already-selected21 tuple. There is no internal extra cap here.
-/

public meta section
namespace JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate
open Lean Meta Elab Command Term

def targetNS := `JanetCartan.PhysicalBackground.NativeReferenceSource

def store (name : Name) (params : Array Expr) (value : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let actual ← inferType value
  let target := target?.getD actual
  unless ← isDefEq target actual do
    throwError "native reference source: changed target {name}"
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← mkForallFVars params target)
  if value.hasMVar || type.hasMVar || value.hasFVar || type.hasFVar ||
      value.hasLevelMVar || type.hasLevelMVar || value.hasSorry || type.hasSorry then
    throwError "native reference source: future scale/order/history or open witness in {name}"
  let name := targetNS ++ name
  if data then
    addDecl (.defnDecl { name, type, value, levelParams := [], hints := .abbrev, safety := .safe })
      (forceExpose := true)
  else
    addDecl (.thmDecl { name, type, value, levelParams := [] }) (forceExpose := true)
  pure (mkAppN (mkConst name) params)

/-- Name the checked application's inputs without selecting any outputs. -/
def namedInputs (name : Name) (args : Array Expr) : MetaM (Array (Name × Expr)) := do
  let mut type := (← getConstInfo name).type
  let mut result := #[]
  for arg in args do
    let .forallE name _ body _ := type |
      throwError "native reference source: changed input telescope at {result.size}/{args.size} ({name})"
    result := result.push (name.eraseMacroScopes, arg)
    type := body.instantiate1 arg
  pure result

def lookup (fields : Array (Name × Expr)) (name : Name) : MetaM Expr := do
  let some (_, value) := fields.find? (fun p => p.1 == name) |
    throwError "native reference source: missing checked field {name}"
  pure value

/-- Elaborate a local consequence, then inline its temporary named bindings. -/
def termWith (bindings : List (Name × Expr)) (code : String)
    (target? : Option Expr := none) : TermElabM Expr := do
  match bindings with
  | (name, value) :: rest =>
    withLetDecl name (← inferType value) value fun fvar => do
      let result ← termWith rest code target?
      pure (result.replaceFVar fvar value)
  | [] =>
    Term.withoutErrToSorry do
      let stx ← match Parser.runParserCategory (← getEnv) `term code with
        | .ok stx => pure stx
        | .error error => throwError "native reference source: term parser: {error}"
      let value ← Term.elabTerm stx target?
      Term.synthesizeSyntheticMVarsNoPostponing
      let value ← instantiateMVars value
      if value.hasMVar || value.hasSorry then
        throwError "native reference source: incomplete local consequence"
      pure value

elab "realize_native_protected_reference_source" : command => liftTermElabM do
  let original := `JanetCartan.PhysicalNormalInverse.StrongSource.exists_history_coercivity
  let originalInfo ← getConstInfo original
  let oldFull := `JanetCartan.PhysicalBackground.originalProductSourceFull
  let oldGeometry := `JanetCartan.PositiveBackground.exists_constructed_source_on_selected_product_cells
  let oldFullInfo ← getConstInfo oldFull
  let some oldFullBody := oldFullInfo.value? (allowOpaque := true) |
    throwError "native reference source: static product proof requires import all"
  let geometryArity ← forallTelescope (← getConstInfo oldGeometry).type fun xs _ => pure xs.size
  forallBoundedTelescope originalInfo.type (some 29) fun params _ => do
    unless params.size == 29 do
      throwError "native reference source: expected actualSource29 selected tuple"
    let fixed := params[:21].toArray
    let scales := params[21:23].toArray
    let extra := params[23:].toArray
    let rawArgs ← PhysicalNormalInverse.StrongToleranceApplication.actualSourceArguments params
    let oldInputs ← namedInputs
      `JanetCartan.PhysicalNormalInverse.exists_prescribed_source_history_coercivity (rawArgs[:133].toArray)
    let withoutOrders (value : Expr) : MetaM Expr := do
      let occurs (term : Expr) := term.hasAnyFVar (fun id =>
        extra.any (fun p => p.fvarId! == id))
      if !occurs value then return value
      let some name := value.getAppFn.constName? |
        throwError "native reference source: composite order-dependent actualSource field"
      unless (`JanetCartan.PhysicalNormalInverse.StrongSource.Arguments).isPrefixOf name do
        throwError "native reference source: unexpected order-dependent getter {name}"
      let value := ((← getConstInfo name).value! (allowOpaque := true)).beta value.getAppArgs
      if occurs value then
        throwError "native reference source: genuine dependence on a future history order"
      pure value
    let sourceField (name : Name) : MetaM Expr := do
       let value ← lookup oldInputs name
       withoutOrders value
    let actualCurrent ← sourceField `cSource
    let current ← store `current fixed (← mkLambdaFVars scales actualCurrent) true
    let capValue := mkAppN (mkConst `JanetCartan.PhysicalSeed.SourceInverseBoundary.sourceCap) fixed
    let sourceCap ← store `sourceCap fixed capValue true
    let hcap ← store `sourceCap_pos fixed
      (mkAppN (mkConst `JanetCartan.PhysicalBackground.original_sourceCap_pos) fixed)
    let atCap ← mkAppM ``And.intro #[hcap, ← mkAppM `le_refl #[sourceCap]]
    let scaleOne ← mkLambdaFVars scales (← sourceField `hσone)
    let hcapOne ← store `sourceCap_le_one fixed (mkAppN scaleOne #[sourceCap, atCap])
    let oldProof ← Core.betaReduce (← zetaReduce (oldFullBody.beta fixed))
    let some geometry := oldProof.find? (·.isAppOfArity oldGeometry geometryArity) |
      throwError "native reference source: unchanged seed/product INPUT application missing"
    if geometry.hasLooseBVars then
      throwError "native reference source: original product geometry has an unretained witness"
    let staticInputs ← namedInputs oldGeometry geometry.getAppArgs
    let static (name : Name) := lookup staticInputs name
    let outer (name : Name) := mkAppN
      (mkConst (`JanetCartan.PhysicalBackground.OriginalOuterCutoff ++ name)) fixed
    let χ ← store `χ fixed (outer `χ) true
    let hχ ← store `χ_smooth fixed (outer `smooth)
    let hχc ← store `χ_compact fixed (outer `compact)
    let W ← store `window fixed (outer `window) true
    let hW ← store `window_open fixed (outer `hwindow)
    let hχW ← store `χ_support fixed (outer `support_window)
    let seed ← store `seed fixed (← static `seed) true
    let hflow ← static `hflow
    let hRc ← static `hRc
    let τbind := [(`τeq, ← static `hτeq), (`hRc, hRc), (`T, ← static `T), (`hM, ← static `hM)]
    let τpos := "by intro a; dsimp only; rw [τeq a]; exact div_pos (JanetCartan.NullTransport.ActualFlow.existenceTime_pos (hRc a) (JanetCartan.NullTransport.ActualFlow.liftedLowBound_nonneg (T a) (hM a))) (by norm_num)"
    let τbound := "by intro a; have hh := (JanetCartan.NullTransport.ActualFlow.existenceTime_le (hRc a) (JanetCartan.NullTransport.ActualFlow.liftedLowBound_nonneg (T a) (hM a))).1; dsimp only; rw [τeq a]; linarith"
    let genericNS := `JanetCartan.PhysicalBackground.RetainedMeasuredSource
    let mut type := (← getConstInfo (genericNS ++ `cap)).type
    let mut selected : Array Expr := #[]
    let mut selectedNames : Array (Name × Expr) := #[]
    let mut hτ? : Option Expr := none
    while true do
      let .forallE rawName domain body _ := type | break
      let name := rawName.eraseMacroScopes
      let argument ← if domain.isAppOf `Fintype then do
          let mut instance? : Option Expr := none
          for (_, value) in staticInputs do
            if (← inferType value).isAppOf `Fintype then instance? := some value
          let some value := instance? | throwError "native reference source: original finite index instance missing"
          pure value
        else if name == `χ then pure χ
        else if name == `hχ then pure hχ
        else if name == `hχcompact then pure hχc
        else if name == `V then pure W
        else if name == `hV then pure hW
        else if name == `hχV then pure hχW
        else if name == `c₀ then pure seed
        else if name == `cap then pure sourceCap
        else if name == `hcap then pure hcap
        else if name == `hcap1 then pure hcapOne
        else if name == `cσ then pure current
        else if name == `hball then static `h6U
        else if name == `hτ then do
          let proof ← termWith τbind τpos (some domain)
          hτ? := some proof
          pure proof
        else if name == `hτR then termWith τbind τbound (some domain)
        else if name == `E then
          termWith [(`Rcell, ← static `Rcell), (`Vnative, ← static `V)]
            "fun a ↦ Set.prod (Metric.ball 0 (Rcell a)) (Vnative a)" (some domain)
        else if name == `hproduct then
          termWith [(`protectedProduct, outer `product_buffer)]
            "by intro a q hq; have hh := protectedProduct a hq; exact ⟨hh.1, hh.2.1⟩" (some domain)
        else if name == `hseed || name == `hcurrent then do
          let some hτ := hτ? | throwError "native reference source: missing actual positive time"
          let bindings := [(`hFlow, hflow), (`hRc, hRc), (`hTau, hτ), (`seed, seed), (`current, current)]
          let code := if name == `hseed then
              "by intro a; exact ((hFlow a).mono_right (JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.outputCylinder_spec (hRc a) (hTau a)).2).mono_right (seed a).small_subset"
            else
              "by intro σ hσ a; exact ((hFlow a).mono_right (JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.outputCylinder_spec (hRc a) (hTau a)).2).mono_right (current σ hσ a).small_subset"
          termWith bindings code (some domain)
        else static name
      unless ← isDefEq (← inferType argument) domain do
        throwError "native reference source: actual retained argument mismatch {name}"
      selected := selected.push argument
      selectedNames := selectedNames.push (name, argument)
      type := body.instantiate1 argument
    for name in #[`G, `U, `P, `T, `Ω, `z₀, `ρ, `Rc, `M, `τ, `row, `col, `E, `r] do
      discard <| store name fixed (← lookup selectedNames name) true
    for name in #[`hr, `hcell, `hP, `hΩ, `hKΩ, `hpatch, `hRc, `hτ, `hτR,
        `hbuffer, `hphysical, `hball, `hproduct, `hseed, `hcurrent] do
      discard <| store name fixed (← lookup selectedNames name)
    for (name, input) in #[(`Rproduct, `Rcell), (`Voriginal, `V), (`root, `zRoot),
        (`theta, `θ), (`am, `am), (`width, `width)] do
      discard <| store name fixed (← static input) true
    for (name, input) in #[(`original_window_open, `hV), (`product_radius_le_physical, `hRphysical),
        (`product_flow, `hflow), (`measure_lt_carrier, `hram), (`inner_support_product, `hselected),
        (`am_pos, `ham), (`width_pos, `hwidth)] do
      discard <| store name fixed (← static input)
    discard <| store `carrier_cell fixed (← sourceField `hcell)
    discard <| store `source_gap_pos fixed (← sourceField `hglobalGap)
    let nativeSelected (field : Name) := mkAppN
      (mkConst (`JanetCartan.PhysicalSeed.SelectedBoundary ++ field)) fixed
    discard <| store `coefficient_cutoff fixed (nativeSelected `χcoeff) true
    discard <| store `measurement_six_cell fixed (nativeSelected `fact59)
    discard <| store `coefficient_cutoff_plateau fixed (nativeSelected `fact66)
    for (name, data) in #[(`cap, true), (`cap_pos, false), (`cap_le, false),
        (`C, true), (`C_pos, false), (`stress_smooth, false), (`residual_smooth, false), (`bound, false)] do
      discard <| store name fixed (mkAppN (mkConst (genericNS ++ name)) selected) data
    let hQ := mkAppN (mkConst (targetNS ++ `stress_smooth)) (fixed ++ scales)
    let hR := mkAppN (mkConst (targetNS ++ `residual_smooth)) (fixed ++ scales)
    let qArgs := (← inferType hQ).getAppArgs
    let rArgs := (← inferType hR).getAppArgs
    let Q := qArgs[qArgs.size - 2]!
    let R ← Core.betaReduce (← zetaReduce rArgs[rArgs.size - 2]!)
    unless R.isAppOf `JanetCartan.PositiveBackground.referenceMeanResidual do
      throwError "native reference source: the literal normalized residual changed"
    let residualArgs := R.getAppArgs
    let H0 ← store `H0 fixed residualArgs[residualArgs.size - 2]! true
    let originalSource := mkAppN
      (mkConst `JanetCartan.PositiveBackground.exists_retained_fixedSource_sobolev_bounds) selected
    discard <| store `H0_posSemidef fixed (← mkAppM ``And.left #[originalSource])
    let mean ← store `mean (fixed ++ scales) residualArgs.back! true
    let X0linear ← mkAppM `JanetCartan.PositiveBackground.referenceVectorField #[H0]
    let X0 ← termWith [(`X0linear, X0linear)] "fun x ↦ X0linear x"
    discard <| store `X0 fixed X0 true
    let hX0 ← termWith [(`X0linear, X0linear)]
      "show ContDiff ℝ ∞ (fun x ↦ X0linear x) from X0linear.contDiff"
    discard <| store `X0_smooth fixed hX0
    let hr ← lookup selectedNames `hr
    let hcell ← lookup selectedNames `hcell
    let index ← static `A
    let initial ← termWith [(`A, index), (`n, fixed[0]!), (`sigma, scales[0]!)]
      "fun (_ : A) (_ : JanetCartan.Euclidean (n - 1) × JanetCartan.Euclidean 3) ↦ sigma"
    let angular ← withLocalDeclD `i index fun i => do
      let mask ← mkAppM `JanetCartan.ContinuumRow.CanonicalConic.angularMask
        #[mkApp (← static `zRoot) i, mkApp (← static `θ) i,
          mkApp (← static `ham) i, mkApp (← static `hwidth) i]
      mkLambdaFVars #[i] mask
    let high ← withLocalDeclD `i index fun i =>
      mkLambdaFVars #[i] (mkConst `JanetCartan.ContinuumRow.FixedCutoffs.highFrequency)
    let meanEq ← mkAppM `JanetCartan.PositiveBackground.physicalDensityMean_retainedChart_zero
      #[actualCurrent, initial, χ, hr, hcell, angular, high]
    let equality := (← inferType meanEq).getAppArgs
    let left := equality[equality.size - 2]!
    unless left.isAppOfArity `JanetCartan.PositiveBackground.physicalDensityMean 7 do
      throwError "native reference source: retained mean formula changed"
    let meanCarrier ← store `meanCarrier (fixed ++ scales) left.getAppArgs[4]! true
    let nativeMean := mkAppN left.getAppFn (left.getAppArgs.set! 4 meanCarrier)
    unless ← isDefEq equality.back! mean do
      throwError "native reference source: chosen mean is not the literal retained source mean"
    discard <| store `mean_zero_formula (fixed ++ scales) meanEq false (some (← mkEq nativeMean mean))
    let e ← mkAppM `JanetCartan.PhysicalBackground.measuredSourceToL2 #[hr, hcell, Q, R, hQ, hR]
    discard <| store `source (fixed ++ scales) e true
    withLocalDeclD `s (mkConst ``Nat) fun s => do
      let mem ← mkAppM `JanetCartan.PhysicalBackground.measuredSourceToL2_mem
        #[hr, hcell, Q, R, hQ, hR, s]
      discard <| store `source_mem (fixed ++ scales ++ #[s]) mem
    logInfo "actual selected21, SAME native c_sigma/source radius, ONE protected chi; fresh H0/X0 and literal cutoff1 factor-two source; caps/C before sigma"

end JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate
end
