module

public meta import Lean
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate

/-!
# Close the actual PhysicalSeed reference raw half-budget

This command consumes the original native rawSeed ABI. It applies exactly one
strong cap, instantiates task76's actual reference source on task74's weight,
and identifies that literal source with the existing native reference datum.
The old uncorrected inverse is not reconstructed: its same native strong bound
is applied to this source. Only a positive numerical source cap is then chosen.
-/

public meta section
namespace JanetCartan.PhysicalBackground.NativeRawSeedBudgetTemplate
open Lean Meta Elab Command Term
open NativeReferenceSourceTemplate (termWith)

def targetNS := `JanetCartan.PhysicalBackground.NativeRawSeedBudget

def store (name : Name) (params : Array Expr) (value : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let actual ← inferType value
  let target := target?.getD actual
  unless ← isDefEq target actual do throwError "native raw budget: changed target {name}"
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let type ← instantiateMVars (← mkForallFVars params target)
  if value.hasMVar || type.hasMVar || value.hasFVar || type.hasFVar ||
      value.hasLevelMVar || type.hasLevelMVar || value.hasSorry || type.hasSorry then
    throwError "native raw budget: open or future-scale dependence in {name}"
  let name := targetNS ++ name
  if data then
    addDecl (.defnDecl { name, type, value, levelParams := [], hints := .abbrev, safety := .safe })
      (forceExpose := true)
  else
    addDecl (.thmDecl { name, type, value, levelParams := [] }) (forceExpose := true)
  pure (mkAppN (mkConst name) params)

/-- Unfold only the top-level native alias chain, not its operators or cutoff. -/
def exposeMeasured (value : Expr) : MetaM Expr := do
  let mut value := value
  for _ in [:24] do
    value ← Core.betaReduce (← zetaReduce value)
    if value.isAppOf `JanetCartan.PhysicalBackground.measuredSourceToL2 then return value
    let some name := value.getAppFn.constName? |
      throwError "native raw budget: measured datum has an unexpected alias head"
    let some body := (← getConstInfo name).value? (allowOpaque := true) |
      throwError "native raw budget: missing native datum body {name}; import all required"
    value := body.beta value.getAppArgs
  throwError "native raw budget: native measured datum alias chain did not close"

/-- Pure arithmetic is the existing `reference_rawSeed_half_budget`; all of its
source and inverse estimates here are supplied by the concrete original data. -/
def halfBudgetCode : String :=
  "(by\n" ++
  "  classical\n" ++
  "  let m := kappa + (3 + (n - 1)) + 2\n" ++
  "  let X := JanetCartan.CarrierSobolev.augmentedInputSobolevScale n Rows\n" ++
  "  let S := JanetCartan.periodicSobolevScale n (JanetCartan.Euclidean n)\n" ++
  "  let capBoth := min profileCap originalCap\n" ++
  "  have hBoth : 0 < capBoth := lt_min hProfile hOriginal\n" ++
  "  have hBothProfile : capBoth ≤ profileCap := min_le_left _ _\n" ++
  "  have hBothOriginal : capBoth ≤ originalCap := min_le_right _ _\n" ++
  "  let rawGrade := fun sigma ↦ if hs : sigma ∈ Set.Ioc (0 : ℝ) sourceCap then X.gradeNorm m (raw sigma hs) else 0\n" ++
  "  let sourceGrade := fun sigma ↦ if hs : sigma ∈ Set.Ioc (0 : ℝ) sourceCap then S.gradeNorm m (source sigma hs) else 0\n" ++
  "  let sourceNorm := fun sigma ↦ if hs : sigma ∈ Set.Ioc (0 : ℝ) sourceCap then ‖source sigma hs‖ else 0\n" ++
  "  have hraw : ∀ sigma ∈ Set.Ioc (0 : ℝ) capBoth, rawGrade sigma ≤ Cfull m * (sourceGrade sigma + sourceNorm sigma) := by\n" ++
  "    intro sigma hs\n" ++
  "    have hsp : sigma ≤ profileCap := hs.2.trans hBothProfile\n" ++
  "    have hss : sigma ∈ Set.Ioc (0 : ℝ) sourceCap := ⟨hs.1, hsp.trans hProfileSource⟩\n" ++
  "    have hp := (pairEstimate sigma hss m).2\n" ++
  "    have hi := S.gradeNorm_nonneg m ((JanetCartan.CoerciveInverse.normalOperator (row sigma hss)).inverse (source sigma hss))\n" ++
  "    have hb : X.gradeNorm m (raw sigma hss) ≤ Cfull m * (S.gradeNorm m (source sigma hss) + ‖source sigma hss‖) := by\n" ++
  "      change S.gradeNorm m ((JanetCartan.CoerciveInverse.normalOperator (row sigma hss)).inverse (source sigma hss)) + X.gradeNorm m (raw sigma hss) ≤ Cfull m * (S.gradeNorm m (source sigma hss) + ‖source sigma hss‖) at hp\n" ++
  "      linarith only [hp, hi]\n" ++
  "    simpa only [rawGrade, sourceGrade, sourceNorm, dite_eq_left hss] using hb\n" ++
  "  have he : ∀ sigma ∈ Set.Ioc (0 : ℝ) capBoth, sourceGrade sigma ≤ C m * sigma := by\n" ++
  "    intro sigma hs\n" ++
  "    have hsp : sigma ≤ profileCap := hs.2.trans hBothProfile\n" ++
  "    have hss : sigma ∈ Set.Ioc (0 : ℝ) sourceCap := ⟨hs.1, hsp.trans hProfileSource⟩\n" ++
  "    have hb := sourceBound m sigma hss hsp\n" ++
  "    change S.gradeNorm m (source sigma hss) ≤ C m * sigma at hb\n" ++
  "    simpa only [sourceGrade, dite_eq_left hss] using hb\n" ++
  "  have hen : ∀ sigma ∈ Set.Ioc (0 : ℝ) capBoth, sourceNorm sigma ≤ C 0 * sigma := by\n" ++
  "    intro sigma hs\n" ++
  "    have hsp : sigma ≤ profileCap := hs.2.trans hBothProfile\n" ++
  "    have hss : sigma ∈ Set.Ioc (0 : ℝ) sourceCap := ⟨hs.1, hsp.trans hProfileSource⟩\n" ++
  "    have hb := sourceBound 0 sigma hss hsp\n" ++
  "    change S.gradeNorm 0 (source sigma hss) ≤ C 0 * sigma at hb\n" ++
  "    simpa only [sourceNorm, dite_eq_left hss, JanetCartan.GradedScale.gradeNorm_zero] using hb\n" ++
  "  obtain ⟨halfCap, hHalf, hHalfBoth, hHalfBound⟩ := JanetCartan.PhysicalBackground.reference_rawSeed_half_budget m delta capBoth hDelta hBoth Cfull C hCfull (fun s ↦ (hC s).le) rawGrade sourceGrade sourceNorm hraw he hen\n" ++
  "  have result : ∃ halfCap > (0 : ℝ), halfCap ≤ originalCap ∧ halfCap ≤ profileCap ∧ ∀ sigma, sigma ∈ Set.Ioc (0 : ℝ) halfCap → ∀ hs : sigma ∈ Set.Ioc (0 : ℝ) sourceCap, X.gradeNorm m (raw sigma hs) ≤ delta / 2 := by\n" ++
  "    refine ⟨halfCap, hHalf, hHalfBoth.trans hBothOriginal, hHalfBoth.trans hBothProfile, ?_⟩\n" ++
  "    intro sigma hs hss\n" ++
  "    simpa only [rawGrade, dite_eq_left hss] using hHalfBound sigma hs\n" ++
  "  exact result\n" ++
  "  : ∃ halfCap > (0 : ℝ), halfCap ≤ originalCap ∧ halfCap ≤ profileCap ∧ ∀ sigma, sigma ∈ Set.Ioc (0 : ℝ) halfCap → ∀ hs : sigma ∈ Set.Ioc (0 : ℝ) sourceCap, (JanetCartan.CarrierSobolev.augmentedInputSobolevScale n Rows).gradeNorm (kappa + (3 + (n - 1)) + 2) (raw sigma hs) ≤ delta / 2)"

elab "realize_native_raw_seed_half_budget" : command => liftTermElabM do
  let nativeNS := `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original
  let refNS := `JanetCartan.PhysicalBackground.NativeReferenceSource
  let outerNS := `JanetCartan.PhysicalBackground.OriginalOuterCutoff
  let seedInfo ← getConstInfo (nativeNS ++ `rawSeed)
  forallBoundedTelescope seedInfo.type (some 23) fun params _ => do
    unless params.size == 23 do throwError "native raw budget: expected raw original21 and its strong source scale"
    let fixed := params[:21].toArray
    let scales := params[21:].toArray
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[fixed[0]!, fixed[1]!, fixed[20]!]
    let selected := fixed.set! 20 capped
    let ref (name : Name) := mkAppN (mkConst (refNS ++ name)) selected
    let outer (name : Name) := mkAppN (mkConst (outerNS ++ name)) selected
    let chosen := #[ref `χ, ref `χ_smooth, ref `χ_compact, outer `support_original,
      ref `X0, ref `X0_smooth]
    let nativeArgs := params ++ chosen
    let nativeSource := mkAppN (mkConst (nativeNS ++ `reference)) nativeArgs
    let nativeRaw := mkAppN (mkConst (nativeNS ++ `rawSeed)) nativeArgs
    let nativeRow := mkAppN (mkConst (nativeNS ++ `referenceRow)) params
    let e := mkAppN (ref `source) scales
    let ebody ← exposeMeasured e
    let nbody ← exposeMeasured nativeSource
    unless ebody.getAppArgs.size == 8 && nbody.getAppArgs.size == 8 do
      throwError "native raw budget: literal measured-source arity changed"
    let ea := ebody.getAppArgs
    let na := nbody.getAppArgs
    unless (← isDefEq ea[0]! na[0]!) && (← isDefEq ea[1]! na[1]!) do
      throwError "native raw budget: physical dimension or NATIVE measurement radius changed"
    let nativeResidual ← Core.betaReduce (← zetaReduce na[5]!)
    let some nativeMean := nativeResidual.find? (·.isAppOfArity
        `JanetCartan.PositiveBackground.physicalDensityMean 7) |
      throwError "native raw budget: native reference lost its physical zero-density mean"
    let actualMean := mkAppN (ref `mean) scales
    let meanEq ← termWith []
      "by rw [JanetCartan.PositiveBackground.physicalDensityMean_zero]; rfl"
      (some (← mkEq nativeMean actualMean))
    discard <| store `mean_eq_native params meanEq
    let residualEq ← termWith [(`meanIdentity, meanEq)]
      "by rw [meanIdentity]; rfl" (some (← mkEq na[5]! ea[5]!))
    let qEq ← mkEqRefl na[4]!
    unless ← isDefEq na[4]! ea[4]! do
      throwError "native raw budget: reference projected frame changed"
    let sourceEq ← mkAppM `JanetCartan.PhysicalBackground.nativeReference_measuredSource_congr
      #[ea[2]!, ea[3]!, na[6]!, ea[6]!, na[7]!, ea[7]!, qEq, residualEq]
    discard <| store `source_eq_native params sourceEq false (some (← mkEq nativeSource e))
    for (name, data) in #[(`χ, true), (`X0, true), (`sourceCap, true), (`sourceCap_pos, false),
        (`cap, true), (`cap_pos, false), (`cap_le, false), (`C, true), (`C_pos, false)] do
      discard <| store name fixed (ref name) data
    let originalCap ← store `currentInverseCap fixed
      (mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.StrongCurrent.Cap.cap) fixed) true
    let hOriginal ← store `currentInverseCap_pos fixed
      (mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.StrongCurrent.Cap.fact1) fixed)
    let Cfull ← store `Cfull fixed
      (mkAppN (mkConst `JanetCartan.PhysicalSeed.SourceInverseBoundary.Cfull) selected) true
    let hCfull ← store `Cfull_nonneg fixed
      (mkAppN (mkConst `JanetCartan.PhysicalSeed.SourceInverseBoundary.fact23) selected)
    discard <| store `source params e true
    let sourceStrong := mkAppN (mkConst `JanetCartan.PhysicalBackground.originalReferenceRow_strong)
      (selected ++ scales)
    withLocalDeclD `s (mkConst ``Nat) fun s => do
      let mem := mkAppN (ref `source_mem) (scales ++ #[s])
      let pair := mkAppN sourceStrong #[s, e, mem]
      let rawMem ← mkAppM ``And.left #[pair]
      let rawValue := (← inferType rawMem).getAppArgs.back!
      let some rawOperator := rawValue.find? (·.isAppOf
          `JanetCartan.CoerciveInverse.rightInverse) |
        throwError "native raw budget: native strong theorem lost the actual right inverse"
      let rawArgs := rawValue.getAppArgs
      let rowValue := rawOperator.getAppArgs.back!
      unless ← isDefEq rawArgs.back! e do
        throwError "native raw budget: source in strong inverse changed"
      unless ← isDefEq rowValue nativeRow do
        throwError "native raw budget: same native augmented row guard failed"
      let row ← store `row params rowValue true
      discard <| store `row_eq_native params (← mkEqRefl rowValue) false (some (← mkEq row nativeRow))
      let raw ← store `raw params rawValue true
      let rawEq ← mkAppM ``congrArg
        #[mkAppN rawValue.getAppFn rawArgs[:rawArgs.size - 1].toArray, sourceEq]
      discard <| store `raw_eq_native params rawEq false (some (← mkEq nativeRaw raw))
      let replace (type : Expr) := type.replace fun x =>
        if x == rawValue then some raw else if x == rowValue then some row else none
      discard <| store `raw_mem (params ++ #[s]) rawMem false (some (replace (← inferType rawMem)))
      discard <| store `pair_estimate (params ++ #[s]) pair false (some (replace (← inferType pair)))
    let row ← mkLambdaFVars scales (mkAppN (mkConst (targetNS ++ `row)) params)
    let raw ← mkLambdaFVars scales (mkAppN (mkConst (targetNS ++ `raw)) params)
    let source ← mkLambdaFVars scales e
    let pair ← mkLambdaFVars scales (mkAppN (mkConst (targetNS ++ `pair_estimate)) params)
    let χtype ← whnf (← inferType (ref `χ))
    let .forallE _ index _ _ := χtype |
      throwError "native raw budget: original carrier index is not finite-family input"
    withLocalDeclD `κ (mkConst ``Nat) fun κ =>
      withLocalDeclD `δ (mkConst `Real) fun δ => do
        let positive ← termWith [(`delta, δ)] "(0 : ℝ) < delta"
        withLocalDeclD `hδ positive fun hδ => do
          let all := fixed ++ #[κ, δ, hδ]
          let bindings := [(`n, fixed[0]!), (`Rows, index), (`kappa, κ), (`delta, δ), (`hDelta, hδ),
            (`sourceCap, ref `sourceCap), (`profileCap, ref `cap), (`hProfile, ref `cap_pos),
            (`hProfileSource, ref `cap_le), (`originalCap, originalCap), (`hOriginal, hOriginal),
            (`Cfull, Cfull), (`hCfull, hCfull), (`C, ref `C), (`hC, ref `C_pos),
            (`sourceBound, ref `bound), (`pairEstimate, pair), (`row, row), (`raw, raw), (`source, source)]
          let halfExists ← store `exists_half all (← termWith bindings halfBudgetCode)
          discard <| store `halfCap all (← mkAppM ``Classical.choose #[halfExists]) true
          let spec ← store `half_spec all (← mkAppM ``Classical.choose_spec #[halfExists])
          discard <| store `halfCap_pos all (.proj ``And 0 spec)
          discard <| store `halfCap_le_current_inverse all (.proj ``And 0 (.proj ``And 1 spec))
          let hProfile := Expr.proj ``And 0 (.proj ``And 1 (.proj ``And 1 spec))
          discard <| store `halfCap_le_profile all hProfile
          discard <| store `halfCap_le_source all (← mkAppM `le_trans #[hProfile, ref `cap_le])
          let bound := Expr.proj ``And 1 (.proj ``And 1 (.proj ``And 1 spec))
          discard <| store `half all bound
          forallTelescope (← inferType bound) fun halfScales _ => do
            unless halfScales.size == 3 do throwError "native raw budget: numerical half-cap continuation changed"
            let atSource := fixed ++ #[halfScales[0]!, halfScales[2]!]
            let atNative := mkAppN (mkConst (nativeNS ++ `rawSeed)) (atSource ++ chosen)
            let atRaw := mkAppN (mkConst (targetNS ++ `raw)) atSource
            let nativeEquality := mkAppN (mkConst (targetNS ++ `raw_eq_native)) atSource
            let actualBound := mkAppN bound halfScales
            let actualType ← Core.betaReduce (← zetaReduce (← inferType actualBound))
            let nativeType := actualType.replace fun e => if e == atRaw then some atNative else none
            unless nativeType.find? (· == atNative) |>.isSome do
              throwError "native raw budget: final half bound did not retain the exact native rawSeed"
            let nativeBound ← termWith [(`rawIdentity, nativeEquality), (`actualBound, actualBound)]
              "by rw [rawIdentity]; exact actualBound" (some nativeType)
            discard <| store `half_native (all ++ halfScales) nativeBound
    logInfo "actual PhysicalSeed rawSeed equality and native originalReferenceStrong applied; one strong cap only, both source intervals and factor-two source budget fixed before sigma"

end JanetCartan.PhysicalBackground.NativeRawSeedBudgetTemplate
end
