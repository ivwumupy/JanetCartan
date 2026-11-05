module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaves
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.CompletionAssembly.CanonicalPrimary
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWavesTemplate

/-!
# The exact before-B raw field on the original native input

The positive baseline is unscaled, and the second summand is the ONE original
full-angular raw wave on a freely bound native WideInput. A separate actual53
application inserts the unchanged component adjoint and supplied source.
The response acts after synthesis. This identity adds no inverse, cutoff,
mask-support assumption, angular source estimate, or Fourier re-selection.
It is not yet the unshifted-phase amplitude factorization or its R^q profile.
Consumer: the actual full-strain source for `main:eq:primary-strain`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalRawSourceFieldApplication

run_cmd Lean.Elab.Command.liftTermElabM do
  let out ← liftM IO.getStderr
  liftM <| out.putStrLn "native raw identity: minimal imports loaded"
  liftM <| out.flush

private theorem corrected_add {n N : ℕ}
    (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    {X : Set (Euclidean n)} (hX : IsOpen X) (hχX : tsupport χ ⊆ X)
    (Z W : Euclidean n → EuclideanSpace ℂ (Fin N))
    (hZ : ContDiffOn ℝ ∞ Z X) (hW : ContDiffOn ℝ ∞ W X) :
    CorrectedAtoms.complexCorrectedAtom F χ B (Z + W) =
      CorrectedAtoms.complexCorrectedAtom F χ B Z +
        CorrectedAtoms.complexCorrectedAtom F χ B W := by
  simpa only [Finset.sum_singleton] using
    UniformStep.complexCorrectedAtom_add_sum_of_contDiffOn F χ B hX hχX
      ({()} : Finset Unit) Z (fun _ ↦ W) hZ (fun _ _ ↦ hW)

private theorem raw_add_smooth {n N : ℕ}
    (Z W : Euclidean n → EuclideanSpace ℂ (Fin N)) (X : Set (Euclidean n))
    (hZ : ContDiffOn ℝ ∞ Z X) (hW : ContDiffOn ℝ ∞ W X) :
    ContDiffOn ℝ ∞ (Z + W) X := hZ.add hW

end JanetCartan.PhysicalPrimary.OriginalRawSourceFieldApplication
end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPrimary.OriginalRawSourceFieldApplication
open Lean Meta Elab Command
private def ns := `JanetCartan.PhysicalPrimary.OriginalRawSourceField
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def bodyAt (e : Expr) : MetaM Expr := do
  let info ← getConstInfo e.getAppFn.constName!
  let some value := info.value? (allowOpaque := true) |
    throwError "actual raw source: missing saved body {e.getAppFn}"
  return ((value.instantiateLevelParams info.levelParams e.getAppFn.constLevels!).beta e.getAppArgs).headBeta
private def store (key : Name) (p : Array Expr) (value : Expr)
    (data := false) (expected : Option Expr := none) : MetaM Expr := do
  let out ← liftM IO.getStderr
  liftM <| out.putStrLn s!"actual raw source: preparing {key}/{p.size}"
  liftM <| out.flush
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual raw source: unresolved declaration {key}"
    let used := e.getUsedConstantsAsSet
    for bad in #[`JanetCartan.PhysicalMean.OriginalCanonicalSource.iterate,
        `JanetCartan.PhysicalMean.OriginalCanonicalSource.selected_iterate] do
      if used.contains bad then
        throwError "actual raw source: background-only iteration leaked into {key}"
  let name := ns ++ key
  let shared := Lean.ShareCommon.shareCommon (type,value)
  let out ← liftM IO.getStderr
  liftM <| out.putStrLn s!"actual raw source: checking {key}/{p.size}"
  liftM <| out.flush
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := shared.1,value := shared.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := shared.1,value := shared.2}) (forceExpose := true)
  logInfo m!"actual raw source: checked {key}/{p.size}"
  return app name p

private def nativeKeys := #[`raw,`raw_smooth,`source,`correction_add,
  `components_eq_corrected,`field_eq_components,`combined_eq_corrected_raw]

/-- The complete source input remains a freely bound native WideInput while
checking the raw algebra. Only the final aliases substitute the actual adjoint. -/
elab "check_actual_raw_native_identity " which:num : command => liftTermElabM do
  let mode := which.getNat
  unless mode < 7 do throwError "actual raw source: unknown native field"
  let needsSmooth := #[1,3,6].contains mode
  let count := if needsSmooth then 70 else 69
  let original := wave ++ (if needsSmooth then `Combined.active_smooth else `Combined.field)
  let out ← liftM IO.getStderr
  liftM <| out.putStrLn s!"actual raw source: native mode {mode}, opening {count}"
  liftM <| out.flush
  forallBoundedTelescope (← getConstInfo original).type (some count) fun all _ => do
    liftM <| out.putStrLn s!"actual raw source: native mode {mode}, opened {all.size}"
    liftM <| out.flush
    unless all.size == count do throwError "actual raw source: native69/70 changed"
    let p := if needsSmooth then all[:68].toArray.push all[69]! else all
    let field := app (wave ++ `Combined.field) p
    let combined ← bodyAt field
    unless combined.isAppOfArity ``HAdd.hAdd 6 do
      throwError "actual raw source: combined field is not the original two summands"
    let baseline := combined.getAppArgs[4]!
    let angular := combined.getAppArgs[5]!
    unless baseline.isAppOf (wave ++ `Corrected.unrestricted_atom) &&
        angular.isAppOf (wave ++ `Whole.full_angular.corrected) do
      throwError "actual raw source: changed baseline or single whole-angular wave"
    let nativeBase ← bodyAt baseline
    unless nativeBase.isAppOfArity `JanetCartan.CorrectedAtoms.fullCorrectedPrimaryAtom 17 do
      throwError "actual raw source: changed literal full baseline"
    let T := nativeBase.getAppArgs[5]!
    unless T.isAppOfArity (wave ++ `T) 53 do
      throwError "actual raw source: missing the same source53 current"
    let s := T.getAppArgs
    let correctedBase ← bodyAt nativeBase
    unless correctedBase.isAppOfArity `JanetCartan.CorrectedAtoms.complexCorrectedAtom 6 do
      throwError "actual raw source: baseline is not the original source correction"
    let a := correctedBase.getAppArgs
    let rawBase := a[5]!
    let rawAngular := app (wave ++ `Whole.full_angular.raw) angular.getAppArgs
    let key := `Native ++ nativeKeys[mode]!
    if mode == 0 then
      let value := mkAppN combined.getAppFn ((combined.getAppArgs.set! 4 rawBase).set! 5 rawAngular)
      discard <| store key p value true (some (← inferType field))
      return
    let raw := app (ns ++ `Native.raw) p
    let corrected := app `JanetCartan.CorrectedAtoms.complexCorrectedAtom
      #[a[0]!,a[1]!,a[2]!,a[3]!,a[4]!,raw]
    let correctedAngular := mkAppN correctedBase.getAppFn (a.set! 5 rawAngular)
    let correctedParts := mkAppN combined.getAppFn
      ((combined.getAppArgs.set! 4 correctedBase).set! 5 correctedAngular)
    if mode == 2 then
      let source := app `JanetCartan.CorrectedAtoms.complexAtomicSource #[a[0]!,a[1]!,a[2]!,a[3]!,raw]
      discard <| store key p source true
      return
    if mode == 4 then
      discard <| store key p (← mkEqRefl combined) false (some (← mkEq combined correctedParts))
      return
    if mode == 5 then
      discard <| store key p (← mkEqRefl combined) false (some (← mkEq field combined))
      return
    if mode == 6 then
      let hAdd := app (ns ++ `Native.correction_add) all
      let eq ← inferType hAdd
      unless eq.isAppOfArity ``Eq 3 do throwError "actual raw source: native additive Eq changed"
      let level := eq.getAppFn.constLevels!
      let reversed := mkAppN (mkConst ``Eq.symm level)
        #[eq.getAppArgs[0]!,corrected,correctedParts,hAdd]
      let partJoin := mkAppN (mkConst ``Eq.trans level)
        #[eq.getAppArgs[0]!,combined,correctedParts,corrected,
          app (ns ++ `Native.components_eq_corrected) p,reversed]
      let joined := mkAppN (mkConst ``Eq.trans level)
        #[eq.getAppArgs[0]!,field,combined,corrected,
          app (ns ++ `Native.field_eq_components) p,partJoin]
      discard <| store key all joined false (some (← mkEq field corrected))
      return
    let smooth := app (wave ++ `Combined.active_smooth) all
    let smoothBody ← bodyAt smooth
    let some hBase := smoothBody.find? (·.isAppOf (wave ++ `Corrected.on_cutoff_chart)) |
      throwError "actual raw source: missing the active OUTER admission"
    let admission := hBase.getAppArgs.back!
    let parameter := baseline.getAppArgs.back!
    let hRawBase := app (wave ++ `raw_on_source_chart) (s ++ #[parameter,admission])
    let hAngularCutoff := app (wave ++ `Whole.full_angular_smooth.raw) angular.getAppArgs
    let hAngularBody ← bodyAt hAngularCutoff
    unless hAngularBody.isAppOfArity ``ContDiffOn.mono 14 do
      throwError "actual raw source: source-chart restriction changed"
    let hRawAngular := hAngularBody.getAppArgs[11]!
    let hBaseType ← inferType hRawBase
    unless hBaseType.isAppOfArity ``ContDiffOn 11 do
      throwError "actual raw source: baseline source-chart smoothness changed"
    let X := hBaseType.getAppArgs[10]!
    if mode == 1 then
      let hRaw := app ``raw_add_smooth #[a[0]!,a[1]!,rawBase,rawAngular,X,hRawBase,hRawAngular]
      let hRawType ← inferType hRaw
      let rawTarget := mkAppN hRawType.getAppFn (hRawType.getAppArgs.set! 9 raw)
      discard <| store key all hRaw false (some rawTarget)
    else
      let hX := app (masks ++ `chart_open) s[:23].toArray
      let hχX := app (masks ++ `χ₂_support_chart) s[:23].toArray
      let proof := app ``corrected_add #[a[0]!,a[1]!,a[2]!,a[3]!,a[4]!,X,hX,hχX,
        rawBase,rawAngular,hRawBase,hRawAngular]
      discard <| store key all proof false (some (← mkEq corrected correctedParts))

/-- No original factory or source expression is reconstructed: apply the
already checked native theorem to the literal frozen actual69/70 spines. -/
elab "check_actual_raw_source_identity " which:num : command => liftTermElabM do
  let mode := which.getNat
  unless mode < 7 do throwError "actual raw source: unknown actual alias"
  let actual := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourceCombinedWave
  forallBoundedTelescope (← getConstInfo actual).type (some 53) fun p _ => do
    unless p.size == 53 do throwError "actual raw source: saved source53 changed"
    let literalField ← bodyAt (app actual p)
    unless literalField.isAppOfArity (wave ++ `Combined.field) 69 do
      throwError "actual raw source: saved literal field69 changed"
    let native := literalField.getAppArgs
    let nativeArgs ← if #[1,3,6].contains mode then do
        let smooth ← bodyAt (app `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles.selectedSourceCombinedWave_smooth p)
        unless smooth.isAppOfArity (wave ++ `Combined.active_smooth) 70 do
          throwError "actual raw source: saved literal smooth70 changed"
        pure smooth.getAppArgs
      else pure native
    let key := nativeKeys[mode]!
    let value := app (ns ++ `Native ++ key) nativeArgs
    let target ← inferType value
    let nativeRaw := app (ns ++ `Native.raw) native
    let target := if mode == 0 then target else target.replace fun e =>
      if e == nativeRaw then some (app (ns ++ `raw) p)
      else if e == literalField then some (app actual p)
      else none
    discard <| store key p value (mode == 0 || mode == 2) (some target)

check_actual_raw_native_identity 0
check_actual_raw_native_identity 1
check_actual_raw_native_identity 2
check_actual_raw_native_identity 3
check_actual_raw_native_identity 4
check_actual_raw_native_identity 5
check_actual_raw_native_identity 6
#print axioms JanetCartan.PhysicalPrimary.OriginalRawSourceField.Native.raw
#print axioms JanetCartan.PhysicalPrimary.OriginalRawSourceField.Native.raw_smooth
#print axioms JanetCartan.PhysicalPrimary.OriginalRawSourceField.Native.source
#print axioms JanetCartan.PhysicalPrimary.OriginalRawSourceField.Native.correction_add
#print axioms JanetCartan.PhysicalPrimary.OriginalRawSourceField.Native.components_eq_corrected
#print axioms JanetCartan.PhysicalPrimary.OriginalRawSourceField.Native.field_eq_components
#print axioms JanetCartan.PhysicalPrimary.OriginalRawSourceField.Native.combined_eq_corrected_raw
end JanetCartan.PhysicalPrimary.OriginalRawSourceFieldApplication
end
