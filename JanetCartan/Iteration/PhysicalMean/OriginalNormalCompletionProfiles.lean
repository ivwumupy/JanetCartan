module

public import JanetCartan.Iteration.PhysicalMean.Profiles
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalCoreResidual
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
public meta import Lean

/-!
# The normal completion on the original physical history and core

Apply the existing physical-history multiplier theorem to the SAME native39
current used by the measured cancellation, with its original closed core
`ri / 2` and open measurement buffer `4 * mu`. Only the tensor is new DATA;
no completed-mean, source, mass, or quadratic profile is assumed.

The threshold and all-order coefficient budget close on prehistory44, before
R₀, the history, tensor and requested order. The additional gate is genuinely
`Scomp ≤ R₀`, not a later-stage reach. It is not asserted to follow from the
old selected Tref; a final prehistory maximum must pay it if necessary.
Consumer: the normal term of the SAME completed mean in `main:eq:mean-normal-field`
and its physical profile in `main:prop:mean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff BigOperators Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

public meta section
namespace JanetCartan.PhysicalMean.OriginalNormalCompletionProfilesTemplate
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate (bodyAt)

private def root := `JanetCartan.PhysicalMean.OriginalNormalCompletionProfiles
private def measured := `JanetCartan.PhysicalBackground.NativeMeasuredCancellation
private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def termWith (bindings : List (Name × Expr)) (code : String)
    (expected : Option Expr := none) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code expected)

private def save (name : Name) (params : Array Expr) (value : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Expr := do
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "original normal completion: unresolved or later input escaped {name}"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "original normal completion: unavailable producers {missing.toList}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ name
  liftM <| IO.eprintln s!"original normal completion: kernel checking {name} / {params.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  addDocStringCore name "Actual normal completion on the SAME native39 F and original closed core, with constants fixed on prehistory44 and an explicit INITIAL Scomp ≤ R₀ gate. The tensor is arbitrary DATA; no completed-mean profile is assumed (main:eq:mean-normal-field, main:prop:mean)."
  liftM <| IO.eprintln s!"original normal completion: kernel passed {name}"
  return app name params

/-- Read the native cancellation's literal operands. No sample/shift argument
from the callback is retained in the completion producer. -/
private def withActual
    (next : Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit :=
  OriginalCanonicalSourceApplication.withActualQuadratic fun trial _ native _ _ =>
    withTransparency .default do
      unless trial.size == 52 && native.size == 39 do
        throwError "original normal completion: changed native50/native39 boundary"
      let raw ← bodyAt (measured ++ `on_exterior_plateau) native
      unless raw.isAppOfArity `JanetCartan.PhysicalBackground.retained_measured_physical_core_cancellation 64 do
        throwError "original normal completion: missing actual measured cancellation64"
      next trial[:50].toArray native raw.getAppArgs

/-- Specialize the existing mathematical producer before choosing its budget. -/
elab "construct_original_normal_completion_budget" : command => liftTermElabM do
  withActual fun p native c => do
    let n := c[0]!
    let mu := c[21]!
    let original := native[:21].toArray
    let capped := app `JanetCartan.PhysicalNormalInverse.strongCappedExtra
      #[original[0]!,original[1]!,original[20]!]
    let selected := original.set! 20 capped
    let source (key : Name) := app (`JanetCartan.PhysicalSeed.SourceInverseBoundary ++ key) selected
    let boundary (key : Name) := app (`JanetCartan.PhysicalSeed.SelectedBoundary ++ key) selected
    let ri := source `rInner
    let Gref := app `JanetCartan.PhysicalBackground.NativeCoefficientProfiles.Gref native[:23].toArray
    let geometry := [(`n,n),(`mu,mu),(`hmu,c[22]!),(`ri,ri),(`hri,source `hrInner),
      (`hInner,source `fact7),(`Gref,Gref),(`hSix,boundary `fact58)]
    let hr ← termWith geometry "(half_pos hri : 0 < ri / 2)"
    let hrR ← termWith geometry
      "(by have hm : 0 < mu := hmu; have hi : 0 < ri := hri; have h : ri ≤ mu := hInner; linarith only [hm,hi,h] : ri / 2 < 4 * mu)"
    let hR ← termWith geometry
      "(by have hm : 0 < mu := hmu; have h : 6 * mu < Gref.domain.chartRadius := hSix; linarith only [hm,h] : 4 * mu < Gref.domain.chartRadius)"
    let hStar ← termWith [(`n,n),(`rStar,native[26]!),(`h,native[28]!)]
      "(by change (2 * (n + 1) + 14) ≤ rStar at h; omega : 8 ≤ rStar)"
    let producer ← mkAppM ``exists_history_meanNormalCorrection_bounds
      #[Gref,hr,hrR,hR,native[25]!,hStar,native[29]!]
    discard <| save `exists_bounds p[:44].toArray producer

/-- Read the literal existential type once; no inference over its long native
application is needed to select the SAME witnesses and their specifications. -/
private def choiceAt (key : Name) (type proof : Expr) : MetaM Expr := do
  unless type.isAppOfArity ``Exists 2 do
    throwError "original normal completion: changed actual existential"
  return mkAppN (mkConst key type.getAppFn.constLevels!) (type.getAppArgs.push proof)

/-- Project one named budget from the SAME actual existential. All types are
literal subexpressions of that checked producer, with only its witnesses named. -/
elab "select_original_normal_completion_budget " mode:num : command => liftTermElabM do
  unless mode.getNat < 5 do throwError "original normal completion: unknown budget field"
  forallBoundedTelescope (← getConstInfo (root ++ `exists_bounds)).type (some 44) fun fixed existsType =>
    withTransparency .default do
      unless fixed.size == 44 do throwError "original normal completion: changed static44"
      let existsBounds := app (root ++ `exists_bounds) fixed
      let rawS ← choiceAt ``Classical.choose existsType existsBounds
      if mode.getNat == 0 then
        discard <| save `Scomp fixed rawS true (some (mkConst ``Real))
      else
        let S := app (root ++ `Scomp) fixed
        let hS ← choiceAt ``Classical.choose_spec existsType existsBounds
        let sType := existsType.appArg!.beta #[rawS]
        unless sType.isAppOfArity ``And 2 do throwError "original normal completion: missing threshold specification"
        if mode.getNat == 1 then
          let expected := sType.getAppArgs[0]!.replace fun e => if e == rawS then some S else none
          discard <| save `two_le_Scomp fixed (.proj ``And 0 hS) false (some expected)
        else
          let hasC := Expr.proj ``And 1 hS
          let cType := sType.getAppArgs[1]!
          let rawC ← choiceAt ``Classical.choose cType hasC
          if mode.getNat == 2 then
            discard <| save `Ccomp fixed rawC true (some cType.getAppArgs[0]!)
          else
            let C := app (root ++ `Ccomp) fixed
            let spec ← choiceAt ``Classical.choose_spec cType hasC
            let specType := cType.appArg!.beta #[rawC]
            unless specType.isAppOfArity ``And 2 do throwError "original normal completion: missing coefficient specification"
            let index := if mode.getNat == 3 then 0 else 1
            let expected := specType.getAppArgs[index]!.replace fun e =>
              if e == rawC then some C else if e == rawS then some S else none
            discard <| save (if mode.getNat == 3 then `Ccomp_nonneg else `continuation) fixed
              (.proj ``And index spec) false (some expected)

/-- Actualize the chosen bound on exactly the native history and original core.
The only added analytic datum is the arbitrary smooth tensor itself. -/
elab "specialize_original_normal_completion_profiles " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "original normal completion: unknown actual field"
  withActual fun p native c => do
    let F := c[34]!
    let fixed := p[:44].toArray
    if mode.getNat == 0 then
      let Gref := app `JanetCartan.PhysicalBackground.NativeCoefficientProfiles.Gref native[:23].toArray
      let historical ← termWith [(`Gref,Gref),(`u,native[36]!)]
        "JanetCartan.RevisedGlobal.finiteMap Gref.map u"
      discard <| save `current_map_eq p (← mkEqRefl F) false (some (← mkEq F historical))
    else
      let core := app (measured ++ `core) native[:21].toArray
      let S := app (root ++ `Scomp) fixed
      let C := app (root ++ `Ccomp) fixed
      unless ← isDefEq native[33]! p[44]! do
        throwError "original normal completion: different initial scale"
      let reached ← termWith [(`S,S),(`R0,p[44]!)] "S ≤ R0"
      withLocalDeclNoLocalInstanceUpdate `hCompletionReached .default reached fun hReached => do
        let bound := mkAppN (app (root ++ `continuation) fixed)
          (#[native[33]!,hReached] ++ native[35:39].toArray)
        forallBoundedTelescope (← inferType bound) (some 3) fun tensorOrder _ => do
          unless tensorOrder.size == 3 do
            throwError "original normal completion: changed tensor/smoothness/order tail"
          let expected ← termWith [(`K,core),(`F,F),(`T,tensorOrder[0]!),(`s,tensorOrder[2]!),(`C,C),
            (`R0,p[44]!),(`j,p[46]!)]
            ("JanetCartan.cNorm K s (JanetCartan.CurrentMean.meanNormalCorrection F T) ≤ " ++
             "∑ q ∈ Finset.range (s+1), ∑ i ∈ Finset.range (q+1), " ++
             "(q.choose i : ℝ) * C i * JanetCartan.currentCoefficientScale R0 j ^ i * " ++
             "JanetCartan.cNorm K (q-i) T")
          discard <| save `meanNormalCorrection_bound (p ++ #[hReached] ++ tensorOrder)
            (mkAppN bound tensorOrder) false (some expected)
      logInfo "actual original normal completion: source-only Scomp44/Ccomp44, same native39 map/core, arbitrary tensor DATA; genuine initial gate remains explicit"

end JanetCartan.PhysicalMean.OriginalNormalCompletionProfilesTemplate
end

construct_original_normal_completion_budget
select_original_normal_completion_budget 0
select_original_normal_completion_budget 1
select_original_normal_completion_budget 2
select_original_normal_completion_budget 3
select_original_normal_completion_budget 4
specialize_original_normal_completion_profiles 0
specialize_original_normal_completion_profiles 1
