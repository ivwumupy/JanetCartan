module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseGeometry
public import JanetCartan.Iteration.PhysicalMean.Profiles
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# The original normal multiplier on the unchanged physical cutoff buffer

Unlike the smaller background core, the verified closed buffer 11a/12 contains
the physical cutoff support 5a/6, where a is the SAME original χ₂ inner radius.
Its smoothness domain is exactly the unchanged `OriginalSmoothing.Dsmooth`
chart a, not an assumed relation with the positive-background core.

Specialize the existing normal multiplier producer on this geometry, retaining
the SAME native39 current and arbitrary smooth tensor DATA. Sbuffer and Cbuffer
close on prehistory44 and the extra reach is genuinely INITIAL. The old
`OriginalNormalCompletionProfiles` and its independent smaller-core choice are
unchanged. Consumer: the physical completed-mean cutoff profile
(`main:eq:mean-normal-field`, `main:prop:mean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Set Metric JanetCartan
open scoped ContDiff BigOperators Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

public meta section
namespace JanetCartan.PhysicalMean.OriginalNormalCompletionBufferProfilesTemplate
open Lean Meta Elab Command
open OriginalCanonicalInverseProfilesTemplate (withActualInverse)
open OriginalBackgroundHermitianTemplate (bodyAt)

private def root := `JanetCartan.PhysicalMean.OriginalNormalCompletionBufferProfiles
private def base := `JanetCartan.PhysicalMean.OriginalCanonicalBaseProfiles
private def measured := `JanetCartan.PhysicalBackground.NativeMeasuredCancellation
private def app (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def termWith (bindings : List (Name × Expr)) (code : String)
    (expected : Option Expr := none) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code expected)

private def save (key : Name) (params : Array Expr) (value : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Expr := do
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "original normal buffer: unresolved or later input escaped {key}"
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do throwError "original normal buffer: unavailable producers {missing.toList}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  liftM <| IO.eprintln s!"original normal buffer: kernel checking {name} / {params.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Actual normal multiplier on the SAME original native39 F, with the verified 11a/12 physical cutoff buffer and exactly the original Dsmooth.chart smoothness domain. Sbuffer and Cbuffer precede R₀/history/tensor; only a genuine initial numerical gate is added (main:eq:mean-normal-field, main:prop:mean)."
  liftM <| IO.eprintln s!"original normal buffer: kernel passed {name}"
  return app name params

elab "construct_original_normal_buffer_budget" : command => liftTermElabM do
  withActualInverse fun d => withTransparency .default do
    let fixed := d.parameters[:44].toArray
    let native := d.native39
    let Gref := app `JanetCartan.PhysicalBackground.NativeCoefficientProfiles.Gref native[:23].toArray
    let h := app (base ++ `radius_geometry) fixed
    let hR ← termWith [(`h,h)] "h.2.2.1.trans (h.2.2.2.1.trans h.2.2.2.2.1)"
    let hStar ← termWith [(`n,native[0]!),(`rStar,native[26]!),(`h,native[28]!)]
      "(by change (2 * (n + 1) + 14) ≤ rStar at h; omega : 8 ≤ rStar)"
    let producer ← mkAppM ``exists_history_meanNormalCorrection_bounds
      #[Gref,Expr.proj ``And 0 h,Expr.proj ``And 0 (Expr.proj ``And 1 h),hR,
        native[25]!,hStar,native[29]!]
    discard <| save `exists_bounds fixed producer

private def choiceAt (key : Name) (type proof : Expr) : MetaM Expr := do
  unless type.isAppOfArity ``Exists 2 do throwError "original normal buffer: changed actual existential"
  return mkAppN (mkConst key type.getAppFn.constLevels!) (type.getAppArgs.push proof)

elab "select_original_normal_buffer_budget " mode:num : command => liftTermElabM do
  unless mode.getNat < 5 do throwError "original normal buffer: unknown budget field"
  forallBoundedTelescope (← getConstInfo (root ++ `exists_bounds)).type (some 44) fun fixed existsType =>
    withTransparency .default do
      let bounds := app (root ++ `exists_bounds) fixed
      let rawS ← choiceAt ``Classical.choose existsType bounds
      if mode.getNat == 0 then
        discard <| save `Sbuffer fixed rawS true (some (mkConst ``Real))
      else
        let S := app (root ++ `Sbuffer) fixed
        let hS ← choiceAt ``Classical.choose_spec existsType bounds
        let sType := existsType.appArg!.beta #[rawS]
        unless sType.isAppOfArity ``And 2 do throwError "original normal buffer: missing threshold specification"
        if mode.getNat == 1 then
          let expected := sType.getAppArgs[0]!.replace fun e => if e == rawS then some S else none
          discard <| save `two_le_Sbuffer fixed (.proj ``And 0 hS) false (some expected)
        else
          let hasC := Expr.proj ``And 1 hS
          let cType := sType.getAppArgs[1]!
          let rawC ← choiceAt ``Classical.choose cType hasC
          if mode.getNat == 2 then
            discard <| save `Cbuffer fixed rawC true (some cType.getAppArgs[0]!)
          else
            let C := app (root ++ `Cbuffer) fixed
            let spec ← choiceAt ``Classical.choose_spec cType hasC
            let specType := cType.appArg!.beta #[rawC]
            unless specType.isAppOfArity ``And 2 do throwError "original normal buffer: missing coefficient specification"
            let index := if mode.getNat == 3 then 0 else 1
            let expected := specType.getAppArgs[index]!.replace fun e =>
              if e == rawC then some C else if e == rawS then some S else none
            discard <| save (if mode.getNat == 3 then `Cbuffer_nonneg else `continuation) fixed
              (.proj ``And index spec) false (some expected)

elab "specialize_original_normal_buffer_profile" : command => liftTermElabM do
  withActualInverse fun d => withTransparency .default do
    let p := d.parameters
    let native := d.native39
    let fixed := p[:44].toArray
    let raw ← bodyAt (measured ++ `on_exterior_plateau) native
    unless raw.isAppOfArity `JanetCartan.PhysicalBackground.retained_measured_physical_core_cancellation 64 do
      throwError "original normal buffer: changed actual cancellation64"
    let F := raw.getAppArgs[34]!
    let n := native[0]!
    let radius := app (base ++ `rBuffer) fixed
    let S := app (root ++ `Sbuffer) fixed
    let C := app (root ++ `Cbuffer) fixed
    let reached ← termWith [(`S,S),(`R0,p[44]!)] "S ≤ R0"
    withLocalDeclNoLocalInstanceUpdate `hBufferReached .default reached fun hReached => do
      let bound := mkAppN (app (root ++ `continuation) fixed)
        (#[native[33]!,hReached] ++ native[35:39].toArray)
      forallBoundedTelescope (← inferType bound) (some 3) fun tensorOrder _ => do
        unless tensorOrder.size == 3 do throwError "original normal buffer: changed tensor/smoothness/order tail"
        let expected ← termWith [(`n,n),(`r,radius),(`F,F),(`T,tensorOrder[0]!),(`s,tensorOrder[2]!),(`C,C),
          (`R0,p[44]!),(`j,p[46]!)]
          ("cNorm (closedBall (0 : Euclidean n) r) s (CurrentMean.meanNormalCorrection F T) ≤ " ++
           "∑ q ∈ Finset.range (s+1), ∑ i ∈ Finset.range (q+1), " ++
           "(q.choose i : ℝ) * C i * currentCoefficientScale R0 j ^ i * " ++
           "cNorm (closedBall (0 : Euclidean n) r) (q-i) T")
        discard <| save `meanNormalCorrection_bound (p ++ #[hReached] ++ tensorOrder)
          (mkAppN bound tensorOrder) false (some expected)
    logInfo "actual original normal buffer: SAME native39, unchanged Dsmooth support, source-only Sbuffer44/Cbuffer44 and genuine INITIAL gate"

end JanetCartan.PhysicalMean.OriginalNormalCompletionBufferProfilesTemplate
end

construct_original_normal_buffer_budget
select_original_normal_buffer_budget 0
select_original_normal_buffer_budget 1
select_original_normal_buffer_budget 2
select_original_normal_buffer_budget 3
select_original_normal_buffer_budget 4
specialize_original_normal_buffer_profile
