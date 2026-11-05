module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanProfiles.BudgetTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularityTemplate
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean
/-! The exact fixed-normal completed/physical costs can be selected as soon as
actual117 CW34 and116 CH34 are published. No full-field profile, fullg canonical
reproduction, R0 reach proof or approximation-stage threshold is needed to
publish these definitions (`main:eq:mean-size`). -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanProfileBudgetApplication
open Lean Meta Elab Command
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def root := `JanetCartan.PhysicalMean.OriginalSelectedMeanProfiles
private def termWith (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)
private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual static mean budget: missing {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual static mean budget: history, source or approximation datum escaped"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  liftM <| IO.eprintln s!"actual static mean budget: kernel checking {name}/34"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Exact prehistory mean coefficient from genuine fixed110 Cbuffer,117 CW_N,14 uniform normalized tensor and116 CH_N; optional original physical cutoff cost. No geometric threshold is selected after N and no field-profile premise is added (main:eq:mean-size)."
  liftM <| IO.eprintln s!"actual static mean budget: kernel passed {name}/34"
elab "construct_original_selected_mean_static_budget " mode:num : command => liftTermElabM do
  unless mode.getNat < 4 do throwError "actual static mean budget: unknown mode"
  OriginalSelectedMeanDataTemplate.withActualSelectedFields fun p f native _ _ => do
    withTransparency .default do
      let selected := p[:52].toArray
      let early := selected[:33].toArray.push p[53]!
      let fixed := native[:44].toArray
      let u ← OriginalSelectedMeanRegularity.targetArguments selected
      let Cn := app `JanetCartan.PhysicalMean.OriginalNormalCompletionBufferProfiles.Cbuffer fixed
      let hn := app `JanetCartan.PhysicalMean.OriginalNormalCompletionBufferProfiles.Cbuffer_nonneg fixed
      let Cw := app `JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.CW early
      let hw := app `JanetCartan.PhysicalMean.OriginalSelectedMeanFieldProfiles.CW_nonneg early
      let Ct := app `JanetCartan.PhysicalMean.OriginalNormalizedTargetProfiles.Ctarget #[f[0]!,u[1]!]
      let ht := app `JanetCartan.PhysicalMean.OriginalNormalizedTargetProfiles.Ctarget_nonneg #[f[0]!,u[1]!]
      let Ch := app `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.CH early
      let hh := app `JanetCartan.PhysicalMean.OriginalSelectedHermitianProfiles.CH_nonneg early
      let C := #[Cn,Cw,Ct,Ch]
      if mode.getNat == 0 then
        let value := app ``completedMeanOrderConstant C
        save `Cmean early value (← inferType value) true
      else
        withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s => do
          if mode.getNat == 1 then
            let proof := app ``completedMeanOrderConstant_nonneg (C ++ #[hn,hw,ht,hh,s])
            let old := app ``completedMeanOrderConstant (C.push s)
            let named := mkApp (app (root ++ `Cmean) early) s
            let t := (← inferType proof).replace fun e => if e == old then some named else none
            save `Cmean_nonneg early (← mkLambdaFVars #[s] proof) (← mkForallFVars #[s] t)
          else
            let D := app `JanetCartan.PhysicalMean.OriginalCanonicalBaseProfiles.Dsmooth fixed
            let cut := app ``physicalMeanCutoffConstant #[f[0]!,f[1]!,D,s]
            let mean := mkApp (app (root ++ `Cmean) early) s
            let value ← termWith [(`C,cut),(`M,mean)] "C * M"
            if mode.getNat == 2 then
              let value ← mkLambdaFVars #[s] value
              save `CphysicalMean early value (← inferType value) true
            else
              let hc := app ``physicalMeanCutoffConstant_nonneg #[f[0]!,f[1]!,D,s]
              let hm := mkApp (app (root ++ `Cmean_nonneg) early) s
              let proof ← termWith [(`hc,hc),(`hm,hm)] "mul_nonneg hc hm"
              let named := mkApp (app (root ++ `CphysicalMean) early) s
              let t := (← inferType proof).replace fun e => if e == value then some named else none
              save `CphysicalMean_nonneg early (← mkLambdaFVars #[s] proof) (← mkForallFVars #[s] t)
end JanetCartan.PhysicalMean.OriginalSelectedMeanProfileBudgetApplication
end
