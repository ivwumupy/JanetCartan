module
public import JanetCartan.Iteration.PhysicalPairs.OriginalSourceSchwartz
public import JanetCartan.Iteration.PhysicalPrimary.OriginalSampledPhysicalProfilesApplication
/-! # The actual physical primary is unchanged by the original observation

The final primary keeps the original aggregate `physicalCutoff Dsmooth`.
Its support lies in Dsmooth.chart, which lies in the unchanged source chart.
The actual Schwartz source representatives have the raw-wave germ on that
ENTIRE chart; hence the same weighted aggregate is identical globally. No new
cutoff, modified weight, inner carrier, or source-success premise is introduced
(`main:eq:primary`, `main:eq:metric-ledger`, `main:prop:pairs`).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
open Set Filter
open scoped Topology
namespace JanetCartan.PhysicalPairs.OriginalSourcePrimary
open UniformStep
/-- The original aggregate cutoff only samples its own chart. This elementary
finite-sum identity is instantiated below by the ACTUAL source-wave germs. -/
theorem cutoff_aggregate_eq_of_germs {n N : ℕ} {ι : Type*} [Fintype ι]
    (D : LocalDomain) (b : ℝ) (μ : ι → ℝ)
    (W Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (h : ∀ i x, x ∈ D.chart n → W i =ᶠ[𝓝 x] Z i) :
    (fun x ↦ physicalCutoff (n := n) D x • sampledPrimary b μ W x) =
      (fun x ↦ physicalCutoff (n := n) D x • sampledPrimary b μ Z x) := by
  funext x
  by_cases hx : physicalCutoff (n := n) D x = 0
  · simp only [hx,zero_smul]
  · have hchart : x ∈ D.chart n :=
      (physicalCutoff_properties D).2.1 (subset_tsupport _ hx)
    have hW (i) : W i x = Z i x := (h i x hchart).eq_of_nhds
    simp only [sampledPrimary,Pi.smul_apply,Finset.sum_apply,Function.comp_apply,hW]
end JanetCartan.PhysicalPairs.OriginalSourcePrimary
end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPairs.OriginalSourcePrimaryTemplate
open Lean Meta Elab Command
open PhysicalPrimary.OriginalSampledPhysicalProfilesQuantitativeTemplate
private def ns := `JanetCartan.PhysicalPairs.OriginalSourcePrimary
private def actual := `JanetCartan.PhysicalPrimary.OriginalSampledPhysicalProfiles
private def schw := `JanetCartan.PhysicalPairs.OriginalSourceSchwartz
private def app (key : Name) (args : Array Expr) := mkAppN (mkConst key) args
private def body (key : Name) (p : Array Expr) : MetaM Expr := do
  return ((← getConstInfo key).value! (allowOpaque := true)).beta p
private def remainingType (key : Name) (args : Array Expr) : MetaM Expr := do
  let mut type := (← getConstInfo key).type
  for v in args do
    unless type.isForall do throwError "actual source primary: changed parameter telescope"
    type := type.bindingBody!.instantiate1 v
  return type
private def save (key : Name) (params : Array Expr) (value type : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params type)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "actual source primary: unresolved source/sample or field {key}"
  let pair := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  liftM <| IO.eprintln s!"actual source primary: kernel checking {name}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
  liftM <| IO.eprintln s!"actual source primary: kernel passed {name}"

elab "identify_original_observed_source_primary " which:num : command => liftTermElabM do
  unless which.getNat < 2 do throwError "actual source primary: unknown publication mode"
  withActualSelectedSourceWave fun p _ _ _ _ _ _ => do
    withLocalDeclD `δ (mkConst ``Real) fun δ => do
      let all := p[:52].toArray.push δ
      let original ← body (actual ++ `selectedSourcePrimary) all
      unless original.isAppOfArity `JanetCartan.PhysicalPrimary.cutSampledPrimary 9 do
        throwError "actual source primary: the original aggregate construction changed"
      let a := original.getAppArgs
      let n := a[0]!
      let N := a[1]!
      let index := a[2]!
      let finite := a[3]!
      let D := a[4]!
      let b := a[5]!
      let μ := a[6]!
      let raw := a[7]!
      let observed := app (schw ++ `wave) p
      let observedFn ← mkAppM ``DFunLike.coe #[observed]
      let W ← mkLambdaFVars #[p[52]!] observedFn
      let chartD := app ``JanetCartan.LocalDomain.chart #[D,n]
      let gt ← remainingType (schw ++ `germ_statement) p
      unless gt.isForall do throwError "actual source primary: missing actual germ point"
      let germs ← withLocalDeclD `x gt.bindingDomain! fun x => do
        let tail := gt.bindingBody!.instantiate1 x
        unless tail.isForall do throwError "actual source primary: missing original source-chart admission"
        let hxType := tail.bindingDomain!
        unless hxType.isAppOfArity ``Membership.mem 5 do
          throwError "actual source primary: changed actual source-chart membership"
        let chart := hxType.getAppArgs[3]!
        unless chart.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart 23 do
          throwError "actual source primary: not the unchanged original source chart23"
        let inclusion := app `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry.smoothing_chart_in_source_chart chart.getAppArgs
        withLocalDeclD `hx (← mkAppM ``Membership.mem #[chartD,x]) fun hx => do
          let inSource := mkAppN inclusion #[x,hx]
          let proof := app (schw ++ `germ_on_original_chart) (p ++ #[x,inSource])
          mkLambdaFVars #[p[52]!,x,hx] proof
      let aggregate := mkAppN (mkConst ``JanetCartan.PhysicalPairs.OriginalSourcePrimary.cutoff_aggregate_eq_of_germs [.zero])
        #[n,N,index,finite,D,b,μ,W,raw,germs]
      let primary ← mkAppM ``funext #[app (actual ++ `selectedSourcePrimary_apply) all]
      let proof ← mkAppM ``Eq.trans #[primary,← mkAppM ``Eq.symm #[aggregate]]
      let target ← inferType proof
      unless target.getUsedConstantsAsSet.contains (actual ++ `selectedSourcePrimary) &&
          target.getUsedConstantsAsSet.contains (schw ++ `wave) do
        throwError "actual source primary: lost the SAME final primary or actual Schwartz DATA"
      if which.getNat == 0 then save `statement all target (mkSort .zero) true
      else save `aggregate_primary_eq all proof (app (ns ++ `statement) all)
end JanetCartan.PhysicalPairs.OriginalSourcePrimaryTemplate
end
