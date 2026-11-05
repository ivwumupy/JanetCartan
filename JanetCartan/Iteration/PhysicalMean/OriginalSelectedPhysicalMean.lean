module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularity
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalBaseGeometry
public import JanetCartan.Iteration.PhysicalMean.Field
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# The actual Schwartz full-source mean on the unchanged physical cutoff

The SAME initialized field, literal normalized tensor and complete sampled
self are completed ONCE. Their actual wide-ball smoothness and the original
physical cutoff support produce a real Schwartz map, with its exact values,
physical-core germ and FULL linearized metric. There is no new threshold,
field choice or analytic success input. The physical domain stays Dsmooth;
it is not replaced by the smaller background cancellation core.
Consumer: the finite Picard residual error and quantitative cutoff profiles
(`main:eq:mean-normal-field`, `main:prop:mean`). Those quantitative estimates
remain separate actual producer obligations.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
@[expose] noncomputable section
namespace JanetCartan.PhysicalMean.OriginalSelectedPhysicalMean
private theorem full_strain_of_germ {n N : ℕ}
    (F V W : Euclidean n → Euclidean N) (x : Euclidean n)
    (h : V =ᶠ[𝓝 x] W) : linearizedMetric F V x = linearizedMetric F W x := by
  ext i j
  simp only [linearizedMetric, partialDeriv, h.fderiv_eq]
private theorem cut_support {n N : ℕ} (D : LocalDomain)
    (V : Euclidean n → Euclidean N) {U : Set (Euclidean n)}
    (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (hcut : tsupport (UniformStep.physicalCutoff (n := n) D) ⊆ U) :
    tsupport (PhysicalPrimary.cutSchwartzOfSupport D V hU hV hcut : Euclidean n → Euclidean N) ⊆ D.chart n :=
  (tsupport_smul_subset_left (UniformStep.physicalCutoff D) V).trans
    (UniformStep.physicalCutoff_properties D).2.1
end JanetCartan.PhysicalMean.OriginalSelectedPhysicalMean
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedPhysicalMean
open Lean Meta Elab Command
open OriginalSelectedMeanDataTemplate (withActualSelectedFields)
private def root := `JanetCartan.PhysicalMean.OriginalSelectedMeanData
private def base := `JanetCartan.PhysicalMean.OriginalCanonicalBaseProfiles
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
private def termWith (bindings : List (Name × Expr)) (text : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings text)
private def save (key : Name) (p : Array Expr) (value target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual physical mean: missing {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual physical mean: extra or unproved field input in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  liftM <| IO.eprintln s!"actual physical mean: kernel checking {name}/{p.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .regular 0,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME actual full-source Picard mean, completed ONCE then cut by the original physical cutoff on unchanged Dsmooth. Genuine original wide-ball smoothness and cutoff support, exact physical-core germ and FULL strain; no successful profile or field premise (main:eq:mean-normal-field; main:prop:mean)."
  logInfo m!"actual original physical Schwartz mean {key}/{p.size}: unchanged Dsmooth cutoff and one completion"

elab "construct_actual_selected_physical_mean " mode:num : command => liftTermElabM do
  unless mode.getNat < 5 do throwError "actual physical mean: unknown publication mode"
  withActualSelectedFields fun p f native _ _ => do
    withTransparency .default do
      let stage := p[:54].toArray
      let fixed := native[:44].toArray
      let D := app (base ++ `Dsmooth) fixed
      let V := app (root ++ `completedMean) stage
      let hV := app (root ++ `completedMean_smooth) stage
      let U := (← inferType hV).getAppArgs.back!
      let hU ← termWith [(`U,U)] "(Metric.isOpen_ball : IsOpen U)"
      let hcutBuffer := app (base ++ `cutoff_support_buffer) fixed
      let buffers := app (base ++ `buffer_containments) fixed
      let hcut ← termWith [(`h,hcutBuffer),(`b,buffers)] "h.trans (b.2.2.1.trans b.2.2.2)"
      let raw := app `JanetCartan.PhysicalPrimary.cutSchwartzOfSupport #[f[0]!,f[1]!,D,V,U,hU,hV,hcut]
      let physical := app (root ++ `physicalMean) stage
      if mode.getNat == 0 then
        save `physicalMean stage raw (← inferType raw) true
      else if mode.getNat == 4 then
        let proof := app ``cut_support #[f[0]!,f[1]!,D,V,U,hU,hV,hcut]
        let target := (← inferType proof).replace fun e => if e == raw then some physical else none
        save `physicalMean_support stage proof target
      else
        let x := p[54]!
        if mode.getNat == 1 then
          let proof := app `JanetCartan.PhysicalPrimary.cutSchwartzOfSupport_apply #[f[0]!,f[1]!,D,V,U,hU,hV,hcut,x]
          let target := (← inferType proof).replace fun e => if e == raw then some physical else none
          save `physicalMean_value p[:55].toArray proof target
        else
          let core ← termWith [(`D,D),(`n,f[0]!),(`x,x)] "x ∈ D.core n"
          withLocalDeclNoLocalInstanceUpdate `hxPhysicalCore .default core fun hx => do
            let params := p[:55].toArray.push hx
            let germ := app `JanetCartan.PhysicalPrimary.cutSchwartzOfSupport_eventuallyEq #[f[0]!,f[1]!,D,V,U,hU,hV,hcut,x,hx]
            if mode.getNat == 2 then
              let target := (← inferType germ).replace fun e => if e == raw then some physical else none
              save `physicalMean_core_germ params germ target
            else
              let h := app (root ++ `physicalMean_core_germ) params
              let Vfun ← termWith [(`V,physical),(`n,f[0]!),(`N,f[1]!)]
                "(V : JanetCartan.Euclidean n → JanetCartan.Euclidean N)"
              let proof := app ``full_strain_of_germ #[f[0]!,f[1]!,f[2]!,Vfun,V,x,h]
              save `physicalMean_full_strain params proof (← inferType proof)
end JanetCartan.PhysicalMean.OriginalSelectedPhysicalMean
end

construct_actual_selected_physical_mean 0
construct_actual_selected_physical_mean 1
construct_actual_selected_physical_mean 2
construct_actual_selected_physical_mean 3
construct_actual_selected_physical_mean 4
