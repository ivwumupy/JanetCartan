module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanTargetRegularity
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanInitializedRegularity
import all JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanRegularityTemplate
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
set_option warningAsError true
set_option Elab.async false

/-! Genuine completed mean on the ORIGINAL wide ball, from independently checked
actual target/full-self and initialized-field producers (main:eq:mean-normal-field). -/
public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanRegularity
open Lean Meta Elab Command
open OriginalSelectedMeanDataTemplate (withActualSelectedFields)
run_elab do
  withActualSelectedFields fun p f _ native39 _ => do
    withTransparency .default do
      let stage := p[:54].toArray
      let raw ← bodyAt `JanetCartan.PhysicalBackground.NativeAdmission.raw native39
      unless raw.isAppOfArity `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original.rawCurrent 47 do
        throwError "actual completed smoothness: changed original raw47"
      let geometry (key : Name) := app (`JanetCartan.PhysicalBackground.NativeDensity ++ key) raw.getAppArgs
      let W := app (root ++ `initializedField) stage
      let hW := app (root ++ `initializedField_smooth) stage
      let U := (← inferType hW).getAppArgs.back!
      let target := app (root ++ `normalizedTarget) p[:52].toArray
      let H := app (root ++ `fullSampledSelf) stage
      let hT := app (root ++ `normalizedTarget_smooth) p[:52].toArray
      let hH := app (root ++ `fullSampledSelf_smooth) stage
      let hTon ← termWith [(`h,hT),(`T,target),(`U,U)] "(h.contDiffOn : ContDiffOn ℝ ∞ T U)"
      let hHon ← termWith [(`h,hH),(`H,H),(`U,U)] "(h.contDiffOn : ContDiffOn ℝ ∞ H U)"
      let hU ← termWith [(`U,U)] "(Metric.isOpen_ball : IsOpen U)"
      let proof := app `JanetCartan.CurrentMean.contDiffOn_completedMeanField
        #[f[0]!,f[1]!,f[2]!,W,target,H,U,hU,geometry `current_hF_on,hW,hTon,hHon,
          geometry `current_immersion,geometry `current_fullNormalRank]
      let expected ← termWith [(`V,app (root ++ `completedMean) stage),(`U,U)] "ContDiffOn ℝ ∞ V U"
      save `completedMean_smooth stage proof expected
end JanetCartan.PhysicalMean.OriginalSelectedMeanRegularity
end
