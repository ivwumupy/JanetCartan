module

public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanData
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingSelected
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingScaled
import all JanetCartan.Iteration.PhysicalBackground.NativeAdmission
import all JanetCartan.Iteration.PhysicalBackground.NativeDensity
import all JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean

/-!
# Genuine regularity of the original selected mean fields

Consumer: the actual completed-mean error transfer and physical Schwartz mean.
The full initialized raw sum uses the SAME global inverse/source regularity;
its current immersion is retained on the original WIDE ball-R. The normalized
target and full sampled self are globally smooth. Symmetry uses the original
metric, SAME finite-moment tensor and an explicit numerical 2*m ≤ R gate.
No successful source, mean field or geometry estimate is a hypothesis
(`new:eq:mean-error-formula`, `main:eq:mean-normal-field`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

@[expose] noncomputable section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanRegularity
open CurrentMean SmoothPeriodicFamily CanonicalChange PhysicalSmoothing DefectSmoothing
private theorem normalized_smooth {n j : ℕ} (D : LocalDomain) (G : FlatReference n)
    {R : ℝ} {m : ℕ} (hm : 1 ≤ m) {gs : MetricField n}
    (hgs : ContDiffOn ℝ ∞ gs (D.chart n)) {δ : ℝ} (hδ : 0 < δ)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
    (hR : OriginalCompleteForcing.targetFrequency n D m hm ≤ R)
    (hsmall : cNorm (D.core n) 0 (inducedMetric (RevisedGlobal.finiteMap G.map u) - gs) ≤ δ^2) :
    ContDiff ℝ ∞ (normalizedSource D R m δ gs G.map u) := by
  have he := contDiffOn_historyDefect hgs G.contDiff u
  have hb : cNorm (D.core n) 0 (historyDefect gs G.map u) ≤ δ^2 := by
    change cNorm _ 0 (gs - inducedMetric (RevisedGlobal.finiteMap G.map u)) ≤ _
    rw [← neg_sub (inducedMetric (RevisedGlobal.finiteMap G.map u)) gs, cNorm_neg]
    exact hsmall
  exact ((OriginalCompleteForcing.original_normalized_estimates n D m hm).choose_spec.2.choose_spec
    R hR (historyDefect gs G.map u) he δ hδ hb).1
private theorem normalized_isSymm {n j : ℕ} (D : LocalDomain) (G : FlatReference n)
    {R : ℝ} {m : ℕ} (hm : 1 ≤ m) {gs : MetricField n}
    (hgs : ContDiffOn ℝ ∞ gs (D.chart n))
    (hs : ∀ x ∈ D.core n, (gs x).IsSymm) (δ : ℝ)
    (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
    (hR : (2 : ℝ)*m ≤ R) (x : Euclidean n) :
    (normalizedSource D R m δ gs G.map u x).IsSymm := by
  have he := (contDiffOn_historyDefect hgs G.contDiff u).continuousOn.mono
    (closedBall_subset_ball D.coreRadius_lt_chartRadius)
  exact (finiteMomentTensor_isSymm D hm hR he
    (fun y hy ↦ PhysicalSmoothing.historyDefect_isSymm (hs y hy) G.map u) x).smul
      (((δ * R ^ RevisedScales.forcingExponent n) ^ 2)⁻¹)
private theorem full_self_smooth {n N : ℕ} {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (Z : SmoothPeriodicFamily n ι (Matrix (Fin N) (Fin n) ℂ)) :
    ContDiff ℝ ∞ (fun x ↦ weightedHermitianTensor μ Z.val (torusQuotient x)) := by
  simpa only [periodicLift, Function.comp_def, tensorBilinear_self] using
    (smooth (tensorBilinear μ Z Z) ()).2
private theorem full_self_isSymm {n N : ℕ} {ι : Type} [Fintype ι]
    (μ : ι → ℝ) (Z : SmoothPeriodicFamily n ι (Matrix (Fin N) (Fin n) ℂ))
    (x : Euclidean n) : (weightedHermitianTensor μ Z.val (torusQuotient x)).IsSymm := by
  unfold weightedHermitianTensor Matrix.IsSymm
  rw [Matrix.transpose_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ (hermitianTensor_isSymm _).smul _)
end JanetCartan.PhysicalMean.OriginalSelectedMeanRegularity
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedMeanRegularity
open Lean Meta Elab Command
open OriginalSelectedMeanDataTemplate (withActualSelectedFields)
private def root := `JanetCartan.PhysicalMean.OriginalSelectedMeanData
private def forcing := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def app (key : Name) (p : Array Expr) : Expr := mkAppN (mkConst key) p
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "actual mean regularity: unavailable original {key}"
  return (value.beta p).headBeta
private def termWith (bindings : List (Name × Expr)) (text : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings text)
private def save (key : Name) (p : Array Expr) (value target : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "actual mean regularity: missing {missing.toList}"
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual mean regularity: extra or unresolved input in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Genuine SAME original selected mean regularity: native wide-ball geometry, full initialized raw source, literal normalized finite-moment target and full sampled self. No successful source/field/profile assumption; symmetry retains its explicit numerical finite-moment order gate (main:eq:mean-normal-field; new:eq:mean-error-formula)."
  logInfo m!"actual original mean regularity {key}/{p.size}"

private def targetArguments (selected : Array Expr) : MetaM (Array Expr) := do
  let chosen ← bodyAt (forcing ++ `selectedMeasuredTarget) selected
  unless chosen.isAppOfArity ``Classical.choose 3 do throwError "actual mean regularity: target selection changed"
  let actual := chosen.getAppArgs[2]!
  unless actual.isAppOfArity (forcing ++ `scaled_measured_target) 63 do
    throwError "actual mean regularity: changed actual scaled target63 {actual.getAppFn.constName?}/{actual.getAppNumArgs}"
  let measured ← bodyAt (forcing ++ `scaled_measured_target) actual.getAppArgs
  unless measured.isAppOfArity (forcing ++ `measure_normalized_history_uniform) 21 do
    throwError "actual mean regularity: changed same normalized producer21 {measured.getAppFn.constName?}/{measured.getAppNumArgs}"
  return measured.getAppArgs

elab "prove_original_selected_target_regularity " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "actual mean regularity: unknown target mode"
  withActualSelectedFields fun p f _ _ _ => do
    withTransparency .default do
      let selected := p[:52].toArray
      let t := app (root ++ `normalizedTarget) selected
      let u ← targetArguments selected
      if mode.getNat == 0 then
        let hR ← mkAppM ``le_trans #[app (forcing ++ `targetFrequency_le_uniform)
          #[u[0]!,u[1]!,u[3]!,u[13]!,u[14]!],u[19]!]
        let proof ← mkAppM ``normalized_smooth
          #[u[1]!,u[2]!,u[14]!,u[16]!,u[18]!,u[8]!,hR,u[20]!]
        let expected ← termWith [(`T,t)] "ContDiff ℝ ∞ T"
        save `normalizedTarget_smooth selected proof expected
      else
        unless u[16]!.isAppOfArity (forcing ++ `scaled_target_smooth) 10 do
          throwError "actual mean regularity: lost original scaled metric's smoothness producer"
        let a := u[16]!.getAppArgs
        let hs ← termWith [(`n,u[0]!),(`D,u[1]!),(`g,a[2]!),(`hg,a[4]!),(`hmaps,a[7]!),
            (`s,a[8]!),(`hs,a[9]!),(`rho,a[5]!)]
          ("(fun x (hx : x ∈ D.core n) => (hg.2 _ (hmaps s hs x " ++
            "(Metric.closedBall_subset_closedBall D.coreRadius_lt_chartRadius.le hx))).isHermitian.isSymm : " ++
            "∀ x ∈ D.core n, (JanetCartan.scaledMetric g (s*rho) x).IsSymm)")
        let frequency := f[4]!.getAppArgs[4]!
        let gate ← termWith [(`m,u[13]!),(`R,frequency)] "(2 : ℝ)*(m : ℝ) ≤ R"
        withLocalDeclNoLocalInstanceUpdate `hMomentFrequency .default gate fun hR => do
          let x := p[54]!
          let proof ← mkAppM ``normalized_isSymm #[u[1]!,u[2]!,u[14]!,u[16]!,hs,u[17]!,u[8]!,hR,x]
          let expected ← termWith [(`T,t),(`x,x)] "(T x).IsSymm"
          save `normalizedTarget_isSymm (selected ++ #[hR,x]) proof expected

elab "prove_original_selected_self_regularity " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "actual mean regularity: unknown self mode"
  withActualSelectedFields fun p f _ _ _ => do
    withTransparency .default do
      let atX := (mkApp f[5]! p[54]!).headBeta
      unless atX.isAppOfArity `JanetCartan.CurrentMean.weightedHermitianTensor 9 do
        throwError "actual mean regularity: changed full weighted self tensor9 {atX.getAppFn.constName?}/{atX.getAppNumArgs}"
      let a := atX.getAppArgs
      unless a[7]!.isAppOfArity ``Subtype.val 3 do
        throwError "actual mean regularity: full self is no longer the same smooth-family value"
      let Z := a[7]!.getAppArgs[2]!
      let H := app (root ++ `fullSampledSelf) p[:54].toArray
      if mode.getNat == 0 then
        let proof ← mkAppM ``full_self_smooth #[a[6]!,Z]
        let expected ← termWith [(`H,H)] "ContDiff ℝ ∞ H"
        save `fullSampledSelf_smooth p[:54].toArray proof expected
      else
        let proof ← mkAppM ``full_self_isSymm #[a[6]!,Z,p[54]!]
        let expected ← termWith [(`H,H),(`x,p[54]!)] "(H x).IsSymm"
        save `fullSampledSelf_isSymm p[:55].toArray proof expected

elab "prove_original_selected_initialized_smooth" : command => liftTermElabM do
  withActualSelectedFields fun p f native native39 _ => do
    withTransparency .default do
      let W := f[3]!
      unless W.isAppOfArity `JanetCartan.PhysicalBackground.baseVariation 8 do
        throwError "actual mean regularity: changed literal initialized baseVariation8"
      let w := W.getAppArgs
      let raw ← bodyAt `JanetCartan.PhysicalBackground.NativeAdmission.raw native39
      unless raw.isAppOfArity `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original.rawCurrent 47 do
        throwError "actual mean regularity: changed literal raw-current47"
      let geometry (key : Name) := app (`JanetCartan.PhysicalBackground.NativeDensity ++ key) raw.getAppArgs
      let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift native
      let E ← bodyAt `JanetCartan.PhysicalMean.OriginalCanonicalSource.linear (native ++ #[shift,p[52]!])
      unless E.isAppOfArity `JanetCartan.PhysicalMean.fixedSourceLinear 28 do
        throwError "actual mean regularity: changed SAME linear/source regularity"
      let e := E.getAppArgs
      let c ← bodyAt `JanetCartan.PhysicalBackground.NativeMeasuredCancellation.on_exterior_plateau native39
      unless c.isAppOfArity `JanetCartan.PhysicalBackground.retained_measured_physical_core_cancellation 64 do
        throwError "actual mean regularity: changed original initial regularity"
      logInfo "actual initialized smooth: extracted current geometry/source regularity/initial regularity"
      let source := app `JanetCartan.PhysicalMean.OriginalCanonicalSource.selected_iterateWithForcing
        (native ++ #[p[52]!,app (forcing ++ `selectedFullSource) p[:52].toArray,p[53]!])
      let hAll ← termWith [(`n,w[0]!),(`iota,w[2]!),(`hinit,c.getAppArgs[60]!),(`hreg,e[21]!),(`source,source)]
        "fun s => (JanetCartan.CarrierSobolev.augmentedInputLevel n iota s).add_mem (hinit s) (hreg source s)"
      logInfo "actual initialized smooth: proved full raw all-order input membership"
      let radius := app `JanetCartan.PhysicalSeed.OriginalBoundary.R native39[:2].toArray
      let U ← termWith [(`n,w[0]!),(`R,radius)] "Metric.ball (0 : JanetCartan.Euclidean n) R"
      let hU ← termWith [(`U,U)] "(Metric.isOpen_ball : IsOpen U)"
      let original := native39[:21].toArray
      let capped := app `JanetCartan.PhysicalNormalInverse.strongCappedExtra
        #[original[0]!,original[1]!,original[20]!]
      let hX := app `JanetCartan.PhysicalBackground.NativeReferenceSource.X0_smooth (original.set! 20 capped)
      let hXon ← termWith [(`h,hX),(`U,U),(`X,w[7]!)] "(h.contDiffOn : ContDiffOn ℝ ∞ X U)"
      logInfo "actual initialized smooth: obtained X0 smoothness on original wide ball"
      let proof := mkAppN (mkConst `JanetCartan.PhysicalBackground.contDiffOn_baseVariation [.zero])
        #[w[0]!,w[1]!,w[2]!,w[3]!,w[4]!,e[17]!,w[5]!,hAll,
          w[6]!,w[7]!,U,hU,geometry `current_hF_on,hXon,geometry `current_immersion]
      logInfo "actual initialized smooth: instantiated real base variation smoothness"
      let expected ← termWith [(`W,app (root ++ `initializedField) p[:54].toArray),(`U,U)]
        "ContDiffOn ℝ ∞ W U"
      save `initializedField_smooth p[:54].toArray proof expected

elab "prove_original_selected_completed_smooth" : command => liftTermElabM do
  withActualSelectedFields fun p _ _ native39 _ => do
    withTransparency .default do
      let stage := p[:54].toArray
      let raw ← bodyAt `JanetCartan.PhysicalBackground.NativeAdmission.raw native39
      unless raw.isAppOfArity `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original.rawCurrent 47 do
        throwError "actual completed smoothness: changed original raw47"
      let geometry (key : Name) := app (`JanetCartan.PhysicalBackground.NativeDensity ++ key) raw.getAppArgs
      let hW := app (root ++ `initializedField_smooth) stage
      let U := (← inferType hW).getAppArgs.back!
      let target := app (root ++ `normalizedTarget) p[:52].toArray
      let H := app (root ++ `fullSampledSelf) stage
      let hT := app (root ++ `normalizedTarget_smooth) p[:52].toArray
      let hH := app (root ++ `fullSampledSelf_smooth) stage
      let hTon ← termWith [(`h,hT),(`T,target),(`U,U)] "(h.contDiffOn : ContDiffOn ℝ ∞ T U)"
      let hHon ← termWith [(`h,hH),(`H,H),(`U,U)] "(h.contDiffOn : ContDiffOn ℝ ∞ H U)"
      let hU ← termWith [(`U,U)] "(Metric.isOpen_ball : IsOpen U)"
      let proof ← mkAppM `JanetCartan.CurrentMean.contDiffOn_completedMeanField
        #[hU,geometry `current_hF_on,hW,hTon,hHon,geometry `current_immersion,geometry `current_fullNormalRank]
      let expected ← termWith [(`V,app (root ++ `completedMean) stage),(`U,U)] "ContDiffOn ℝ ∞ V U"
      save `completedMean_smooth stage proof expected

end JanetCartan.PhysicalMean.OriginalSelectedMeanRegularity
end

