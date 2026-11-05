module
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcing
import all JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcing
public import JanetCartan.Iteration.PhysicalMean.OriginalCompleteForcingUniform
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfilesTemplate
public meta import Lean
import all JanetCartan.Iteration.PhysicalSampling.OriginalJointEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSmoothEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonStageApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredCurrentApplication
import all JanetCartan.Iteration.PhysicalPrimary.OriginalJointResponseRegularityTemplate
import all JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaveGeometryTemplate
import all JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrentApplication
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity

/-!
# The measured defect of the original scaled metric

Fix the actual final-core smoothing interval *before* the frequency, history
or requested finite-moment accuracy. Every dilation in that very interval
gives a smooth scaled target on the original chart. At the prescribed physical
defect `R^(-k)`, construct the measured, normalized, finite-moment smoothed
tensor and its uniform source budget (`new:eq:mean-source`, `new:eq:source-bound`).
This is one summand of the source, not an assumption that the complete stage succeeds.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalMean.OriginalCompleteForcing

/-- The history's original high map order pays the first derivative required
by its already fixed target interval (`main:lem:smoothing`). -/
theorem interval_order_one {n rStar kMin : ℕ} (hs : ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n ≤ rStar)
    (h : RevisedScales.displacementLoss n + bandExponent * ((rStar : ℝ) + n / 2) + 2 < (kMin : ℝ)) :
    RevisedScales.displacementLoss n + bandExponent * (1 + (n : ℝ) / 2) + 2 < (kMin : ℝ) := by
  have hs' : 1 ≤ rStar := (show 1 ≤ ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder n by
    unfold ContinuumRow.CanonicalCarrier.canonicalCarrierLowOrder; omega).trans hs
  have hreal : (1 : ℝ) ≤ rStar := by exact_mod_cast hs'
  have hscale : 0 ≤ bandExponent := by norm_num [bandExponent]
  have hp := mul_le_mul_of_nonneg_left (add_le_add_left hreal ((n : ℝ) / 2)) hscale
  linarith only [h,hp]

/-- Use the original metric's smoothness and the actual interval's map into
its domain, rather than assuming a smooth target or arbitrary smoothed field. -/
theorem scaled_target_smooth {n : ℕ} (D : LocalDomain) {g : MetricField n} {U : Set (Euclidean n)}
    (hg : IsRiemannianMetricOn g U) {ρ s₀ : ℝ}
    (hmaps : ∀ s ∈ Icc (0 : ℝ) s₀, ∀ x ∈ D.closureChart n, (s * ρ) • x ∈ U)
    (s : ℝ) (hs : s ∈ Icc 0 s₀) : ContDiffOn ℝ ∞ (scaledMetric g (s * ρ)) (D.chart n) :=
  hg.1.comp (contDiff_id.const_smul (s * ρ)).contDiffOn (fun x hx ↦ hmaps s hs x (ball_subset_closedBall hx))

theorem prescribed_defect_pos {R₀ : ℝ} (h : 2 ≤ R₀) (j k : ℕ) :
    0 < (iterationScale R₀ growthExponent j) ^ (-(k : ℝ)) := by
  unfold iterationScale
  exact Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by linarith) _) _

end JanetCartan.PhysicalMean.OriginalCompleteForcing
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalCompleteScaledApplication
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate (bodyAt)
open OriginalCanonicalInverseProfilesTemplate (withActualInverse app)
private def ns := `JanetCartan.PhysicalMean.OriginalCompleteForcing
private def fc := `JanetCartan.RevisedUniform.OriginalFinalCore
private def nativeTel (type : Expr) (count : Nat) (go : Array Expr → Expr → MetaM Unit) : MetaM Unit := loop count type #[]
where
  loop : Nat → Expr → Array Expr → MetaM Unit
    | 0,t,p => go p t
    | k+1,t,p => do
      let .forallE name dom body bi := t.consumeMData | throwError "scaled target: missing binder {p.size}"
      if bi == .instImplicit then withLocalDecl name bi dom fun a => loop k (body.instantiate1 a) (p.push a)
      else withLocalDeclNoLocalInstanceUpdate name bi dom fun a => loop k (body.instantiate1 a) (p.push a)

private def save (key : Name) (p : Array Expr) (proof target : Expr) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p proof)
  let env ← getEnv
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
    unless missing.isEmpty do throwError "scaled target: missing {missing.toList}"
    if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasSorry then
      throwError "scaled target: non-original input in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := ns ++ key
  if data then addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "Original target dilation on the same final core and reference, fixed before histories and accuracy. The physical metric is evaluated at s times the original source dilation; the normalized defect has exactly the prescribed signed exponent (new:eq:mean-source)."
  logInfo m!"actual original target interval {key}/{p.size}"

private def withInterval (next : Array Expr → Array Expr → Array Expr → Array Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit :=
  withActualInverse fun d => do
    let p := d.parameters
    let y := d.source45
    let a := (← bodyAt (ns ++ `measured_target) p).getAppArgs
    let reg := a[2]!.getAppArgs
    unless reg.size == 25 do throwError "scaled target: existing producer does not use the original reference"
    let base := app (fc ++ `source_interval) reg
    let order := app (ns ++ `interval_order_one) #[a[0]!,y[26]!,y[27]!,y[28]!,y[29]!]
    nativeTel (← inferType base) 6 fun target _ => do
      let original := mkAppN base (target ++ #[y[24]!,y[25]!,y[27]!,order])
      next p a reg target (p[:44].toArray ++ target) original

run_cmd liftTermElabM <| withTransparency .reducible <| withInterval fun _ _ _ _ stat original => do
  let s₀ ← mkAppM ``Classical.choose #[original]
  save `targetDilation stat s₀ (mkConst ``Real) true

run_cmd liftTermElabM <| withTransparency .reducible <| withInterval fun _ _ _ _ stat _ => do
  let named := app (ns ++ `targetDilation) stat
  let raw ← bodyAt (ns ++ `targetDilation) stat
  unless raw.isAppOfArity ``Classical.choose 3 do throwError "not the chosen interval of the existing physical smoother"
  let args := raw.getAppArgs
  let root := (args[1]!.beta #[named]).headBeta
  unless root.isAppOfArity ``And 2 do throwError "missing original lower bound"
  let mid := root.getAppArgs[1]!
  unless mid.isAppOfArity ``And 2 do throwError "missing original upper bound"
  let rest := mid.getAppArgs[1]!
  unless rest.isAppOfArity ``And 2 do throwError "missing original map property"
  let spec := mkAppN (mkConst ``Classical.choose_spec raw.getAppFn.constLevels!) args
  let pos := Expr.proj ``And 0 spec
  let upper := Expr.proj ``And 0 (.proj ``And 1 spec)
  let maps := Expr.proj ``And 0 (.proj ``And 1 (.proj ``And 1 spec))
  let lo := root.getAppArgs[0]!
  let hi := mid.getAppArgs[0]!
  let mp := rest.getAppArgs[0]!
  let hiMaps := mkApp2 (mkConst ``And) hi mp
  let v := mkAppN (mkConst ``And.intro) #[lo,hiMaps,pos,mkAppN (mkConst ``And.intro) #[hi,mp,upper,maps]]
  save `targetDilation_spec stat v (mkApp2 (mkConst ``And) lo hiMaps)

run_cmd liftTermElabM <| withTransparency .reducible <| withInterval fun p a reg target stat _ => do
  let named := app (ns ++ `targetDilation) stat
  let h := app (ns ++ `targetDilation_spec) stat
  let hmaps := Expr.proj ``And 1 (.proj ``And 1 h)
  let mapType := (← inferType h).getAppArgs[1]!.getAppArgs[1]!
  let n := a[0]!
  let start := app (ns ++ `measure_normalized_history_uniform) a
  nativeTel mapType 2 fun sh _ => do
    let smooth := app (ns ++ `scaled_target_smooth)
      (#[n,a[1]!,target[0]!,target[1]!,target[4]!,reg[23]!,named,hmaps] ++ sh)
    let st ← inferType smooth
    let gs := st.getAppArgs[st.getAppNumArgs-2]!
    unless gs.isAppOfArity `JanetCartan.scaledMetric 3 do throwError "scaled target: wrong originally supplied metric"
    nativeTel (← inferType start) 2 fun mh _ => do
      withLocalDeclNoLocalInstanceUpdate `k .default (mkConst ``Nat) fun k => do
        let hδ := app (ns ++ `prescribed_defect_pos) #[p[44]!,a[6]!,p[46]!,k]
        let δ := (← inferType hδ).getAppArgs[3]!
        let v := mkAppN start (mh ++ #[gs,smooth,δ,hδ])
        let oldCore := app `JanetCartan.LocalDomain.core #[a[1]!,n]
        let originalCore := app (fc ++ `D) reg[:23].toArray
        let vt := (← inferType v).replace fun e => if e == oldCore then some originalCore else none
        unless (vt.find? (· == gs)).isSome && (vt.find? (· == δ)).isSome && (vt.find? (· == originalCore)).isSome &&
            (vt.find? (·.isAppOf (ns ++ `uniformTargetBudget))).isSome do throwError "scaled target: lost original metric, power, uniform budget, or final core"
        save `scaled_measured_target (p ++ target ++ sh ++ mh ++ #[k]) v vt
end JanetCartan.PhysicalMean.OriginalCompleteScaledApplication
end
