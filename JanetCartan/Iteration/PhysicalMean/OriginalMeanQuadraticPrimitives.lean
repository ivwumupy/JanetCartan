module

public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticStatic
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowMeasuredAmplitude
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRow
public import JanetCartan.Iteration.PhysicalMean.CanonicalLowQuadratic
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSourceQuadratic
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSelection
public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundMeasurementProfiles
public import JanetCartan.Iteration.PhysicalSampling.OriginalNativeTesterBudgets
public import JanetCartan.Iteration.PhysicalSamplingShells.Native
public import Mathlib.Topology.MetricSpace.Gluing
public meta import Lean
public import JanetCartan.Iteration.PhysicalMean.OriginalMeanQuadraticCoordinates
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalActual
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalRowMeasuredMoment
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInverseProfiles

/-!
# The one actual original sampled quadratic tuple and sharp low estimate

This leaf consumes the frozen coordinate, static, measured-moment and inverse
producers. Every mathematical field is checked against the literal consumer
`fixedSourceQuadratic_low_bound`, preserving the original sample type, weights,
measure, ONE selected shift and arbitrary fixed prefix. It keeps the full annular
sum and the asymmetric H^0(u) H^(n/2+2)(v) endpoint. The static budget is fixed
before history, sample, prefix and source DATA.

The public `OriginalMeanQuadraticRealization.withActualQuadraticPrimitives`
callback is the sole shared factory for the actual linear and quadratic source
consumers (`app:ch_mean_pairs:eq:block-fields`,
`app:ch_mean_pairs:eq:block-bilinear`). All displayed analytic obligations are
proved from the original data; none is a new callback hypothesis.
-/

/-! ## Exact original primitive stage: PrimitivePacking -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public noncomputable section
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Packing
open JanetCartan
open JanetCartan.PhysicalMean
open Set

/-- Exact source order for the sharp low bound, with the existing chart reserve. -/
theorem chart_reserve {n rStar : ℕ} (h : 20*(n+1)+5 ≤ rStar) :
    2*(n/2+2)+(n/2+1)+5 ≤ rStar := by omega

/-- Use the original measured jets with the one before-history shared cost. -/
theorem measured_budget_mono {n : ℕ}
    (a : Fin n → Euclidean (n-1) → Euclidean n → ℂ)
    (K : Set (Euclidean n)) (A B : ℕ → ℝ) {T : ℝ} (hT : 1 ≤ T)
    (hAB : ∀ j, A j ≤ B j)
    (ha : ∀ c η x j, ‖iteratedFDeriv ℝ j (a c η) x‖ ≤ A j*T^(j-(2*(n/2+2)+(n/2+1)))) :
    ∀ c η, ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (a c η) x‖ ≤ B j*T^(j-(2*(n/2+2)+(n/2+1))) := by
  intro c η x _ j
  exact (ha c η x j).trans (mul_le_mul_of_nonneg_right (hAB j) (pow_nonneg (zero_le_one.trans hT) _))

/-- Only the cost, not the same trade or its active set, is enlarged. -/
theorem trade_budget_mono {n J : ℕ}
    (L : RawInputPartition.RefinedIndex J → Euclidean (n-1) → Euclidean (n-1) → Euclidean n → Euclidean n)
    (m : RawInputPartition.RefinedIndex J × Euclidean (n-1) → ℝ)
    (K : Set (Euclidean n)) (A B : ℕ → ℝ) {T : ℝ} (hT : 1 ≤ T)
    (hAB : ∀ j, A j ≤ B j)
    (hL : ∀ i η, m (i,η) ≠ 0 → ∀ v, ‖v‖ ≤ 1 → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (L i η v) x‖ ≤ A j*T^(j-(2*(n/2+2)+(n/2+1)))) :
    ∀ i η, m (i,η) ≠ 0 → ∀ v, ‖v‖ ≤ 1 → ∀ x ∈ K, ∀ j,
      ‖iteratedFDeriv ℝ j (L i η v) x‖ ≤ B j*T^(j-(2*(n/2+2)+(n/2+1))) := by
  intro i η hm v hv x hx j
  exact (hL i η hm v hv x hx j).trans
    (mul_le_mul_of_nonneg_right (hAB j) (pow_nonneg (zero_le_one.trans hT) _))

open MeasureTheory

/-- The original chosen scalar operator keeps its norm bound and action after
rewriting only the proved equality of its full phase. -/
theorem native_tester_phase_transport {n : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (φ ψ : X → Euclidean n → ℝ) (heq : φ = ψ)
    (m : X → ℝ) (χ : X → Euclidean n → ℂ)
    (P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (h : ∀ f, P f =ᵐ[volume] fun x ↦ ∫ z, sampledMomentKernel φ m χ x z * f z ∂μ) :
    ∀ f, P f =ᵐ[volume] fun x ↦ ∫ z, sampledMomentKernel ψ m χ x z * f z ∂μ := by
  subst ψ
  exact h

end JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Packing
end
#print axioms JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Packing.chart_reserve
#print axioms JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Packing.measured_budget_mono
#print axioms JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Packing.trade_budget_mono
#print axioms JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Packing.native_tester_phase_transport

/-! ## Exact original primitive stage: RepresentationPacking -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public noncomputable section
open MeasureTheory
open JanetCartan JanetCartan.RawInputPartition JanetCartan.PhysicalMean JanetCartan.PhysicalSamplingShells
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Representation
/-- Convert the existing pointwise original `hArep` to the literal operator
composition consumed by `fixedSourceQuadratic_low_bound`, using the SAME annular
isometry and no analytic premise (`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem hArep_of_pointwise {n J : ℕ}
    (A : RefinedInput n J →L[ℝ] ContinuumRow.OutputL2 n)
    (An : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (h : ∀ v, A v = PeriodicLocalL2.transferOutputOperator (realQuadratureChannel An)
      ((annularShellEquiv (V := ℂ) (n := n) (refinedRadius (J := J))).symm v)) :
    A.comp ((annularShellEquiv (V := ℂ) (n := n) (refinedRadius (J := J))).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) =
      PeriodicLocalL2.transferOutputOperator (realQuadratureChannel An) := by
  ext1 f
  change A ((annularShellEquiv (V := ℂ) (n := n) (refinedRadius (J := J))) f) =
    PeriodicLocalL2.transferOutputOperator (realQuadratureChannel An) f
  simpa only [LinearIsometryEquiv.symm_apply_apply] using
    h ((annularShellEquiv (V := ℂ) (n := n) (refinedRadius (J := J))) f)
end JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Representation
end
#print axioms JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Representation.hArep_of_pointwise

/-! ## Exact original primitive stage: CoreFields -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
open JanetCartan.PhysicalMean
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Core
private meta def app (n : Name) (p : Array Expr) := mkAppN (mkConst n) p
meta def withCore (next : Array Expr → Expr → Array (Name × Expr) → MetaM Unit) : MetaM Unit := do
  OriginalCanonicalSourceApplication.withActualQuadratic fun ps J _ explicit term => do
    let p := ps[:50].toArray
    let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift p
    let repl (e : Expr) := e.replaceFVar ps[50]! shift
    let term := repl term
    let explicit := explicit.map repl
    unless term.isAppOf `JanetCartan.PhysicalMean.fixedSourceQuadratic do throwError "lost original quadratic"
    let .const fn levels := term.getAppFn | throwError "lost original quadratic constant"
    let ci ← getConstInfo fn
    let mut metadata := ci.type.instantiateLevelParams ci.levelParams levels
    let mut fi : Option Expr := none
    let wt ← inferType explicit[0]!
    let .forallE _ ν _ _ := wt | throwError "lost actual weight sample domain"
    for v in term.getAppArgs do
      let .forallE _ d s _ := metadata | throwError "changed original quadratic spine"
      if d.isAppOfArity ``Fintype 1 && d.appArg! == ν then fi := some v
      metadata := s.instantiate1 v
    let some exactFintype := fi | throwError "lost exact original sample Fintype"
    let source := p[:44].toArray
    let static ← OriginalMeanQuadraticRealization.staticFieldsAt source
    let bg := `JanetCartan.PhysicalMean.OriginalBackgroundHermitian
    let C := app (bg ++ `commonC) p
    let event := `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent
    let hR ← mkAppM `le_trans #[app (event ++ `hS) source,p[45]!]
    let hT := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
      #[p[44]!,hR,p[46]!]
    let fields := static ++ #[(`ν,ν),(`instFintype,exactFintype),(`J,J),
      (`weight,explicit[0]!),(`C,C),(`hC,app (bg ++ `commonC_smooth) p),
      (`Cp,explicit[1]!),(`hCp,explicit[2]!),
      (`hCeq,app `JanetCartan.PhysicalMean.OriginalCanonicalMeasurement.Cper_native p),
      (`A,explicit[3]!),(`G,explicit[4]!),(`Q₀,explicit[5]!),
      (`T,app `JanetCartan.currentCoefficientScale #[p[44]!,p[46]!]),(`hT,hT)]
    next p ps[51]! fields
meta def bodyAtApp (e : Expr) (extra : Array Expr := #[]) : MetaM Expr := do
  let .const name levels := e.getAppFn | throwError "sampled original spine is not a named application"
  let info ← getConstInfo name
  unless info.levelParams.length == levels.length do throwError "sampled original spine has changed universe arity"
  let some body := info.value? | throwError "sampled original spine has no exposed definition"
  return (body.instantiateLevelParams info.levelParams levels).beta (e.getAppArgs ++ extra)
meta def actualAtSample (G sample : Expr) : MetaM (Array Expr) := do
  let outer ← bodyAtApp G
  let pref ← bodyAtApp outer #[sample]
  let some native := pref.find? (·.isAppOf `JanetCartan.PhysicalMean.OriginalCanonicalSampled.sampledDerivative)
    | throwError "lost original native prefix row"
  let value ← bodyAtApp native
  unless value.isAppOfArity `JanetCartan.PhysicalMean.OriginalCanonicalActual.G 53 do
    throwError "changed actual same-sample row/color/node"
  if value.hasLevelParam || value.hasLevelMVar then throwError "sampled original spine leaked generic universes"
  return value.getAppArgs

end JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Core

/-! ## Exact original primitive stage: PrimitiveFields -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
open JanetCartan.PhysicalMean
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build
meta def app (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
meta def actual := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual
meta def get (fields : Array (Name × Expr)) (k : Name) : MetaM Expr := do
  let some (_,v) := fields.find? (·.1 == k) | throwError "actual primitives missing {k}"
  return v
meta def binderKey (k : Name) (d : Expr) (bi : BinderInfo) : Name := Id.run do
  if bi == .instImplicit then
    for (head,key) in #[( ``Fintype,`instFintype),(``MetricSpace,`instMetricSpace),
        (``DiscreteTopology,`instDiscreteTopology),(``MeasurableSpace,`instMeasurableSpace),(``BorelSpace,`instBorelSpace)] do
      if d.isAppOf head then return key
  return k.eraseMacroScopes
meta def fieldDomain (key : Name) (fields : Array (Name × Expr)) : MetaM Expr := do
  let ci ← getConstInfo `JanetCartan.PhysicalMean.fixedSourceQuadratic_low_bound
  let mut type := ci.type.instantiateLevelParams ci.levelParams (ci.levelParams.map (fun _ => .zero))
  while type.isForall do
    let .forallE k d b bi := type | throwError "unexpected primitive consumer binder"
    let k := binderKey k d bi
    if k == key then
      let d ← instantiateMVars d
      if d.hasMVar then throwError "primitive domain {key} depends on an unassembled field"
      return d
    let v ← match fields.find? (·.1 == k) with
      | some (_,v) => pure v
      | none => mkFreshExprMVar d
    type := b.instantiate1 v
  throwError "consumer has no primitive {key}"
meta def pair (a b : Expr) : MetaM Expr := do
  return mkAppN (mkConst ``Prod.mk [.zero,.zero]) #[← inferType a,← inferType b,a,b]
meta def retainCheckedFields (params : Array Expr) (fields : Array (Name × Expr)) : MetaM (Array (Name × Expr)) := do
  let env ← getEnv
  fields.mapM fun (key,value) => do
    let name := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled ++ key
    match env.find? name with
    | some (.defnInfo _) | some (.thmInfo _) => return (key,app name params)
    | some _ => throwError "unproved dummy original primitive {name}"
    | none => return (key,value)
meta def withFamilies (next : Array Expr → Array (Name × Expr) → MetaM Unit) : MetaM Unit := do
  JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Core.withCore fun p cut core => do
    let ν ← get core `ν
    let sig ← whnf ν
    unless sig.isAppOfArity ``Sigma 2 do throwError "same sample type is no longer Sigma"
    let metric ← mkAppOptM ``Metric.Sigma.metricSpace #[some sig.getAppArgs[0]!,some sig.getAppArgs[1]!,none]
    let top ← synthInstance (← mkAppM ``TopologicalSpace #[ν])
    let ms ← synthInstance (← mkAppM ``MeasurableSpace #[ν])
    let discrete ← synthInstance (mkAppN (mkConst ``DiscreteTopology [.zero]) #[ν,top])
    let singleton := mkAppN (mkConst `JanetCartan.PhysicalSamplingShells.sampleIndex_measurableSingletonClass [.zero]) ν.getAppArgs
    let countable ← synthInstance (← mkAppM ``Countable #[ν])
    let borel := mkAppN (mkConst ``Countable.instBorelSpace [.zero]) #[ν,countable,ms,singleton,top,discrete]
    let core := core ++ #[(`instMetricSpace,metric),(`instDiscreteTopology,discrete),(`instMeasurableSpace,ms),(`instBorelSpace,borel)]
    withLocalDeclNoLocalInstanceUpdate `sample .default ν fun q => do
      let native ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Core.actualAtSample (← get core `G) q
      OriginalMeanQuadraticApplication.withActualMomentAt native fun hγ hR _ => do
        let params := p ++ #[hγ,hR,cut]
        for h in #[hγ,hR] do
          if (← inferType h).containsFVar q.fvarId! then throwError "numeric guard depends on a sample"
        let chart := app (actual ++ `raw_moment_chart) (native ++ #[hγ,hR,cut])
        let ca := (← inferType chart).getAppArgs
        unless ca.size == 11 do throwError "changed exact chart arity {ca.size}"
        let ph := app (actual ++ `rawPhase) native
        let normphase := ca[3]!
        let trade := ca[5]!
        let mask := ca[4]!
        let amp := app (actual ++ `forwardAmplitude) native
        let ameas := app `JanetCartan.PhysicalMean.OriginalCanonicalRow.ameasAtPoint native
        let mut fields := core
        let replace (e sample : Expr) := e.replaceFVar q sample
        let domain ← fieldDomain `φ fields
        let φ ← forallBoundedTelescope domain (some 1) fun z _ => do
          let sample : Expr := .proj ``Prod 0 (.proj ``Prod 0 z[0]!)
          let loc ← pair (.proj ``Prod 1 (.proj ``Prod 0 z[0]!)) (.proj ``Prod 1 z[0]!)
          mkLambdaFVars z (mkApp (replace ph sample) loc)
        fields := fields.push (`φ,φ)
        let Φ ← forallBoundedTelescope (← fieldDomain `Φ fields) (some 1) fun z _ => do
          mkLambdaFVars z (mkApp (replace normphase (.proj ``Prod 0 z[0]!)) (.proj ``Prod 1 z[0]!))
        fields := fields.push (`Φ,Φ)
        let A ← forallBoundedTelescope (← fieldDomain `amp fields) (some 3) fun z _ => do
          mkLambdaFVars z (mkAppN (replace amp (.proj ``Prod 0 z[2]!)) z[:2].toArray)
        fields := fields.push (`amp,A)
        let a ← forallBoundedTelescope (← fieldDomain `ameas fields) (some 2) fun z _ => do
          mkLambdaFVars z (mkApp (replace ameas (.proj ``Prod 0 z[1]!)) z[0]!)
        fields := fields.push (`ameas,a)
        let L ← forallBoundedTelescope (← fieldDomain `L fields) (some 1) fun z _ => do
          mkLambdaFVars z (mkApp (replace trade (.proj ``Prod 0 z[0]!)) (.proj ``Prod 1 z[0]!))
        fields := fields.push (`L,L)
        let m ← forallBoundedTelescope (← fieldDomain `m fields) (some 1) fun z _ => do
          let sample : Expr := .proj ``Prod 0 (.proj ``Prod 0 z[0]!)
          let loc ← pair (.proj ``Prod 1 (.proj ``Prod 0 z[0]!)) (.proj ``Prod 1 z[0]!)
          mkLambdaFVars z (mkApp (replace mask sample) loc)
        fields := fields.push (`m,m)
        let shift := app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift p
        let rowp := p ++ #[shift,cut]
        fields := fields ++ #[(`An,app `JanetCartan.PhysicalMean.OriginalCanonicalRow.An rowp),
          (`hCj,app (actual ++ `common_measurement_physical_jets) p),
          (`Q0_regular,app (actual ++ `Q0_regular) p)]
        let hweight ← withLocalDeclNoLocalInstanceUpdate `sample .default ν fun z => do
          mkLambdaFVars #[z] (app (actual ++ `sample_weights_nonneg) (p ++ #[shift,z]))
        fields := fields.push (`hweight,hweight)
        next params (← retainCheckedFields params fields)
end JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build

/-! ## Metadata declarations before generated mathematical expressions

The declarations below are elaborated in the small static environment. Their
invocations remain below in the original proof-dependency order; no mathematical
field is used before its own kernel check. -/

private meta def publishOriginalMeasuredRow : MetaM Unit := do
  JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.withFamilies fun p original => do
    let analyticalKeys : Array Name := #[`hφ,`hm,`hms,`ha,`haK]
    let data : Array (Name × Expr) := original.filter (fun e => !analyticalKeys.contains e.1) ++
      analyticalKeys.map (fun k => (k, mkAppN (mkConst (`JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled ++ k)) p))
    let ν ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.get data `ν
    unless ν.isAppOfArity `JanetCartan.CanonicalRowComparison.SampleIndex 7 do throwError "same measured row lost original sample type"
    let singleton := mkAppN (mkConst `JanetCartan.PhysicalSamplingShells.sampleIndex_measurableSingletonClass [.zero]) ν.getAppArgs
    let fields := data ++ #[(`hAn,JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled.hAn p),
      (`hArep,JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled.hArep p),(`instMeasurableSingletonClass,singleton)]
    let name := `JanetCartan.PhysicalMean.OriginalCanonicalRow.measured_hrow_of_hAn
    let ci ← getConstInfo name
    let levels := ci.levelParams.map (fun _ => Level.zero)
    let mut t := ci.type.instantiateLevelParams ci.levelParams levels
    let mut args := #[]
    while t.isForall do
      let .forallE binder domain body bi := t | throwError "changed actual row binder"
      let key := binder.eraseMacroScopes
      let mut actualKey := if key == `a then `ameas else key
      if bi == .instImplicit then
        actualKey ← match domain.getAppFn.constName? with
          | some ``Fintype => pure `instFintype
          | some ``MeasurableSpace => pure `instMeasurableSpace
          | some ``MeasurableSingletonClass => pure `instMeasurableSingletonClass
          | some ``MetricSpace => pure `instMetricSpace
          | some ``DiscreteTopology => pure `instDiscreteTopology
          | some ``BorelSpace => pure `instBorelSpace
          | _ => throwError "unexpected actual row instance {domain.getAppFn}"
      let a ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.get fields actualKey
      args := args.push a
      t := body.instantiate1 a
    let proof := mkAppN (mkConst name levels) args
    let target ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.fieldDomain `hrow fields
    let type ← instantiateMVars (← mkForallFVars p target)
    let value ← instantiateMVars (← mkLambdaFVars p proof)
    let env ← getEnv
    for e in #[type,value] do
      let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
      unless missing.isEmpty do throwError "same actual hrow missing {missing.toList}"
      if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasSorry then throwError "open same actual hrow"
    let pair := Lean.ShareCommon.shareCommon (type,value)
    let out ← IO.getStdout
    out.putStrLn "kernel checking actual hrow from SAME proven measured tuple, original A/An and sampledShellEquiv"
    out.flush
    addDecl (.thmDecl {name := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled.hrow,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
    out.putStrLn "kernel passed actual hrow from SAME proven measured tuple, original A/An and sampledShellEquiv"
    out.flush
public meta section
open Lean Meta Elab Command
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization
private def checkedSampledKeys : Array Name :=
  #[`φ,`Φ,`amp,`ameas,`L,`m,`hφ,`hφs,`hΦ,`hamp,`ha,`hL,`hm,`hms,`hhigh,
    `hampK,`haK,`hagree,`hphase,`hCj,`hGj,`hΦj,`haj,`hLj,`Tbare,`hTbare,`hTbareBound,
    `Tfull,`hTfull,`hTfullBound,`hG,`hArep,`hweight,`hAn,`hrow]
/-- ONE actual tuple on the original sample type, measure, weights, selected
shift and fixed prefix, with every consumer field kernel checked. Parameters are
native50 ++ [hγMoment,hR90,L]. This reuses `staticFieldsAt` through the sole Core
mapper and introduces no analytic input (`app:ch_mean_pairs:eq:block-fields`). -/
def withActualQuadraticPrimitives (next : Array Expr → Array (Name × Expr) → MetaM Unit) : MetaM Unit := do
  JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.withFamilies fun p original => do
    unless p.size == 53 do throwError "changed actual native50+two moment guards+prefix ABI"
    let mut fields := original.filter (fun e => !checkedSampledKeys.contains e.1)
    for key in checkedSampledKeys do
      let name := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled ++ key
      match ← getConstInfo name with
      | .thmInfo _ | .defnInfo _ => pure ()
      | _ => throwError "unproved actual sampled primitive {key}"
      fields := fields.push (key,JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.app name p)
    next p fields
end JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization
end
open Lean Meta Elab Command
private meta def auditOriginalSampledPrimitives : MetaM Unit := do
  for k in #[`φ,`Φ,`amp,`ameas,`L,`m,`hφ,`hφs,`hΦ,`hamp,`ha,`hL,`hm,`hms,`hhigh,
      `hampK,`haK,`hagree,`hphase,`hCj,`hGj,`hΦj,`haj,`hLj,`Tbare,`hTbare,`hTbareBound,
      `Tfull,`hTfull,`hTfullBound,`hG,`hArep,`hweight,`hAn,`hrow] do
    let name := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled ++ k
    let info ← getConstInfo name
    let some value := info.value? (allowOpaque := true) | throwError "unproved original primitive {k}"
    for e in #[info.type,value] do
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then throwError "open original primitive {k}"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "nonstandard original primitive {k}: {axioms}"
    logInfo m!"std3 complete same original primitive {k}: {axioms}"
private meta def auditOriginalPrimitiveCallback : MetaM Unit := do
  JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun p fields => do
    let env ← getEnv
    for (k,v) in fields do
      let value ← instantiateMVars (← mkLambdaFVars p v)
      let missing := value.getUsedConstants.filter (fun c => (env.find? c).isNone)
      unless missing.isEmpty do throwError "complete actual tuple {k}: missing {missing.toList}"
      if value.hasFVar || value.hasMVar || value.hasLevelMVar || value.hasLevelParam || value.hasLooseBVars || value.hasSorry then throwError "open complete actual tuple {k}"
      discard <| inferType v
    logInfo "complete SAME actual tuple native50+hgamma+hR90+prefix, all33 primitives plus actual hAn+hrow"
private meta def auditOriginalLowBound : MetaM Unit := do
  let name := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.low_bound
  let .thmInfo info ← getConstInfo name | throwError "actual original low bound was not kernel checked"
  for e in #[info.type,info.value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "open actual original low estimate"
  unless (info.type.find? (·.isAppOf `JanetCartan.PhysicalMean.OriginalCanonicalSource.quadratic)).isSome &&
      (info.type.find? (·.isAppOf `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift)).isSome &&
      (info.type.find? (·.isAppOf `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.lowConstant)).isSome do
    throwError "actual low bound lost the original quadratic, sole selected shift or static budget"
  let axioms ← collectAxioms name
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "nonstandard actual original low estimate: {axioms}"
  logInfo m!"std3 ACTUAL ORIGINAL asymmetric low bound: {axioms}"

/-! ## Exact original primitive stage: CheckedFamilyData -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
elab "construct_actual_quadratic_sampled_data " key:ident : command => liftTermElabM do
  let key := key.getId.eraseMacroScopes
  JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.withFamilies fun p fields => do
    let body ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.get fields key
    let target ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.fieldDomain key fields
    let type ← instantiateMVars (← mkForallFVars p target)
    let value ← instantiateMVars (← mkLambdaFVars p body)
    let env ← getEnv
    let name := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled ++ key
    for e in #[type,value] do
      let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
      unless missing.isEmpty do throwError "same sampled family {key}: missing {missing.toList}"
      if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasSorry then
        throwError "open same sampled family {key}"
    let pair := Lean.ShareCommon.shareCommon (type,value)
    let out ← IO.getStdout
    out.putStrLn s!"kernel checking SAME original sampled family {key}/53"
    out.flush
    addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
    out.putStrLn s!"kernel passed SAME original sampled family {key}/53"
    out.flush
construct_actual_quadratic_sampled_data φ
construct_actual_quadratic_sampled_data Φ
construct_actual_quadratic_sampled_data amp
construct_actual_quadratic_sampled_data ameas
construct_actual_quadratic_sampled_data L
construct_actual_quadratic_sampled_data m
run_meta do
  for k in #[`φ,`Φ,`amp,`ameas,`L,`m] do
    let name := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled ++ k
    let .defnInfo _ ← getConstInfo name | throwError "sampled family {k} is not checked DATA"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "nonstandard same sampled family {k}: {axioms}"
    logInfo m!"std3 original sampled DATA {k}: {axioms}"

/-! ## Exact original primitive stage: PrimitiveProofs -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
open JanetCartan.PhysicalMean
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build
private meta def tail (e : Expr) (j : Nat) := Nat.repeat (fun q => Expr.proj ``And 1 q) j e
private meta def part (e : Expr) (j : Nat) := Expr.proj ``And 0 (tail e j)
private meta def forallField (key : Name) (fields : Array (Name × Expr))
    (body : Array Expr → MetaM Expr) : MetaM Expr := do
  let out ← IO.getStdout
  out.putStrLn s!"assembling original field {key}"
  out.flush
  let result ← forallTelescope (← fieldDomain key fields) fun xs _ => do mkLambdaFVars xs (← body xs)
  out.putStrLn s!"assembled original field {key}"
  out.flush
  return result
meta def withAnalyticPrimitives (next : Array Expr → Array (Name × Expr) → MetaM Unit) : MetaM Unit := do
  withFamilies fun p original => do
    let mut fields := original
    let n ← get fields `n
    let J ← get fields `J
    let ν ← get fields `ν
    let cut := p[52]!
    let fixed := p[:44].toArray
    let native50 := p[:50].toArray
    let G ← get original `G
    let getNative (q : Expr) := JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Core.actualAtSample G q
    let getChart (q : Expr) : MetaM Expr := do
      return app (actual ++ `raw_moment_chart) ((← getNative q) ++ p[50:].toArray)
    let qOf (z : Expr) : Expr := .proj ``Prod 0 (.proj ``Prod 0 z)
    let ijSample (z : Expr) : Expr := .proj ``Prod 0 z
    let ijBand (z : Expr) : Expr := .proj ``Prod 1 z
    let localPoint (z : Expr) := pair (.proj ``Prod 1 (.proj ``Prod 0 z)) (.proj ``Prod 1 z)
    let family (f : Expr → MetaM Expr) :=
      withLocalDeclNoLocalInstanceUpdate `sample .default ν fun q => do mkLambdaFVars #[q] (← f q)
    let localPh ← family fun q => return app (actual ++ `rawPhase) (← getNative q)
    let hph ← family fun q => return part (← getChart q) 0
    let top ← synthInstance (← mkAppM ``TopologicalSpace #[ν])
    let disc ← get fields `instDiscreteTopology
    fields := fields.push (`hφ,mkAppN (mkConst (actual ++ `sampled_phase_continuous) [.zero]) #[ν,top,disc,n,J,localPh,hph])
    fields := fields.push (`hφs,← forallField `hφs fields fun z => do
      return mkApp (part (← getChart (qOf z[0]!)) 3) (← localPoint z[0]!))
    fields := fields.push (`hΦ,← forallField `hΦ fields fun z => do
      return mkApp (part (← getChart (ijSample z[0]!)) 1) (ijBand z[0]!))
    fields := fields.push (`hamp,← forallField `hamp fields fun z => do
      return app (actual ++ `forwardAmplitude_contDiff) ((← getNative (ijSample z[2]!)) ++ z[:2].toArray))
    fields := fields.push (`ha,← forallField `ha fields fun z => do
      return app `JanetCartan.PhysicalMean.OriginalCanonicalRow.ameasAtPoint_contDiff ((← getNative (ijSample z[1]!)).push z[0]!))
    fields := fields.push (`hL,← forallField `hL fields fun z => do
      return mkAppN (part (← getChart (ijSample z[0]!)) 2) #[ijBand z[0]!,z[1]!])
    let localMask ← family fun q => return (← inferType (← getChart q)).getAppArgs[4]!
    let localRegular (q : Expr) : MetaM Expr := do
      return app (actual ++ `rawMask_regular) (← getNative q)
    let localPrefixContinuous ← family fun q => do
      let mask := app (actual ++ `rawMask) (← getNative q)
      return app (actual ++ `prefixMask_continuous) #[n,J,cut,mask,part (← localRegular q) 0]
    let localPrefixCompact ← family fun q => do
      let mask := app (actual ++ `rawMask) (← getNative q)
      return app (actual ++ `prefixMask_compact) #[n,J,cut,mask,part (← localRegular q) 1]
    fields := fields.push (`hm,mkAppN (mkConst (actual ++ `sampled_mask_continuous) [.zero])
      #[ν,top,disc,n,J,localMask,localPrefixContinuous])
    fields := fields.push (`hms,mkAppN (mkConst (actual ++ `sampled_mask_compact) [.zero])
      #[ν,← get fields `instFintype,top,disc,n,J,localMask,localPrefixCompact])
    fields := fields.push (`hhigh,← forallField `hhigh fields fun z => do
      let q := qOf z[0]!
      let mask := app (actual ++ `rawMask) (← getNative q)
      return app (actual ++ `prefixMask_high) #[n,J,cut,mask,tail (← localRegular q) 2,← localPoint z[0]!,z[1]!])
    let K ← get fields `K
    let hψ := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Geometry.observation_support K.getAppArgs
    let composeSupport (h₁ h₂ : Expr) : MetaM Expr := do
      let t ← inferType h₁
      let args ← if t.isAppOfArity ``Set.Subset 3 then pure t.getAppArgs else do
        unless t.isAppOfArity ``LE.le 4 && t.getAppArgs[0]!.isAppOfArity ``Set 1 do
          throwError "changed original support relation {t.getAppFn} / {t.getAppNumArgs}"
        pure #[t.getAppArgs[0]!.getAppArgs[0]!,t.getAppArgs[2]!,t.getAppArgs[3]!]
      return mkAppN (mkConst ``Set.Subset.trans [.zero]) (args ++ #[K,h₁,h₂])
    fields := fields.push (`hampK,← forallField `hampK fields fun z => do
      let h := app (actual ++ `forwardAmplitude_tsupport) ((← getNative (ijSample z[2]!)) ++ #[z[0]!,z[1]!,z[3]!])
      composeSupport h hψ)
    fields := fields.push (`haK,← forallField `haK fields fun z => do
      let h := app `JanetCartan.PhysicalMean.OriginalCanonicalRow.ameasAtPoint_support_measurement
        ((← getNative (ijSample z[1]!)) ++ #[z[0]!,z[2]!])
      composeSupport h (app (actual ++ `common_measurement_support) native50))
    fields := fields.push (`hagree,← forallField `hagree fields fun z => do
      return mkAppN (part (← getChart (qOf z[0]!)) 5) (#[← localPoint z[0]!] ++ z[1:].toArray))
    fields := fields.push (`hphase,← forallField `hphase fields fun z => do
      return mkAppN (part (← getChart (qOf z[0]!)) 6) (#[← localPoint z[0]!] ++ z[1:].toArray))
    fields := fields.push (`hGj,← forallField `hGj fields fun z => do
      return app (actual ++ `forwardAmplitude_total_jets) ((← getNative (ijSample z[2]!)) ++
        #[z[0]!,z[1]!,z[3]!,z[5]!,z[6]!,z[7]!]))
    let rSource := app ``Nat.mul #[mkNatLit 2,app ``Nat.add #[app ``Nat.div #[n,mkNatLit 2],mkNatLit 2]]
    let hreserve := app ``JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Packing.chart_reserve #[n,p[31]!,p[39]!]
    let localJets (q : Expr) := do
      return mkAppN (tail (← getChart q) 7) #[rSource,hreserve]
    fields := fields.push (`hΦj,← forallField `hΦj fields fun z => do
      return mkAppN (.proj ``And 1 (← localJets (ijSample z[0]!))) (#[ijBand z[0]!] ++ z[1:].toArray))
    let T ← get fields `T
    let hT ← get fields `hT
    let Badj ← get fields `Badj
    let hMeasured ← get fields `measuredBudget_le_Badj
    let hDirection ← get fields `directionBudget_le_Badj
    fields := fields.push (`haj,← forallField `haj fields fun z => do
      let native ← getNative (ijSample z[1]!)
      let bounded := app ``JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Packing.measured_budget_mono
        #[n,app `JanetCartan.PhysicalMean.OriginalCanonicalRow.ameasAtPoint native,K,
          app `JanetCartan.PhysicalMean.OriginalCanonicalRow.measuredAmplitudeBudget fixed,Badj,T,hT,hMeasured,
          app `JanetCartan.PhysicalMean.OriginalCanonicalRow.ameasAtPoint_jets native]
      return mkAppN bounded #[z[0]!,z[2]!,z[4]!,z[5]!,z[6]!])
    fields := fields.push (`hLj,← forallField `hLj fields fun z => do
      let q := ijSample z[0]!
      let ca := (← inferType (← getChart q)).getAppArgs
      let bounded := app ``JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Packing.trade_budget_mono
        #[n,J,ca[5]!,ca[4]!,K,app (actual ++ `directionBudgetTotal) fixed,Badj,T,hT,hDirection,
          .proj ``And 0 (← localJets q)]
      return mkAppN bounded (#[ijBand z[0]!] ++ z[1:].toArray))
    next p (← retainCheckedFields p fields)
end JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build

/-! ## Exact original primitive stage: CheckedAnalyticFields -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
elab "construct_actual_quadratic_analytic_field " key:ident : command => liftTermElabM do
  let key := key.getId.eraseMacroScopes
  JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.withAnalyticPrimitives fun p fields => do
    let proof ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.get fields key
    let target ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.fieldDomain key fields
    let type ← instantiateMVars (← mkForallFVars p target)
    let value ← instantiateMVars (← mkLambdaFVars p proof)
    let env ← getEnv
    let name := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled ++ key
    for e in #[type,value] do
      let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
      unless missing.isEmpty do throwError "same analytic field {key}: missing {missing.toList}"
      if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasSorry then
        throwError "open same analytic field {key}"
    let pair := Lean.ShareCommon.shareCommon (type,value)
    let out ← IO.getStdout
    out.putStrLn s!"kernel checking SAME original analytic field {key}/53"
    out.flush
    addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
    out.putStrLn s!"kernel passed SAME original analytic field {key}/53"
    out.flush
construct_actual_quadratic_analytic_field hφ
construct_actual_quadratic_analytic_field hφs
construct_actual_quadratic_analytic_field hΦ
construct_actual_quadratic_analytic_field hamp
construct_actual_quadratic_analytic_field ha
construct_actual_quadratic_analytic_field hL
construct_actual_quadratic_analytic_field hm
construct_actual_quadratic_analytic_field hms
construct_actual_quadratic_analytic_field hhigh
construct_actual_quadratic_analytic_field hampK
construct_actual_quadratic_analytic_field haK
construct_actual_quadratic_analytic_field hagree
construct_actual_quadratic_analytic_field hphase
construct_actual_quadratic_analytic_field hCj
construct_actual_quadratic_analytic_field hGj
construct_actual_quadratic_analytic_field hΦj
construct_actual_quadratic_analytic_field haj
construct_actual_quadratic_analytic_field hLj
run_meta do
  for k in #[`hφ,`hφs,`hΦ,`hamp,`ha,`hL,`hm,`hms,`hhigh,`hampK,`haK,`hagree,`hphase,
      `hCj,`hGj,`hΦj,`haj,`hLj] do
    let name := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled ++ k
    let .thmInfo _ ← getConstInfo name | throwError "same analytic field {k} is not a checked theorem"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "nonstandard same analytic field {k}: {axioms}"
    logInfo m!"std3 original analytic field {k}: {axioms}"

/-! ## Exact original primitive stage: CheckedRepresentationFields -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
elab "construct_actual_quadratic_representation_field " key:ident : command => liftTermElabM do
  let key := key.getId.eraseMacroScopes
  JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.withFamilies fun p fields => do
    let p50 := p[:50].toArray
    let shift := JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.app `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift p50
    let rowp := p50 ++ #[shift,p[52]!]
    let target ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.fieldDomain key fields
    let proof ← if key == `hArep then do
      let n ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.get fields `n
      let J ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.get fields `J
      let A ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.get fields `A
      let An ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.get fields `An
      let native := JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.app `JanetCartan.PhysicalMean.OriginalCanonicalRow.hArep rowp
      forallBoundedTelescope target (some 1) fun q _ => do
        mkLambdaFVars q (JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.app ``JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Representation.hArep_of_pointwise
          #[n,J,mkApp A q[0]!,mkApp An q[0]!,mkApp native q[0]!])
    else if key == `hweight then
      pure (JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.sample_weights_nonneg
        (p50.push shift))
    else throwError "unexpected original representation key {key}"
    let type ← instantiateMVars (← mkForallFVars p target)
    let value ← instantiateMVars (← mkLambdaFVars p proof)
    let env ← getEnv
    for e in #[type,value] do
      let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
      unless missing.isEmpty do throwError "same original representation {key}: missing {missing.toList}"
      if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasSorry then
        throwError "open original representation {key}"
    let pair := Lean.ShareCommon.shareCommon (type,value)
    let out ← IO.getStdout
    out.putStrLn s!"kernel checking SAME original representation {key}/53"
    out.flush
    addDecl (.thmDecl {name := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled ++ key,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
    out.putStrLn s!"kernel passed SAME original representation {key}/53"
    out.flush
construct_actual_quadratic_representation_field hArep
construct_actual_quadratic_representation_field hweight
run_meta do
  for k in #[`hArep,`hweight] do
    let name := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled ++ k
    let .thmInfo _ ← getConstInfo name | throwError "original representation {k} is not a checked theorem"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "nonstandard original representation {k}: {axioms}"
    logInfo m!"std3 original representation {k}: {axioms}"

/-! ## Exact original primitive stage: TesterPhaseData -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
elab "construct_actual_quadratic_individual_phase " mode:num : command => liftTermElabM do
  let app (s : Name) (p : Array Expr) := mkAppN (mkConst s) p
  JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Core.withCore fun p cut fields => do
    let get (s : Name) := (fields.find? (·.1 == s)).get!.2
    withLocalDeclNoLocalInstanceUpdate `sample .default (get `ν) fun q => do
      let native ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Core.actualAtSample (get `G) q
      let rawSample : Expr := .proj ``Subtype 0 (.proj ``Sigma 1 q)
      let h := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.individualTester
        (p ++ #[cut,native[50]!,rawSample])
      let ex ← inferType h
      unless ex.isAppOfArity ``Exists 2 do throwError "lost original individual tester"
      withLocalDeclNoLocalInstanceUpdate `P .default ex.getAppArgs[0]! fun P => do
        withLocalDeclNoLocalInstanceUpdate `spec .default (ex.getAppArgs[1]!.beta #[P]) fun spec => do
          forallBoundedTelescope (← inferType (.proj ``And 1 spec)) (some 1) fun _ result => do
            let some k := result.find? (·.isAppOfArity `JanetCartan.PhysicalMean.sampledMomentKernel 7)
              | throwError "lost same original tester phase"
            let phase := k.getAppArgs[2]!
            let ty ← inferType phase
            let params := p.push q
            let name := if mode.getNat == 0 then `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.IndividualTesterPhase.phase51 else `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.IndividualTesterPhase.same_raw
            let named := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.IndividualTesterPhase.phase51 params
            let rhs := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.rawPhase native
            let target := if mode.getNat == 0 then ty else mkAppN (mkConst ``Eq [.succ .zero]) #[ty,named,rhs]
            let proof := if mode.getNat == 0 then phase else mkAppN (mkConst ``Eq.refl [.succ .zero]) #[ty,named]
            let type ← instantiateMVars (← mkForallFVars params target)
            let value ← instantiateMVars (← mkLambdaFVars params proof)
            let env ← getEnv
            for e in #[type,value] do
              let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
              unless missing.isEmpty do throwError "same tester phase missing {missing.toList}"
              if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasSorry then throwError "open same tester phase"
            let pair := Lean.ShareCommon.shareCommon (type,value)
            let out ← IO.getStdout
            out.putStrLn s!"kernel checking {name}/51 by separate data and rfl commands"
            out.flush
            if mode.getNat == 0 then
              addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
            else
              addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
            out.putStrLn s!"kernel passed {name}/51"
            out.flush
construct_actual_quadratic_individual_phase 0
construct_actual_quadratic_individual_phase 1
#print axioms JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.IndividualTesterPhase.phase51
#print axioms JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.IndividualTesterPhase.same_raw

/-! ## Exact original primitive stage: AggregateTesterPhase -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
elab "construct_actual_quadratic_aggregate_phase " mode:num : command => liftTermElabM do
  let app (s : Name) (p : Array Expr) := mkAppN (mkConst s) p
  JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Core.withCore fun p cut fields => do
    let get (s : Name) := (fields.find? (·.1 == s)).get!.2
    let h := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.aggregateTester (p.push cut)
    let ex ← inferType h
    unless ex.isAppOfArity ``Exists 2 do throwError "lost original aggregate tester"
    withLocalDeclNoLocalInstanceUpdate `P .default ex.getAppArgs[0]! fun P => do
      withLocalDeclNoLocalInstanceUpdate `spec .default (ex.getAppArgs[1]!.beta #[P]) fun spec => do
        forallBoundedTelescope (← inferType (.proj ``And 1 spec)) (some 1) fun _ result => do
          let some k := result.find? (·.isAppOfArity `JanetCartan.PhysicalMean.sampledMomentKernel 7)
            | throwError "lost same original aggregate phase"
          let phase := k.getAppArgs[2]!
          let ty ← inferType phase
          let name := if mode.getNat == 0 then `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.AggregateTesterPhase.phase50 else `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.AggregateTesterPhase.same_raw
          let (proof,target) ← if mode.getNat == 0 then pure (phase,ty) else do
            let (rhs,eqPointwise) ← forallBoundedTelescope ty (some 1) fun z _ => do
              let q : Expr := .proj ``Prod 0 (.proj ``Prod 0 z[0]!)
              let j : Expr := .proj ``Prod 1 (.proj ``Prod 0 z[0]!)
              let η : Expr := .proj ``Prod 1 z[0]!
              let loc := mkAppN (mkConst ``Prod.mk [.zero,.zero]) #[← inferType j,← inferType η,j,η]
              let native ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Core.actualAtSample (get `G) q
              let value := mkApp (app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.rawPhase native) loc
              let eq ← mkAppM ``congrFun #[app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.IndividualTesterPhase.same_raw (p.push q),loc]
              return (← mkLambdaFVars z value,← mkLambdaFVars z eq)
            let eq ← mkAppM ``funext #[eqPointwise]
            pure (eq,mkAppN (mkConst ``Eq [.succ .zero]) #[ty,app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.AggregateTesterPhase.phase50 p,rhs])
          let type ← instantiateMVars (← mkForallFVars p target)
          let value ← instantiateMVars (← mkLambdaFVars p proof)
          let env ← getEnv
          for e in #[type,value] do
            let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
            unless missing.isEmpty do throwError "same aggregate phase missing {missing.toList}"
            if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasSorry then throwError "open same aggregate phase"
          let pair := Lean.ShareCommon.shareCommon (type,value)
          let out ← IO.getStdout
          out.putStrLn s!"kernel checking {name}/50 from SAME local phase equality"
          out.flush
          if mode.getNat == 0 then
            addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
          else
            addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
          out.putStrLn s!"kernel passed {name}/50"
          out.flush
construct_actual_quadratic_aggregate_phase 0
construct_actual_quadratic_aggregate_phase 1
#print axioms JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.AggregateTesterPhase.phase50
#print axioms JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.AggregateTesterPhase.same_raw

/-! ## Exact original primitive stage: TesterPrimitives -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
open JanetCartan.PhysicalMean
namespace JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build
private meta def chooseTester (h : Expr) : MetaM (Expr × Expr) := do
  return (← mkAppM ``Classical.choose #[h],← mkAppM ``Classical.choose_spec #[h])
private meta def moveTesterPhase (P action eq : Expr) : MetaM Expr := do
  let k ← forallBoundedTelescope (← inferType action) (some 1) fun _ t => do
    let some k := t.find? (·.isAppOfArity `JanetCartan.PhysicalMean.sampledMomentKernel 7)
      | throwError "same tester lost its kernel"
    return k
  let a := k.getAppArgs
  if a[2]!.hasLooseBVars || a[3]!.hasLooseBVars || a[4]!.hasLooseBVars then throwError "tester primitive escaped native integral"
  let actionType ← inferType action
  let some lp := actionType.bindingDomain!.find? (·.isAppOfArity ``MeasureTheory.Lp 6)
    | throwError "same selected tester lost native Lp input"
  let la := lp.getAppArgs
  let et ← inferType eq
  unless et.isAppOfArity ``Eq 3 do throwError "same tester lost checked phase equality"
  let phaseArgs := et.getAppArgs
  -- The exact-field kernel check compares this proved phase with the shared
  -- data; MetaM deliberately does not unfold the original current to do so.
  return mkAppN (mkConst ``JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Packing.native_tester_phase_transport [.zero])
    #[a[0]!,a[1]!,la[2]!,la[5]!,phaseArgs[1]!,phaseArgs[2]!,eq,a[3]!,a[4]!,P,action]
meta def withTesterAndForwardPrimitives (next : Array Expr → Array (Name × Expr) → MetaM Unit) : MetaM Unit := do
  withAnalyticPrimitives fun p original => do
    let mut fields := original
    let p50 := p[:50].toArray
    let cut := p[52]!
    let G ← get fields `G
    let native (q : Expr) := JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Core.actualAtSample G q
    let bare (q : Expr) : MetaM Expr := do
      let args ← native q
      let node : Expr := .proj ``Subtype 0 (.proj ``Sigma 1 q)
      return app (actual ++ `individualTester) (p50 ++ #[cut,args[50]!,node])
    let Tbare ← forallBoundedTelescope (← fieldDomain `Tbare fields) (some 1) fun q _ => do
      mkLambdaFVars q (← chooseTester (← bare q[0]!)).1
    fields := fields.push (`Tbare,Tbare)
    let hTbare ← forallBoundedTelescope (← fieldDomain `hTbare fields) (some 1) fun q _ => do
      let (op,spec) ← chooseTester (← bare q[0]!)
      let eq := app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.IndividualTesterPhase.same_raw (p50.push q[0]!)
      let action ← moveTesterPhase op (.proj ``And 1 spec) eq
      mkLambdaFVars q action
    fields := fields.push (`hTbare,hTbare)
    let hTbareBound ← forallBoundedTelescope (← fieldDomain `hTbareBound fields) (some 1) fun q _ => do
      mkLambdaFVars q (.proj ``And 0 (← chooseTester (← bare q[0]!)).2)
    fields := fields.push (`hTbareBound,hTbareBound)
    let (Tfull,fullSpec) ← chooseTester (app (actual ++ `aggregateTester) (p50.push cut))
    fields := fields.push (`Tfull,Tfull)
    let hTfull ← moveTesterPhase Tfull (.proj ``And 1 fullSpec)
      (app `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.AggregateTesterPhase.same_raw p50)
    fields := fields ++ #[(`hTfull,hTfull),(`hTfullBound,.proj ``And 0 fullSpec)]
    let hG ← forallBoundedTelescope (← fieldDomain `hG fields) (some 3) fun xs _ => do
      let args ← native xs[0]!
      let n ← get fields `n
      let N ← get fields `N
      let J ← get fields `J
      let amp := app (actual ++ `forwardAmplitude) args
      let A ← forallBoundedTelescope (← inferType amp) (some 2) fun ac _ => do
        withLocalDeclNoLocalInstanceUpdate `j .default (app `JanetCartan.RawInputPartition.RefinedIndex #[J]) fun j => do
          mkLambdaFVars (ac.push j) (mkAppN amp ac)
      let proof := app (actual ++ `prefix_annular_realization)
        #[n,N,J,app `JanetCartan.PhysicalMean.OriginalCanonicalActual.G args,
          app (actual ++ `rawPhase) args,app (actual ++ `rawMask) args,A,
          app (actual ++ `unprefixed_forward_realization) args,cut,xs[1]!,xs[2]!]
      mkLambdaFVars xs proof
    fields := fields.push (`hG,hG)
    next p (← retainCheckedFields p fields)
end JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build

/-! ## Exact original primitive stage: CheckedTesterFields -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
elab "construct_actual_quadratic_operator_field " key:ident : command => liftTermElabM do
  let key := key.getId.eraseMacroScopes
  JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.withTesterAndForwardPrimitives fun p fields => do
    let proof ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.get fields key
    let target ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.fieldDomain key fields
    let type ← instantiateMVars (← mkForallFVars p target)
    let value ← instantiateMVars (← mkLambdaFVars p proof)
    let env ← getEnv
    let name := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled ++ key
    for e in #[type,value] do
      let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
      unless missing.isEmpty do throwError "same original tester {key}: missing {missing.toList}"
      if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasSorry then
        throwError "open same original tester field {key}"
    let pair := Lean.ShareCommon.shareCommon (type,value)
    let out ← IO.getStdout
    out.putStrLn s!"kernel checking SAME original tester/forward field {key}/53"
    out.flush
    if ← isProp target then
      addDecl (.thmDecl {name,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
    else
      addDecl (.defnDecl {name,levelParams := [],type := pair.1,value := pair.2,hints := .abbrev,safety := .safe}) (forceExpose := true)
    out.putStrLn s!"kernel passed SAME original tester/forward field {key}/53"
    out.flush
construct_actual_quadratic_operator_field Tbare
construct_actual_quadratic_operator_field hTbare
construct_actual_quadratic_operator_field hTbareBound
construct_actual_quadratic_operator_field Tfull
construct_actual_quadratic_operator_field hTfull
construct_actual_quadratic_operator_field hTfullBound
construct_actual_quadratic_operator_field hG
run_meta do
  for k in #[`Tbare,`hTbare,`hTbareBound,`Tfull,`hTfull,`hTfullBound,`hG] do
    let name := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled ++ k
    match ← getConstInfo name with
    | .thmInfo _ | .defnInfo _ => pure ()
    | _ => throwError "same tester/forward field {k} was not kernel checked"
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
      throwError "nonstandard same tester/forward field {k}: {axioms}"
    logInfo m!"std3 original tester/forward field {k}: {axioms}"

/-! ## Exact original primitive stage: CheckedMeasuredField -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
run_elab do
  JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.withFamilies fun p fields => do
    let target ← JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.fieldDomain `hAn fields
    let proof := JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.app `JanetCartan.PhysicalMean.OriginalCanonicalRow.hAn_sampledMoment
      (p[:50].toArray.push p[52]!)
    let type ← instantiateMVars (← mkForallFVars p target)
    let value ← instantiateMVars (← mkLambdaFVars p proof)
    let env ← getEnv
    for e in #[type,value] do
      let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
      unless missing.isEmpty do throwError "same actual hAn missing {missing.toList}"
      if e.hasFVar || e.hasLooseBVars || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasSorry then throwError "open same actual hAn"
    let pair := Lean.ShareCommon.shareCommon (type,value)
    let out ← IO.getStdout
    out.putStrLn "kernel checking actual measured hAn on the SAME sampled raw phase/mask/amplitude families"
    out.flush
    addDecl (.thmDecl {name := `JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled.hAn,levelParams := [],type := pair.1,value := pair.2}) (forceExpose := true)
    out.putStrLn "kernel passed actual measured hAn on the SAME sampled raw phase/mask/amplitude families"
    out.flush
#print axioms JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled.hAn

/-! ## Exact original primitive stage: CheckedMeasuredRow -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
run_elab publishOriginalMeasuredRow
#print axioms JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.Sampled.hrow

/-! ## Exact original primitive stage: CheckedPrimitiveFields -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
run_meta auditOriginalSampledPrimitives
run_meta auditOriginalPrimitiveCallback

/-! ## Exact original primitive stage: CheckedLowBudget -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Elab Command
run_elab do
  JanetCartan.PhysicalMean.OriginalMeanQuadraticPrimitives.Build.withFamilies fun p fields => do
    JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization.publishLowBudget p fields
#print axioms JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.lowConstant
#print axioms JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.lowConstant_nonneg

/-! ## Exact original primitive stage: CheckedActualLowBound -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Lean Meta Elab Command
run_elab do
  JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization.withActualQuadraticPrimitives fun p fields => do
    JanetCartan.PhysicalMean.OriginalMeanQuadraticRealization.publishLowBound p fields
run_meta auditOriginalLowBound
#print axioms JanetCartan.PhysicalMean.OriginalMeanQuadraticProfiles.Actual.low_bound
