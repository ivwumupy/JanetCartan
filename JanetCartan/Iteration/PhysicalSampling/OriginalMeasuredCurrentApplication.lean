module

public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonCurrent
public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredBandBudgets
public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredSupport
public meta import Lean

/-!
# Actual measured Mean and Band geometry/profile applications

Use the original joined Graph/native current (one fixed source scale, exact
physical Schwartz history) to discharge the geometry, phase, metric and normal
gaps, measurement, fixed cutoff, and every retained coefficient/free-covector
jet in the measured Mean/Band continuations. The positive initial density and
its high profile belong to the actual background construction; the same uncut
response still has its own later field estimates. No sampling event is chosen
here (`app:ch_waves:eq:sampling-operator-bounds`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.PhysicalSampling.OriginalMeasuredCurrentApplication

private theorem pointwise_at_order_zero {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} {r : ℕ} {L : ℝ} {A : ℕ → ℝ} (hg : ContDiff ℝ ∞ g)
    (h : ∀ K : Set E, HasDerivativeProfile K g r L A) : ∀ x, ‖g x‖ ≤ A 0 := by
  intro x
  have h₀ := norm_le_cNorm (s := ({x} : Set E)) (r := 0) isCompact_singleton
    (hg.of_le (by simp)) (mem_singleton x)
  have hp := h ({x} : Set E) 0
  simpa only [Nat.zero_sub, pow_zero, mul_one] using h₀.trans hp

private theorem order_floor (n : ℕ) :
    20 * (n + 1) + 1 ≤ RawPrimary.SliceBounds.rawSliceParameterOrder n := by
  simp only [RawPrimary.SliceBounds.rawSliceParameterOrder, RawPrimary.SliceBounds.rawSliceJetOrder]
  omega

private theorem measure_reserve {r rStar : ℕ} (h : 14 + (r + 2) ≤ rStar) :
    2 + r ≤ rStar := by omega

private theorem one_le_scale {S R : ℝ} (htwo : 2 ≤ S) (hR : S ≤ R) (j : ℕ) :
    1 ≤ currentCoefficientScale R j := one_le_currentCoefficientScale
      ((by norm_num : (1 : ℝ) ≤ 2).trans (htwo.trans hR)) j

private theorem band_geometry_order {n N : ℕ} {K : Set (Euclidean n)}
    {F : Euclidean n → Euclidean N} {M : ℝ} (h : cNorm K (20 * (n + 1) + 5) F ≤ M) :
    cNorm K (20 * n + 5) F ≤ M := (cNorm_mono_order (by omega)).trans h

private theorem ball_in_domain {E : Type*} [PseudoMetricSpace E] {x : E} {r : ℝ} {s : Set E}
    (h : closedBall x r ⊆ s) : ball x r ⊆ s := ball_subset_closedBall.trans h

end JanetCartan.PhysicalSampling.OriginalMeasuredCurrentApplication
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalMeasuredCurrentApplication
open Lean Meta Elab Command

private def root := `JanetCartan.PhysicalSampling.OriginalMeasuredCurrent
private def current := `JanetCartan.PhysicalNormalInverse.OriginalComparisonCurrent
private def mean := `JanetCartan.PhysicalSampling.OriginalMeasuredMean
private def band := `JanetCartan.PhysicalSampling.OriginalMeasuredBand
private def choices := `JanetCartan.PhysicalSampling.OriginalChoices

private def save (short : Name) (params : Array Expr) (proof : Expr) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars params (← inferType proof))
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  if type.hasMVar || value.hasMVar || type.hasFVar || value.hasFVar ||
      type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then
    throwError "actual measured current: open or recovered field {short}"
  addDecl (.thmDecl {name := root ++ short, levelParams := [], type, value}) (forceExpose := true)
  logInfo m!"checked actual original measured current {short} on {params.size} inputs"

private def field (h : Expr) (k : Nat) (last := false) : Expr :=
  let tail := (List.range k).foldl (fun v _ ↦ Expr.proj ``And 1 v) h
  if last then tail else .proj ``And 0 tail

private def withCurrent (k : Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let info ← getConstInfo (current ++ `current)
  forallBoundedTelescope info.type (some 49) fun xs _ => do
    unless xs.size == 49 do throwError "actual measured current: expected original43 plus reached history6"
    let info ← getConstInfo (current ++ `S)
    let some body := info.value? | throwError "actual measured current: joined threshold body missing"
    let maxTerm := (body.beta xs[:43].toArray).headBeta
    let some old := maxTerm.find? (·.isAppOfArity `JanetCartan.PhysicalNormalInverse.OriginalComparison.S 35)
      | throwError "actual measured current: actual shared prehistory35 source missing"
    k xs old.getAppArgs

/-- Global MC=Cmeasure(0) and the actual sharp core support, proved from the
same current49; no density, response, or estimate premise. -/
elab "cache_original_measured_current_measurement " which:num : command =>
    liftTermElabM <| withTransparency .reducible <| withCurrent fun xs _ => do
  let h := mkAppN (mkConst (current ++ `measurement)) xs
  let hC := field h 0
  let C := (← inferType hC).appArg!
  unless C.isAppOfArity `JanetCartan.Sampling.canonicalSamplingMeasurement 4 do
    throwError "actual measured current: actual Euclidean stress measurement missing"
  match which.getNat with
  | 0 => save `measurement_bound xs (← mkAppM ``pointwise_at_order_zero #[hC, field h 1])
  | 1 => save `measurement_support xs (mkAppN
      (mkConst `JanetCartan.PhysicalSampling.OriginalMeasuredSupport.measurement_support_in_original_sharp_ball)
      (xs[:22].toArray ++ #[xs[40]!, C.getAppArgs[1]!]))
  | _ => throwError "actual measured current: invalid measurement field"

private def withInputs (xs fixed : Array Expr)
    (k : Array Expr → Array Expr → Array Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  let measure := mkAppN (mkConst (current ++ `measurement)) xs
  let C := (← inferType (field measure 0)).appArg!
  unless C.isAppOfArity `JanetCartan.Sampling.canonicalSamplingMeasurement 4 do
    throwError "actual measured current: native measurement head changed"
  let n := C.getAppArgs[0]!
  let order := mkApp (mkConst `JanetCartan.RawPrimary.SliceBounds.rawSliceParameterOrder) n
  let base := mkAppN (mkConst (mean ++ `initialized)) fixed
  forallBoundedTelescope (← inferType base) (some 2) fun response _ => do
    let static := fixed ++ response
    let info ← getConstInfo (mean ++ `initialized)
    let some body := info.value? (allowOpaque := true) | throwError "actual measured current: mean factory body missing"
    let actual := (body.beta static).headBeta
    unless actual.isAppOfArity (choices ++ `Mean.continuation) 62 do
      throwError "actual measured current: no actual retained mean geometry"
    let retained := mkAppN (mkConst (current ++ `retained_profiles)) xs
    forallBoundedTelescope (← inferType retained) (some 5) fun density _ => do
      let specified := mkAppN retained (density.push order)
      forallBoundedTelescope (← inferType specified) (some 1) fun highReserve _ => do
        let specified := mkAppN specified (highReserve.push (mkApp (mkConst ``order_floor) n))
        forallBoundedTelescope (← inferType specified) (some 3) fun high _ => do
          unless response.size == 2 && density.size == 5 && highReserve.size == 1 && high.size == 3 do
            throwError "actual measured current: expected fixed response2, positive density5 and actual high reserve/profile4"
          let result := mkAppN specified high
          let parameters := xs[:43].toArray ++ response ++ xs[43:49].toArray ++ density ++ highReserve ++ high
          k parameters static actual.getAppArgs result order high[0]!

/-- Discharge the genuine smooth/current coefficients up to the remaining
finite-rate response input. The source cutoff and linear response map here
are data, universally quantified (not assumed successful); the parent applies
these functions to its literal chi2 and full physical inverse. -/
elab "apply_original_measured_current_factory " which:num : command =>
    liftTermElabM <| withTransparency .reducible <| withCurrent fun xs fixed =>
      withInputs xs fixed fun params static initial coeff order reserve => do
  let isMean := which.getNat == 0
  unless isMean || which.getNat == 1 do throwError "actual measured current: invalid factory"
  let geometry := initial[:7].toArray
  let namespacePart := if isMean then `Mean else `Band
  let actual (name : Name) := mkAppN (mkConst (current ++ name)) xs
  let ambient := actual `ambient_geometry
  let hF := field ambient 0
  let mapType ← inferType hF
  let F := mapType.getAppArgs[mapType.getAppNumArgs - 2]!
  let hC := field (actual `measurement) 0
  let C := (← inferType hC).appArg!
  let smooth0 := field coeff 4
  let smoothType ← inferType smooth0
  let amplitude := smoothType.getAppArgs[smoothType.getAppNumArgs - 2]!
  unless amplitude.isAppOfArity `JanetCartan.RawPrimary.AmplitudeGrades.Polynomial.fullLeadingNormal 13 do
    throwError "actual measured current: expected literal fullLeadingNormal13, got {amplitude.getAppFn} at {amplitude.getAppNumArgs}"
  let a := amplitude.getAppArgs
  let rowData := a[8:12].toArray
  let density := a[12]!
  let margin := field (actual `phase_margins) (if isMean then 1 else 2)
  let threshold := mkAppN (mkConst (choices ++ namespacePart ++ `hδ_threshold)) geometry
  let low ← mkAppM `lt_of_lt_of_le #[margin, threshold]
  let hL ← mkAppM ``one_le_scale #[mkAppN (mkConst (current ++ `hS)) xs[:43].toArray, xs[44]!, xs[45]!]
  let L := (← inferType hL).appArg!
  let continuation := mkAppN (mkConst ((if isMean then mean else band) ++ `continuation)) static
  let mapBound ← if isMean then pure (field coeff 0) else mkAppM ``band_geometry_order #[field coeff 0]
  let currentArgs := #[F, hF, field ambient 1, field ambient 2 true,
    mapBound, field coeff 1, field coeff 2, margin, low]
  let first := if isMean then #[C, hC] ++ currentArgs else currentArgs.push (field coeff 3)
  let partialApp := mkAppN continuation (first ++ rowData)
  forallBoundedTelescope (← inferType partialApp) (some 2) fun source _ => do
    unless source.size == 2 do throwError "actual measured current: source cutoff and full operator required"
    let partialApp := mkAppN partialApp (source.push density)
    let smooth := #[smooth0, field coeff 5, field coeff 6, field coeff 7]
    let profiles := #[field coeff 8, field coeff 9, field coeff 10, field coeff 11, field coeff 12]
    if isMean then
      let lower := mkAppN (actual `measurement_at_reserve) #[order, ← mkAppM ``measure_reserve #[reserve]]
      let joint := mkApp (field lower 2 true) initial[28]!
      let inputs := #[← mkAppM ``ball_in_domain #[field coeff 3]] ++ smooth ++
        #[L, order, hL, mkApp (mkConst ``order_floor) C.getAppArgs[0]!, joint] ++ profiles
      let proof := mkAppN partialApp inputs
      save `mean_before_response params (← mkLambdaFVars source proof)
    else
      let fixedRow := xs[:22].toArray.push xs[40]!
      let jets := mkAppN (mkConst (band ++ `cutoff_jets)) fixedRow
      let inputs := #[initial[33]!, initial[34]!, initial[35]!, initial[36]!, jets] ++ smooth ++ #[L, hL] ++ profiles
      let partialApp := mkAppN partialApp inputs
      let next ← whnf (← inferType partialApp)
      unless next.isForall do throwError "actual measured current: missing free-covector jets"
      let free ← forallBoundedTelescope next.bindingDomain! (some 2) fun jw _ =>
        mkLambdaFVars jw (mkApp (field coeff 13 true) jw[0]!)
      let proof := mkApp partialApp free
      save `band_before_response params (← mkLambdaFVars source proof)

end JanetCartan.PhysicalSampling.OriginalMeasuredCurrentApplication
