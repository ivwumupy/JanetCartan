module

public import JanetCartan.Iteration.PhysicalNormalInverse.OriginalComparisonBudgets
public meta import Lean

/-!
# The measured mean on the retained original analytic budgets

The already checked original Comparison factory records the actual common
measurement, five current-geometry budgets, two gaps, cutoffs and masks. Apply
its sibling Mean geometry to those SAME values. Only the Mean-specific side of
the joint minimum and its detector admission differ. The nine Comparison
quadrature arguments are absent even from the resulting declaration's proof;
the one uncut-response budget and sign precede every history and frequency.
No new source, density, current or five-profile tuple is selected
(`app:ch_waves:eq:sampling-operator-bounds`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
open Set Metric
namespace JanetCartan.PhysicalSampling.OriginalMeasuredMeanBudgetsApplication

private theorem support_min_left {E : Type*} [TopologicalSpace E] {n : ℕ}
    {κ : E → ℝ} {g : E → Euclidean n} {s₁ s₂ : ℝ}
    (h : g '' tsupport κ ⊆ closedBall 0 (min s₁ s₂ / 4)) :
    g '' Function.support κ ⊆ closedBall 0 (s₁ / 4) :=
  ((image_mono (subset_tsupport κ)).trans h).trans
    (closedBall_subset_closedBall (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)))

private theorem ball_min_left {E : Type*} [PseudoMetricSpace E]
    {x c : E} {a b : ℝ} (h : x ∈ closedBall c (min a b)) :
    x ∈ closedBall c a := closedBall_subset_closedBall (min_le_left _ _) h

private theorem half_ball_min_left {E : Type*} [PseudoMetricSpace E]
    {x c : E} {a b : ℝ} (h : x ∈ closedBall c (min a b / 2)) :
    x ∈ closedBall c (a / 2) := closedBall_subset_closedBall
      (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)) h

end JanetCartan.PhysicalSampling.OriginalMeasuredMeanBudgetsApplication
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalMeasuredMeanBudgetsApplication
open Lean Meta Elab Command

private def ns := `JanetCartan.PhysicalSampling.OriginalMeasuredMean
private def choices := `JanetCartan.PhysicalSampling.OriginalChoices

private def store (short : Name) (params : Array Expr) (proof : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let n := ns ++ short
  let target ← match target? with
    | some t => pure t
    | none => inferType proof
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params proof)
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar ||
      type.hasLevelMVar || value.hasLevelMVar || type.hasSorry || value.hasSorry then
    throwError "original measured mean: open, quadrature-dependent or recovered proof {short}"
  if data then
    addDecl (.defnDecl {name := n, levelParams := [], type, value, hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name := n, levelParams := [], type, value}) (forceExpose := true)
  logInfo m!"checked SAME original measured-mean budget {short} at {params.size} fixed inputs"
  return mkAppN (mkConst n) params

/-- Publish the literal actual Mean continuation application, sharing the
fixed numerical tuple with Comparison but NOT its geometric radius or analytic
constant. -/
elab "cache_original_measured_mean_factory" : command =>
    liftTermElabM <| withTransparency .reducible do
  let source := `JanetCartan.PhysicalNormalInverse.OriginalComparison.initialized
  let info ← getConstInfo source
  let some body := info.value? (allowOpaque := true)
    | throwError "original measured mean: actual comparison application unavailable"
  forallBoundedTelescope info.type (some 37) fun params tail => do
    unless params.size == 37 do throwError "original measured mean: expected native35 and response2"
    forallBoundedTelescope tail (some 9) fun quadrature _ => do
      unless quadrature.size == 9 do throwError "original measured mean: comparison quadrature ABI changed"
      let comparison := (body.beta (params ++ quadrature)).headBeta
      unless comparison.isAppOfArity (choices ++ `Comparison.continuation) 71 do
        throwError "original measured mean: not the actual retained Comparison continuation"
      let xs := comparison.getAppArgs
      let geometry := xs[:7].toArray
      let choice (name : Name) := mkAppN (mkConst (choices ++ `Cutoff ++ name)) geometry
      let hphysical ← mkAppM ``support_min_left #[choice `hκ_s]
      let support := choice `hψ_support
      let support ← forallBoundedTelescope (← inferType support) (some 3) fun test _ => do
        let hs := mkAppN support test
        let a := Expr.proj ``And 0 hs
        let b := Expr.proj ``And 0 (.proj ``And 1 hs)
        let tail := Expr.proj ``And 1 (.proj ``And 1 hs)
        let c ← mkAppM ``ball_min_left #[Expr.proj ``And 0 tail]
        let d ← mkAppM ``half_ball_min_left #[Expr.proj ``And 1 tail]
        mkLambdaFVars test (← mkAppM ``And.intro #[a, ← mkAppM ``And.intro
          #[b, ← mkAppM ``And.intro #[c, d]]])
      let angle := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalAdmission.mean_detector_support)
        (params[:22].toArray.push params[32]!)
      let hφ ← mkAppM `ContDiff.continuous #[xs[60]!]
      let args := geometry ++ xs[7:16].toArray ++ xs[18:30].toArray ++ xs[30:40].toArray ++
        #[hphysical] ++ xs[41:50].toArray ++ #[angle] ++ xs[51:55].toArray ++ #[support] ++
        xs[56:60].toArray ++ #[hφ, xs[61]!, xs[16]!, xs[17]!]
      unless args.size == 62 do throwError "original measured mean: expected Mean7 plus 55 fixed inputs"
      let applied := mkAppN (mkConst (choices ++ `Mean.continuation)) args
      let type ← inferType applied
      unless (← whnf type).isAppOfArity ``Exists 2 do
        throwError "original measured mean: expected prehistory existence of positive Cmean"
      discard <| store `initialized params applied false (some type)

/-- Expose each consequence separately at the ordinary resource limit. -/
elab "cache_original_measured_mean_budget_field " which:num : command =>
    liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (ns ++ `initialized)).type (some 37) fun params _ => do
    let actual (name : Name) := mkAppN (mkConst (ns ++ name)) params
    let init := actual `initialized
    match which.getNat with
    | 0 => discard <| store `Cmean params (← mkAppM ``Classical.choose #[init]) true
    | 1 =>
      let ty := (← whnf (← inferType init)).appArg!.beta #[actual `Cmean]
      discard <| store `spec params (← mkAppM ``Classical.choose_spec #[init]) false (some ty)
    | 2 => discard <| store `positive params (Expr.proj ``And 0 (actual `spec))
    | 3 => discard <| store `continuation params (Expr.proj ``And 1 (actual `spec))
    | _ => throwError "original measured mean: invalid budget field"

end JanetCartan.PhysicalSampling.OriginalMeasuredMeanBudgetsApplication
