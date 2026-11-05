module

public import JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredMeanBudgets
public meta import Lean

/-!
# Original corrected sharp-band budgets on the exact measured-mean tuple

Use the SAME retained metric/normal gaps, five profiles, uncut-response
budget, common joint cutoff, detector, and high-pass as the original measured
mean. The additional free-covector budget is the sibling Pζ of the SAME
native retained choice; the joint cutoff budget is its actual compact C-norm;
the global measurement bound is Cmeasure(0). Every numerical constant precedes
the physical history, frequency ceiling, rate and sample. The dynamic response
and current inputs are not conclusions here
(`app:ch_waves:eq:sampling-operator-bounds`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.PhysicalSampling.OriginalMeasuredBandBudgetsApplication

private def cutoffBudget {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (κ : E → ℝ) (j : ℕ) : ℝ := cNorm K j κ

private theorem cutoffBudget_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (κ : E → ℝ) : ∀ j, 0 ≤ cutoffBudget K κ j := fun j ↦ cNorm_nonneg K j κ

private theorem cutoffBudget_controls {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} {κ : E → ℝ} (hK : IsCompact K) (hκ : ContDiff ℝ ∞ κ) :
    ∀ j, ∀ w ∈ K, ‖iteratedFDeriv ℝ j κ w‖ ≤ cutoffBudget K κ j :=
  fun j _ hw ↦ norm_iteratedFDeriv_le_cNorm hK (hκ.of_le (by simp)) hw (le_refl j)

private theorem profile_nonnegative {C : ℕ → ℝ} (h : ∀ j, 0 < C j) :
    ∀ j, 0 ≤ C j := fun j ↦ (h j).le

end JanetCartan.PhysicalSampling.OriginalMeasuredBandBudgetsApplication
end

public meta section
namespace JanetCartan.PhysicalSampling.OriginalMeasuredBandBudgetsApplication
open Lean Meta Elab Command

private def ns := `JanetCartan.PhysicalSampling.OriginalMeasuredBand
private def mean := `JanetCartan.PhysicalSampling.OriginalMeasuredMean

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
    throwError "original measured band: open or recovered declaration {short}"
  if data then
    addDecl (.defnDecl {name := n, levelParams := [], type, value, hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name := n, levelParams := [], type, value}) (forceExpose := true)
  logInfo m!"checked SAME original measured sharp-band budget {short} at {params.size} fixed inputs"
  return mkAppN (mkConst n) params

private def withMean (k : Array Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  let info ← getConstInfo (mean ++ `initialized)
  let some body := info.value? (allowOpaque := true)
    | throwError "original measured band: original measured mean application unavailable"
  forallBoundedTelescope info.type (some 37) fun params _ => do
    unless params.size == 37 do throwError "original measured band: expected 37 prehistory inputs"
    let applied := (body.beta params).headBeta
    unless applied.isAppOfArity `JanetCartan.PhysicalSampling.OriginalChoices.Mean.continuation 62 do
      throwError "original measured band: not the SAME actual original mean continuation"
    k params applied.getAppArgs

/-- The fixed cutoff's compact seminorm and all-orders bound are geometry
only: the raw original22 and row, with no native scale, history or response. -/
elab "cache_original_measured_band_cutoff_field " which:num : command =>
    liftTermElabM <| withTransparency .reducible <| withMean fun params xs => do
  let rootParams := params[:22].toArray.push params[32]!
  let Acut := mkAppN (mkConst (ns ++ `Acut)) rootParams
  match which.getNat with
  | 0 => discard <| store `Acut rootParams (← mkAppM ``cutoffBudget #[xs[28]!, xs[33]!]) true
  | 1 =>
    let proof ← mkAppM ``cutoffBudget_nonneg #[xs[28]!, xs[33]!]
    let source ← mkAppM ``cutoffBudget #[xs[28]!, xs[33]!]
    let type := (← inferType proof).replace fun e => if e == source then some Acut else none
    discard <| store `hAcut rootParams proof false (some type)
  | 2 =>
    let proof ← mkAppM ``cutoffBudget_controls #[xs[30]!, xs[34]!]
    let source ← mkAppM ``cutoffBudget #[xs[28]!, xs[33]!]
    let type := (← inferType proof).replace fun e => if e == source then some Acut else none
    discard <| store `cutoff_jets rootParams proof false (some type)
  | _ => throwError "original measured band: invalid cutoff field"

/-- The original Band7 sharp coefficient sees exactly its own retained geometry
and the SAME prehistory37 source/profile packet as the measured mean. -/
elab "cache_original_measured_band_factory" : command =>
    liftTermElabM <| withTransparency .reducible <| withMean fun params xs => do
  let full := xs[60]!
  unless full.isAppOfArity `JanetCartan.PhysicalNormalInverse.OriginalMeasurement.Budgets.Cmeasure 31 do
    throwError "original measured band: actual common measurement changed"
  let profiles := full.getAppArgs ++ params[32:35].toArray
  let retained := `JanetCartan.PhysicalNormalInverse.OriginalRetained.Budgets
  let pζ := mkAppN (mkConst (retained ++ `Pζ)) profiles
  let hpζ ← mkAppM ``profile_nonnegative #[mkAppN (mkConst (retained ++ `fact4)) profiles]
  let rootParams := params[:22].toArray.push params[32]!
  let Acut := mkAppN (mkConst (ns ++ `Acut)) rootParams
  let hAcut := mkAppN (mkConst (ns ++ `hAcut)) rootParams
  let MC := mkApp full (mkNatLit 0)
  let hMC := mkApp xs[61]! (mkNatLit 0)
  let args := xs[:16].toArray ++ xs[16:22].toArray ++ #[pζ] ++ xs[22:28].toArray ++
    #[hpζ, Acut, hAcut] ++ xs[39:46].toArray ++ #[MC, hMC]
  unless args.size == 41 do throwError "original measured band: expected Band7 plus 34 fixed inputs"
  let applied := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalChoices.Band.continuation) args
  let type ← inferType applied
  unless (← whnf type).isAppOfArity ``Exists 2 do
    throwError "original measured band: expected nonnegative sharp constant before history"
  discard <| store `initialized params applied false (some type)

elab "cache_original_measured_band_budget_field " which:num : command =>
    liftTermElabM <| withTransparency .reducible do
  forallBoundedTelescope (← getConstInfo (ns ++ `initialized)).type (some 37) fun params _ => do
    let actual (name : Name) := mkAppN (mkConst (ns ++ name)) params
    let init := actual `initialized
    match which.getNat with
    | 0 => discard <| store `Csharp params (← mkAppM ``Classical.choose #[init]) true
    | 1 =>
      let ty := (← whnf (← inferType init)).appArg!.beta #[actual `Csharp]
      discard <| store `spec params (← mkAppM ``Classical.choose_spec #[init]) false (some ty)
    | 2 => discard <| store `nonnegative params (Expr.proj ``And 0 (actual `spec))
    | 3 => discard <| store `continuation params (Expr.proj ``And 1 (actual `spec))
    | _ => throwError "original measured band: invalid budget field"

end JanetCartan.PhysicalSampling.OriginalMeasuredBandBudgetsApplication
