module
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.MetricRemainder
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanResidualCore
public meta import Lean
/-!
# Domain C0 consequence of the actual fixed-core mean precision

Reuse the existing metric C0 transfer on the already selected OriginalFinalCore.
The actual execution must supply the genuine physical mean pointwise precision;
that proof is applied internally, never added to a final theorem telescope.
Consumer: `UniformHistoryCorrection.correction`, `main:eq:step-error`.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set
open scoped Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
@[expose] noncomputable section
namespace JanetCartan.PhysicalMean.OriginalSelectedPhysicalMeanDefectTemplate
private theorem cNorm_of_pointwise_on_core {n : ℕ} (C : Set (Euclidean n))
    (E : Euclidean n → MetricTensor n) (B : ℝ) (hzero : (0 : Euclidean n) ∈ C)
    (h : ∀ x ∈ C, ‖E x‖ ≤ B) : cNorm C 0 E ≤ B :=
  cNorm_zero_le_of_norm_bound ((norm_nonneg _).trans (h 0 hzero)) h
end JanetCartan.PhysicalMean.OriginalSelectedPhysicalMeanDefectTemplate
end
public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedPhysicalMeanDefectTemplate
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalSelectedMeanData
private def cores := `JanetCartan.PhysicalMean.OriginalSelectedMeanResidualCore
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
elab "publish_actual_physical_mean_defect " mode:num : command => liftTermElabM do
  unless mode.getNat < 2 do throwError "actual mean C0 defect: unknown mode"
  let old := root ++ (if mode.getNat == 0 then `physicalMean_error_le_precision_on_common_core
    else `physicalMean_error_le_requested_precision_on_common_core)
  let count := if mode.getNat == 0 then 59 else 60
  forallBoundedTelescope (← getConstInfo old).type (some count) fun p target => do
    unless p.size == count && target.isAppOfArity ``LE.le 4 do
      throwError "actual mean C0 defect: original pointwise precision boundary changed"
    let lhs := target.getAppArgs[2]!
    unless lhs.isAppOfArity ``Norm.norm 3 do
      throwError "actual mean C0 defect: not the literal Frobenius error norm"
    let some C := (← inferType p[58]!).find? (·.isAppOfArity (cores ++ `core) 44)
      | throwError "actual mean C0 defect: lost SAME existing original fixed core"
    let n := app ``Nat.succ #[p[0]!]
    let E ← mkLambdaFVars #[p[57]!] lhs.getAppArgs[2]!
    let hpoint ← mkLambdaFVars #[p[57]!,p[58]!] (app old p)
    let hi := Expr.proj ``And 1 (app (cores ++ `compact_neighborhood) C.getAppArgs)
    let hzero ← Term.TermElabM.run'
      (PhysicalBackground.NativeReferenceSourceTemplate.termWith [(`h,hi)] "interior_subset h")
    let proof := app ``cNorm_of_pointwise_on_core #[n,C,E,target.getAppArgs[3]!,hzero,hpoint]
    let params := p[:57].toArray ++ (if mode.getNat == 0 then #[] else #[p[59]!])
    let type ← instantiateMVars (← mkForallFVars params (← inferType proof))
    let value ← instantiateMVars (← mkLambdaFVars params proof)
    let env ← getEnv
    for e in #[type,value] do
      let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
      unless missing.isEmpty do throwError "actual mean C0 defect: missing original producers {missing.toList}"
      if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
        throwError "actual mean C0 defect: point or analytic premise escaped"
    let (type,value) := Lean.ShareCommon.shareCommon (type,value)
    let name := root ++ (if mode.getNat == 0 then `physicalMean_error_cNorm_le_precision_on_common_core
      else `physicalMean_error_cNorm_le_requested_precision_on_common_core)
    liftM <| IO.eprintln s!"actual mean C0 defect: kernel checking {name}/{params.size}"
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
    addDocStringCore name "Actual SAME full-source Schwartz mean C0 defect on the existing OriginalFinalCore. The actual pointwise mean precision and proven fixed-core neighborhood supply the existing C0 transfer internally; only numerical initial/current reaches remain. No alternate domain or analytic success assumption (main:eq:step-error, main:eq:mean-equation)."
    liftM <| IO.eprintln s!"actual mean C0 defect: kernel passed {name}/{params.size}"
end JanetCartan.PhysicalMean.OriginalSelectedPhysicalMeanDefectTemplate
end
