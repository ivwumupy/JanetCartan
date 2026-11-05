module
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedPhysicalMean
public import JanetCartan.Iteration.PhysicalMean.OriginalSelectedMeanError
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
public meta import Lean
/-!
# Genuine cut mean error on the common physical and residual core

The physical cutoff remains the original Dsmooth cutoff. Its exact full-strain
germ transfers actual completedMean_error58 to the SAME Schwartz carrier.
The residual cancellation core and physical-cutoff core are explicit and kept
distinct; no false containment or altered support is used. The later fixed-core
join and genuine115 precision supply those domain/numerical inputs
(`new:eq:mean-error-formula`, `main:eq:mean-equation`).
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open scoped Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
@[expose] noncomputable section
namespace JanetCartan.PhysicalMean.OriginalSelectedPhysicalMeanError
private theorem norm_error_of_same_strain {n : ℕ} (A B H T : MetricTensor n)
    (b : ℝ) (h : A = B) (hb : ‖B+H-T‖ ≤ b) : ‖A+H-T‖ ≤ b := by
  rw [h]
  exact hb
end JanetCartan.PhysicalMean.OriginalSelectedPhysicalMeanError
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalSelectedPhysicalMeanError
open Lean Meta Elab Command
private def root := `JanetCartan.PhysicalMean.OriginalSelectedMeanData
private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
run_elab do
  let old := root ++ `completedMean_error_le_picard_residual
  forallBoundedTelescope (← getConstInfo old).type (some 58) fun p oldType => do
    unless p.size == 58 && oldType.isAppOfArity ``LE.le 4 do
      throwError "actual physical mean error: completed error58 changed"
    let stage := p[:54].toArray
    let x := p[56]!
    let germ := app (root ++ `physicalMean_full_strain) (stage.push x)
    forallBoundedTelescope (← inferType germ) (some 1) fun core _ => do
      unless core.size == 1 do throwError "actual physical mean error: physical core germ boundary changed"
      let eqProof := mkAppN germ core
      let eqType ← inferType eqProof
      unless eqType.isAppOfArity ``Eq 3 do throwError "actual physical mean error: full strain equality changed"
      let A := eqType.getAppArgs[1]!
      let B := eqType.getAppArgs[2]!
      unless B.isAppOfArity `JanetCartan.linearizedMetric 5 do
        throwError "actual physical mean error: not the full linearized metric"
      let n := B.getAppArgs[0]!
      let H := mkApp (app (root ++ `fullSampledSelf) stage) x
      let T := mkApp (app (root ++ `normalizedTarget) p[:52].toArray) x
      let proof := app ``norm_error_of_same_strain
        #[n,A,B,H,T,oldType.getAppArgs[3]!,eqProof,app old p]
      let params := p ++ core
      let type ← instantiateMVars (← mkForallFVars params (← inferType proof))
      let value ← instantiateMVars (← mkLambdaFVars params proof)
      let env ← getEnv
      for e in #[type,value] do
        let missing := e.getUsedConstants.filter (fun c => (env.find? c).isNone)
        unless missing.isEmpty do throwError "actual physical mean error: missing {missing.toList}"
        if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
          throwError "actual physical mean error: unresolved or added analytic premise"
      let (type,value) := Lean.ShareCommon.shareCommon (type,value)
      let name := root ++ `physicalMean_error_le_picard_residual
      addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
      addDocStringCore name "Actual SAME full-source Schwartz mean error bounded by its genuine Picard residual on the intersection of original residual cancellation and physical-cutoff cores. The unchanged Dsmooth cutoff has the exact full-strain germ; only original numerical reach and explicit core memberships remain, no analytic success hypothesis (main:eq:mean-equation)."
      logInfo "actual physical Schwartz mean error59: SAME full strain and Picard residual, unchanged cutoff, both original core memberships"
end JanetCartan.PhysicalMean.OriginalSelectedPhysicalMeanError
end
