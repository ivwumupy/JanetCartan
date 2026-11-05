module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles
public import JanetCartan.Iteration.PhysicalMean.FixedPicardPrecisionSelection
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Frame
import all JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Template
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEvent
import all JanetCartan.Iteration.PhysicalPrimary.OriginalPrimarySourcePhaseGeometry
import all JanetCartan.Iteration.PhysicalPairs.OriginalMaskGeometry
import all JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean

/-!
# The actual ordinary phase at the current history scale

The primary first mask uses the same scale as its complete raw amplitude.
The already reached operator threshold implies `2 ≤ R₀`, so the existing
history arithmetic gives `currentCoefficientScale R₀ j ≤ historyScale R₀ γ j`.
This specializes the actual ordinary phase jets without adding a scale gate
or changing the phase, its original chart, or its prehistory price
(`main:eq:primary-strain`, `app:ch_regular:eq:source-tail` in paper-v2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Template

open Lean Meta Elab Command

run_meta do
  withCostPhase fun c => do
    let p := c.native51
    let native := p[:51].toArray
    let hInitial ← mkAppM ``le_trans
      #[app (op ++ `fact0) c.op33, app (ns ++ `operator_reached) native]
    let facts ← mkAppM ``JanetCartan.PhysicalMean.fixedPicard_history_scale_facts
      #[hInitial, p[46]!]
    let hTR := Expr.proj ``And 0 (.proj ``And 1 (.proj ``And 1 facts))
    let R := app ``JanetCartan.historyScale
      #[p[44]!, mkConst ``JanetCartan.growthExponent, p[46]!]
    let T := app ``JanetCartan.currentCoefficientScale #[p[44]!, p[46]!]
    unless ← isDefEq (← inferType hTR) (← mkAppM ``LE.le #[T, R]) do
      throwError "ordinary primary phase: original history scale comparison changed"
    let source := app (ns ++ `jets_of_le) native
    forallBoundedTelescope (← inferType source) (some 2) fun gz _ => do
      unless gz.size == 2 do
        throwError "ordinary primary phase: original group/cube inputs changed"
      let proof := app (ns ++ `jets_of_le) (native ++ gz ++ #[R, hTR])
      save `jets_at_historyScale (native ++ gz) proof (← inferType proof)

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.PhaseProfiles.Template
end
