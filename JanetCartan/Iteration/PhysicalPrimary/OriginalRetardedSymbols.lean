module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalRegular
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AmplitudeBounds.EvolutionCoordinates
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedSymbolsTemplate

/-!
# Actual primitive symbols of the original retarded operators

Project the complete current chart and three buffered/conic symbols from the
SAME original regular construction. The full extended Q, full B, native order-one
amplitude, phases, chart, masks and both retained operators are unchanged. No
source contraction, threshold, witness, response bound or operator is chosen.

Consumers are `PhysicalEllipticWords.exists_physical_history_measured_residual_hstep`
and `PhysicalPrimary.exists_physical_history_paired_solver_hstep`
(`app:ch_response:eq:response-graded-reduced`, `retarded-kernel`,
`app:ch_regular_base:eq:energy-complete-residual`). The parent still supplies its
common geometric cap, stationary/whole-source data and final family application.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option maxRecDepth 16000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalRetardedSymbols
open RegularSector.Characteristic
open RegularSector.Characteristic.AmplitudeBounds
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open RegularSector.Characteristic.UniformEvolution

/-- Only regroup the four original coordinates of the SAME collared matrix.
This supplies native W1 joint smoothness, with no replacement symbol
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem joint_smooth_of_matrix_smooth {d : ℕ}
    {F : RegularSector.Characteristic.TwoTimePoint (Euclidean d) →
      Matrix (Fin (d+1)) (Fin (d+1)) ℂ}
    (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (jointAmplitude (curryCharacteristicMatrix F)) :=
  hF.comp (contDiff_fst.fst.prodMk
    (contDiff_fst.snd.fst.prodMk (contDiff_fst.snd.snd.prodMk contDiff_snd)))

/-- The literal native order-zero solver and order-one residual certificates
supply BOTH orders for the SAME Op, retaining the actual phase, masks, full Q/B
and every signed/adjoint clause (`retarded-kernel`, `negative-duality`). -/
theorem retained_signed_bounds_both_orders {d : ℕ}
    {KQ : Set (Euclidean (d+1))}
    {Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1)}
    {B : Euclidean (d+1) → MetricTensor (d+1)} {Δ a : ℝ}
    {Ψ : TwoTimePhase d} {χout χsource β : Euclidean (d+1) → ℂ}
    (hs : ContDiff ℝ ∞ χsource) (W : Fin 3 → TwoTimeAmplitude d (d+1))
    (base : Fin 2 → ℝ) (cost : Fin 2 → ℕ → ℝ)
    (Op : Fin 2 → SpacetimeL2 d (d+1) →L[ℂ] SpacetimeL2 d (d+1))
    (h0 : RetainedSignedRetardedBounds KQ Q B Δ a Ψ (W 0+W 1)
      χout χsource β hs 0 (base 0) (cost 0) (Op 0))
    (h1 : RetainedSignedRetardedBounds KQ Q B Δ a Ψ (W 2)
      χout χsource β hs 1 (base 1) (cost 1) (Op 1)) :
    ∀ o : Fin 2, RetainedSignedRetardedBounds KQ Q B Δ a Ψ
      (if o=0 then W 0+W 1 else W 2) χout χsource β hs o.val
      (base o) (cost o) (Op o) := by
  intro o
  fin_cases o
  · exact h0
  · exact h1

end JanetCartan.PhysicalPrimary.OriginalRetardedSymbols

set_option maxHeartbeats 600000 in
retain_original_current_retarded_symbols
