module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalLetterGeometry
public import JanetCartan.Iteration.PhysicalPrimary.OriginalWordProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedRanges
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedSymbols
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLetterCurrentTemplate

/-! The actual original history families in the native four-case letter and
final-solver receivers. The arbitrary index is fixed before every threshold.
Current/phase/operator objects are the literal original ones; only thresholds
are joined. The final analytic/source continuation is retained explicitly
until the parent completes its actual application. Consumer:
`actual_finite_residual_word_reserved_bounds_of_one_step`
(`app:ch_regular:lem:finite-chain`). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalLetterCurrent

/-- The native reserve ledger and strengthened history order imply the two
actual joint-phase profile orders, without modifying the physical history. -/
theorem native_profile_reserves {rHistory rCoeff Rstar low : ℕ}
    (hCoeff : 2+rCoeff ≤ rHistory) (hreserve : Rstar+10 ≤ rCoeff)
    (hRstar : low+2 < Rstar) : Rstar+3 ≤ rHistory ∧ 2 ≤ Rstar := by omega

/-- The unchanged sector low-order cap bounds exactly the algebraic native
coefficient grade, without discarding the full reduced zeroth coefficient. -/
theorem native_low_coefficient_bounds {d : ℕ}
    (K : Set (Euclidean (d+1)))
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1))
    (B : Euclidean (d+1) → MetricTensor (d+1)) {M : ℝ}
    (hQ : cNorm K (RegularSector.FiniteEvolution.sectorLowOrder d) Q ≤ M)
    (hB : cNorm K (RegularSector.FiniteEvolution.sectorLowOrder d) B ≤ M) :
    cNorm K (2*(d+2)+2) Q ≤ M ∧ cNorm K (2*(d+2)+2) B ≤ M := by
  have h : 2*(d+2)+2 ≤ RegularSector.FiniteEvolution.sectorLowOrder d := by
    have := (RegularSector.FiniteEvolution.sectorLowOrder_bounds d).2.2
    omega
  exact ⟨(cNorm_mono_order h).trans hQ,(cNorm_mono_order h).trans hB⟩

/-- The existing small forcing cutoff fits the unchanged full word ball.
This statement does not localize any inverse or solver output. -/
theorem native_word_source_support {d : ℕ} {r radius : ℝ} (hr : 0 < radius)
    (χ : Euclidean (d+1) → ℝ)
    (hχ : tsupport χ ⊆ Metric.ball (0 : Euclidean (d+1)) (min r radius)) :
    tsupport χ ⊆ Metric.ball (0 : Euclidean (d+1)) (3*radius) := by
  exact hχ.trans (Metric.ball_subset_ball (by linarith [min_le_right r radius]))

apply_original_current_letter_geometry

end JanetCartan.PhysicalPrimary.OriginalLetterCurrent
