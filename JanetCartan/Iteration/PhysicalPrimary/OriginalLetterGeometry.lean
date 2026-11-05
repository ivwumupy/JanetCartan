module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalSourceProfiles
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedCurrent
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRetardedWhole
public import JanetCartan.Iteration.PhysicalEllipticWords.MeasuredResidualAllCasesTemplate
public import JanetCartan.Iteration.PhysicalPrimary.SolverStep
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalLetterGeometryTemplate

/-!
# The native letter and solver thresholds on the same original fixed geometry

Substitute only the original static objects and their checked certificates.
The arbitrary history index precedes each native threshold existential. Every
actual current family, stationary family and analytic profile in the native
continuation stays unchanged; its application belongs to the parent response
construction. The parameter source is the support of the SAME small cell
cutoff, not the large protected source set.
Consumers: `exists_physical_history_measured_residual_hstep` and
`exists_physical_history_paired_solver_hstep`
(`app:ch_response:eq:fixed-factor-transfer`, `app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 16000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalLetterGeometry
open PhysicalSeed PhysicalInitialization
open RegularSector.FiniteMasks.ActualFamily
open RegularSector.FinitePdo RegularSector.FiniteResidual.SelectedChart

/-- The exact small parameter support is closed and lies in the original
whole window. No source cutoff or larger source compact is substituted
(`app:ch_response:eq:response-graded-source`). -/
theorem original_parameter_source_spec {n : ℕ} (hn : 5 ≤ n) (a : OriginalPatchIndex hn)
    (cell : OriginalBoundary.centers hn a) :
    let θ : Euclidean 3 × Euclidean (n-1) → ℝ := OriginalSourceProfiles.parameterCutoff hn a cell
    IsClosed (tsupport θ) ∧ tsupport θ ⊆ OriginalRegular.wholeWindow hn a := by
  exact ⟨isClosed_tsupport _,
    (OriginalSourceProfiles.parameterCutoff_spec hn a cell).2.2.1.trans
      (OriginalSourceMasks.parameterWindow_spec hn a cell).2.1⟩

/-- The already constructed real unit-interval output has the native norm
bound, without replacing it by either the raw source or the terminal mask
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem original_output_norm_bound {E : Type} (output : E → ℝ)
    (h : ∀ y, output y ∈ Icc (0 : ℝ) 1) : ∀ y, ‖output y‖ ≤ 1 := by
  intro y
  simpa only [Real.norm_eq_abs,abs_of_nonneg (h y).1] using (h y).2

/-- The exact native endpoint output is in the same original time plateau;
only the existing common-output support certificate is used
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem original_endpoint_time_plateau {d : ℕ} {Ω : Set (Euclidean (d+1))}
    {x : Euclidean (d+1)} {RQ M : ℝ} {A₀ : Fin (d+1) → MetricTensor (d+1)}
    {K : Set (Euclidean (d+1))} (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hbuffer : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsource : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius/4)
    (output : Euclidean (d+1) → ℝ) (hsupport : tsupport output ⊆ ball x f.physicalRadius) :
    ∀ y, endpointOutputMask f p output y ≠ 0 →
      (f.chart p).timeMask =ᶠ[𝓝 (y 0)] fun _ ↦ (1 : ℝ) := by
  intro y hy
  exact (common_output_retained_geometry f p hbuffer hsource output hsupport).2.2 y
    (subset_tsupport _ hy)

apply_original_fixed_letter_geometry

end JanetCartan.PhysicalPrimary.OriginalLetterGeometry
