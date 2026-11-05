module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Estimates

/-!
# The common endpoint plateau and source PDO

The smaller output constructed by the retained evolution is absorbed by the
family's original output. Its source PDO uses the SAME input mask and exact
enlarged physical multiplier. Consumers: all direct terms in
`app:ch_regular_base:eq:energy-complete-residual` and `measured-adjoint`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FinitePdo
open Characteristic Characteristic.ResidualCoordinates Characteristic.PdoRealization
open Characteristic.EvolutionIntegral Characteristic.EndpointPdoBounds
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic AmplitudeBound FourierIntegral
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)

/-- The smaller common plateau is absorbed by the original output on every
selected chart. No support or angular cover is replaced
(`energy-complete-residual`, `measured-adjoint`). -/
theorem endpointOutputMask_mul_chartOutputMask
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {output : E → ℝ} (hsupp : tsupport output ⊆ ball x f.physicalRadius) (y : E) :
    endpointOutputMask f p output y * chartOutputMask f p y = endpointOutputMask f p output y := by
  by_cases hy : output (physicalCoordinates (f.chart p).index y) = 0
  · simp only [endpointOutputMask, hy, Complex.ofReal_zero, zero_mul]
  have he := interior_subset (f.outputMask_plateau
    (ball_subset_closedBall (hsupp (subset_tsupport output hy))))
  change f.outputMask (physicalCoordinates (f.chart p).index y) = 1 at he
  simp only [chartOutputMask, he, Complex.ofReal_one, mul_one]

/-- The retained common output multiplication identity in chart coordinates
(`energy-complete-residual`). -/
theorem endpointOutputMask_mul_retained_output
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (output : E → ℝ) (χout : E → ℂ)
    (h : ∀ y, (output y : ℂ) * χout ((physicalCoordinates (f.chart p).index).symm y) =
      (output y : ℂ)) (y : E) :
    endpointOutputMask f p output y * χout y = endpointOutputMask f p output y := by
  simpa only [endpointOutputMask, ContinuousLinearEquiv.symm_apply_apply] using
    h (physicalCoordinates (f.chart p).index y)

/-- The retained source plateau absorbs the unchanged common input mask;
this is multiplication in position, with no Fourier commutation
(`measured-adjoint`). -/
theorem retained_source_mul_chartInputMask
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (χsource : E → ℂ)
    (h : ∀ y, χsource ((physicalCoordinates (f.chart p).index).symm y) *
      (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) (y : E) :
    χsource y * chartInputMask f p y = chartInputMask f p y := by
  simpa only [chartInputMask, ContinuousLinearEquiv.symm_apply_apply] using
    h (physicalCoordinates (f.chart p).index y)

/-- All source PDO budgets with the smaller constructed output, the original
input and the exact doubled multiplier. Combined with the source agreement
in `SelectedChartEndpointAt`, this is index one on the SAME retarded collar
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem exists_endpoint_source_pdo_budgets
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers) (L : ℝ)
    {output : E → ℝ} (ho : ContDiff ℝ ∞ output) (hc : HasCompactSupport output)
    (hsupp : tsupport output ⊆ ball x f.physicalRadius) :
    ∃ R > (0 : ℝ), ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      GraphNormalAmplitudeBounds
        (maskedPhysicalPDOCycleSymbol (endpointOutputMask f p output) (chartInputMask f p)
          (selectedSourceSymbol f p (2*L))) R (C (2*(d+2))) ∧
      ∀ m ξ is, is.length ≤ m → ∀ z,
        ‖matrixAmplitudeCoordinateDerivList is
          (maskedPhysicalPDOCycleSymbol (endpointOutputMask f p output) (chartInputMask f p)
            (selectedSourceSymbol f p (2*L)) ξ) z‖ ≤ C m := by
  obtain ⟨hout, hcout, hcarrier⟩ := endpointOutputMask_properties f p ho hc hsupp
  obtain ⟨_, hs, _, hcs, _⟩ := chartPhysicalMasks_properties f p
  obtain ⟨hρ, hsρ, _⟩ := chartConicMask_properties f p
  obtain ⟨bound, hbound⟩ := (hcout.union hcs).exists_bound_of_continuousOn
    continuous_id.continuousOn
  let R := |bound|+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hoR y (hy : y ∈ tsupport (endpointOutputMask f p output)) : ‖y‖ ≤ R :=
    (hbound y (Or.inl hy)).trans (by dsimp [R]; linarith [le_abs_self bound])
  have hsR y (hy : y ∈ tsupport (chartInputMask f p)) : ‖y‖ ≤ R :=
    (hbound y (Or.inr hy)).trans (by dsimp [R]; linarith [le_abs_self bound])
  have hβ := selectedEndpointMultiplier_bounds f p L
  have hbρ := (complex_conicMask_pdo_bounds (f.spatialMask p)
    (f.spatialMask_properties p).1 (f.spatialMask_properties p).2.1).2
  obtain ⟨C, hC, hb⟩ := exists_source_pdo_budgets (q := d+1)
    (isCompact_closedBall ((physicalCoordinates (f.chart p).index).symm x) (2*f.physicalRadius))
    _ _ hout hs hcarrier hcs (f.chart p).sourceMask
    (f.chart p).sourceMask_smooth (f.chart p).sourceMask_compact
    (f.chart p).radialSection _ _ hρ hsρ hβ.1
    zero_le_one zero_le_one hbρ hβ.2 R hoR hsR
  exact ⟨R, hR, C, hC, hb⟩

end JanetCartan.RegularSector.FinitePdo
