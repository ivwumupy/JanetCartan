module

public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.SelectedChart
public import JanetCartan.Analysis.Microlocal.RegularSector.FinitePdo.Endpoint.Masks

/-!
# Actual endpoint PDOs on the already selected finite family

The input family is the one supplied by
`FiniteAlgebraic.exists_finite_physical_algebraic_pdos`, with its retained
radius inequalities. One application of the physical evolution constructor
supplies the common masks and each exact phase, W₀/W₁/PW₁ and both retarded
operators. We enrich those SAME witnesses with the supported upper-endpoint
PDO budgets and positive/negative gains of its physical operator and literal
adjoint. There is no second existential choice of phase or amplitude.

The smaller common output plateau absorbs the original and retained outputs;
the original common input is unchanged. Source PDO budgets and exact source
agreement hold on these masks at the enlarged physical threshold. Both angular
and low-frequency complements remain in the finite source partition.
Consumer: direct PDO index two of `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6400000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FinitePdo
open ActualCarriers Characteristic Characteristic.ResidualCoordinates
open Characteristic.ConicPhase Characteristic.UniformEvolution
open Characteristic.EvolutionIntegral Characteristic.ConicAmplitude
open FiniteMasks FiniteMasks.ActualFamily FiniteEvolution RetainedConstruction
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}

/-- Construct the actual upper-endpoint PDO on the SAME finite family as the
algebraic terms. Every analytic input is discharged by the retained physical
evolution and its joint two-time amplitude budget. The output retains all
old phase, full-B, W₀/W₁/PW₁ and retarded conclusions together with the
endpoint certificate on their SAME witnesses. Source agreement and source
budgets use the same common masks. Constants precede Q, B and Sobolev order;
`sectorLowOrder` controls the fixed low requirement and the high reserve is
`2*(d+2)+11`. Final finite summation, full residual and real pairing belong to
the parent sector construction (`energy-complete-residual`,
`sector-theorem-residual`, `measured-adjoint`). -/
theorem exists_finite_physical_endpoint_pdos
    (hΩ : IsOpen Ω) (hKΩ : closedBall x RQ ⊆ Ω)
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (hradii : ∀ p : f.centers, (f.chart p).bufferRadius ≤ (f.chart p).targetRadius ∧
      (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (hM : 0 ≤ M) :
    ∃ L : ℝ, 1 ≤ L ∧ f.radialThreshold ≤ L ∧ f.radialThreshold ≤ 2 * L ∧
    ∃ (angular : f.centers → Euclidean d → ℝ)
      (χout χsource : f.centers → E → ℂ),
    ∃ hs : ∀ p, ContDiff ℝ ∞ (χsource p),
      (∀ p, ContDiff ℝ ∞ (angular p) ∧
        (∀ η, angular p η ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport (angular p) ∧
        tsupport (angular p) ⊆ angularCone (f.chart p).radialSection
          (coordinateSplit (f.chart p).index p.val.val).2
          (retainedRadius (f.chart p).targetRadius (f.chart p).bufferRadius / 2) ∧
        (∀ η ∈ tsupport (angular p), 0 < (f.chart p).radialSection η)) ∧
      (∀ p, ContDiff ℝ ∞ (χout p) ∧ HasCompactSupport (χout p) ∧
        HasCompactSupport (χsource p) ∧
        tsupport (χsource p) ⊆ (physicalCoordinates (f.chart p).index) ⁻¹' Ω ∧
        (physicalCoordinates (f.chart p).index).symm '' tsupport f.inputMask ⊆
          interior {y | χsource p y = 1} ∧
        (∀ y ∈ tsupport (χout p), (f.chart p).timeMask =ᶠ[𝓝 (y 0)] (fun _ ↦ 1))) ∧
    ∃ (output : E → ℝ) (r : ℝ), 0 < r ∧
      ContDiff ℝ ∞ output ∧ (∀ y, output y ∈ Icc (0 : ℝ) 1) ∧
      HasCompactSupport output ∧ tsupport output ⊆ ball x f.physicalRadius ∧
      closedBall x r ⊆ interior {y | output y = 1} ∧
      (∀ p, tsupport output ⊆ (physicalCoordinates (f.chart p).index).symm ⁻¹'
        interior {y | χout p y = 1}) ∧
      (∀ p y, χsource p ((physicalCoordinates (f.chart p).index).symm y) *
        (f.inputMask y : ℂ) = (f.inputMask y : ℂ)) ∧
      (∀ p y, (output y : ℂ) *
        χout p ((physicalCoordinates (f.chart p).index).symm y) = (output y : ℂ)) ∧
      (∀ ζ : E, (∑ p, dilatedConicMask (f.angularMask p) (2*L) ζ) +
        dilatedConicMask (fun η ↦ 1 - ∑ p, f.angularMask p η) (2*L) ζ +
        FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0 ((2*L)⁻¹ • ζ) = 1) ∧
      (∀ p y, endpointOutputMask f p output y * FiniteAlgebraic.chartOutputMask f p y =
        endpointOutputMask f p output y) ∧
      (∀ p y, endpointOutputMask f p output y * χout p y = endpointOutputMask f p output y) ∧
      (∀ p y, χsource p y * FiniteAlgebraic.chartInputMask f p y =
        FiniteAlgebraic.chartInputMask f p y) ∧
      (∀ p : f.centers, ∀ L' ≥ L,
        ∃ R > (0 : ℝ), ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
          FourierIntegral.GraphNormalAmplitudeBounds
            (Characteristic.PdoRealization.maskedPhysicalPDOCycleSymbol
              (endpointOutputMask f p output) (FiniteAlgebraic.chartInputMask f p)
              (selectedSourceSymbol f p (2*L'))) R (C (2*(d+2))) ∧
          ∀ m ξ is, is.length ≤ m → ∀ z,
            ‖AmplitudeBound.matrixAmplitudeCoordinateDerivList is
              (Characteristic.PdoRealization.maskedPhysicalPDOCycleSymbol
                (endpointOutputMask f p output) (FiniteAlgebraic.chartInputMask f p)
                (selectedSourceSymbol f p (2*L')) ξ) z‖ ≤ C m) ∧
      (∀ L' ≥ L, ∀ y ∈ closedBall x (4*f.physicalRadius), ∀ ζ : E,
        (∑ p, selectedSourceSymbol f p (2*L')
          ((physicalCoordinates (f.chart p).index).symm y)
          ((physicalCoordinates (f.chart p).index).symm ζ)) +
          (dilatedConicMask (fun η ↦ 1-∑ p, f.angularMask p η) (2*L') ζ : ℂ) •
            (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) +
          (FourierIntegral.LowBounds.FrequencyCutoff.physicalCutoff 0
            ((2*L')⁻¹ • ζ) : ℂ) • (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) = 1) ∧
      ∀ p : f.centers, SelectedChartEndpointAt f p
        L (angular p) (χout p) (χsource p) (hs p) output := by
  obtain ⟨L, hLone, hLf, hLf2, angular, χout, χsource, hs, hang, hmasks,
    output, r, hr, ho, horange, hoc, hos, hop, houtput, hsourceMul, houtputMul,
    hpartition, hevolution⟩ :=
    exists_finite_physical_evolution_data_with_diagonal hΩ f hradii hM
  refine ⟨L, hLone, hLf, hLf2, angular, χout, χsource, hs, hang, hmasks,
    output, r, hr, ho, horange, hoc, hos, hop, houtput, hsourceMul, houtputMul,
    hpartition, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun p ↦ endpointOutputMask_mul_chartOutputMask f p hos
  · exact fun p ↦ endpointOutputMask_mul_retained_output f p output (χout p) (houtputMul p)
  · exact fun p ↦ retained_source_mul_chartInputMask f p (χsource p) (hsourceMul p)
  · exact fun p L' _ ↦ exists_endpoint_source_pdo_budgets f p L' ho hoc hos
  · exact fun L' hLL y hy ζ ↦ selectedSourceSymbols_complete_partition_enlarged f
      (hLf.trans hLL) hy ζ
  · intro p
    exact selectedChartEndpointAt_of_retained hΩ hKΩ f p hM (hradii p).1 (hradii p).2
      hLf ho hoc hos (hevolution p)

end JanetCartan.RegularSector.FinitePdo
