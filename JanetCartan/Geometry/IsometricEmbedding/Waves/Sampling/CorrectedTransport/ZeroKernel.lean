module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.ZeroEndpoint
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.TransportKernel

/-!
# Literal leading kernel at the corrected transport endpoint

Use the same compact coefficient cutoff and carrier extension to construct
the zero endpoint. Its phase is the derivative of the original retained phase,
and its amplitude is the measured square of the same leading matrix. The
qualitative compactness bound only constructs the operator.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedTransport
open CanonicalRowComparison RawPrimary CorrectedAtoms CorrectedMean MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave LeadingWave.FullModulation
open FullNormalGeometry FullPhaseCharts MeanNormalBound.NormalizedFullPhase
open RawPrimary.MaskProfiles RawKernel RawInputPartition SamplingKernelBounds
open CanonicalAtomRealization MeasuredAmplitude.ColoredApplication SeparatedSampling
open CurrentMean NullTransport ActualFlow FlowAmplitude
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.LeadingPrimitive

variable {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
    Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (χ : Euclidean (m + 1) → ℝ)
  (B : MetricField (m + 1) →ₗ[ℝ] (Euclidean (m + 1) → Euclidean N))
  (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
  (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
  (C : Euclidean (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
    Euclidean (m + 1))
  (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)


variable (hκc : HasCompactSupport κ)
    (hA₀ : Continuous (fun w ↦ κ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w))
    (hC : Continuous C) {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    (mask : Euclidean (m + 1 - 1) → ℂ) (hd : Continuous mask)
    (Md : ℝ) (hMd : 0 ≤ Md) (hdb : ∀ η, ‖mask η‖ ≤ Md)

/-- The literal leading endpoint of the corrected cross kernel, with the
same measurement, compact cutoff, extended carrier, detector and phase
normalization. Compactness is used solely to form the existing band-kernel
interface (`app:ch_waves:eq:colored-normal-comparison`). -/
def leadingCrossTransportKernelData (J : ℕ) : BandKernelData (Fin J × Point) (m + 1) :=
  let A₀ := fun w ↦ κ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w
  let ζ := fun z : Point ↦ extendedRetainedCarrier T z₀ hρ (WithLp.toLp 2 z)
  let hζ : Continuous ζ :=
    (contDiff_extendedRetainedCarrier T hP z₀ hρ hcarrier).continuous.comp (by fun_prop)
  let hb := exists_coloredCanonicalCrossKernel_bound (fun _ : Unit ↦ A₀) (fun _ ↦ hA₀)
    (fun _ ↦ hκc.smul_right) C hC (hκc.image continuous_fst)
    (fun _ x z ξ hx ↦ by
      have hz : κ (x, z, ξ) = 0 := image_eq_zero_of_notMem_tsupport
        (fun hw ↦ hx ⟨(x, z, ξ), hw, rfl⟩)
      simp only [A₀, hz, zero_smul])
  let A := fun (z : Point) (x : Euclidean (m + 1)) (_ : Euclidean (m + 1 - 1)) ↦
    complexCrossMeasurement (C x) (A₀ (x, WithLp.toLp 2 z, ζ z))
      (A₀ (x, WithLp.toLp 2 z, ζ z))
  let hA : Continuous (fun q : (Point × Euclidean (m + 1)) × Euclidean (m + 1 - 1) ↦
      A q.1.1 q.1.2 q.2) :=
    (continuous_coloredCanonicalCrossKernel (fun _ : Unit ↦ A₀) (fun _ ↦ hA₀) C hC
      (fun _ : Point ↦ ()) continuous_const (WithLp.toLp 2) (by fun_prop) ζ hζ).comp
      (f := fun q : (Point × Euclidean (m + 1)) × Euclidean (m + 1 - 1) ↦
        (q.1, ζ q.1.1)) (by fun_prop)
  let D := bandKernelData (J := J) (fun _ _ _ ↦ (0 : ℝ)) A ζ (fun _ ↦ 1)
    mask continuous_const hA hζ continuous_const (fun _ ↦ one_ne_zero) hd
    (Prod.fst '' tsupport κ) (hκc.image continuous_fst)
    (fun z x _ hx ↦ by
      have hz : κ (x, WithLp.toLp 2 z, ζ z) = 0 := image_eq_zero_of_notMem_tsupport
        (fun hw ↦ hx ⟨(x, WithLp.toLp 2 z, ζ z), hw, rfl⟩)
      simp only [A, A₀, hz, zero_smul, map_zero])
    hb.choose Md hb.choose_spec.1 hMd
    (fun z x _ ↦ hb.choose_spec.2 () x (WithLp.toLp 2 z) (ζ z) (ζ z)) hdb
  { D with
    phase := retainedTransportPhase T Q
      (0, z₀, T.reference.spatialPatch z₀) hρ
    phase_continuous := continuous_retainedTransportPhase T Q
      (0, z₀, T.reference.spatialPatch z₀) hρ hP hcarrier }

/-- The leading endpoint amplitude is the zero cross homotopy evaluated
at the original extended carrier, with its Fourier scalar and radial band
unchanged (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem leadingCrossTransportKernelData_amplitude (J : ℕ) (τ : ℝ) :
    (leadingCrossTransportKernelData T Q F row col Φ Y r κ C z₀ hρ
      hκc hA₀ hC hP hcarrier mask hd Md hMd hdb J).amplitude =
      measuredBandAmplitude
        (fun z x ξ ↦ correctedTransportCrossHomotopy T Q F row col Φ Y χ B r κ C z₀ hρ
          τ (0, x, WithLp.toLp 2 z, ξ))
        (fun z : Point ↦ extendedRetainedCarrier T z₀ hρ (WithLp.toLp 2 z))
        (fun _ ↦ 0) := by
  funext q
  simp only [leadingCrossTransportKernelData, bandKernelData, measuredBandAmplitude,
    zero_smul, add_zero, correctedTransportCrossHomotopy_zero, retainedCarrierInsertion]

end JanetCartan.Sampling.CorrectedTransport
