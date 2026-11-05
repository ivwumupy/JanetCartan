module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.ColoredApplication.TransportEndpoint
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.CommonPhysicalCutoff

/-!
# The literal original-row kernel at the transport endpoint

Match the constructed Hermitian zero kernel to the original continuum carrier
row, with its physical measurement, carrier mask, directional cutoff and
high-pass unchanged. The same raw/carrier scalar compatibility is used on both
sides. The identity retains the physical Fourier scalar and every dyadic band.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius ENNReal Topology
namespace JanetCartan.Sampling.BackgroundModulation
open ColoredApplication
open MeasuredAmplitude MeasuredAmplitude.ColoredApplication
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation RawKernel
open SamplingKernelBounds RawPrimary.MaskProfiles RawInputPartition FullPhaseCharts
open MeanNormalBound MeanNormalBound.NormalizedFullPhase MeanNormalBound.CanonicalGap ContinuumRow
open NormalComparison ColoredNormalComparison SeparatedSampling
open ContinuumRow.CanonicalCarrier ContinuumRow.LeadingPrimitive NullTransport
open scoped InnerProductSpace

variable {m N J : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
    Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ)
  (χ : Euclidean (m + 1) → ℝ)
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
  {ρ : ℝ} (hρ : 0 < ρ)
  {c C : ℝ} (hP : P.IsValid c C)
  (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  (hs : ContDiff ℝ ∞ (fun q : ℝ × (Euclidean (m + 1) ×
    (Euclidean 3 × Euclidean (m + 1 - 1))) ↦
      supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ
        q.1 q.2.2.1 q.2.1 q.2.2.2))
  (M : ℝ) (hM : 0 ≤ M)
  (hb : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x ξ,
    ‖supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ
      τ z x ξ‖ ≤ M)
  (angle : Euclidean (m + 1 - 1) → ℝ) (high : ℝ → ℝ)

variable
  (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ (fun η : Euclidean (m + 1 - 1) ↦ (angle (NormedSpace.normalize η) : ℂ)) θ)
  (hH : ContDiff ℝ ∞ (fun η : Euclidean (m + 1 - 1) ↦ high ‖η‖)) (hH₀ : ∀ η, ‖η‖ ≤ 1 → (fun η : Euclidean (m + 1 - 1) ↦ high ‖η‖) η = 0)
  (B : ℝ) (hB : 0 ≤ B) (hdB : ∀ η, ‖detectorMask (fun η : Euclidean (m + 1 - 1) ↦ (angle (NormedSpace.normalize η) : ℂ)) (fun η : Euclidean (m + 1 - 1) ↦ high ‖η‖) η‖ ≤ B)



/-- The transport phase differential in the actual product is exactly the
original row's retained Hamilton covector derivative. This holds for the
literal functions without an additional chart estimate
(`app:ch_background:defn:bg-carriers`, `app:ch_background:eq:bg-T`). -/
theorem phaseDifferential_eq_transportPosition_inner
    (x : Euclidean (m + 1)) (z : CarrierParameter) (η : Euclidean (m + 1 - 1)) :
    fderiv ℝ (phase T Q x) (T.reference.spatialPatch (parameter z)) η =
      inner ℝ (transportPosition T Q (x, z)) η := by
  rw [transportPosition_eq_hamiltonGradient, inner_gradient_left]
  rfl

/-- On the original measurement and carrier buffer, the zero kernel is
precisely the SAME continuum carrier kernel, with its supplied carrier weight,
direction mask and high-pass. The common physical measurement removes only the
local sampling bump through its plateau. The identity keeps the original
Fourier scalar and smooth radial band, so it can identify every prefix in
`app:ch_waves:eq:colored-normal-comparison` with `app:ch_background:eq:bg-T`. -/
theorem retainedBackgroundModulationTransportKernelData_eq_original_carrierKernel
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (φ y : ℝ × (Euclidean (m + 1 - 1) × Euclidean 3) →
      Euclidean (m + 1 - 1) × Euclidean 3)
    {V : Set (ℝ × (Euclidean (m + 1 - 1) × Euclidean 3))}
    (hcompat : ∀ q ∈ V,
      let w := (FlowAmplitude.coordinates (ActualFlow.adaptedCoordinates T.data.adapted)).symm q
      scalarAmplitude T Q F row col Φ Y r
          (w.1, (w.2, T.reference.spatialPatch w.2)) =
        carrierScalarAmplitude T Q F row col φ y r w)
    {b : ℝ} (hbpos : 0 < b) (hbcell : 4 * b < 1 / 2)
    (hplateau : ∀ x, FixedCutoffs.physical hbpos 1 x ≠ 0 → χ x = 1)
    (carrierWeight : CarrierParameter → ℝ)
    (j : Fin J) (x : Torus (m + 1)) (u : CarrierVariable (m + 1))
    (hx : x ∈ (data T Q F row col φ y r hbpos hbcell
      (fun z θ ↦ carrierWeight z * angle θ) high).outputChart)
    (hz : (parameter u.1, T.reference.spatialPatch (parameter u.1)) ∈
      closedBall a.2 (ρ / 4))
    (hp : FlowAmplitude.coordinates (ActualFlow.adaptedCoordinates T.data.adapted)
      (AmplitudeBound.centeredTorusRepresentative x, parameter u.1) ∈ V) :
    (carrierWeight u.1 : ℂ) •
      (FixedCutoffs.physical hbpos 1 (AmplitudeBound.centeredTorusRepresentative x) : ℂ) •
        (retainedBackgroundModulationTransportKernelData (J := J)
          T Q F row col Φ Y r χ a hρ hP hcarrier hs M hM hb
          (fun η : Euclidean (m + 1 - 1) ↦ (angle (NormedSpace.normalize η) : ℂ)) (fun η : Euclidean (m + 1 - 1) ↦ high ‖η‖) ha hH hH₀ B hB hdB).kernel (j, (parameter u.1).ofLp) u.2
          (AmplitudeBound.centeredTorusRepresentative x) =
      ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) : ℝ) •
        (radialBand (m + 1) j.val u.2 : ℂ) •
          carrierKernel (data T Q F row col φ y r hbpos hbcell
            (fun z θ ↦ carrierWeight z * angle θ) high) x u := by
  rw [retainedBackgroundModulationTransportKernelData_kernel_eq_raw
    T Q F row col Φ Y r χ a hρ hP hcarrier hs M hM hb
    (fun η : Euclidean (m + 1 - 1) ↦ (angle (NormedSpace.normalize η) : ℂ)) (fun η : Euclidean (m + 1 - 1) ↦ high ‖η‖) ha hH hH₀ B hB hdB hphase hχ j (parameter u.1).ofLp hz]
  rw [carrierKernel_eq_backgroundModulation_zero T Q F row col Φ Y r φ y hcompat
    hbpos hbcell (fun z θ ↦ carrierWeight z * angle θ) high x u hx hp]
  rw [phaseDifferential_eq_transportPosition_inner T Q]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_comm
    (FixedCutoffs.physical hbpos 1 (AmplitudeBound.centeredTorusRepresentative x) : ℂ)]
  rw [measuredBackgroundModulationPolynomial_common_cutoff
    T Q F row col Φ Y r χ (FixedCutoffs.physical hbpos 1) hplateau]
  simp only [weightedRadialBand, detectorMask, NormedSpace.normalize,
    Complex.ofReal_mul, smul_smul]
  congr 1
  ac_rfl

end JanetCartan.Sampling.BackgroundModulation
