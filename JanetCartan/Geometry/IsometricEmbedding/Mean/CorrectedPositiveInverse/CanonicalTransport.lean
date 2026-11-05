module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CorrectedPositiveInverse.SameDensity

/-!
# The corrected normal is the actual scalar transport

The flow and geometric normal are the SAME canonical fields. Only the initial
scalar changes to `σ sqrt(1+v)`. The original ODE/phase footpoint identification
therefore gives exactly `correctedCarrierData` on the carrier kernel support.
This lets the actual wider-density row producer supply the realization input
of `exists_correctedQ0_for_uncorrected_density` without a new geometric choice.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.CorrectedPositiveInverse
open ContinuumRow PositiveBackground ContinuumAdjoint.Canonical
open ActualCarriers FrozenMenu CurrentFullPhase

variable {n N : ℕ} {P : Patch n} {W : Set (Euclidean n)} {hW : IsOpen W}
    (T : PatchQuantitativeFamily P W hW)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q W ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)

/-- Scalar-transport linearity, derived from its exponential formula, gives
the corrected normal of the SAME density at the original footpoint. The
footpoint equality is the retained leading-flow producer's geometric output;
no normal-field or kernel equality is assumed
(`app:ch_waves:thm:leading`, `app:ch_background:eq:bg-affine-mean`). -/
theorem canonical_normal_same_density (σ : ℝ) (v : CarrierVariable n → ℝ)
    (x : Euclidean n) (z : CarrierParameter)
    (hfoot : odeInitialPoint T Y (z, x) =
      (CanonicalCarrier.transportPosition T Q (x, z), CanonicalCarrier.parameter z)) :
    CanonicalCarrier.normalField T Q F row col Φ Y
        (fun q ↦ positiveDensityAmplitude σ (densityOnInitialLabels v q)) x z =
      Real.sqrt (1 + v (z, CanonicalCarrier.transportPosition T Q (x, z))) •
        CanonicalCarrier.normalField T Q F row col Φ Y (fun _ ↦ σ) x z := by
  have hv : densityOnInitialLabels v (odeInitialPoint T Y (z, x)) =
      v (z, CanonicalCarrier.transportPosition T Q (x, z)) := by
    rw [hfoot]
    exact congrFun (initialScalar_densityOnInitialLabels v)
      (z, CanonicalCarrier.transportPosition T Q (x, z))
  rw [normalField_eq_initial_flow, normalField_eq_initial_flow, hv]
  simp only [positiveDensityAmplitude, smul_smul]
  congr 1
  ring

/-- The wider-class canonical row with initial scalar `σ sqrt(1+v)` has
exactly the kernel of `correctedCarrierData`. Only the original supported
footpoint identity is needed; no equality outside the measurement/angular
support is imposed. This supplies the literal realization used in
`exists_correctedQ0_for_uncorrected_density`
(`app:ch_background:eq:bg-T`, `app:ch_background:prop:bg-frame`). -/
theorem canonical_kernel_same_density (σ : ℝ) (v : CarrierVariable n → ℝ)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
    (hfoot : ∀ x ∈ PeriodicLocalL2.torusChart (closedBall (0 : Euclidean n) (4 * r)),
      ∀ u : CarrierVariable n, FixedCutoffs.periodic hr hcell 1 x ≠ 0 →
      angular u.1 (‖u.2‖⁻¹ • u.2) ≠ 0 →
      odeInitialPoint T Y (u.1, AmplitudeBound.centeredTorusRepresentative x) =
        (CanonicalCarrier.transportPosition T Q
          (AmplitudeBound.centeredTorusRepresentative x, u.1), CanonicalCarrier.parameter u.1)) :
    carrierKernel (correctedCarrierData
      (CanonicalCarrier.data T Q F row col Φ Y (fun _ ↦ σ) hr hcell angular high) v) =
      carrierKernel (CanonicalCarrier.data T Q F row col Φ Y
        (fun q ↦ positiveDensityAmplitude σ (densityOnInitialLabels v q))
        hr hcell angular high) := by
  classical
  let d₀ := CanonicalCarrier.data T Q F row col Φ Y (fun _ ↦ σ) hr hcell angular high
  let d₁ := CanonicalCarrier.data T Q F row col Φ Y
    (fun q ↦ positiveDensityAmplitude σ (densityOnInitialLabels v q)) hr hcell angular high
  funext x u
  change carrierKernel (correctedCarrierData d₀ v) x u = carrierKernel d₁ x u
  by_cases hx : x ∈ d₀.outputChart
  · have hamp : carrierAmplitude (correctedCarrierData d₀ v) x u =
        carrierAmplitude d₁ x u := by
      by_cases hm : FixedCutoffs.periodic hr hcell 1 x = 0
      · simp [carrierAmplitude, correctedCarrierData, d₀, d₁, CanonicalCarrier.data, hm]
      by_cases ha : angular u.1 (‖u.2‖⁻¹ • u.2) = 0
      · simp [carrierAmplitude, correctedCarrierData, d₀, d₁, CanonicalCarrier.data, ha]
      have hn := canonical_normal_same_density T Q F row col Φ Y σ v
        (AmplitudeBound.centeredTorusRepresentative x) u.1 (hfoot x hx u hm ha)
      simp only [carrierAmplitude, correctedCarrierData, d₀, d₁, CanonicalCarrier.data,
        reducedCovector, hn]
    have hx' : x ∈ d₁.outputChart := hx
    simp only [carrierKernel, show (correctedCarrierData d₀ v).outputChart =
      d₀.outputChart from rfl, Set.indicator_of_mem hx, Set.indicator_of_mem hx']
    rw [hamp]
    rfl
  · have hx' : x ∉ d₁.outputChart := hx
    exact (carrierKernel_eq_zero_outside (correctedCarrierData d₀ v) hx u).trans
      (carrierKernel_eq_zero_outside d₁ hx' u).symm

end JanetCartan.CorrectedPositiveInverse
