module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.SamplingKernelRegularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.SamplingCutoff

/-!
# The actual colored corrected cross kernel

Instantiate the existing band-kernel interface on the literal corrected
amplitude, one common compact extension, and the original retained phase and
carrier. Derive the qualitative joint bound from compactness, keeping the
zero-atom background separate from the detector and high-pass.
Consumer: the finite cross row in `app:ch_mean_pairs:defn:mean-canonical`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CanonicalRowComparison
open CanonicalAtomRealization CorrectedAtoms Sampling SamplingKernelBounds
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open CurrentMean AmplitudeBound Sampling.MeasuredAmplitude

variable {d N : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1) // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d + 1)) < T.family.threshold})
    (F : Euclidean (d + 1) → Euclidean N) (row col : Fin (d + 1))
    (Φ Y : ℝ × (Euclidean ((d + 1) - 1) × (Euclidean 3 × Euclidean ((d + 1) - 1))) →
      Euclidean ((d + 1) - 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)))
    (χ : Euclidean (d + 1) → ℝ)
    (B : MetricField (d + 1) →ₗ[ℝ] (Euclidean (d + 1) → Euclidean N))
    (r : Euclidean ((d + 1) - 1) × Euclidean 3 → ℝ)
    (κ : Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)) → ℝ)
    (hκc : HasCompactSupport κ)

variable {γ : Type*} [Finite γ] (rate : γ → ℝ)
    (hA : ∀ c, Continuous (fun w ↦ κ w •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w))
    (C : Euclidean (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →L[ℝ] Euclidean (d + 1))
    (hC : Continuous C)

/-- The literal corrected amplitude vanishes outside the physical projection
of its ONE supplied compact cutoff. Neither the carrier nor the zero-atom
background acquires a detector or high-pass (`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem cutCorrectedDerivativeAmplitude_zero_off_projection
    (τ : ℝ) (x : Euclidean (d + 1)) (z : Euclidean 3) (ξ : Euclidean ((d + 1) - 1))
    (hx : x ∉ Prod.fst '' tsupport κ) :
    κ (x, z, ξ) • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ (x, z, ξ) = 0 := by
  have hzero : κ (x, z, ξ) = 0 := image_eq_zero_of_notMem_tsupport
    (fun hw ↦ hx ⟨(x, z, ξ), hw, rfl⟩)
  rw [hzero, zero_smul]

include hκc hA hC in
/-- A finite colored family of the SAME corrected amplitudes supplies the
qualitative cross-kernel bound used to form the actual sampling operators.
The bound is derived from compactness; it is not the uniform sampling-event
estimate (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_correctedColoredCrossKernel_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ c x z ξ ξ',
      ‖complexCrossMeasurement (C x)
        (κ (x, z, ξ) • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) (x, z, ξ))
        (κ (x, z, ξ') • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) (x, z, ξ'))‖ ≤ M :=
  exists_coloredCanonicalCrossKernel_bound
    (fun c w ↦ κ w • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w)
    hA (fun _ ↦ hκc.smul_right) C hC (hκc.image continuous_fst)
    (fun c x z ξ hx ↦ cutCorrectedDerivativeAmplitude_zero_off_projection
      T Q F row col Φ Y χ B r κ (rate c) x z ξ hx)

variable {ι : Type*} [TopologicalSpace ι] [FirstCountableTopology ι] [LocallyCompactSpace ι]
    [TopologicalSpace γ] [DiscreteTopology γ]
    (color : ι → γ) (hcolor : Continuous color)
    (node : ι → Euclidean 3) (hnode : Continuous node)
    {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀) (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    (hrate : ∀ c, rate c ≠ 0)
    (mask : Euclidean ((d + 1) - 1) → ℂ) (hd : Continuous mask)
    (Md : ℝ) (hMd : 0 ≤ Md) (hdb : ∀ ξ, ‖mask ξ‖ ≤ Md)

/-- Instantiate the existing colored sampling constructor with the literal
final corrected derivative and its zero-frequency value. Neither factor at
zero receives a detector or high-pass. The retained phase/carrier extensions
and ONE supplied coefficient cutoff are used for all nodes and colors;
that cutoff's plateau identifies the measured zero atom in the direct-row
consumer. Compactness supplies the auxiliary kernel bound internally;
raw measures, detector and Fourier scalar are unchanged
(`app:ch_waves:eq:sampling-prefix-normal`, `app:ch_mean_pairs:defn:mean-canonical`). -/
def correctedColoredCrossBandData (J : ℕ) : BandKernelData (Fin J × ι) (d + 1) :=
  coloredCanonicalCrossBandData J (fun _ ↦ extendedRetainedPhase T Q)
    ((contDiff_extendedRetainedPhase T Q).continuous.comp
      (f := fun q : (ι × Euclidean (d + 1)) × Euclidean ((d + 1) - 1) ↦ (q.1.2, q.2))
      (by fun_prop))
    (fun c w ↦ κ w • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w)
    hA C hC color hcolor node hnode
    (fun i ↦ extendedRetainedCarrier T z₀ hρ (node i))
    ((contDiff_extendedRetainedCarrier T hP z₀ hρ hcarrier).continuous.comp hnode)
    rate hrate mask hd (Prod.fst '' tsupport κ) (hκc.image continuous_fst)
    (fun c x z ξ hx ↦ cutCorrectedDerivativeAmplitude_zero_off_projection
      T Q F row col Φ Y χ B r κ (rate c) x z ξ hx)
    (exists_correctedColoredCrossKernel_bound T Q F row col Φ Y χ B r κ hκc rate hA C hC).choose
    Md (exists_correctedColoredCrossKernel_bound T Q F row col Φ Y χ B r κ hκc rate hA C hC).choose_spec.1
    hMd (fun i x ξ ↦
      (exists_correctedColoredCrossKernel_bound T Q F row col Φ Y χ B r κ hκc rate hA C hC).choose_spec.2
        (color i) x (node i) (extendedRetainedCarrier T z₀ hρ (node i)) ξ) hdb

end JanetCartan.CanonicalRowComparison
