module
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.PhysicalMeasurement
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.ZeroKernel
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.OriginalRowKernel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.NativePrefix
/-!
# The corrected transport endpoint is the original carrier kernel

The literal leading endpoint, with the compact original measurement, has the
SAME weighted carrier kernel. The cutoff plateaus and scalar compatibility
remove the extensions only on their original domains. Zero carrier weights
and the measurement boundary are handled directly, without dividing by a mask.

Consumer: the corrected transport comparison and original prepared raw-tail
normal in `app:ch_mean_pairs:eq:mean-normal-comparison`.
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
open CurrentMean NullTransport ActualFlow FlowAmplitude AmplitudeBound
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.LeadingPrimitive

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
  (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
  (C : Euclidean (m + 1) → MetricTensor (m + 1) →L[ℝ] Euclidean (m + 1))
  (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
  (hκc : HasCompactSupport κ)
  (hA₀ : Continuous (fun w ↦ κ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w))
  (hC : Continuous C) {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
  (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
  (mask : Euclidean (m + 1 - 1) → ℂ) (hd : Continuous mask)
  (Md : ℝ) (hMd : 0 ≤ Md) (hdb : ∀ η, ‖mask η‖ ≤ Md)

local notation "D₀" => leadingCrossTransportKernelData T Q F row col Φ Y r κ C z₀ hρ
  hκc hA₀ hC hP hcarrier mask hd Md hMd hdb J

/-- The leading kernel vanishes where the SAME physical measurement does,
including outside its original chart (`app:ch_background:defn:bg-row`). -/
theorem leadingCrossTransportKernelData_zero_of_measurement
    (j : Fin J) (z : Point) (η : Euclidean (m + 1 - 1))
    {x : Euclidean (m + 1)} (hx : C x = 0) :
    (D₀).kernel (j,z) η x = 0 := by
  simp [BandKernelData.kernel, bandKernel, leadingCrossTransportKernelData,
    bandKernelData, measuredBandAmplitude, hx, complexCrossMeasurement]

/-- The leading endpoint retains both sharp pieces of each original wide
band (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem leadingCrossTransportKernelData_zero_off_wideBand
    (j : Fin J) (z : Point) (η : Euclidean (m + 1 - 1))
    (hη : η ∉ wideBand (m + 1) j.val) (x : Euclidean (m + 1)) :
    (D₀).kernel (j,z) η x = 0 := by
  rw [BandKernelData.kernel, bandKernel,
    leadingCrossTransportKernelData_amplitude T Q F row col Φ Y (fun _ ↦ 0) 0 r κ C
      z₀ hρ hκc hA₀ hC hP hcarrier mask hd Md hMd hdb J 1,
    measuredBandAmplitude_eq_zero_off_wideBand _ _ _ j z η x hη, smul_zero]

omit C hC mask hd Md hMd hdb in
/-- Identify the actual corrected zero endpoint with the SAME compatible
carrier kernel, using the original physical measurement, carrier weight,
detector and high-pass. The literal cutoff plateau and full/carrier scalar
compatibility supply the identity; no kernel equality is a premise
(`app:ch_background:eq:bg-T`, `app:ch_waves:eq:colored-normal-comparison`). -/
theorem leadingCrossTransportKernelData_eq_weighted_original
    (φ y : ℝ × (Euclidean (m + 1 - 1) × Euclidean 3) →
      Euclidean (m + 1 - 1) × Euclidean 3)
    {V : Set (ℝ × (Euclidean (m + 1 - 1) × Euclidean 3))}
    (hcompat : ∀ q ∈ V,
      let w := (coordinates (adaptedCoordinates T.data.adapted)).symm q
      scalarAmplitude T Q F row col Φ Y r (w.1, (w.2, T.reference.spatialPatch w.2)) =
        carrierScalarAmplitude T Q F row col φ y r w)
    {b : ℝ} (hb : 0 < b) (hbcell : 4 * b < 1 / 2)
    (hball : closedBall (0 : Euclidean (m + 1)) (4 * b) ⊆ U)
    (angle : Euclidean (m + 1 - 1) → ℝ) (high : ℝ → ℝ)
    (hd : Continuous (detectorMask (fun η ↦ (angle (NormedSpace.normalize η) : ℂ))
      (fun η ↦ high ‖η‖)))
    (Md : ℝ) (hMd : 0 ≤ Md)
    (hdb : ∀ η, ‖detectorMask (fun η ↦ (angle (NormedSpace.normalize η) : ℂ))
      (fun η ↦ high ‖η‖) η‖ ≤ Md)
    (ψ : Point → ℝ)
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
    (haz : a.2.1 = z₀) (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (hκ : Prod.fst '' Function.support κ ⊆ closedBall a.1 (ρ / 2))
    (hψgraph : ∀ z : CarrierParameter, ψ (carrierSamplingEquiv z) ≠ 0 →
      (parameter z, T.reference.spatialPatch (parameter z)) ∈ closedBall a.2 (ρ / 4))
    (hκone : ∀ x, FixedCutoffs.physical hb 1 x ≠ 0 → ∀ z : CarrierParameter,
      ψ (carrierSamplingEquiv z) ≠ 0 →
      κ (x, parameter z, T.reference.spatialPatch (parameter z)) = 1)
    (hcoords : ∀ x : Torus (m + 1),
      FixedCutoffs.physical hb 1 (centeredTorusRepresentative x) ≠ 0 →
      ∀ z : CarrierParameter, ψ (carrierSamplingEquiv z) ≠ 0 →
      coordinates (adaptedCoordinates T.data.adapted)
        (centeredTorusRepresentative x, parameter z) ∈ V)
    (j : Fin J) (x : Torus (m + 1)) (u : CarrierVariable (m + 1)) :
    let d := data T Q F row col φ y r hb hbcell
      (fun z θ ↦ Real.sqrt (ψ (carrierSamplingEquiv z)) * angle θ) high
    let C := canonicalSamplingMeasurement Q.1 hb
    let hC := (contDiff_canonicalSamplingMeasurement T Q F row col φ y r hb hbcell
      (fun z θ ↦ Real.sqrt (ψ (carrierSamplingEquiv z)) * angle θ) high hball).continuous
    ((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) * carrierBand (m + 1) j.val u) •
      carrierKernel d x u =
      Real.sqrt (ψ (carrierSamplingEquiv u.1)) •
        (leadingCrossTransportKernelData T Q F row col Φ Y r κ C z₀ hρ hκc hA₀ hC hP hcarrier
          (detectorMask (fun η ↦ (angle (NormedSpace.normalize η) : ℂ))
            (fun η ↦ high ‖η‖)) hd Md hMd hdb J).kernel
          (j, carrierSamplingEquiv u.1) u.2 (centeredTorusRepresentative x) := by
  intro d C hC
  let D := leadingCrossTransportKernelData T Q F row col Φ Y r κ C z₀ hρ hκc hA₀ hC hP hcarrier
    (detectorMask (fun η ↦ (angle (NormedSpace.normalize η) : ℂ)) (fun η ↦ high ‖η‖))
    hd Md hMd hdb J
  change _ = Real.sqrt (ψ (carrierSamplingEquiv u.1)) • D.kernel _ _ _
  by_cases hz : ψ (carrierSamplingEquiv u.1) = 0
  · have hk : carrierKernel d x u = 0 := by
      simp [carrierKernel, carrierAmplitude, d, data, hz]
    simp [hk, hz]
  have hmeasure : C (centeredTorusRepresentative x) = preparationMeasurement d x :=
    canonicalSamplingMeasurement_centered T Q F row col φ y r hb hbcell _ high x
  by_cases hx : FixedCutoffs.physical hb 1 (centeredTorusRepresentative x) = 0
  · have hCzero : C (centeredTorusRepresentative x) = 0 :=
      canonicalSamplingMeasurement_eq_zero_of_cutoff_eq_zero Q.1 hb hx
    have hDz : D.kernel (j, carrierSamplingEquiv u.1) u.2 (centeredTorusRepresentative x) = 0 :=
      leadingCrossTransportKernelData_zero_of_measurement T Q F row col Φ Y r κ C z₀ hρ
        hκc hA₀ hC hP hcarrier _ hd Md hMd hdb j _ _ hCzero
    rw [carrierKernel_eq_principal_cross, ← hmeasure, hCzero]
    simp [complexCrossMeasurement, hDz]
  have hg := hψgraph u.1 hz
  have hzc : parameter u.1 ∈ closedBall z₀ ρ := by
    rw [← closedBall_prod_same] at hg
    rw [← haz]
    exact closedBall_subset_closedBall (by linarith) hg.1
  have hpar : WithLp.toLp 2 (carrierSamplingEquiv u.1) = parameter u.1 := by
    ext i
    fin_cases i <;> rfl
  have hkone := hκone _ hx u.1 hz
  have hxκ : centeredTorusRepresentative x ∈ Prod.fst '' Function.support κ :=
    ⟨(centeredTorusRepresentative x, parameter u.1, T.reference.spatialPatch (parameter u.1)),
      hkone.trans_ne one_ne_zero, rfl⟩
  have hbase : (centeredTorusRepresentative x, T.reference.spatialPatch (parameter u.1)) ∈
      phaseDomain T := by
    have hh := hphase (closedBall_subset_closedBall (by linarith : ρ / 2 ≤ 2 * ρ)
      (retained_shift_mem_plateau T a (hκ hxκ) hg (d := 0) (by simp; positivity)))
    change (centeredTorusRepresentative x, T.reference.spatialPatch (parameter u.1) + 0) ∈
      phaseDomain T at hh
    simpa only [add_zero] using hh
  have heq : fderiv ℝ (extendedRetainedPhase T Q (centeredTorusRepresentative x))
      (T.reference.spatialPatch (parameter u.1)) =
      fderiv ℝ (phase T Q (centeredTorusRepresentative x))
        (T.reference.spatialPatch (parameter u.1)) := by
    apply Filter.EventuallyEq.fderiv_eq
    have hnhood : ∀ᶠ η in 𝓝 (T.reference.spatialPatch (parameter u.1)),
        (centeredTorusRepresentative x, η) ∈ phaseDomain T :=
      (isOpen_ball.preimage (continuous_const.prodMk continuous_id)).mem_nhds hbase
    filter_upwards [hnhood] with η hη
    exact extendedRetainedPhase_eq T Q hη
  have hn := fullLeadingPrincipalMatrix_eq_compatible_carrier T Q F row col Φ Y φ y r
    hcompat (p := (centeredTorusRepresentative x, u.1)) (hcoords x hx u.1 hz)
  dsimp only [carrierGraph, Prod.fst, Prod.snd] at hn
  rw [carrierKernel_eq_principal_cross]
  dsimp only [D, BandKernelData.kernel, bandKernel, leadingCrossTransportKernelData,
    bandKernelData, measuredBandAmplitude]
  change _ = Real.sqrt (ψ (carrierSamplingEquiv u.1)) •
    ((Complex.exp ((retainedTransportPhase T Q (0,z₀,T.reference.spatialPatch z₀) hρ
      (((j,carrierSamplingEquiv u.1),u.2),centeredTorusRepresentative x) : ℂ) * Complex.I) *
      (Real.sqrt ‖u.2‖ : ℂ) * detectorMask
        (fun η ↦ (angle (NormedSpace.normalize η) : ℂ)) (fun η ↦ high ‖η‖) u.2) •
    (((2 * Real.pi) ^ (-((m + 1 : ℕ) : ℝ) / 2) * radialBand (m + 1) j.val u.2 : ℝ) : ℂ) •
      complexCrossMeasurement (C (centeredTorusRepresentative x))
        (κ (centeredTorusRepresentative x, WithLp.toLp 2 (carrierSamplingEquiv u.1),
          extendedRetainedCarrier T z₀ hρ (WithLp.toLp 2 (carrierSamplingEquiv u.1))) •
          fullLeadingPrincipalMatrix T Q F row col Φ Y r
            (centeredTorusRepresentative x, WithLp.toLp 2 (carrierSamplingEquiv u.1),
              extendedRetainedCarrier T z₀ hρ (WithLp.toLp 2 (carrierSamplingEquiv u.1))))
        (κ (centeredTorusRepresentative x, WithLp.toLp 2 (carrierSamplingEquiv u.1),
          extendedRetainedCarrier T z₀ hρ (WithLp.toLp 2 (carrierSamplingEquiv u.1))) •
          fullLeadingPrincipalMatrix T Q F row col Φ Y r
            (centeredTorusRepresentative x, WithLp.toLp 2 (carrierSamplingEquiv u.1),
              extendedRetainedCarrier T z₀ hρ (WithLp.toLp 2 (carrierSamplingEquiv u.1)))))
  rw [retainedTransportPhase, hpar, extendedRetainedCarrier_eq T z₀ hρ hzc,
    heq, hkone, one_smul, hn, hmeasure]
  rw [BackgroundModulation.phaseDifferential_eq_transportPosition_inner]
  simp only [ContinuumRow.carrierPhase, carrierBand, d, data, detectorMask,
    NormedSpace.normalize, RCLike.real_smul_eq_coe_smul (K := ℂ), Complex.ofReal_mul, smul_smul]
  congr 1
  simp only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul]
  ac_rfl

end JanetCartan.Sampling.CorrectedTransport
