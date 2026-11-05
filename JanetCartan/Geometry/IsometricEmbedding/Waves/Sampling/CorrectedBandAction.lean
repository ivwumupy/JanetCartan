module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedKernelBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.BandInput
public import JanetCartan.Analysis.Sobolev.Local.Basic

/-!
# The literal corrected band and its matrix slice integral

Commute the SAME real measurement and unmasked zero atom through each corrected
band integral. The compact extension, detector, smooth radial band, physical
Fourier factor and original Lebesgue input are retained. This connects the
corrected canonical slice estimate to the sampling operator norm.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.Sampling
open CanonicalRowComparison CanonicalAtomRealization CorrectedAtoms
open SamplingKernelBounds RawInputPartition RawInputRealization MeasuredAmplitude
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open RawPrimary RawPrimary.SliceBounds MeanNormalBound

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
    {γ : Type*} [Finite γ] (rate : γ → ℝ)
    (hA : ∀ c, Continuous (fun w ↦ κ w •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w))
    (C : Euclidean (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →L[ℝ] Euclidean (d + 1))
    (hC : Continuous C)
    {ι : Type*} [TopologicalSpace ι] [FirstCountableTopology ι] [LocallyCompactSpace ι]
    [TopologicalSpace γ] [DiscreteTopology γ]
    (color : ι → γ) (hcolor : Continuous color)
    (node : ι → Euclidean 3) (hnode : Continuous node)
    {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀) (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    (hrate : ∀ c, rate c ≠ 0)
    (mask : Euclidean ((d + 1) - 1) → ℂ) (hd : Continuous mask)
    (Md : ℝ) (hMd : 0 ≤ Md) (hdb : ∀ ξ, ‖mask ξ‖ ≤ Md)

/-- The literal corrected wide band is the original measured matrix integral.
The zero atom receives no Fourier mask and both amplitude slots use the SAME
compact extension (`app:ch_mean_pairs:defn:mean-canonical`,
`app:ch_waves:eq:individual-raw-slice`). -/
theorem correctedColoredCrossBandData_wideOperator_ae
    (J : ℕ) (j : Fin J) (p : ι) (f : WideBandL2 (d + 1) j.val) :
    let A := fun c w ↦ κ w •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w
    let ζ := extendedRetainedCarrier T z₀ hρ (node p)
    wideBandKernelOperator
      (correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC
        color hcolor node hnode hP z₀ hρ hcarrier hrate mask hd Md hMd hdb J)
      j.val (j, p) f =ᵐ[volume] fun x ↦
        (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) •
          complexCrossMeasurement (C x) (A (color p) (x, node p, ζ))
            (rawSliceBandIntegral (extendedRetainedPhase T Q)
              (fun x η ↦ A (color p) (x, node p, η)) (fun _ ↦ 1)
              ζ (rate (color p)) (weightedRadialBand mask j.val) j.val f x) := by
  intro A ζ
  let D := correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC
    color hcolor node hnode hP z₀ hρ hcarrier hrate mask hd Md hMd hdb J
  have hraw : wideBandKernelOperator D j.val (j, p) f =ᵐ[volume] fun x ↦
      (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) •
        rawSliceBandIntegral (extendedRetainedPhase T Q)
          (fun y η ↦ complexCrossMeasurement (C y) (A (color p) (y, node p, ζ))
            (A (color p) (y, node p, η))) (fun _ ↦ 1) ζ (rate (color p))
          (weightedRadialBand mask j.val) j.val f x := by
    have hS : Continuous (fun q : (ι × Euclidean (d + 1)) × Euclidean ((d + 1) - 1) ↦
        extendedRetainedPhase T Q q.1.2 q.2) :=
      (contDiff_extendedRetainedPhase T Q).continuous.comp
        (f := fun q : (ι × Euclidean (d + 1)) × Euclidean ((d + 1) - 1) ↦ (q.1.2, q.2))
        (by fun_prop)
    have hζ := (contDiff_extendedRetainedCarrier T hP z₀ hρ hcarrier).continuous.comp hnode
    have hcross := continuous_coloredCanonicalCrossKernel A hA C hC color hcolor node hnode
      (fun i ↦ extendedRetainedCarrier T z₀ hρ (node i)) hζ
    let M := (exists_correctedColoredCrossKernel_bound T Q F row col Φ Y χ B r κ hκc
      rate hA C hC).choose
    have hM := (exists_correctedColoredCrossKernel_bound T Q F row col Φ Y χ B r κ hκc
      rate hA C hC).choose_spec
    exact RawKernel.bandKernelData_wideOperator_ae_rawIntegral
      (fun _ : ι ↦ extendedRetainedPhase T Q)
      (fun i x η ↦ complexCrossMeasurement (C x)
        (A (color i) (x, node i, extendedRetainedCarrier T z₀ hρ (node i)))
        (A (color i) (x, node i, η)))
      (fun i ↦ extendedRetainedCarrier T z₀ hρ (node i)) (fun i ↦ rate (color i)) mask
      hS hcross hζ ((continuous_of_discreteTopology (f := rate)).comp hcolor)
      (fun i ↦ hrate (color i)) hd (Prod.fst '' tsupport κ) (hκc.image continuous_fst)
      (fun i x η hx ↦ by
        have hz := cutCorrectedDerivativeAmplitude_zero_off_projection
          T Q F row col Φ Y χ B r κ (rate (color i)) x (node i) η hx
        change A (color i) (x, node i, η) = 0 at hz
        rw [hz, map_zero]) M Md hM.1 hMd
      (fun i x η ↦ hM.2 (color i) x (node i) _ η) hdb j p f
  refine hraw.trans (Filter.Eventually.of_forall fun x ↦ ?_)
  have hSx : Continuous (extendedRetainedPhase T Q x) :=
    (contDiff_extendedRetainedPhase T Q).continuous.comp
      (f := fun η ↦ (x, η)) (by fun_prop)
  have hAx : Continuous (fun η ↦ A (color p) (x, node p, η)) :=
    (hA (color p)).comp (f := fun η ↦ (x, node p, η)) (by fun_prop)
  have he := complexCrossMeasurement_rawSliceBandIntegral (extendedRetainedPhase T Q)
    (fun x η ↦ A (color p) (x, node p, η)) ζ (rate (color p)) mask
    (C x) (A (color p) (x, node p, ζ)) j.val f x hSx hAx hd
  change _ • rawSliceBandIntegral (extendedRetainedPhase T Q)
    (fun y η ↦ complexCrossMeasurement (C x) (A (color p) (x, node p, ζ))
      (A (color p) (y, node p, η))) (fun _ ↦ 1) ζ (rate (color p))
    (weightedRadialBand mask j.val) j.val f x = _
  rw [← he]

/-- Transfer the SAME corrected matrix slice extension to the literal cross
band. The supplied physical slice cutoff is used only on its plateau for the
original measurement; no new carrier or detector is introduced
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_correctedColoredCrossBandData_wideBand_le_slice
    (J : ℕ) (j : Fin J) (p : ι) (f : WideBandL2 (d + 1) j.val)
    (θ : Euclidean (d + 1) → ℝ)
    {R : Set (Euclidean (d + 1))}
    {u : LocalSobolev.LocalL2 R (Matrix (Fin N) (Fin (d + 1)) ℂ)}
    (e : LocalSobolev.SobolevExtension R 0 u)
    (he : e.toFun = fun x ↦ θ x •
      rawPrimaryDemodulatedIntegral (extendedRetainedPhase T Q)
        (fun x η ↦ κ (x, node p, η) •
          fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate (color p))
            (x, node p, η))
        (extendedRetainedCarrier T z₀ hρ (node p)) (rate (color p)) volume
        (weightedWideDensity mask
          (PiLp.single 2 (⟨j.val, by rw [cutoffCount_two_pow]; omega⟩ :
            Fin (cutoffCount ((2 : ℝ) ^ j.val))) f)) x)
    (hθ : ∀ x, C x ≠ 0 → θ x = 1)
    {MC Mzero : ℝ} (hMC : 0 ≤ MC) (hMzero : 0 ≤ Mzero)
    (hCbound : ∀ x, ‖C x‖ ≤ MC)
    (hzero : ∀ x, ‖κ (x, node p, extendedRetainedCarrier T z₀ hρ (node p)) •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate (color p))
        (x, node p, extendedRetainedCarrier T z₀ hρ (node p))‖ ≤ Mzero) :
    ‖wideBandKernelOperator
      (correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC
        color hcolor node hnode hP z₀ hρ hcarrier hrate mask hd Md hMd hdb J)
      j.val (j, p) f‖ ≤
        ((2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) * (2 * MC * Mzero)) * e.jetNorm := by
  let A c w := κ w • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w
  let ζ := extendedRetainedCarrier T z₀ hρ (node p)
  let w := e.memLp_fun.toLp e.toFun
  have hw : ‖w‖ = e.jetNorm := by
    rw [LocalSobolev.SobolevExtension.jetNorm_zero]
    exact Lp.norm_toLp e.toFun e.memLp_fun
  have hraw := correctedColoredCrossBandData_wideOperator_ae T Q F row col Φ Y χ B r κ hκc
    rate hA C hC color hcolor node hnode hP z₀ hρ hcarrier hrate mask hd Md hMd hdb J j p f
  let cf : ℝ := (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2)
  have hcf : 0 < cf := Real.rpow_pos_of_pos (by positivity) _
  rw [← hw]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hraw, e.memLp_fun.coeFn_toLp] with x hx hwx
  rw [hx]
  by_cases hCx : C x = 0
  · have hh : 0 ≤ (cf * (2 * MC * Mzero)) * ‖w x‖ := by positivity
    simpa [hCx, complexCrossMeasurement, cf] using hh
  have heq : rawSliceBandIntegral (extendedRetainedPhase T Q)
      (fun x η ↦ A (color p) (x, node p, η)) (fun _ ↦ 1) ζ (rate (color p))
      (weightedRadialBand mask j.val) j.val f x = e.toFun x := by
    let j' : Fin (cutoffCount ((2 : ℝ) ^ j.val)) :=
      ⟨j.val, by rw [cutoffCount_two_pow]; omega⟩
    rw [rawSliceBandIntegral_eq_singleDensity _ _ _ _ _ hd.measurable hdb j' f,
      Complex.ofReal_one, one_smul, he]
    dsimp only
    rw [hθ x hCx, one_smul]
  change ‖cf • complexCrossMeasurement (C x) (A (color p) (x, node p, ζ))
    (rawSliceBandIntegral _ _ _ _ _ _ _ _ x)‖ ≤ _
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hcf]
  apply (mul_le_mul_of_nonneg_left (norm_complexCrossMeasurement_le (C x) _ _) hcf.le).trans
  calc
    _ ≤ cf * (2 * MC * Mzero * ‖e.toFun x‖) := by
      gcongr
      · exact hCbound x
      · exact hzero x
    _ = _ := by rw [hwx]; ring

end JanetCartan.Sampling
