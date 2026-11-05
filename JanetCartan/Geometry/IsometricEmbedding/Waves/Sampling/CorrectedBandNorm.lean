module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedBandAction

/-!
# Corrected sampling bands on the original Hamilton phase

Remove the global phase and carrier extensions on their original retained
plateaus, keeping the cut corrected amplitude and its unmasked zero atom.
The resulting matrix slice is the one constructed by `CorrectedSliceBounds`.
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

variable (ζ₀ : Euclidean ((d + 1) - 1))
    (hphase : closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) (2 * ρ) ⊆ domain T)
    (hCsupport : Function.support C ⊆ closedBall 0 (ρ / 2))

include hphase hCsupport

/-- Every original corrected band has its literal Hamilton integral on the
SAME measured support. The full phase difference and detector survive unchanged,
including the high-pass transition (`app:ch_waves:eq:individual-representation`,
`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem correctedColoredCrossBandData_wideOperator_ae_original
    (J : ℕ) (j : Fin J) (p : ι)
    (hz : (node p, T.reference.spatialPatch (node p)) ∈ closedBall (z₀, ζ₀) (ρ / 4))
    (hscale : |rate (color p)| * (2 : ℝ) ^ j.val ≤ ρ / 8)
    (f : WideBandL2 (d + 1) j.val) :
    let A := fun c w ↦ κ w •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w
    let ζ := T.reference.spatialPatch (node p)
    wideBandKernelOperator
      (correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC
        color hcolor node hnode hP z₀ hρ hcarrier hrate mask hd Md hMd hdb J)
      j.val (j, p) f =ᵐ[volume] fun x ↦
        (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) •
          complexCrossMeasurement (C x) (A (color p) (x, node p, ζ))
            (rawSliceBandIntegral (phase T Q)
              (fun x η ↦ A (color p) (x, node p, η)) (fun _ ↦ 1)
              ζ (rate (color p)) (weightedRadialBand mask j.val) j.val f x) := by
  intro A ζ
  have hz' : node p ∈ closedBall z₀ ρ := by
    rw [← closedBall_prod_same] at hz
    exact closedBall_subset_closedBall (by linarith) hz.1
  have hraw := correctedColoredCrossBandData_wideOperator_ae T Q F row col Φ Y χ B r κ hκc
    rate hA C hC color hcolor node hnode hP z₀ hρ hcarrier hrate mask hd Md hMd hdb J j p f
  dsimp only at hraw
  rw [extendedRetainedCarrier_eq T z₀ hρ hz'] at hraw
  refine hraw.trans (Filter.Eventually.of_forall fun x ↦ ?_)
  by_cases hCx : C x = 0
  · simp only [hCx, complexCrossMeasurement]
    simp
  have he : rawSliceBandIntegral (extendedRetainedPhase T Q)
      (fun x η ↦ A (color p) (x, node p, η)) (fun _ ↦ 1)
      ζ (rate (color p)) (weightedRadialBand mask j.val) j.val f x =
      rawSliceBandIntegral (phase T Q)
        (fun x η ↦ A (color p) (x, node p, η)) (fun _ ↦ 1)
        ζ (rate (color p)) (weightedRadialBand mask j.val) j.val f x := by
    unfold rawSliceBandIntegral rawPrimaryDemodulatedIntegral
    congr 1
    apply integral_congr_ae
    filter_upwards [] with η
    by_cases hη : η ∈ wideBand (d + 1) j.val
    · have hnorm : ‖η‖ ≤ 2 * (2 : ℝ) ^ j.val := by
        have hu := hη.1
        simp only [mem_closedBall, dist_zero_right, dyadicScale] at hu
        linarith
      have hdis : ‖rate (color p) • η‖ ≤ ρ / 4 := by
        rw [norm_smul, Real.norm_eq_abs]
        calc
          _ ≤ |rate (color p)| * (2 * (2 : ℝ) ^ j.val) :=
            mul_le_mul_of_nonneg_left hnorm (abs_nonneg _)
          _ = (|rate (color p)| * (2 : ℝ) ^ j.val) * 2 := by ring
          _ ≤ (ρ / 8) * 2 := mul_le_mul_of_nonneg_right hscale (by norm_num)
          _ = ρ / 4 := by ring
      rw [extendedRetainedPhase_difference_eq T Q
        ((0 : Euclidean (d + 1)), (z₀, ζ₀)) hρ hphase (hCsupport hCx) hz _ η hdis]
    · simp only [weightedRadialBand_eq_zero_off_wideBand mask hη,
        mul_zero, zero_mul, zero_smul, smul_zero]
  change _ • complexCrossMeasurement (C x) (A (color p) (x, node p, ζ)) _ = _
  rw [he]

/-- Transfer the SAME corrected matrix slice extension to the literal cross
band. The original phase and carrier are retained, and the physical slice cutoff is used only on its plateau for the
original measurement; no new carrier or detector is introduced
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_correctedColoredCrossBandData_wideBand_le_original_slice
    (J : ℕ) (j : Fin J) (p : ι)
    (hz : (node p, T.reference.spatialPatch (node p)) ∈ closedBall (z₀, ζ₀) (ρ / 4))
    (hscale : |rate (color p)| * (2 : ℝ) ^ j.val ≤ ρ / 8)
    (f : WideBandL2 (d + 1) j.val)
    (θ : Euclidean (d + 1) → ℝ)
    {R : Set (Euclidean (d + 1))}
    {u : LocalSobolev.LocalL2 R (Matrix (Fin N) (Fin (d + 1)) ℂ)}
    (e : LocalSobolev.SobolevExtension R 0 u)
    (he : e.toFun = fun x ↦ θ x •
      rawPrimaryDemodulatedIntegral (phase T Q)
        (fun x η ↦ κ (x, node p, η) •
          fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate (color p))
            (x, node p, η))
        (T.reference.spatialPatch (node p)) (rate (color p)) volume
        (weightedWideDensity mask
          (PiLp.single 2 (⟨j.val, by rw [cutoffCount_two_pow]; omega⟩ :
            Fin (cutoffCount ((2 : ℝ) ^ j.val))) f)) x)
    (hθ : ∀ x, C x ≠ 0 → θ x = 1)
    {MC Mzero : ℝ} (hMC : 0 ≤ MC) (hMzero : 0 ≤ Mzero)
    (hCbound : ∀ x, ‖C x‖ ≤ MC)
    (hzero : ∀ x, ‖κ (x, node p, T.reference.spatialPatch (node p)) •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate (color p))
        (x, node p, T.reference.spatialPatch (node p))‖ ≤ Mzero) :
    ‖wideBandKernelOperator
      (correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC
        color hcolor node hnode hP z₀ hρ hcarrier hrate mask hd Md hMd hdb J)
      j.val (j, p) f‖ ≤
        ((2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) * (2 * MC * Mzero)) * e.jetNorm := by
  let A c w := κ w • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w
  let ζ := T.reference.spatialPatch (node p)
  let w := e.memLp_fun.toLp e.toFun
  have hw : ‖w‖ = e.jetNorm := by
    rw [LocalSobolev.SobolevExtension.jetNorm_zero]
    exact Lp.norm_toLp e.toFun e.memLp_fun
  have hraw := correctedColoredCrossBandData_wideOperator_ae_original T Q F row col Φ Y χ B r κ hκc
    rate hA C hC color hcolor node hnode hP z₀ hρ hcarrier hrate mask hd Md hMd hdb ζ₀ hphase hCsupport J j p hz hscale f
  let cf : ℝ := (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2)
  have hcf : 0 < cf := Real.rpow_pos_of_pos (by positivity) _
  rw [← hw]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hraw, e.memLp_fun.coeFn_toLp] with x hx hwx
  rw [hx]
  by_cases hCx : C x = 0
  · have hh : 0 ≤ (cf * (2 * MC * Mzero)) * ‖w x‖ := by positivity
    simpa [hCx, complexCrossMeasurement, cf] using hh
  have heq : rawSliceBandIntegral (phase T Q)
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
