module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.CorrectedSamplingData
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.JointProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.UniformKernelBounds

/-!
# Quantitative bounds for the literal corrected cross kernel

Apply the corrected-amplitude profile to the original compact cutoff and the
complexification of the SAME real measurement. The resulting amplitude and
trace estimates do not depend on the qualitative bound chosen by
`correctedColoredCrossBandData`. The unmasked zero atom, detector, phase,
Fourier scalar, annular measures and grouped prefixes remain literal.

Consumers: `app:ch_waves:eq:sampling-operator-bounds` and the whole-source
canonical family. The sharp band, colored transport and mean bounds are
separate obligations, as are the original response/preparation profile inputs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.Sampling
open CanonicalRowComparison CanonicalAtomRealization CurrentMean CorrectedAtoms
open SamplingKernelBounds RawInputPartition RawInputRealization
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial

/-- Complexifying the original real measurement costs at most two in the
Frobenius product bound. Both factors are literal amplitudes; no detector is
inserted at the zero atom (`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem norm_complexCrossMeasurement_le {m n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ →L[ℝ] EuclideanSpace ℝ (Fin n)) (B V : Matrix (Fin m) (Fin n) ℂ) :
    ‖complexCrossMeasurement C B V‖ ≤ 2 * ‖C‖ * ‖B‖ * ‖V‖ := by
  change ‖euclideanComplexInclusion (C (hermitianContinuousBilinear B V)) -
    Complex.I • euclideanComplexInclusion
      (C (hermitianContinuousBilinear B (Complex.I • V)))‖ ≤ _
  apply (norm_sub_le _ _).trans
  rw [norm_smul, Complex.norm_I, one_mul, euclideanComplexInclusion_norm,
    euclideanComplexInclusion_norm]
  calc
    _ ≤ ‖C‖ * (‖B‖ * ‖V‖) + ‖C‖ * (‖B‖ * ‖Complex.I • V‖) :=
      add_le_add ((C.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (norm_mixedHermitianTensor_le B V) (norm_nonneg _)))
        ((C.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (norm_mixedHermitianTensor_le B (Complex.I • V)) (norm_nonneg _)))
    _ = _ := by simp only [norm_smul, Complex.norm_I, one_mul]; ring


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

omit [FirstCountableTopology ι] [LocallyCompactSpace ι] in
/-- Uniform amplitude bounds on the SAME cutoff support give a quantitative
bound for the literal corrected sampling coefficient, including its original
Fourier factor and radial band. The qualitative chosen bound is unused
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem norm_correctedColoredCrossBandData_amplitude_le
    {Mκ MC MA : ℝ} (hMκ : 0 ≤ Mκ) (hMC : 0 ≤ MC) (hMA : 0 ≤ MA)
    (hκbound : ∀ w, |κ w| ≤ Mκ)
    (hCbound : ∀ x ∈ Prod.fst '' tsupport κ, ‖C x‖ ≤ MC)
    (hAbound : ∀ c w, w ∈ tsupport κ →
      ‖fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w‖ ≤ MA)
    (J : ℕ) (q : Fin J × ι) (η : Euclidean ((d + 1) - 1)) (x : Euclidean (d + 1)) :
    ‖(correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC
      color hcolor node hnode hP z₀ hρ hcarrier hrate mask hd Md hMd hdb J).amplitude
        ((q, η), x)‖ ≤
      (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) * (2 * MC * (Mκ * MA) ^ 2) := by
  let A c w := κ w • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w
  have hcut (c : γ) (w) : ‖A c w‖ ≤ Mκ * MA := by
    by_cases hw : w ∈ tsupport κ
    · simpa only [A, norm_smul, Real.norm_eq_abs] using
        mul_le_mul (hκbound w) (hAbound c w hw) (norm_nonneg _) hMκ
    · simp only [A, image_eq_zero_of_notMem_tsupport hw, zero_smul, norm_zero]
      exact mul_nonneg hMκ hMA
  have hcross (c : γ) (x z ξ ξ') :
      ‖complexCrossMeasurement (C x) (A c (x,z,ξ)) (A c (x,z,ξ'))‖ ≤
        2 * MC * (Mκ * MA) ^ 2 := by
    by_cases hx : x ∈ Prod.fst '' tsupport κ
    · apply (norm_complexCrossMeasurement_le (C x) (A c (x,z,ξ)) (A c (x,z,ξ'))).trans
      calc
        _ ≤ 2 * MC * (Mκ * MA) * (Mκ * MA) := by
          gcongr
          · exact hCbound x hx
          · exact hcut c (x,z,ξ)
          · exact hcut c (x,z,ξ')
        _ = _ := by ring
    · have hz := cutCorrectedDerivativeAmplitude_zero_off_projection
        T Q F row col Φ Y χ B r κ (rate c) x z ξ' hx
      change A c (x,z,ξ') = 0 at hz
      rw [hz, map_zero, norm_zero]
      positivity
  change ‖RawKernel.measuredBandAmplitude
    (fun i x ξ ↦ complexCrossMeasurement (C x)
      (A (color i) (x, node i, MeasuredAmplitude.extendedRetainedCarrier T z₀ hρ (node i)))
      (A (color i) (x, node i, ξ)))
    (fun i ↦ MeasuredAmplitude.extendedRetainedCarrier T z₀ hρ (node i))
    (fun i ↦ rate (color i)) ((q, η), x)‖ ≤ _
  have hb : |radialBand (d + 1) q.1.val η| ≤ 1 := by
    have h := bandProfile_mem (‖η‖ / dyadicScale q.1.val)
    exact (abs_of_nonneg h.1).trans_le h.2
  simp only [RawKernel.measuredBandAmplitude, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 2 * Real.pi) _)]
  exact mul_le_mul
    ((mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (by positivity) _)).trans_eq
      (mul_one _)) (hcross _ _ _ _ _) (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)

omit [FirstCountableTopology ι] [LocallyCompactSpace ι] in
/-- The actual corrected column has the uniform squared-integral estimate.
It is proved from its measured coefficient and original detector; it does not
assert a bound for the constructor's arbitrary compactness witness
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem correctedColoredCrossBandData_integral_norm_column_sq_le
    {Mκ MC MA : ℝ} (hMκ : 0 ≤ Mκ) (hMC : 0 ≤ MC) (hMA : 0 ≤ MA)
    (hκbound : ∀ w, |κ w| ≤ Mκ)
    (hCbound : ∀ x ∈ Prod.fst '' tsupport κ, ‖C x‖ ≤ MC)
    (hAbound : ∀ c w, w ∈ tsupport κ →
      ‖fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w‖ ≤ MA)
    (J : ℕ) {R : ℝ} (hR : 0 ≤ R) (q : Fin J × ι) :
    (∫ η, ‖(correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC
      color hcolor node hnode hP z₀ hρ hcarrier hrate mask hd Md hMd hdb J).column q η‖ ^ 2
        ∂annularMeasure (d + 1) R) ≤
      (volume.real (Prod.fst '' tsupport κ) * Md ^ 2 *
        ((2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) * (2 * MC * (Mκ * MA) ^ 2)) ^ 2 *
        unitBallVolume (d + 1)) * R ^ (d + 1) := by
  let D := correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC
    color hcolor node hnode hP z₀ hρ hcarrier hrate mask hd Md hMd hdb J
  exact integral_norm_column_sq_le_of_uniform_bounds D (by omega)
    (hκc.image continuous_fst) hR (by positivity) hMd D.amplitude_eq_zero
    (norm_correctedColoredCrossBandData_amplitude_le T Q F row col Φ Y χ B r κ hκc
      rate hA C hC color hcolor node hnode hP z₀ hρ hcarrier hrate mask hd Md hMd hdb
      hMκ hMC hMA hκbound hCbound hAbound J) hdb q

end JanetCartan.Sampling
