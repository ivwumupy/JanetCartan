module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceGrading
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.JointProfiles

/-!
# Corrected amplitudes in the original canonical slice

The corrected raw integral uses the same affine slice, free covector and
Frobenius components as the original raw estimate. The fixed coordinate cost
preserves the entire derivative reserve. This supplies the corrected input to
`SliceBounds.exists_rawPhysicalSliceSobolev_finiteJets`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling
open RawPrimary RawPrimary.SliceBounds SingleChannel CorrectedAtoms
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation

variable {n : ℕ} {ξ : Euclidean n}
  (sec : ActualCarriers.FrozenPhaseReference.AdaptedSection ξ)

/-- The original adapted affine slice preserves the ambient jets with the fixed coordinate cost
(`app:ch_waves:eq:individual-raw-slice`). -/
private theorem norm_iteratedFDeriv_correctedSliceWorking_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) {f : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → E}
    (hf : ContDiffOn ℝ ∞ f Ω) (z : Euclidean 3)
    {q : (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)}
    (hq : (adaptedPhysicalCoordinates sec q.1, (z, q.2)) ∈ Ω) (k : ℕ) :
    ‖iteratedFDeriv ℝ k
      (fun w : (ℝ × Euclidean (n - 1)) × Euclidean (n - 1) ↦
        f (adaptedPhysicalCoordinates sec w.1, (z, w.2))) q‖ ≤
      ‖iteratedFDeriv ℝ k f (adaptedPhysicalCoordinates sec q.1, (z, q.2))‖ *
        rawSliceCoordinateCost sec ^ k := by
  let c : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) := (0, (z, 0))
  let g := fun w ↦ f (c + w)
  let V := (fun w ↦ c + w) ⁻¹' Ω
  have hV : IsOpen V := hΩ.preimage (by fun_prop)
  have hg : ContDiffOn ℝ ∞ g V := hf.comp (by fun_prop) (fun _ h ↦ h)
  have hm : rawSliceWorkingLinear sec q ∈ V := by
    simpa [rawSliceWorkingLinear, V, c] using hq
  have he : (fun w : (ℝ × Euclidean (n - 1)) × Euclidean (n - 1) ↦
      f (adaptedPhysicalCoordinates sec w.1, (z, w.2))) = g ∘ rawSliceWorkingLinear sec := by
    funext w
    simp [g, c, rawSliceWorkingLinear]
  rw [he]
  apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le
    (rawSliceWorkingLinear sec) hV hg hm k).trans
  have hcost : ‖rawSliceWorkingLinear sec‖ ^ k ≤ rawSliceCoordinateCost sec ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
  apply (mul_le_mul_of_nonneg_left hcost (norm_nonneg _)).trans_eq
  simp [g, c, iteratedFDeriv_comp_add_left, rawSliceWorkingLinear]

/-- Frobenius components of the literal corrected matrix amplitude
(`app:ch_waves:eq:individual-raw-slice`). -/
private def correctedSliceMatrixComponents (N n : ℕ) :
    Matrix (Fin N) (Fin n) ℂ →L[ℝ] (Fin (N * n) → ℂ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (N * n) ↦ ℂ)).toContinuousLinearMap.comp
    ((matrixChannelEquiv N n).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)

/-- Flattening the corrected amplitude spends no norm constant
(`app:ch_waves:eq:individual-raw-slice`). -/
private theorem norm_correctedSliceMatrixComponents_le_one (N n : ℕ) :
    ‖correctedSliceMatrixComponents N n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  change ‖(fun i ↦ matrixChannelEquiv N n A i)‖ ≤ 1 * ‖A‖
  rw [one_mul]
  apply pi_norm_le_iff_of_nonneg (norm_nonneg A) |>.mpr
  intro i
  exact (PiLp.norm_apply_le (matrixChannelEquiv N n A) i).trans_eq
    ((matrixChannelEquiv N n).norm_map A)

/-- The SAME slice and Frobenius coordinates retain every original jet
(`app:ch_waves:eq:individual-raw-slice`). -/
private theorem norm_iteratedFDeriv_correctedSliceMatrix_le {N : ℕ}
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω)
    (A : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → Matrix (Fin N) (Fin n) ℂ)
    (hA : ContDiffOn ℝ ∞ A Ω) (z : Euclidean 3)
    {q : (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)}
    (hq : (adaptedPhysicalCoordinates sec q.1, (z, q.2)) ∈ Ω) (k : ℕ) :
    ‖iteratedFDeriv ℝ k
      (fun w : (ℝ × Euclidean (n - 1)) × Euclidean (n - 1) ↦
        fun i ↦ matrixChannelEquiv N n
          (A (adaptedPhysicalCoordinates sec w.1, (z, w.2))) i) q‖ ≤
      ‖iteratedFDeriv ℝ k A (adaptedPhysicalCoordinates sec q.1, (z, q.2))‖ *
        rawSliceCoordinateCost sec ^ k := by
  let B := correctedSliceMatrixComponents N n
  have hBA : ContDiffOn ℝ ∞ (B ∘ A) Ω := B.contDiff.comp_contDiffOn hA
  have hh := norm_iteratedFDeriv_correctedSliceWorking_le sec hΩ hBA z hq k
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (rawSliceCoordinateCost_pos sec).le _)
  have hc := B.norm_iteratedFDeriv_comp_left (hA.contDiffAt (hΩ.mem_nhds hq))
    (by simp : (k : ℕ∞ω) ≤ ∞)
  exact hc.trans ((mul_le_mul_of_nonneg_right (norm_correctedSliceMatrixComponents_le_one N n)
    (norm_nonneg _)).trans_eq (one_mul _))

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The corrected derivative uses the SAME adapted slice and original jet reserve.
Only its ambient derivative estimate is pulled back; no raw/corrected operator
identification is assumed (`app:ch_waves:eq:individual-raw-slice`,
`app:ch_response:eq:current-atomic-amplitudes`). -/
theorem cutCorrectedDerivativeAmplitude_sliceGrade {N : ℕ}
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ) (τ : ℝ)
    (κ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω)
    (hA : ContDiffOn ℝ ∞ (fun w ↦ κ w • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w) Ω)
    (z : Euclidean 3) {k rpar : ℕ} {L C : ℝ}
    {q : (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)}
    (hq : (adaptedPhysicalCoordinates sec q.1, (z, q.2)) ∈ Ω)
    (hgrade : ‖iteratedFDeriv ℝ k (fun w ↦ κ w • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w)
        (adaptedPhysicalCoordinates sec q.1, (z, q.2))‖ ≤ C * L ^ (k - rpar)) :
    ‖iteratedFDeriv ℝ k
      (fun w : (ℝ × Euclidean (n - 1)) × Euclidean (n - 1) ↦
        fun i ↦ matrixChannelEquiv N n
          (κ (adaptedPhysicalCoordinates sec w.1, (z, w.2)) •
            fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ
              (adaptedPhysicalCoordinates sec w.1, (z, w.2))) i) q‖ ≤
      (rawSliceCoordinateCost sec ^ k * C) * L ^ (k - rpar) := by
  apply (norm_iteratedFDeriv_correctedSliceMatrix_le sec hΩ
    (fun w ↦ κ w • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w) hA z hq k).trans
  calc
    _ ≤ (C * L ^ (k - rpar)) * rawSliceCoordinateCost sec ^ k :=
      mul_le_mul_of_nonneg_right hgrade (pow_nonneg (rawSliceCoordinateCost_pos sec).le _)
    _ = _ := by ring

end JanetCartan.Sampling
