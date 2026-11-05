module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.GradedFamily
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.WkbGrades

/-!
# Actual ambient grades in the retained slice coordinates

The same joint amplitude and covector profiles from `GradedFamily` are pulled
back along the fixed adapted coordinate map and the fixed carrier label.
Frobenius flattening is included. The coordinate cost is independent of the
immersion, scalar, inverse frequency, history scale and band count, and no
derivative reserve is spent (`app:ch_waves:eq:individual-raw-slice`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary
open SliceBounds SingleChannel
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation

variable {n : ℕ} {ξ : Euclidean n}
  (sec : ActualCarriers.FrozenPhaseReference.AdaptedSection ξ)

/-- The linear part of the original slice-to-working-chart map, retaining the
free covector (`app:ch_waves:eq:individual-raw-slice`). -/
def rawSliceWorkingLinear :
    ((ℝ × Euclidean (n - 1)) × Euclidean (n - 1)) →L[ℝ]
      Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
  (((NullTransport.ActualFlow.adaptedCoordinates sec).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.fst ℝ _ _)).prod
      ((0 : _ →L[ℝ] Euclidean 3).prod (ContinuousLinearMap.snd ℝ _ _))

/-- Fixed coordinate cost for the primitive WKB jets in the actual slice
norm (`app:ch_waves:eq:individual-raw-slice`). -/
def rawSliceCoordinateCost : ℝ := max 1 ‖rawSliceWorkingLinear sec‖

/-- The coordinate cost is positive and independent of all wave data
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem rawSliceCoordinateCost_pos : 0 < rawSliceCoordinateCost sec :=
  zero_lt_one.trans_le (le_max_left _ _)

private theorem norm_iteratedFDeriv_sliceWorking_le
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

private def sliceMatrixComponents (N n : ℕ) :
    Matrix (Fin N) (Fin n) ℂ →L[ℝ] (Fin (N * n) → ℂ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (N * n) ↦ ℂ)).toContinuousLinearMap.comp
    ((matrixChannelEquiv N n).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)

private theorem norm_sliceMatrixComponents_le_one (N n : ℕ) :
    ‖sliceMatrixComponents N n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  change ‖(fun i ↦ matrixChannelEquiv N n A i)‖ ≤ 1 * ‖A‖
  rw [one_mul]
  apply pi_norm_le_iff_of_nonneg (norm_nonneg A) |>.mpr
  intro i
  exact (PiLp.norm_apply_le (matrixChannelEquiv N n A) i).trans_eq
    ((matrixChannelEquiv N n).norm_map A)

private theorem norm_iteratedFDeriv_sliceMatrix_le {N : ℕ}
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
  let B := sliceMatrixComponents N n
  have hBA : ContDiffOn ℝ ∞ (B ∘ A) Ω := B.contDiff.comp_contDiffOn hA
  have hh := norm_iteratedFDeriv_sliceWorking_le sec hΩ hBA z hq k
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (rawSliceCoordinateCost_pos sec).le _)
  have hc := B.norm_iteratedFDeriv_comp_left (hA.contDiffAt (hΩ.mem_nhds hq))
    (by simp : (k : ℕ∞ω) ≤ ∞)
  exact hc.trans ((mul_le_mul_of_nonneg_right (norm_sliceMatrixComponents_le_one N n)
    (norm_nonneg _)).trans_eq (one_mul _))

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The literal derivative amplitude has precisely the slice profile required
by `exists_rawPhysicalSliceSobolev_wkbGrades`. The joint estimate is the
conclusion of `exists_finite_actual_graded_raw_family`, with baseline `rpar`;
freezing the carrier label and applying the physical coordinate map spend no
reserve (`app:ch_waves:eq:individual-raw-slice`). -/
theorem fullDerivativeAmplitude_sliceGrade {N : ℕ}
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ) (τ : ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω)
    (hA : ContDiffOn ℝ ∞ (fullDerivativeAmplitude T Q F row col Φ Y r τ) Ω)
    (z : Euclidean 3) {k rpar : ℕ} {L C : ℝ}
    {q : (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)}
    (hq : (adaptedPhysicalCoordinates sec q.1, (z, q.2)) ∈ Ω)
    (hgrade : ‖iteratedFDeriv ℝ k (fullDerivativeAmplitude T Q F row col Φ Y r τ)
        (adaptedPhysicalCoordinates sec q.1, (z, q.2))‖ ≤ C * L ^ (k - rpar)) :
    ‖iteratedFDeriv ℝ k
      (fun w : (ℝ × Euclidean (n - 1)) × Euclidean (n - 1) ↦
        fun i ↦ matrixChannelEquiv N n
          (fullDerivativeAmplitude T Q F row col Φ Y r τ
            (adaptedPhysicalCoordinates sec w.1, (z, w.2))) i) q‖ ≤
      (rawSliceCoordinateCost sec ^ k * C) * L ^ (k - rpar) := by
  apply (norm_iteratedFDeriv_sliceMatrix_le sec hΩ
    (fullDerivativeAmplitude T Q F row col Φ Y r τ) hA z hq k).trans
  calc
    _ ≤ (C * L ^ (k - rpar)) * rawSliceCoordinateCost sec ^ k :=
      mul_le_mul_of_nonneg_right hgrade (pow_nonneg (rawSliceCoordinateCost_pos sec).le _)
    _ = _ := by ring

/-- The actual free-covector differential has the consumer's baseline
`rpar+1`. The stronger joint profile exported by `GradedFamily` is restricted
to the SAME original phase, without replacing the covector or increasing the
manuscript reserve (`app:ch_waves:eq:graded-phase`). -/
theorem fullPhase_covector_sliceGrade (z : Euclidean 3)
    {k rpar : ℕ} {L C : ℝ} (hL : 1 ≤ L) (hC : 0 ≤ C)
    {q : (ℝ × Euclidean (n - 1)) × Euclidean (n - 1)}
    (hq : (adaptedPhysicalCoordinates sec q.1, (z, q.2)) ∈ domain T)
    (hgrade : ‖iteratedFDeriv ℝ k
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        fderiv ℝ (phase T Q w.1) w.2.2)
      (adaptedPhysicalCoordinates sec q.1, (z, q.2))‖ ≤ C * L ^ (k - 1 - (rpar + 2))) :
    ‖iteratedFDeriv ℝ k
      (fun w : (ℝ × Euclidean (n - 1)) × Euclidean (n - 1) ↦
        fderiv ℝ (fun η ↦ phase T Q (adaptedPhysicalCoordinates sec w.1) η) w.2) q‖ ≤
      (rawSliceCoordinateCost sec ^ k * C) * L ^ (k - 1 - rpar) := by
  apply (norm_iteratedFDeriv_sliceWorking_le sec (isOpen_domain T)
    (AmplitudeGrades.contDiffOn_fullPhase_parameter_fderiv T Q) z hq k).trans
  calc
    _ ≤ (C * L ^ (k - 1 - (rpar + 2))) * rawSliceCoordinateCost sec ^ k :=
      mul_le_mul_of_nonneg_right hgrade (pow_nonneg (rawSliceCoordinateCost_pos sec).le _)
    _ = (rawSliceCoordinateCost sec ^ k * C) * L ^ (k - 1 - (rpar + 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL (by omega))
      (mul_nonneg (pow_nonneg (rawSliceCoordinateCost_pos sec).le _) hC)

end JanetCartan.RawPrimary
