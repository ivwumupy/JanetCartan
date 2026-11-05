module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualFlow.Coordinates

/-!
# Transfer of the actual low coefficient bound to the lifted field

The quantitative input here is a `C¹` bound for the named
`carrierTransportDirection`, produced by `jc-null-coefficient-tame`. Fixed
linear coordinate maps convert it to the value and derivative bounds used by
the Picard construction. No bound on an unknown flow is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport.ActualFlow
open ActualCarriers FrozenMenu CurrentFullPhase

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
variable (T : PatchQuantitativeFamily P U hU)

/-- The fixed spatial projection of the adapted coordinates, used in the
actual null-characteristic equation (`app:ch_waves:thm:leading`). -/
def directionProjection : Euclidean n →L[ℝ] Euclidean (n - 1) :=
  (ContinuousLinearMap.snd ℝ ℝ (Euclidean (n - 1))).comp
    (adaptedCoordinates T.data.adapted).toContinuousLinearMap

/-- A low bound for the autonomous lift depending only on the named direction's
low bound and the fixed adapted coordinates (`app:ch_waves:thm:leading`). -/
def liftedLowBound (M : ℝ) : ℝ :=
  1 + ‖directionProjection T‖ *
    (1 + ‖(FlowAmplitude.coordinates (Z := Euclidean 3)
      (adaptedCoordinates T.data.adapted)).symm.toContinuousLinearMap‖) * M

/-- The lifted low bound is nonnegative (`app:ch_waves:thm:leading`). -/
theorem liftedLowBound_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ liftedLowBound T M := by
  unfold liftedLowBound
  positivity

variable
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The compact `C¹` bound of the literal physical direction supplies BOTH
Picard bounds for its autonomous lift. The actual producer of `hlow` is
`jc-null-coefficient-tame`; smoothness and the open coefficient patch come from
`exists_projected_null_coefficients`. The compact working set and its contained
adapted state ball are geometric buffers (`app:ch_waves:thm:leading`). -/
theorem liftedDirection_low_bounds (row col : Fin n)
    {Ω K : Set (Euclidean n × Euclidean 3)} (hΩ : IsOpen Ω)
    (hd : ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {M : ℝ} (hM : 0 ≤ M)
    (hlow : cNorm K 1 (carrierTransportDirection T Q row col) ≤ M)
    {q : ℝ × (Euclidean (n - 1) × Euclidean 3)}
    (hq : (FlowAmplitude.coordinates (adaptedCoordinates T.data.adapted)).symm q ∈ K) :
    ‖liftedDirection T Q row col q‖ ≤ liftedLowBound T M ∧
      ‖fderiv ℝ (liftedDirection T Q row col) q‖ ≤ liftedLowBound T M := by
  let C := FlowAmplitude.coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  let d := carrierTransportDirection T Q row col
  let L := directionProjection T
  have hreg (w) (hw : w ∈ K) : ContDiffAt ℝ 1 d w :=
    (hd.contDiffAt (hΩ.mem_nhds (hKΩ hw))).of_le (by simp)
  have hv : ‖d (C.symm q)‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_zero] using
      (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hreg hq (show 0 ≤ 1 by omega)).trans hlow
  have hD : ‖fderiv ℝ d (C.symm q)‖ ≤ M := by
    simpa only [norm_iteratedFDeriv_one] using
      (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hreg hq le_rfl).trans hlow
  have hvalue : ‖L (d (C.symm q))‖ ≤ ‖L‖ * M :=
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
  have hdiff := L.hasFDerivAt.comp q
    (((hreg _ hq).differentiableAt (by simp)).hasFDerivAt.comp q C.symm.hasFDerivAt)
  have hlift : HasFDerivAt (liftedDirection T Q row col)
      ((0 : _ →L[ℝ] ℝ).prod
        ((L.comp ((fderiv ℝ d (C.symm q)).comp C.symm.toContinuousLinearMap)).prod
          (0 : _ →L[ℝ] Euclidean 3))) q :=
    (hasFDerivAt_const (1 : ℝ) q).prodMk (hdiff.prodMk (hasFDerivAt_const (0 : Euclidean 3) q))
  have hderivative : ‖fderiv ℝ (liftedDirection T Q row col) q‖ ≤
      ‖L‖ * (M * ‖C.symm.toContinuousLinearMap‖) := by
    rw [hlift.fderiv]
    simp only [ContinuousLinearMap.opNorm_prod, Prod.norm_def, norm_zero,
      max_eq_left (norm_nonneg _), max_eq_right (norm_nonneg _)]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    exact mul_le_mul_of_nonneg_left
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right hD (norm_nonneg _))) (norm_nonneg _)
  have hL : 0 ≤ ‖L‖ := norm_nonneg _
  have hC : 0 ≤ ‖C.symm.toContinuousLinearMap‖ := norm_nonneg _
  constructor
  · change ‖((1 : ℝ), L (d (C.symm q)), (0 : Euclidean 3))‖ ≤ _
    simp only [Prod.norm_def, norm_one, norm_zero, max_eq_left (norm_nonneg _)]
    apply max_le
    · exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hL (by positivity)) hM)
    · apply hvalue.trans
      change ‖L‖ * M ≤ 1 + ‖L‖ * (1 + ‖C.symm.toContinuousLinearMap‖) * M
      nlinarith [mul_nonneg hL hM, mul_nonneg (mul_nonneg hL hC) hM]
  · apply hderivative.trans
    change ‖L‖ * (M * ‖C.symm.toContinuousLinearMap‖) ≤
      1 + ‖L‖ * (1 + ‖C.symm.toContinuousLinearMap‖) * M
    nlinarith [mul_nonneg hL hM]

end JanetCartan.NullTransport.ActualFlow
