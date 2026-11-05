module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedPhase
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.SeedCovector
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity.Coefficients

/-!
# The unchanged frozen evidence of the normalized family

These identities connect the supplied retained seed to the frozen input of
`app:ch_background:prop:bg-normalized`. They concern the actual covector,
selected adjugate column and canonical normal completion. In particular, no
completion of the rank-degenerate zero-scale immersion is used. The consumer
is the same-row frozen gap in `NormalizedFrozenGap` and its subsequent
positive-scale normal comparison.
-/

@[expose] public noncomputable section

open Set Metric Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.NormalizedFrozenGap

open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier FrozenModel NormalizedBackground
open NullTransport ProjectedStressFrame LeadingWave AmbientResponse

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The origin covector of every normalized scale is the SAME seed covector,
including the integral extension at zero (`app:ch_background:eq:bg-Nsigma`).
This supplies the unchanged incidence detector in the uniform frozen gap. -/
theorem normalizedCovector_origin {c C : ℝ} (hP : P.IsValid c C)
    (σ : ℝ) {z : CarrierParameter}
    (hz : parameter z ∈ parameterInterior (2 * P.radius)) :
    normalizedCovector T Q σ 0 z = T.carrierGradient Q 0 (parameter z) := by
  simpa only [smul_zero] using normalizedCovector_eq_retainedCarrierGradient T Q hP
    (σ := σ) (x := 0) (by simpa using T.physicalRadius_pos) hz

/-- The parameter differential of the origin covector is also unchanged.
Thus the transverse frozen detector geometry uses the same differential at
every normalized scale, not merely the same value at an incidence root
(`app:ch_background:eq:bg-jacobian`, `bg-Nsigma`). -/
theorem normalizedCovector_origin_fderiv {c C : ℝ} (hP : P.IsValid c C)
    (σ : ℝ) {z : CarrierParameter}
    (hz : parameter z ∈ parameterInterior (2 * P.radius)) :
    fderiv ℝ (fun w ↦ normalizedCovector T Q σ 0 w) z =
      fderiv ℝ (fun w ↦ T.carrierGradient Q 0 (parameter w)) z := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [((isOpen_parameterInterior (2 * P.radius)).preimage
    parameter.continuous).mem_nhds hz] with w hw
  exact normalizedCovector_origin T Q hP σ hw

/-- The original seed-covector producer's threshold also identifies every
normalized origin covector with the original patch. The threshold precedes
the admitted frame and scale (`app:ch_seed:eq:seed-frozen-detection`,
`app:ch_background:prop:bg-normalized`). -/
theorem exists_uniform_normalized_patch_covector {c C : ℝ} (hP : P.IsValid c C) :
    ∃ δ > (0 : ℝ), ∀ Q : {Q : Euclidean n → Fin n → MetricTensor n //
        ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ → Q.1 0 = cubeStress n →
      ∀ σ : ℝ, ∀ z : CarrierParameter, parameter z ∈ parameterCube P.radius →
        normalizedCovector T Q σ 0 z = P.toFun (parameter z) := by
  obtain ⟨δ, hδ, hseed⟩ := RetainedFrozen.exists_uniform_seed_carrierGradient_zero T hP
  refine ⟨δ, hδ, ?_⟩
  intro Q hQ hzero σ z hz
  rw [normalizedCovector_origin T Q hP σ
    (parameterCube_subset_doubledInterior hP.1 hz)]
  exact hseed Q hQ hzero _ hz

/-- The retained adjugate column is null for the actual cube pencil, proved
from the original characteristic patch and seed identity. This discharges
the null relation in `exists_retained_frozen_row_gap`; its selected-column
nonvanishing is still supplied by the leading-wave minor
(`app:ch_seed:eq:seed-frozen-detection`, `app:ch_waves:thm:leading`). -/
theorem seed_carrierNullvector_null_of_patch {c C : ℝ} (hP : P.IsValid c C)
    (hzero : Q.1 0 = cubeStress n) (col : Fin n) {z : Euclidean 3}
    (hz : z ∈ parameterCube P.radius) (hseed : T.carrierGradient Q 0 z = P.toFun z) :
    pencil (Q.1 0) (T.carrierGradient Q 0 z) *ᵥ
      (fun k ↦ carrierNullvector T Q col (0, z) k) = 0 := by
  change pencil (Q.1 0) (T.carrierGradient Q 0 z) *ᵥ
    rightNullvector (reducedSymbol (Q.1 0) (T.carrierGradient Q 0 z)) col = 0
  rw [reducedSymbol_eq_pencil]
  apply mulVec_rightNullvector
  rw [hzero, hseed, pencil_cubeStress]
  exact (hP.2.2.2.2.1 z hz).2.1

/-- The selected null column is unchanged when the normalized frame and
covector are frozen at physical zero. This is an equality for the original
column index, so its nonvanishing never has to be reselected with scale
(`app:ch_background:eq:bg-Nsigma`, `app:ch_waves:thm:leading`). -/
theorem normalized_origin_null_column {c C : ℝ} (hP : P.IsValid c C)
    (σ : ℝ) (col : Fin n) {z : CarrierParameter}
    (hz : parameter z ∈ parameterInterior (2 * P.radius)) :
    WithLp.toLp 2 (rightNullvector
      (reducedSymbol (Q.1 (σ • (0 : Euclidean n))) (normalizedCovector T Q σ 0 z)) col) =
      carrierNullvector T Q col (0, parameter z) := by
  rw [smul_zero, normalizedCovector_origin T Q hP σ hz]
  rfl

variable (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- Every normalized scale has the same normal at physical zero, with the
original initial scalar and inverse-flow label (`app:ch_background:eq:bg-Nsigma`).
Thus freezing does not introduce a scale-dependent normal gap. -/
theorem normalizedNormal_origin (σ : ℝ) (z : CarrierParameter) :
    normalizedNormal T Q F row col Φ Y initial σ 0 z =
      normalizedNormal T Q F row col Φ Y initial 0 0 z := by
  simp only [normalizedNormal, normalizedPullback, smul_zero]

/-- The actual source-dilated completion and scaled null amplitude cancel at
the origin. This identifies the frozen normal with the SAME retained seed,
without a uniform lower bound for the shrinking second form
(`app:ch_background:eq:bg-Nsigma`). -/
theorem source_principalNormal_origin {σ : ℝ} (hσ : 0 < σ)
    (hF : ContDiff ℝ ∞ F)
    (hrank : Set.range (normalMap F 0) = (normalSpace F 0 : Set (Euclidean N)))
    (z : CarrierParameter) :
    principalNormal (canonicalNormalCompletion (sourceDilation F σ) 0)
        (T.carrierGradient Q 0 (parameter z))
        (σ • (carrierScalarAmplitude T Q F row col Φ Y initial (0, parameter z) •
          carrierNullvector T Q col (0, parameter z))) =
      normalizedNormal T Q F row col Φ Y initial 0 0 z := by
  have h := normalizedNormal_eq_sourceDilation T Q F row col Φ Y initial hσ hF
    0 z (by simpa only [smul_zero] using hrank)
  simpa only [smul_zero, normalizedNormal_origin] using h.symm

variable {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)

/-- The normalized image frame at the origin is exactly the cube frame at
every scale, including zero (`app:ch_background:prop:bg-normalized`). The
fixed image channel therefore uses one frozen array and one measurement mask. -/
theorem normalizedCarrierData_stressFrame_origin (hzero : Q.1 0 = cubeStress n)
    (σ : ℝ) :
    (normalizedCarrierData T Q F row col Φ Y initial hr hcell angular high σ).stressFrame 0 =
      cubeStress n := by
  simpa only [normalizedCarrierData, smul_zero] using hzero

/-- The actual positive-scale projected stress, rather than only its regular
extension, has the same cube value (`app:ch_background:eq:bg-Nsigma`). -/
theorem projectedStress_sourceDilation_origin (G : FlatReference n)
    {σ : ℝ} (hσ : 0 < σ) :
    projectedStress (sourceDilation G.map σ) 0 = cubeStress n := by
  have h0 : (0 : Euclidean n) ∈ G.domain.chart n :=
    mem_ball_self (G.domain.coreRadius_pos.trans G.domain.coreRadius_lt_chartRadius)
  funext i
  rw [projectedStress_sourceDilation hσ G.contDiff 0
    (by simpa only [smul_zero] using G.fullNormalRank 0 h0), smul_zero]
  exact projectedStress_flatReference_zero G i

/-- The fourth-power normal weight of every normalized frozen slice keeps
the full density interval's factor `1/4`. The original inverse-flow label is
retained; no unit-density replacement is made
(`app:ch_background:eq:bg-full-complex-amplitude`, `bg-Nsigma`). -/
theorem normalizedNormal_origin_density_weight
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ) (σ : ℝ) (z : CarrierParameter)
    (hden : 1 + v (Y (0, (0, parameter z))) ∈ Icc (1 / 2 : ℝ) (3 / 2)) :
    (1 / 4 : ℝ) * ‖normalizedNormal T Q F row col Φ Y (fun _ ↦ 1) 0 0 z‖ ^ 4 ≤
      ‖normalizedNormal T Q F row col Φ Y (fun q ↦ Real.sqrt (1 + v q)) σ 0 z‖ ^ 4 := by
  rw [normalizedNormal_origin T Q F row col Φ Y (fun q ↦ Real.sqrt (1 + v q)) σ z]
  simp only [normalizedNormal_zero]
  rw [frozenSeedNormal_initial_factor T Q F row col Φ Y
    (fun q ↦ Real.sqrt (1 + v q)) z, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  have hpos : 0 ≤ 1 + v (Y (0, (0, parameter z))) := by linarith [hden.1]
  have hsq := Real.sq_sqrt hpos
  have hbound : (1 / 4 : ℝ) ≤ Real.sqrt (1 + v (Y (0, (0, parameter z)))) ^ 4 := by
    rw [show Real.sqrt (1 + v (Y (0, (0, parameter z)))) ^ 4 =
      (Real.sqrt (1 + v (Y (0, (0, parameter z)))) ^ 2) ^ 2 by ring, hsq]
    nlinarith [hden.1, sq_nonneg (v (Y (0, (0, parameter z))) + 1 / 2)]
  exact mul_le_mul_of_nonneg_right hbound (by positivity)

end JanetCartan.ContinuumNormal.NormalizedFrozenGap
