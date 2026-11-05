module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.InitialScalar
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.PrimitiveNorms
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.AmplitudeDifference.PrimitiveDensity.Calculus

/-!
# The original density class in normalized carrier coefficients

The initial density is evaluated on the original initial ball at the divided
ODE footpoint. Only the principal normal is multiplied by its square root;
all three masks and the detector are retained. The finite coefficient order
is `μ+1`, with the original density budget `μ+14`.

Consumer: the supported reflected-amplitude estimate used by
`ContinuumCommutator.exists_normalized_row_elliptic_estimates`.
Sources: `app:ch_background:prop:bg-frame`,
`app:ch_background:eq:bg-Nsigma`, `app:ch_background:eq:bg-commutator`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumCommutator.NormalizedCarrierBaseline
open ContinuumRow CanonicalCarrier ContinuumNormalReduction.TransportSymbol
open ContinuumNormal.CarrierVariation
open AmplitudeDifference AmplitudeDifference.PrimitiveDensity
open FullPhaseCharts.InverseEstimates

private theorem controls_enlarge {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {D : PrimitiveNormChart E} {p : ℕ} {M B M' B' : ℝ} {f : E → F}
    (h : D.Controls p M B 1 f) (hM : M ≤ M') (hB : B ≤ B') :
    D.Controls p M' B' 1 f := by
  refine ⟨h.smooth, h.low.trans hM, ?_⟩
  simpa only [mul_one] using h.high.trans (by simpa only [mul_one] using hB)

/-- Inserting the original density costs no additional derivative of the
principal normal or of the ODE footpoint. Constants precede both fields and
the density. This discharges the density factor in the normalized primitive
baseline, without changing its original initial ball
(`app:ch_background:prop:bg-frame`, `app:ch_background:eq:bg-mixed-input`). -/
theorem exists_original_density_normal_controls {n N : ℕ}
    (D : CoefficientNormCharts n)
    (p₀ : Euclidean (n - 1) × Euclidean 3) {R : ℝ} (hR : 0 < R)
    {M B G : ℝ} (hM : 0 ≤ M) (hB : 1 ≤ B) (hG : 0 ≤ G) :
    ∃ M' > (0 : ℝ), ∃ B' ≥ (1 : ℝ),
      ∀ (a : Coefficients n N)
        (g : Euclidean n × CarrierParameter → Euclidean (n - 1) × Euclidean 3),
      D.Controls (2 * (n + 1) + 1) M B 1 a →
      ContDiffOn ℝ ∞ g D.field.region →
      MapsTo g D.field.region (ball p₀ (R / 4)) →
      MapsTo g D.field.carrier (closedBall p₀ (R / 8)) →
      cNorm D.field.carrier (2 * (n + 1) + 1) g ≤ G →
      ∀ v : Euclidean (n - 1) × Euclidean 3 → ℝ,
      ContDiffOn ℝ ∞ v (ball p₀ (R / 4)) →
      (∀ q ∈ ball p₀ (R / 4), 0 < 1 + v q) →
      (∀ q ∈ closedBall p₀ (R / 8), 1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) →
      cNorm (closedBall p₀ (R / 8)) (2 * (n + 1) + 14) v ≤ 1 →
      D.Controls (2 * (n + 1) + 1) M' B' 1
        {a with normal := fun p ↦ Real.sqrt (1 + v (g p)) • a.normal p} := by
  let p := 2 * (n + 1) + 1
  obtain ⟨C, hC, hscalar⟩ := exists_density_initial_scalar_bound n p
  let E := compositionMultiplicity p * C * (1 + G) ^ p
  have hE : 0 ≤ E := by dsimp [E, compositionMultiplicity]; positivity
  let L : ℝ →L[ℝ] Euclidean N →L[ℝ] Euclidean N := ContinuousLinearMap.lsmul ℝ ℝ
  let A := bilinearDifferenceConstant L p * E * B
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg (bilinearDifferenceConstant_nonneg L p) hE) (zero_le_one.trans hB)
  refine ⟨M + A + 1, by positivity, B + A + 1, by linarith, ?_⟩
  intro a g ha hg hgreg hgK hgG v hv hpos hinterval hvnorm
  have hvlow : cNorm (closedBall p₀ (R / 8)) p v ≤ 1 :=
    (cNorm_mono_order (by dsimp [p]; omega)).trans hvnorm
  obtain ⟨hf, _, _, hfC⟩ := hscalar p₀ hR zero_lt_one v hv hpos hinterval hvlow
  simp only [positiveDensityAmplitude, one_mul] at hf hfC
  let f := fun q ↦ Real.sqrt (1 + v q)
  have hfg : ContDiffOn ℝ ∞ (f ∘ g) D.field.region := hf.comp hg hgreg
  have hfgE : cNorm D.field.carrier p (f ∘ g) ≤ E :=
    cNorm_comp_le_from_bounds (isCompact_closedBall ..) (isCompact_closedBall ..) p
      (fun q hq ↦ hf.contDiffAt (isOpen_ball.mem_nhds
        ((closedBall_subset_ball (by linarith : R / 8 < R / 4)) hq)))
      (fun q hq ↦ hg.contDiffAt (D.field.isOpen_region.mem_nhds (D.field.ball_subset hq)))
      hgK hC.le hfC hgG
  have hnormalB : cNorm D.field.carrier p a.normal ≤ B := by
    have hh := ha.normal.high
    simp only [mul_one] at hh
    linarith
  have hnA : cNorm D.field.carrier p (fun q ↦ f (g q) • a.normal q) ≤ A := by
    have hh := cNorm_bilinear_le_on L (isCompact_closedBall ..)
      D.field.isOpen_region D.field.ball_subset hfg ha.normal.smooth p
    change cNorm D.field.carrier p (fun q ↦ f (g q) • a.normal q) ≤
      bilinearDifferenceConstant L p * cNorm D.field.carrier p (f ∘ g) *
        cNorm D.field.carrier p a.normal at hh
    exact hh.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hfgE (bilinearDifferenceConstant_nonneg L p))
      hnormalB (cNorm_nonneg ..)
      (mul_nonneg (bilinearDifferenceConstant_nonneg L p) hE))
  have hMM : M ≤ M + A + 1 := by linarith
  have hBB : B ≤ B + A + 1 := by linarith
  refine ⟨controls_enlarge ha.measurement hMM hBB,
    controls_enlarge ha.angular hMM hBB, controls_enlarge ha.high hMM hBB, ?_,
    controls_enlarge ha.reduced hMM hBB⟩
  refine ⟨hfg.smul ha.normal.smooth,
    ((cNorm_mono_order (by dsimp [p]; omega : 1 ≤ p)).trans hnA).trans (by linarith), ?_⟩
  change 1 + cNorm D.field.carrier p (fun q ↦ f (g q) • a.normal q) ≤
    (B + A + 1) * 1
  rw [mul_one]
  linarith only [hnA, hB]

end JanetCartan.ContinuumCommutator.NormalizedCarrierBaseline
