module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.ProjectedBounds

/-!
# Closing the correction's scalar budgets

The consumer is the actual finite corrected family for
`app:ch_waves:eq:WKB-grading`. The scalar reserve-thirteen estimates produced
on that family's fixed ball close the correction estimate with reserve
fourteen. The selected-minor gap is retained by `Correction.FamilyInputs`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RawPrimary
open NullTransport ProjectedStressFrame GeometricProfile
open LeadingWave.FullModulation LeadingWave.FullModulation.UniformCoefficients
open ActualCarriers FrozenMenu CurrentFullPhase CorrectionBounds

/-- Close the scalar input in the one-high correction estimate, using the
actual transport's reserve thirteen. Constants precede the immersion, initial
scalar, flow, and frequency. The hypotheses on scalar jets and the selected
minor are produced together by `exists_finite_actual_leading_family_with_correction_inputs`
(`app:ch_waves:eq:primary-algebraic-correction`, `app:ch_waves:eq:WKB-grading`). -/
theorem exists_fullCorrectionCovector_transport_bounds
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hballK : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {σ : ℝ} (hσ : 0 < σ)
    (hx : MapsTo Prod.fst (closedBall a σ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hdom : closedBall a σ ⊆ domain T) (row col : Fin n)
    (M Lα : ℝ) (B : ℕ → ℝ) (hB : ∀ m, 0 < B m)
    {κmet κnormal δ : ℝ}
    (hκmet : 0 < κmet) (hκnormal : 0 < κnormal) (hδ : 0 < δ) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 14 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ v ∈ normalSpace F x,
          κnormal * ‖v‖ ≤ ‖normalPairing F (fun _ ↦ v) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
            Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
          (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
          (Kr : Set (Euclidean (n - 1) × Euclidean 3))
          (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
          IsOpen Ω → closedBall a σ ⊆ Ω → MapsTo Prod.fst Ω U → Ω ⊆ domain T →
          ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω →
          cNorm (closedBall a σ) 1 (scalarAmplitude T Q F row col Φ Y r) ≤ Lα →
          (∀ m, cNorm (closedBall a σ) m (scalarAmplitude T Q F row col Φ Y r) ≤
            B m * (1 + cNorm K (m + 13) F + cNorm Kr (m + 13) r)) →
          (∀ w ∈ closedBall a σ,
            δ ≤ |(reducedSymbol (Q.1 w.1) (phaseGradient T Q w.1 w.2.2)).adjugate row col|) →
          ∀ m, cNorm (closedBall a σ) m (fullCorrectionCovector T Q F row col Φ Y r) ≤
            C m * (1 + cNorm K (m + 14) F + cNorm Kr (m + 14) r) := by
  obtain ⟨A, hA, hinput⟩ := exists_projected_fullInput_bound (N := N)
    T a σ hx hdom hK hKU hballK M hκmet hκnormal
  obtain ⟨D, hD, hcorrection⟩ := exists_fullCorrectionCovector_bounds (N := N)
    T a hσ hK (fun _ hw ↦ hballK (hx hw)) hKU row col (2 * M)
      (2 * (A 1 * (1 + M) + Lα)) hκmet hδ
  let C := fun m ↦ D m * (1 + (m + 2 : ℝ) * (A (m + 1) + B (m + 1)))
  have hC (m) : 0 < C m := by
    dsimp [C]
    have := hD m
    have := hA (m + 1)
    have := hB (m + 1)
    positivity
  refine ⟨C, hC, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow
  dsimp only
  intro Φ Y r Kr Ω hΩ hball hxU hphase hscalar hscalarLow hscalarHigh hminor
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  have hFM4 : cNorm K 4 F ≤ M := (cNorm_mono_order (by omega)).trans hFM
  have hinputHigh := hinput F hF hi hrank hFM4 hmet hnormal hlow
  have hfull : ContDiffOn ℝ ∞ (fullInput T Q) Ω :=
    (smooth_fullInput T Q).mono (fun w hw ↦ ⟨hphase hw, hxU hw⟩)
  have hpack (m) : cNorm (closedBall a σ) m (fullPrimitiveValues T Q F row col Φ Y r) ≤
      (m + 1 : ℝ) * (cNorm (closedBall a σ) m (fullInput T Q) +
        cNorm (closedBall a σ) m (scalarAmplitude T Q F row col Φ Y r)) :=
    NullTransport.CoefficientBounds.cNorm_pair_le a m hΩ hball hfull hscalar
  have hinputLow : cNorm (closedBall a σ) 1 (fullInput T Q) ≤ A 1 * (1 + M) :=
    (hinputHigh 1).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1)
        ((cNorm_mono_order (show 1 + 4 ≤ 14 by omega)).trans hFM)) (hA 1).le)
  have hpackLow : cNorm (closedBall a σ) 1 (fullPrimitiveValues T Q F row col Φ Y r) ≤
      2 * (A 1 * (1 + M) + Lα) := by
    apply (hpack 1).trans
    norm_num only [Nat.cast_one]
    exact mul_le_mul_of_nonneg_left (add_le_add hinputLow hscalarLow) (by norm_num)
  have hjet (x) (hxK : x ∈ K) : ‖stressJet F x‖ ≤ 2 * M :=
    (norm_stressJet_le_cNorm_four hK (fun y hy ↦ hF.contDiffAt (hU.mem_nhds (hKU hy))) hxK).trans
      (mul_le_mul_of_nonneg_left hFM4 (by norm_num))
  have hb := (hcorrection Q F Φ Y r Ω hΩ hball hxU hphase hF hscalar hpackLow hjet hmet hminor).1
  intro m
  let S := 1 + cNorm K (m + 14) F + cNorm Kr (m + 14) r
  have hForder : 1 + cNorm K (m + 5) F ≤ S := by
    dsimp [S]
    have := cNorm_mono_order (f := F) (s := K) (show m + 5 ≤ m + 14 by omega)
    linarith [cNorm_nonneg Kr (m + 14) r]
  have hinputm : cNorm (closedBall a σ) (m + 1) (fullInput T Q) ≤ A (m + 1) * S :=
    (hinputHigh (m + 1)).trans (mul_le_mul_of_nonneg_left hForder (hA _).le)
  have hscalarm : cNorm (closedBall a σ) (m + 1) (scalarAmplitude T Q F row col Φ Y r) ≤
      B (m + 1) * S := hscalarHigh (m + 1)
  have hpackm : cNorm (closedBall a σ) (m + 1) (fullPrimitiveValues T Q F row col Φ Y r) ≤
      (m + 2 : ℝ) * (A (m + 1) + B (m + 1)) * S := by
    apply (hpack (m + 1)).trans
    convert mul_le_mul_of_nonneg_left (add_le_add hinputm hscalarm)
      (by positivity : (0 : ℝ) ≤ m + 2) using 1 <;> push_cast <;> ring
  have hForder' : 1 + cNorm K (m + 2) F ≤ S := by
    dsimp [S]
    have := cNorm_mono_order (f := F) (s := K) (show m + 2 ≤ m + 14 by omega)
    linarith [cNorm_nonneg Kr (m + 14) r]
  exact (hb m).trans ((mul_le_mul_of_nonneg_left (add_le_add hForder' hpackm) (hD m).le).trans_eq
    (by dsimp [C, S]; ring))

end JanetCartan.RawPrimary
