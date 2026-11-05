module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Sobolev
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.RetainedStrain

/-!
# Actual cubic Sobolev envelopes on a retained working ball

Apply the cubic strain producer to the literal full strain and then the
no-loss Fourier conversion. The leading and correction inputs are precisely
the outputs retained by `RawPrimary.exists_finite_retained_raw_primary_family`;
in particular the correction budget is produced by
`RetainedCorrection.exists_retained_cell_correction_bounds`. No envelope or
strain estimate is assumed. The parent supplies its already selected cell,
flows and original scalar, without making a second selection.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ResponsePrimarySources
open RawPrimary NullTransport ActualCarriers FrozenMenu CurrentFullPhase
open LeadingWave.FullModulation ProjectedStressFrame
open ResponseSourceExtension ResponseTransfer.SourceNegative

/-- The actual retained full strain has a compact Sobolev envelope of size
`τ³`, including every prescribed carrier derivative on the SAME extension.
All constants precede the immersion, scalar, carrier, scale and frequency.
The input correction budget and transport equation are retained conclusions
of the actual raw-family producer, not assumptions on the desired source.
Sources: `app:ch_waves:eq:WKB-strain`,
`app:ch_response:eq:response-graded-source`, `app:ch_response:cor:current-atoms`. -/
theorem exists_retained_fullStrainEnvelope_constants
    {n : ℕ} (hn : 5 ≤ n) {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (M : ℝ) {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (AF Ar Γ : ℕ → ℝ) (hAF : ∀ m, 0 ≤ AF m) (hAr : ∀ m, 0 ≤ Ar m)
    (hΓ : ∀ m, 0 ≤ Γ m)
    {core chart : Set (Euclidean n)} (χ : OutputCutoff core chart) (hchart : IsOpen chart)
    {V : Set (Euclidean 3 × Euclidean (n - 1))} (hV : IsOpen V)
    (hproduct : chart ×ˢ V ⊆ closedBall a ρ) (rpar : ℕ) :
    ∃ C : ℕ → ℕ → ℝ, (∀ k p, 0 ≤ C k p) ∧
      ∀ (F : Euclidean n → Euclidean (embeddingDimension n))
        (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (Kr : Set (Euclidean (n - 1) × Euclidean 3))
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
        MapsTo Prod.fst (closedBall a ρ) K →
        Q.1 = projectedStress F → IsOpen Ω → closedBall a ρ ⊆ Ω →
        MapsTo Prod.fst Ω K →
        (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
        ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
        cNorm K 14 F ≤ M →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
        (∀ x ∈ K, ∀ v ∈ normalSpace F x,
          κnormal * ‖v‖ ≤ ‖normalPairing F (fun _ ↦ v) x‖) →
        (∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) <
          ambientStrainFrameThreshold hn) →
        ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω →
        (∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
        (∀ w ∈ Ω, conullvector T Q row w ⬝ᵥ reducedOperator F Q.1
          (fun x ↦ scalarAmplitude T Q F row col Φ Y r (x, w.2) •
            nullvector T Q col (x, w.2)) w.1 = 0) →
        (∀ m, cNorm (closedBall a ρ) m (fullCorrectionCovector T Q F row col Φ Y r) ≤
          Γ m * (1 + cNorm K (m + 14) F + cNorm Kr (m + 14) r)) →
        ∀ (RF Rr : ℕ) (L : ℝ),
          HasDerivativeProfile K F RF L AF → HasDerivativeProfile Kr r Rr L Ar →
          1 ≤ L → 14 + (rpar + 2) ≤ RF → 14 + (rpar + 2) ≤ Rr →
          ∀ τ : ℝ, 0 < τ →
          (∀ c ∈ V, ∃ hf : MemLp (fullStrainEnvelope T Q F row col Φ Y r χ τ c) 2 volume,
            SobolevEnvelopeBounds (fullStrainEnvelope T Q F row col Φ Y r χ τ c)
              hf (τ^3) L (C 0)) ∧
          ∀ k ≤ rpar, ∀ v : Fin k → (Euclidean 3 × Euclidean (n - 1)),
            (∀ i, ‖v i‖ ≤ 1) → ∀ c ∈ V,
            ∃ hf : MemLp (fun x ↦ iteratedFDeriv ℝ k
              (fun d ↦ fullStrainEnvelope T Q F row col Φ Y r χ τ d x) c v) 2 volume,
            SobolevEnvelopeBounds (fun x ↦ iteratedFDeriv ℝ k
              (fun d ↦ fullStrainEnvelope T Q F row col Φ Y r χ τ d x) c v)
                hf (τ^3) L (C k) := by
  obtain ⟨B, hB, hgrade⟩ := exists_fullPrimaryStrain_grade_on_retained_workingBall
    hn T a hρ hK hKU M hκmet hκnormal AF Ar Γ hAF hAr hΓ
  obtain ⟨C, hC, hsob⟩ := exists_fullStrainEnvelope_sobolev_constants
    χ hchart hV B (fun j k ↦ (hB j k).le) rpar
  refine ⟨C, hC, ?_⟩
  intro F Q row col Φ Y r Kr Ω hball hQ hΩ hballΩ hΩK hphase hF hi hrank
    hFM hmet hnormal hframe hα hnonzero htransport hcorr RF Rr L hpF hpr hL hRF hRr τ hτ
  have hsub : chart ×ˢ V ⊆ Ω := hproduct.trans hballΩ
  exact hsob T Q F row col Φ Y r τ (τ^3) L (by positivity) hL
    (fun w hw ↦ hKU (hΩK (hsub hw))) (fun w hw ↦ hphase w (hsub hw))
    hF hi hrank (hα.mono hsub) (fun w hw ↦ hnonzero w (hsub hw))
    (fun x hx c hc j k hk ↦ hgrade F Q row col Φ Y r Kr Ω hball hQ hΩ hballΩ
      hΩK hphase hF hi hrank hFM hmet hnormal hframe hα hnonzero htransport hcorr
      RF Rr rpar L hpF hpr hL hRF hRr j k hk (x, c) (hproduct ⟨hx, hc⟩) τ hτ)

end JanetCartan.ResponsePrimarySources
