module

public import JanetCartan.Geometry.IsometricEmbedding.Response.RetainedCharacteristicEnvelopes.SourceFourier
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.ReducedSource.LocalizedRetained

/-!
# Ordered Fourier profiles of the actual localized reduced source

Apply the mixed-L² producer to the same retained strain, full projected stress,
physical masks and parameter plateau. Constants precede the varying immersion,
history and frequency. The source amplitude remains `τ³` and the derivative
reserve remains sixteen.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
open RawPrimary NullTransport ActualCarriers FrozenMenu CurrentFullPhase
open LeadingWave.FullModulation ProjectedStressFrame ResponsePrimarySources
open ResponseSourceExtension Sampling.BackgroundModulation Pseudodifferential

/-- The literal localized reduced source supplies every ordered full-parameter
Fourier word required by `FullSourceEnvelopes.fullSource_capped_solver_residual_envelopes`.
The selected parameter cutoff, original spatial support, exact source germ,
full stress contraction and cubic size are retained
(`app:ch_response:eq:response-graded-reduced`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_localized_retained_reducedSource_fourier_profiles
    {n : ℕ} (hn : 5 ≤ n) {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (center : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : MapsTo Prod.fst (closedBall center ρ) K)
    (M : ℝ) {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (AF Ar Γ : ℕ → ℝ) (hAF : ∀ m, 0 ≤ AF m) (hAr : ∀ m, 0 ≤ Ar m)
    (hΓ : ∀ m, 0 ≤ Γ m)
    {core chart : Set (Euclidean n)} (χ : OutputCutoff core chart) (hchart : IsOpen chart)
    (χsrc η : Euclidean n → ℝ) (hχsrc : ContDiff ℝ ∞ χsrc) (hη : ContDiff ℝ ∞ η)
    {V : Set (Euclidean 3 × Euclidean (n - 1))} (hV : IsOpen V)
    (hproduct : chart ×ˢ V ⊆ closedBall center ρ)
    {Kparam : Set (Euclidean 3 × Euclidean (n - 1))}
    (hKparam : IsCompact Kparam) (hKparamV : Kparam ⊆ V) :
    ∃ θ : (Euclidean 3 × Euclidean (n - 1)) → ℝ,
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ V ∧
      ∃ W : Set (Euclidean 3 × Euclidean (n - 1)),
        IsOpen W ∧ Kparam ⊆ W ∧ W ⊆ V ∧
        (∀ c ∈ W, θ =ᶠ[𝓝 c] (fun _ ↦ 1)) ∧
    ∃ C : ℕ → ℕ → ℝ, (∀ k s, 0 ≤ C k s) ∧
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
        Q.1 = projectedStress F → IsOpen Ω → closedBall center ρ ⊆ Ω →
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
        (∀ m, cNorm (closedBall center ρ) m (fullCorrectionCovector T Q F row col Φ Y r) ≤
          Γ m * (1 + cNorm K (m + 14) F + cNorm Kr (m + 14) r)) →
        ∀ (RF Rr : ℕ) (L : ℝ),
          HasDerivativeProfile K F RF L AF → HasDerivativeProfile Kr r Rr L Ar →
          1 ≤ L → 16 ≤ RF → 16 ≤ Rr → ∀ τ : ℝ, 0 < τ →
          let b := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
            χsrc w.1 • (η w.1 • ((1 / 2 : ℝ) • complexStressContraction (Q.1 w.1)
              (fullStrainEnvelope T Q F row col Φ Y r χ τ w.2 w.1)))
          let a := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦ θ w.2 • b w
          ContDiff ℝ ∞ a ∧
            (∀ w, w.1 ∉ tsupport χ.toFun → a w = 0) ∧
            (∀ w, w.1 ∉ tsupport χsrc → a w = 0) ∧
            (∀ c ∈ W, (fun q ↦ fun x ↦ a (x,q)) =ᶠ[𝓝 c]
              (fun q ↦ fun x ↦ b (x,q))) ∧
            ∀ c ∈ W, ∀ k (v : Fin k → (Euclidean 3 × Euclidean (n - 1))),
              (∀ j, ‖v j‖ ≤ 1) → ∀ s : ℕ,
              let f := fun x ↦ iteratedFDeriv ℝ k (fun q ↦ a (x,q)) c v
              ∃ hm : MemLp f 2 volume,
                MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
                  vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤ C k s * τ^3 * L^(s+k) := by
  obtain ⟨θ,hθ,hcθ,hsθ,W,hW,hKW,hWV,hplateau,D,hD,hsource⟩ :=
    ReducedSource.exists_localized_retained_reducedSource_mixedL2_profiles
      hn T center hρ hK hKU hball M hκmet hκnormal AF Ar Γ hAF hAr hΓ
      χ hchart χsrc η hχsrc hη hV hproduct hKparam hKparamV
  let C : ℕ → ℕ → ℝ := fun k s ↦ (n : ℝ) *
    LowEnvelope.compactCoordinateSobolevConstant n s *
      ∑ j ∈ Finset.range (s + 1), D (j + k)
  have hC : ∀ k s, 0 ≤ C k s := fun k s ↦ mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (LowEnvelope.compactCoordinateSobolevConstant_pos n s).le)
    (Finset.sum_nonneg (fun j _ ↦ hD (j + k)))
  refine ⟨θ,hθ,hcθ,hsθ,W,hW,hKW,hWV,hplateau,C,hC,?_⟩
  intro F Q row col Φ Y r Kr Ω hQ hΩ hballΩ hΩK hphase hF hi hrank hFM
    hmet hnormal hframe hα hn' ht hcorr RF Rr L hpF hpr hL hRF hRr τ hτ b a
  obtain ⟨ha,hza,hzsrc,he,hmixed⟩ := hsource F Q row col Φ Y r Kr Ω hQ hΩ hballΩ hΩK
    hphase hF hi hrank hFM hmet hnormal hframe hα hn' ht hcorr
    RF Rr L hpF hpr hL hRF hRr τ hτ
  refine ⟨ha,hza,hzsrc,he,?_⟩
  intro c hc k v hv s
  exact fullSource_parameterWord_fourier_of_mixedL2 χ.compact hW a ha hza D hD
    (pow_nonneg hτ.le 3) hL hc (hmixed c hc) k v hv s

end JanetCartan.ResponseTransfer.RetainedCharacteristicEnvelopes
