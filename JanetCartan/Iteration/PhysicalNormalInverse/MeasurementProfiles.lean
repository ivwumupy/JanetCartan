module

public import JanetCartan.Iteration.PhysicalSmoothing.Measurement
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.PhysicalMeasurement

/-!
# Literal physical measurement profiles for the corrected normal comparison

The measurement in `FullComparison` is the original common physical cutoff
contracting the projected stress of the SAME Schwartz history.  Apply the
physical-history preparation producer and its exact compact representative;
never substitute a periodic history or a carrier-specific measurement radius.
The reserve is two, and every constant precedes the history and density.
The other corrected-amplitude and full-response profiles remain separate
producer applications.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalNormalInverse
open CurrentMean ContinuumRow CanonicalCarrier ActualCarriers FrozenMenu
  CurrentFullPhase ProjectedStressFrame Sampling

/-- The SAME compact measurement supplies the actual `Cmeasure` input of
`app:ch_waves:eq:sampling-operator-bounds` and the middle corrected-normal term
of `main:eq:mean-error-decomposition`.  The common measurement radius is
independent of every carrier weight.  The arbitrary flow, density and correction
weight merely identify the already-produced preparation measurement; they do
not change the literal output `canonicalSamplingMeasurement (projectedStress F)`.
No measurement profile is assumed. -/
theorem exists_physical_history_sampling_measurement_profiles
    {n : ℕ} (G : FlatReference n) {μ R : ℝ}
    (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2)
    (h4μR : 4 * μ < R) (hR : R < G.domain.chartRadius)
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar rpar kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : 2 + rpar ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ Cmeasure : ℕ → ℝ, (∀ s, 0 < Cmeasure s) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (stage : ℕ)
        (u : Fin stage → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin stage → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      ∀ {P : Patch n} (T : PatchQuantitativeFamily P (ball 0 R) isOpen_ball)
        (Q : {Q : Euclidean n → Fin n → MetricTensor n //
          ContDiffOn ℝ ∞ Q (ball 0 R) ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold}),
      Q.1 = projectedStress F → ∀ (_row _col : Fin n)
        (_φ _y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (_initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (_angular : CarrierParameter → Euclidean (n - 1) → ℝ) (_high : ℝ → ℝ)
        (_w : CarrierVariable n → ℝ),
      let C := canonicalSamplingMeasurement (projectedStress F) hμ
      ContDiff ℝ ∞ C ∧
        (∀ K : Set (Euclidean n), HasDerivativeProfile K C rpar
          (currentCoefficientScale R₀ stage) Cmeasure) ∧
        ∀ K : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1))),
          HasDerivativeProfile K (fun q ↦ C q.1) rpar
            (currentCoefficientScale R₀ stage) Cmeasure := by
  obtain ⟨S, hS, Cmeasure, hCmeasure, hprofiles⟩ :=
    PhysicalSmoothing.exists_history_preparation_measurement_profiles
      G hμ hμcell h4μR hR hBband hStar hreserve horder
  refine ⟨S, hS, Cmeasure, hCmeasure, ?_⟩
  intro R₀ hR₀ stage u ell hu F P T Q hQ row col φ y initial angular high w C
  obtain ⟨_hperiodic, hprofile⟩ :=
    hprofiles R₀ hR₀ stage u ell hu T Q hQ row col φ y initial angular high w
  dsimp only [C]
  rw [← hQ]
  refine ⟨contDiff_canonicalSamplingMeasurement T Q F row col φ y initial
    hμ hμcell angular high (closedBall_subset_ball h4μR), ?_, ?_⟩
  · intro K s
    apply (cNorm_canonicalSamplingMeasurement_le T Q F row col φ y initial
      hμ hμcell angular high (closedBall_subset_ball h4μR) K s).trans
    simpa only [F, preparationMeasurement_correctedCarrierData] using hprofile s
  · intro K
    apply canonicalSamplingMeasurement_hasDerivativeProfile T Q F row col φ y initial
      hμ hμcell angular high (closedBall_subset_ball h4μR) K
    simpa only [HasDerivativeProfile, F, preparationMeasurement_correctedCarrierData] using hprofile

end JanetCartan.PhysicalNormalInverse
