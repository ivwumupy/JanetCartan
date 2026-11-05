module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.ReducedSource.Retained
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.ReducedSource.ParameterLocalization

/-!
# Globally smooth data for the original retained response

Apply the actual mixed reduced-source producer on its original full parameter
domain, then one fixed parameter cutoff. The representative is globally smooth,
has the original physical support and agrees with the entire original source
family near the retained compact parameter set. Its mixed L² profiles are
unchanged (`app:ch_response:eq:direct-envelope-profile`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.ResponseTransfer.ReducedSource
open RawPrimary NullTransport ActualCarriers FrozenMenu CurrentFullPhase
open LeadingWave.FullModulation ProjectedStressFrame ResponsePrimarySources
open ResponseSourceExtension Sampling.BackgroundModulation

/-- Apply parameter localization to the SAME actual retained reduced source.
One cutoff, open plateau and all constants precede the immersion, scalar,
frequency and histories. The sharp mixed L² profiles keep the original
reserve sixteen (`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_localized_retained_reducedSource_mixedL2_profiles
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
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
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
            ∀ c ∈ W, ∀ j, ∃ hm : MemLp (fun x : Euclidean n ↦ iteratedFDeriv ℝ j a (x,c)) 2 volume,
              ‖hm.toLp (fun x : Euclidean n ↦ iteratedFDeriv ℝ j a (x,c))‖ ≤ C j * τ^3 * L^j := by
  obtain ⟨θ,hθ,hcθ,hsθ,W,hW,hKW,hWV,hplateau⟩ :=
    exists_full_source_parameter_cutoff hV hKparam hKparamV
  obtain ⟨C,hC,hsource⟩ := exists_retained_reducedSource_mixedL2_profiles
    hn T center hρ hK hKU hball M hκmet hκnormal AF Ar Γ hAF hAr hΓ
    χ hchart χsrc η hχsrc hη hV hproduct
  refine ⟨θ,hθ,hcθ,hsθ,W,hW,hKW,hWV,hplateau,C,hC,?_⟩
  intro F Q row col Φ Y r Kr Ω hQ hΩ hballΩ hΩK hphase hF hi hrank hFM
    hmet hnormal hframe hα hn' ht hcorr RF Rr L hpF hpr hL hRF hRr τ hτ b a
  obtain ⟨hb,hbj⟩ := hsource F Q row col Φ Y r Kr Ω hQ hΩ hballΩ hΩK
    hphase hF hi hrank hFM hmet hnormal hframe hα hn' ht hcorr
    RF Rr L hpF hpr hL hRF hRr τ hτ
  refine ⟨contDiff_parameterLocalizedSource hV hθ hsθ hb,?_,?_,?_,?_⟩
  · intro w hw
    have hχw : χ.toFun w.1 = 0 := image_eq_zero_of_notMem_tsupport hw
    simp only [a,b,fullStrainEnvelope_eq,hχw,zero_smul,map_zero,smul_zero]
  · intro w hw
    have hχw : χsrc w.1 = 0 := image_eq_zero_of_notMem_tsupport hw
    simp only [a,b,hχw,zero_smul,smul_zero]
  · intro c hc
    exact parameterLocalizedSource_slice_eventuallyEq b (hplateau c hc)
  · intro c hc j
    dsimp only
    convert parameterLocalizedSource_mixedL2_bound b (hplateau c hc) j (C j * τ^3 * L^j)
      (hbj c (hWV hc) j) using 1

end JanetCartan.ResponseTransfer.ReducedSource
