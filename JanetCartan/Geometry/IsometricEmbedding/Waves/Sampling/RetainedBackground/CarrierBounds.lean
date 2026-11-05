module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.CarrierBounds.Pullback
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.CarrierBounds.Matching

/-!
# Actual retained background carrier budgets

The supported Hermitian polynomial is restricted to the original sampling
carrier graph. All joint inverse-frequency/carrier/physical jets, with and
without the original sampling weight, follow from the retained `AF`, `Ar`,
`E`, and `Γ` outputs. Constants precede fields, inverse frequencies, radial
labels and the scale `L`; the scalar norm domain `I` is unchanged.

The actual scalar smoothness and nonvanishing leading outputs supply both
covector regularity inputs. The SAME tensor agrees with the original localized
background on the prescribed measurement support; its zero endpoint is the
transported rank-one tensor in `weighted_retainedBackgroundCarrier_zero`.

Consumer: the deterministic quadrature, rough bound, and transport comparison
assembly in `RetainedBackground` (`app:ch_waves:eq:background-quadrature`,
`app:ch_waves:eq:background-quadrature-rough`). These final estimates remain
with that consumer; no change of sampling or physical measure is made here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.RetainedBackground
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer MeasuredAmplitude

/-- Construct the actual smooth carrier background and its weighted joint
budgets from the original profiles and retained leading/correction outputs.
`RawPrimary.exists_finite_retained_graded_raw_family_with_primitives` supplies
the scalar smoothness, nonzero minors and `E`/`Γ` estimates on the SAME `Ω`,
`Φ`, `Y`, and original scalar norm domain `I`. Apply
`exists_retained_supportedBackground_budgets` to these outputs; no carrier
derivative estimate or prepared-current datum is assumed. Constants and
common compact physical support precede all varying fields and frequencies
(`app:ch_waves:eq:background-quadrature`,
`app:ch_waves:eq:background-quadrature-rough`). -/
theorem exists_retainedBackgroundCarrier_budgets
    {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    {K : Set (Euclidean (m + 1))} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ K)
    (hspace : closedBall a.1 (2 * ρ) ⊆ K)
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (I : Set (Euclidean ((m + 1) - 1) × Euclidean 3))
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF Ar E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j)
    (χ : Euclidean (m + 1) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hχsupport : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    (hψsupport : ∀ z, ψ z ≠ 0 → (WithLp.toLp 2 z,
      T.reference.spatialPatch (WithLp.toLp 2 z)) ∈ closedBall a.2 (ρ / 4)) :
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (F : Euclidean (m + 1) → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin (m + 1))
        (Φ Y : ℝ × (Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1))) →
          Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
        (r : Euclidean ((m + 1) - 1) × Euclidean 3 → ℝ)
        (Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))),
      IsOpen Ω → closedBall a (2 * ρ) ⊆ Ω →
      ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω →
      (∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) →
      (∀ j,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)) ↦
          phaseGradient T Q w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      (∀ j, cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
        Γ j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      ∀ (RF Rr rpar : ℕ) (L : ℝ), 1 ≤ L →
      14 + (rpar + 2) ≤ RF → 14 + (rpar + 2) ≤ Rr →
      HasDerivativeProfile K F RF L AF → HasDerivativeProfile I r Rr L Ar →
      let H := retainedBackgroundCarrier T a hρ Q F row col Φ Y r χ
      let f := fun q : ℝ × (SeparatedSampling.Point × Euclidean (m + 1)) ↦
        H q.1 q.2.1 q.2.2
      ContDiff ℝ ∞ f ∧
      ContDiff ℝ ∞ (fun q ↦ ψ q.2.1 • f q) ∧
      (∀ τ z, tsupport (H τ z) ⊆ closedBall a.1 (3 * ρ / 4) ∧
        tsupport (fun x ↦ ψ z • H τ z x) ⊆ closedBall a.1 (3 * ρ / 4)) ∧
      (∀ τ ∈ Icc (-1 : ℝ) 1, ∀ z x j,
        ‖iteratedFDeriv ℝ j f (τ, (z, x))‖ ≤ A j * L ^ (j - rpar) ∧
        ‖iteratedFDeriv ℝ j (fun q ↦ ψ q.2.1 • f q) (τ, (z, x))‖ ≤
          A j * L ^ (j - rpar)) ∧
      (∀ τ, τ ≠ 0 → ∀ z x, ψ z • H τ z x =
        ψ z • localizedBackground T Q F row col Φ Y r χ τ (WithLp.toLp 2 z) x) := by
  obtain ⟨A, hA, hraw⟩ := exists_retained_supportedBackground_budgets
    (N := N) T a hρ hK hKU hball hspace hphase I hγ hκ AF Ar E Γ hAF hAr hE hΓ χ hχ
  obtain ⟨B, hB, hpull⟩ := exists_retainedCarrierPullback_budgets T hP a hρ hcarrier
    χ ψ hψ A (fun j ↦ (hA j).le)
  refine ⟨B, hB, ?_⟩
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hα hnonzero
    hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr H f
  let O := Ω ∩ ((Prod.fst ⁻¹' U) ∩ domain T)
  have hO : IsOpen O := hΩ.inter ((hU.preimage continuous_fst).inter (isOpen_domain T))
  have hOspace : ∀ w ∈ O, w.1 ∈ U := fun _ hw ↦ hw.2.1
  have hOphase : ∀ w ∈ O, (w.1, w.2.2) ∈ phaseDomain T := fun _ hw ↦ hw.2.2
  have hOflow : closedBall a (2 * ρ) ⊆ O := by
    intro w hw
    refine ⟨hflow hw, ?_, hphase hw⟩
    rw [← closedBall_prod_same] at hw
    exact hKU (hspace hw.1)
  have hOα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) O :=
    hα.mono (fun _ hw ↦ hw.1)
  have hOnonzero : ∀ w ∈ O, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0 :=
    fun w hw ↦ hnonzero w hw.1
  have hb₀ := contDiffOn_fullLeadingCovector T Q F row col Φ Y r hOspace hOphase hOα
  have hb₁ := contDiffOn_fullCorrectionCovector_of_leading_outputs T Q F row col Φ Y r
    hO hOspace hOphase hF hi hOα hOnonzero
  obtain ⟨hs, hj⟩ := hraw F hF hi hrank hmetric hnormal hlow row col Φ Y r
    O hO hOflow hb₀ hb₁ hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨hf, hwf, hbounds⟩ := hpull _ hs L rpar hL hj
  refine ⟨hf, hwf, ?_, hbounds, ?_⟩
  · intro τ z
    exact ⟨retainedCarrierPullback_tsupport_subset T a hρ χ _ τ z,
      weighted_retainedCarrierPullback_tsupport_subset T a hρ χ ψ _ τ z⟩
  · intro τ hτ z x
    exact weighted_retainedBackgroundCarrier_eq_localized T a hρ Q F row col Φ Y r
      hO hOspace hOphase ((closedBall_subset_closedBall (by linarith)).trans hOflow)
      hF hi hrank hOα hOnonzero χ ψ hχsupport hψsupport hτ z x

end JanetCartan.Sampling.RetainedBackground
