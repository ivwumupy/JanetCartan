module

public import JanetCartan.Geometry.IsometricEmbedding.Response.PrimarySources.Envelopes.Retained
public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.Channels

/-!
# Fixed-reserve profiles of the literal full strain

The source profile for a word of length `k` in
`app:ch_response:thm:response-literal-transfer` allows a factor `L^k`.
The retained raw producer already bounds the joint tensor of every total
order with the reserve for zero free parameter derivatives. Use this tensor
at order `j+k` before taking the Fourier norm in the physical variable.
This keeps the reserve fixed even when the source word is arbitrarily long.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.ResponseTransfer.FullSourceEnvelopes
open RawPrimary NullTransport ActualCarriers FrozenMenu CurrentFullPhase
open LeadingWave.FullModulation ProjectedStressFrame
open ResponseSourceExtension SourceNegative ResponsePrimarySources Pseudodifferential

/-- On the original row, cutoff and covector family, all parameter words of
the full strain have spatial Fourier profile `C k p * τ³ * L^(p+k)` at the
single reserve `16 ≤ RF,Rr`. Apply the joint raw grade at `rpar=0` and
choose the Fourier constants before the varying frame, flow, history and
frequency. The last projection gives both vector Fourier membership and the
exact scale power for the original channel word. This supplies the source for
`app:ch_response:eq:response-graded-source` and the fixed response factors
in `app:ch_response:eq:fixed-factor-transfer`. -/
theorem exists_fullSource_strainWord_profiles
    {n : ℕ} (hn : 5 ≤ n) {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (M : ℝ) {κmet κnormal : ℝ} (hκmet : 0 < κmet) (hκnormal : 0 < κnormal)
    (AF Ar Γ : ℕ → ℝ) (hAF : ∀ m, 0 ≤ AF m) (hAr : ∀ m, 0 ≤ Ar m)
    (hΓ : ∀ m, 0 ≤ Γ m)
    {core chart : Set (Euclidean n)} (χ : OutputCutoff core chart) (hchart : IsOpen chart)
    {V : Set (Euclidean 3 × Euclidean (n - 1))} (hV : IsOpen V)
    (hproduct : chart ×ˢ V ⊆ closedBall a ρ) :
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
          1 ≤ L → 16 ≤ RF → 16 ≤ Rr →
          ∀ τ : ℝ, 0 < τ → ∀ k (v : Fin k → (Euclidean 3 × Euclidean (n - 1))),
          (∀ j, ‖v j‖ ≤ 1) → ∀ c ∈ V,
          let f := fun x ↦ iteratedFDeriv ℝ k
            (fun b ↦ fullStrainEnvelope T Q F row col Φ Y r χ τ b x) c v
          ∃ hf : MemLp f 2 volume, SobolevEnvelopeBounds f hf (τ ^ 3 * L ^ k) L (C k) ∧
            ∀ (m : ℕ) (R : Matrix (Fin n) (Fin n) ℂ →L[ℂ] EuclideanSpace ℂ (Fin m)),
              let g := fun x ↦ iteratedFDeriv ℝ k
                (fun b ↦ R (fullStrainEnvelope T Q F row col Φ Y r χ τ b x)) c v
              ∃ hg : MemLp g 2 volume, ∀ p : ℕ,
                MemVectorFourierSobolev (p : ℝ) (hg.toLp g) ∧
                  vectorFourierSobolevNorm (p : ℝ) (hg.toLp g) ≤
                    (‖R‖ * C k p) * τ ^ 3 * L ^ (p + k) := by
  obtain ⟨B, hB, hraw⟩ := exists_fullPrimaryStrain_grade_on_retained_workingBall
    hn T a hρ hK hKU M hκmet hκnormal AF Ar Γ hAF hAr hΓ
  choose D hD hs using fun k : ℕ ↦ exists_fullStrainEnvelope_sobolev_constants
    χ hchart hV (fun j l ↦ B (j + l) 0) (fun j l ↦ (hB (j + l) 0).le) k
  refine ⟨fun k ↦ D k k, fun k p ↦ hD k k p, ?_⟩
  intro F Q row col Φ Y r Kr Ω hball hQ hΩ hballΩ hΩK hphase hF hi hrank
    hFM hmet hnormal hframe hα hn' ht hcorr RF Rr L hpF hpr hL hRF hRr τ hτ k v hv c hc f
  have raw := hraw F Q row col Φ Y r Kr Ω hball hQ hΩ hballΩ hΩK hphase hF hi hrank
    hFM hmet hnormal hframe hα hn' ht hcorr RF Rr 0 L hpF hpr hL hRF hRr
  have hsub := hproduct.trans hballΩ
  have htensor (x) (hx : x ∈ chart) b (hb : b ∈ V) j l (hl : l ≤ k) :
      ‖iteratedFDeriv ℝ (j+l) (fullPrimaryStrainAmplitude T Q F row col Φ Y r τ) (x,b)‖ ≤
        B (j+l) 0 * (τ^3 * L^k) * L^j := by
    have h := raw (j + l) 0 le_rfl (x, b) (hproduct ⟨hx, hb⟩) τ hτ
    rw [Nat.add_zero, pow_add] at h
    calc
      _ ≤ B (j + l) 0 * τ^3 * (L^j * L^l) := h
      _ ≤ B (j + l) 0 * τ^3 * (L^j * L^k) := by
        have hL₀ := zero_le_one.trans hL
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hl) (pow_nonneg hL₀ _))
          (mul_nonneg (hB _ _).le (pow_nonneg hτ.le _))
      _ = _ := by ring
  obtain ⟨hf, hb⟩ := (hs k T Q F row col Φ Y r τ (τ^3 * L^k) L
    (mul_nonneg (pow_nonneg hτ.le _) (pow_nonneg (zero_le_one.trans hL) _)) hL
    (fun w hw ↦ hKU (hΩK (hsub hw))) (fun w hw ↦ hphase w (hsub hw))
    hF hi hrank (hα.mono hsub) (fun w hw ↦ hn' w (hsub hw)) htensor).2 k le_rfl v hv c hc
  have hloc := contDiffOn_fullPrimaryStrainAmplitude_of_leading_outputs T Q F row col Φ Y r τ
    hΩ (fun w hw ↦ hKU (hΩK hw)) hphase hF hi hrank hα hn'
  have hparam (x : Euclidean n) :
      ContDiffAt ℝ ∞ (fun b ↦ fullStrainEnvelope T Q F row col Φ Y r χ τ b x) c := by
    simp_rw [fullStrainEnvelope_eq]
    by_cases hx : χ.toFun x = 0
    · simpa only [hx, zero_smul] using (contDiffAt_const (c := (0 : Matrix (Fin n) (Fin n) ℂ))
        (x := c) (n := ∞) (𝕜 := ℝ))
    · have hxc := χ.support_chart (subset_tsupport _ hx)
      exact (contDiffAt_const (c := χ.toFun x) (x := c) (𝕜 := ℝ)).smul
        ((hloc.contDiffAt (hΩ.mem_nhds (hsub ⟨hxc, hc⟩))).comp c
        (contDiffAt_const.prodMk contDiffAt_id))
  have hcompact : HasCompactSupport f := by
    dsimp only [f, fullStrainEnvelope]
    rw [primary_zeroExtend_carrier_derivative_eq χ hchart hV (hloc.mono hsub) k v hc]
    exact χ.hasCompactSupport_zeroExtend _
  exact ⟨hf, hb, fun _ R ↦ fullSource_channelWord_fourier_profile R
    (fullStrainEnvelope T Q F row col Φ Y r χ τ) c hparam k v _ _ _ hf hcompact hb⟩

end JanetCartan.ResponseTransfer.FullSourceEnvelopes
