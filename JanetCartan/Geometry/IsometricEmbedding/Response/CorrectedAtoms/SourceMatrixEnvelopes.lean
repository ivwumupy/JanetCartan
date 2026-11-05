module

public import JanetCartan.Geometry.IsometricEmbedding.Response.FullSourceEnvelopes.StrainProfiles

/-!
# Literal matrix source inputs for corrected-atom reconstruction

Apply the retained full-strain producer to the exact scalar Fourier channels
used by the fixed solver reconstruction. Flattening and reindexing preserve
the Frobenius Fourier norm, all parameter words and reserve sixteen.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CorrectedAtoms
open ResponseTransfer ResponseTransfer.FullSourceEnvelopes
open RawPrimary NullTransport ActualCarriers FrozenMenu CurrentFullPhase
open LeadingWave.FullModulation ProjectedStressFrame
open ResponseSourceExtension SourceNegative ResponsePrimarySources Pseudodifferential

/-- Construct the exact source matrix in the Fourier space used by
`CompatibleResponse.exists_admissible_history_fullPrimary_response_envelopes`.
The retained full-strain producer supplies every bound; the coordinate isometry
costs no derivative or dimension factor. Constants precede histories, scalars,
independent covectors and frequency, with reserve sixteen for all parameter
words (`app:ch_response:eq:response-graded-source`,
`app:ch_response:cor:current-atoms`). -/
theorem exists_retained_fullStrain_matrixFourier_profiles
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
          ∃ ua : PiLp 2 (fun _ : Fin n × Fin n ↦ Lp ℂ 2 (volume : Measure (Euclidean n))),
            (∀ ij, ua ij =ᵐ[volume] fun x ↦ f x ij.1 ij.2) ∧
            ∀ p : ℕ, MemMatrixFourierSobolev (p : ℝ) ua ∧
              matrixFourierSobolevNorm (p : ℝ) ua ≤ C k p * τ ^ 3 * L ^ (p + k) := by
  obtain ⟨C, hC, hsource⟩ := exists_fullSource_strainWord_profiles
    hn T a hρ hK hKU M hκmet hκnormal AF Ar Γ hAF hAr hΓ χ hchart hV hproduct
  refine ⟨C, hC, ?_⟩
  intro F Q row col Φ Y r Kr Ω hball hQ hΩ hballΩ hΩK hphase hF hi hrank
    hFM hmet hnormal hframe hα hn' ht hcorr RF Rr L hpF hpr hL hRF hRr τ hτ k v hv c hc f
  obtain ⟨_hf, _hbound, hchannels⟩ := hsource F Q row col Φ Y r Kr Ω
    hball hQ hΩ hballΩ hΩK hphase hF hi hrank hFM hmet hnormal hframe hα hn' ht hcorr
    RF Rr L hpF hpr hL hRF hRr τ hτ k v hv c hc
  let π := (SingleChannel.matrixChannelEquiv n n).toContinuousLinearEquiv.toContinuousLinearMap
  let g := fun x ↦ iteratedFDeriv ℝ k
    (fun b ↦ π (fullStrainEnvelope T Q F row col Φ Y r χ τ b x)) c v
  obtain ⟨hg, hgb⟩ := hchannels (n*n) π
  let coords := finiteL2CoordinateIsometry volume (hg.toLp g)
  let ua : PiLp 2 (fun _ : Fin n × Fin n ↦ Lp ℂ 2 (volume : Measure (Euclidean n))) :=
    WithLp.toLp 2 (fun ij ↦ coords (finProdFinEquiv ij))
  have hsub : chart ×ˢ V ⊆ Ω := hproduct.trans hballΩ
  have hloc := contDiffOn_fullPrimaryStrainAmplitude_of_leading_outputs T Q F row col Φ Y r τ
    hΩ (fun w hw ↦ hKU (hΩK hw)) hphase hF hi hrank hα hn'
  have hparam (x : Euclidean n) :
      ContDiffAt ℝ ∞ (fun b ↦ fullStrainEnvelope T Q F row col Φ Y r χ τ b x) c := by
    simp_rw [fullStrainEnvelope_eq]
    by_cases hx : χ.toFun x = 0
    · simpa only [hx, zero_smul] using
        (contDiffAt_const (c := (0 : Matrix (Fin n) (Fin n) ℂ)) (x := c) (n := ∞) (𝕜 := ℝ))
    · have hxc := χ.support_chart (subset_tsupport _ hx)
      exact (contDiffAt_const (c := χ.toFun x) (x := c) (𝕜 := ℝ)).smul
        ((hloc.contDiffAt (hΩ.mem_nhds (hsub ⟨hxc, hc⟩))).comp c
          (contDiffAt_const.prodMk contDiffAt_id))
  have hg_eq (x) : g x = π (f x) :=
    congrArg (fun D : (Euclidean 3 × Euclidean (n-1)) [×k]→L[ℝ]
      EuclideanSpace ℂ (Fin (n*n)) ↦ D v)
      ((π.restrictScalars ℝ).iteratedFDeriv_comp_left (hparam x) (i := k) (by simp))
  have hπ : ‖π‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro A
    simpa only [π, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, one_mul] using
      (SingleChannel.matrixChannelEquiv n n).norm_map A |>.le
  refine ⟨ua, ?_, ?_⟩
  · intro ij
    filter_upwards [finiteL2Coordinates_apply_ae volume (hg.toLp g) (finProdFinEquiv ij),
      hg.coeFn_toLp] with x hx hy
    change coords (finProdFinEquiv ij) x = _ at hx ⊢
    rw [hx, hy]
    change g x (finProdFinEquiv ij) = _
    rw [hg_eq]
    change f x (finProdFinEquiv.symm (finProdFinEquiv ij)).1
      (finProdFinEquiv.symm (finProdFinEquiv ij)).2 = _
    rw [Equiv.symm_apply_apply]
  · intro p
    refine ⟨fun ij ↦ (hgb p).1 (finProdFinEquiv ij), ?_⟩
    have heq : matrixFourierSobolevNorm (p : ℝ) ua =
        vectorFourierSobolevNorm (p : ℝ) (hg.toLp g) := by
      apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      change matrixFourierSobolevNorm (p : ℝ) ua ^ 2 =
        vectorFourierSobolevNorm (p : ℝ) (hg.toLp g) ^ 2
      rw [matrixFourierSobolevNorm_sq, vectorFourierSobolevNorm, matrixFourierSobolevNorm_sq]
      exact Equiv.sum_comp finProdFinEquiv
        (fun i ↦ fourierSobolevNorm (p : ℝ) (coords i) ^ 2)
    rw [heq]
    apply (hgb p).2.trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (hC k p) hπ) (pow_nonneg hτ.le _))
      (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.CorrectedAtoms
