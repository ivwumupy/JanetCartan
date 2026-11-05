module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.Amplitude
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceMatching.UniformDirection
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.SourceDirectionBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.UniformFlow
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.ActualAmplitude.Buffers

/-!
# Common source flows with seed inverse evidence retained

For `paper.tex`, `app:ch_background:eq:bg-Nsigma`, and `paper-v2.tex`,
`new:lem:scaling`. The same actual ODE witnesses supply both the smooth seed
scalar and its identification at every positive contraction. The producer is
`exists_uniform_actual_flow_chart`; consumer: `MatchedSeedAmplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open SourceMatching HamiltonPhase NormalizedBackground.SourceGeometry
open ActualCarriers CurrentFullPhase NullTransport NullTransport.ActualFlow
open NullTransport.FlowAmplitude LeadingWave AmbientResponse

/-- Construct common source flow buffers and retain the seed domain, both
inverse equations and label preservation, in addition to scalar matching.
These are actual ODE outputs, needed by `carrierScalarAmplitude_spec` on the
SAME seed witnesses. No matching or scalar smoothness is assumed.
Source: `app:ch_background:eq:bg-Nsigma`, `new:lem:scaling`. -/
theorem exists_retained_source_matched_null_flows
    {n N : ℕ} {P : FrozenMenu.Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q₀ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {F : Euclidean n → Euclidean N} (hF : ContDiff ℝ ∞ F)
    (hrank : HasFullNormalRankOn F U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hseed : Q₀.1 = ProjectedStressFrame.projectedStress F)
    (htrans : ∀ z ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
      ⟪(normalizedHomogeneousSymbol hU Q₀.1 Q₀.2.1).hp z, T.data.adapted.normal⟫_ℝ ≠ 0)
    (hflat : ∀ x ∈ U, inducedMetric F x = 1)
    (row col : Fin n) {z₀ : Euclidean 3} {r : ℝ} (hr : 0 < r)
    (hpatch : ball ((0 : Euclidean n), z₀) r ⊆ ball 0 T.physicalRadius ×ˢ
      FrozenMenu.parameterCube (2 * P.radius))
    (hd : ContDiffOn ℝ ∞ (carrierTransportDirection T Q₀ row col) (ball (0, z₀) r))
    (hk : ContDiffOn ℝ ∞ (carrierNullvector T Q₀ col) (ball (0, z₀) r)) :
    ∃ R τ : ℝ, 0 < R ∧ 0 < τ ∧ τ ≤ R / 16 ∧
      let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
      let I := Ioo (-τ) τ
      let L := ball ((0 : Euclidean (n - 1)), z₀) (R / 8)
      let W := I ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (R / 32)
      ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
      ∃ D₀ : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
      ∃ Φ₀ Y₀ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
        IsOpen D₀ ∧ W ⊆ D₀ ∧ C ⁻¹' D₀ ⊆ ball (0, z₀) r ∧
        D₀ ⊆ I ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (R / 4) ∧
        ContDiffOn ℝ ∞ Φ₀ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Y₀ D₀ ∧
        MapsTo (fun q ↦ (q.1, Φ₀ q)) (I ×ˢ L) D₀ ∧
        MapsTo (fun q ↦ (q.1, Y₀ q)) D₀ (I ×ˢ L) ∧
        (∀ p ∈ L, Φ₀ (0, p) = p) ∧
        (∀ p ∈ L, ∀ t ∈ I, Y₀ (t, Φ₀ (t, p)) = p) ∧
        (∀ q ∈ D₀, Φ₀ (q.1, Y₀ q) = q.2) ∧
        (∀ q ∈ D₀, (Y₀ q).2 = q.2.2) ∧
        (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φ₀ (s, p))
          ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Q₀ row col
            (C.symm (t, Φ₀ (t, p))))).2, 0) t) ∧
        ∀ (σ : ℝ), 0 < σ → σ ≤ 1 →
          ∀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
            cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
              (Q - fun _ ↦ cubeStress n) < T.family.threshold},
            Qσ.1 = ProjectedStressFrame.projectedStress (sourceDilation F σ) →
          ∃ Dσ : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
          ∃ Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
            IsOpen Dσ ∧ W ⊆ Dσ ∧ C ⁻¹' Dσ ⊆ ball (0, z₀) r ∧
            ContDiffOn ℝ ∞ Φσ (I ×ˢ L) ∧ ContDiffOn ℝ ∞ Yσ Dσ ∧
            ContDiffOn ℝ ∞ Yσ
              (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball ((0 : Euclidean (n - 1)), z₀) (R / 4)) ∧
            (∀ m, cNorm (Icc (-τ) τ ×ˢ closedBall (0, z₀) (R / 8)) m Φσ +
              cNorm (Icc (-τ) τ ×ˢ closedBall (0, z₀) (R / 8)) m Yσ ≤ B m) ∧
            MapsTo (fun q ↦ (q.1, Φσ q)) (I ×ˢ L) Dσ ∧
            (∀ q ∈ Dσ, (Yσ q).2 = q.2.2) ∧
            MapsTo (fun q ↦ (q.1, Yσ q)) Dσ (I ×ˢ L) ∧
            (∀ p ∈ L, Φσ (0, p) = p) ∧
            (∀ p ∈ L, ∀ t ∈ I, Yσ (t, Φσ (t, p)) = p) ∧
            (∀ q ∈ Dσ, Φσ (q.1, Yσ q) = q.2) ∧
            (∀ p ∈ L, ∀ t ∈ I, HasDerivAt (fun s ↦ Φσ (s, p))
              ((adaptedCoordinates T.data.adapted (carrierTransportDirection T Qσ row col
                (C.symm (t, Φσ (t, p))))).2, 0) t) ∧
            EqOn Φσ (sourceTransportFlow Φ₀ σ) (I ×ˢ L) ∧
            EqOn Yσ (sourceTransportFlow Y₀ σ) Dσ ∧
            let α₀ := carrierScalarAmplitude T Q₀ F row col Φ₀ Y₀ (fun _ ↦ 1)
            let ασ := carrierScalarAmplitude T Qσ (sourceDilation F σ) row col Φσ Yσ (fun _ ↦ σ)
            let b₀ := fun w ↦ α₀ w • carrierNullvector T Q₀ col w
            let bσ := fun w ↦ ασ w • carrierNullvector T Qσ col w
            EqOn ασ (sourceAmplitude α₀ σ) (C ⁻¹' Dσ) ∧
            EqOn bσ (sourceAmplitude b₀ σ) (C ⁻¹' Dσ) ∧
            ∀ (measurement : Euclidean n → ℝ)
              (angular : (ℝ × Euclidean 2) × Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
              (p : Euclidean n × (ℝ × Euclidean 2)),
              C (p.1, ContinuumRow.CanonicalCarrier.parameter p.2) ∈ Dσ →
              (normalizedSourceCoefficients F
                (fun q ↦ T.carrierGradient Q₀ q.1 (ContinuumRow.CanonicalCarrier.parameter q.2))
                (fun q ↦ b₀ (q.1, ContinuumRow.CanonicalCarrier.parameter q.2))
                measurement angular high σ).normal p =
              principalNormal (canonicalNormalCompletion (sourceDilation F σ) p.1)
                (T.carrierGradient Qσ p.1 (ContinuumRow.CanonicalCarrier.parameter p.2))
                (bσ (p.1, ContinuumRow.CanonicalCarrier.parameter p.2)) := by
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  obtain ⟨ρ, R, _, hR, hwork, _, hbuffer'⟩ :=
    exists_adapted_coefficient_ball T isOpen_ball z₀ (mem_ball_self (half_pos hr))
  have hbuffer : MapsTo C.symm (closedBall (0, (0, z₀)) R)
      (closedBall (0, z₀) (r / 2)) :=
    fun q hq ↦ ball_subset_closedBall (hwork (hbuffer' hq))
  let K := closedBall ((0 : Euclidean n), z₀) (r / 2)
  let M := 2 * cNorm K 1 (carrierTransportDirection T Q₀ row col)
  have hM : 0 ≤ M := mul_nonneg (by norm_num) (cNorm_nonneg _ _ _)
  have hKr : K ⊆ ball (0, z₀) r := closedBall_subset_ball (half_lt_self hr)
  obtain ⟨A, hA, hflow⟩ := exists_uniform_actual_flow_chart T isOpen_ball
    (isCompact_closedBall _ _) hKr hM hR hbuffer
  let τ := existenceTime R (liftedLowBound T M) / 4
  have hτR : τ ≤ R / 16 := by
    have hh := (existenceTime_le hR (liftedLowBound_nonneg T hM)).1
    dsimp [τ]
    linarith
  have hlow₀ : cNorm K 1 (carrierTransportDirection T Q₀ row col) ≤ M := by
    dsimp [M]
    linarith [cNorm_nonneg K 1 (carrierTransportDirection T Q₀ row col)]
  obtain ⟨D₀, Φ₀, Y₀, hτ, hD₀, hsmall₀, hbig₀, _, hΦ₀, hY₀, hdomain₀, hΦD₀, hYU₀,
    hinit₀, hYΦ₀, hΦY₀, _, hYz₀, hvelocity₀, _, _, _⟩ := hflow Q₀ row col hd hlow₀
  have hrange₀ (p : Euclidean (n - 1) × Euclidean 3) (hp : p ∈ ball (0, z₀) (R / 8)) (t) (ht : t ∈ Ioo (-τ) τ) :=
    (hbig₀ (hΦD₀ (show (t, p) ∈ Ioo (-τ) τ ×ˢ ball (0, z₀) (R / 8) from ⟨ht, hp⟩))).2
  have hreg (w) (hw : w ∈ K) := hd.contDiffAt (isOpen_ball.mem_nhds (hKr hw))
  have hkreg (w) (hw : w ∈ K) := hk.contDiffAt (isOpen_ball.mem_nhds (hKr hw))
  have hphys₀ : C ⁻¹' D₀ ⊆ ball (0, z₀) r := by
    intro w hw
    simpa only [C, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hdomain₀ hw
  let B : ℕ → ℝ := fun m ↦ A m *
    (1 + (m + 1) * cNorm K m (carrierTransportDirection T Q₀ row col))
  have hB (m) : 0 < B m := mul_pos (hA m) (by
    have := cNorm_nonneg K m (carrierTransportDirection T Q₀ row col)
    positivity)
  refine ⟨R, τ, hR, hτ, hτR, B, hB, D₀, Φ₀, Y₀, hD₀, hsmall₀, hphys₀, hbig₀,
    hΦ₀, hY₀.mono hbig₀, hΦD₀, hYU₀, hinit₀, hYΦ₀, hΦY₀, hYz₀, hvelocity₀, ?_⟩
  intro σ hσ hσ₁ Qσ hscaled
  obtain ⟨hdσ, hlowσ⟩ := current_carrierTransportDirection_uniform_bound T Q₀ Qσ
    hF hrank hphysical hseed htrans row col (half_lt_self hr) hpatch hd hσ hσ₁ hscaled
  obtain ⟨Dσ, Φσ, Yσ, _, hDσ, hsmallσ, hbigσ, _, hΦσ, hYσ, hdomainσ, hΦDσ, hYUσ,
    hinitσ, hYΦσ, hΦYσ, _, hYzσ, hvelocityσ, _, hYbufferσ, hnormσ⟩ :=
    hflow Qσ row col hdσ hlowσ
  have hrangeσ (p : Euclidean (n - 1) × Euclidean 3) (hp : p ∈ ball (0, z₀) (R / 8)) (t) (ht : t ∈ Ioo (-τ) τ) :=
    (hbigσ (hΦDσ (show (t, p) ∈ Ioo (-τ) τ ×ˢ ball (0, z₀) (R / 8) from ⟨ht, hp⟩))).2
  have hpatchσ (p : Euclidean (n - 1) × Euclidean 3) (hp : p ∈ ball (0, z₀) (R / 8)) (t) (ht : t ∈ Ioo (-τ) τ) :=
    hpatch (hdomainσ (hΦDσ (show (t, p) ∈ Ioo (-τ) τ ×ˢ ball (0, z₀) (R / 8) from ⟨ht, hp⟩)))
  obtain ⟨hmatch, hfoot⟩ := current_nullFlow_source_dilation T Q₀ Qσ hF hrank
    hphysical hseed htrans hσ hσ₁ hscaled row col hR hτ hτR hbuffer hreg
    hinit₀ hinitσ hrange₀ hrangeσ hpatchσ hvelocity₀ hvelocityσ
  refine ⟨Dσ, Φσ, Yσ, hDσ, hsmallσ, ?_, hΦσ, hYσ.mono hbigσ, hYbufferσ, ?_, hΦDσ, hYzσ, hYUσ,
    hinitσ, hYΦσ, hΦYσ, hvelocityσ, hmatch, hfoot Y₀ Yσ Dσ hYUσ hYΦ₀ hΦYσ, ?_⟩
  · intro w hw
    have hh := hdomainσ hw
    simpa only [mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using hh
  · intro m
    have hb := (current_carrierTransportDirection_uniform_finite_bound T Q₀ Qσ
      hF hrank hphysical hseed htrans row col (half_lt_self hr) hpatch hd
      hσ hσ₁ hscaled m).2
    exact (hnormσ m).trans (mul_le_mul_of_nonneg_left
      (by linarith [hb]) (hA m).le)
  · exact current_nullAmplitude_source_dilation T Q₀ Qσ hF hrank hphysical hseed htrans
      hσ hσ₁ hscaled row col hR hτ hτR hbuffer hreg hinit₀ hinitσ hrange₀ hrangeσ
      hpatchσ hvelocity₀ hvelocityσ hflat hkreg hYUσ hYΦ₀ hΦYσ

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
