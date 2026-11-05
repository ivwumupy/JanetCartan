module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.RetainedCorrection.PrimitiveBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients.Inputs

/-!
# Reserve-fourteen correction bounds on retained estimate balls

The scalar reserve-thirteen estimate and the positive null-column lower bound
are primitive outputs of
`CurrentCoefficientProfiles.exists_finite_retained_leading_family_before_geometry`.
The estimates below apply to the SAME arbitrary flow witnesses and selected
indices. All constants precede the immersion, scalar, frequency and history.
No selected-minor or inverse budget is added.

The scalar producer estimates on its compact cylinder image `W`. The public
endpoint retains that set explicitly and requires the estimate ball to lie in
it. `RetainedCorrection.CellBounds` supplies this containment from the exact
working-ball output, and `RetainedCorrection.Finite` applies it to the original
finite witnesses (`app:ch_waves:thm:individual`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.RetainedCorrection
open NullTransport ProjectedStressFrame GeometricProfile
open LeadingWave.FullModulation LeadingWave.FullModulation.UniformCoefficients
open ActualCarriers FrozenMenu CurrentFullPhase CorrectionBounds

private theorem exists_transport_bounds_of_column
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
    {κmet κnormal b : ℝ}
    (hκmet : 0 < κmet) (hκnormal : 0 < κnormal) (hb : 0 < b) :
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
            b ≤ ‖nullvector T Q col w‖) →
          ∀ m, cNorm (closedBall a σ) m (fullCorrectionCovector T Q F row col Φ Y r) ≤
            C m * (1 + cNorm K (m + 14) F + cNorm Kr (m + 14) r) := by
  obtain ⟨A, hA, hinput⟩ := exists_projected_fullInput_bound (N := N)
    T a σ hx hdom hK hKU hballK M hκmet hκnormal
  obtain ⟨D, hD, hcorrection⟩ := exists_fullCorrectionCovector_primitive_bounds_of_retained_column (N := N)
    T a hσ hK (fun _ hw ↦ hballK (hx hw)) hKU row col (2 * M)
      (2 * (A 1 * (1 + M) + Lα)) hκmet hb
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
  intro Φ Y r Kr Ω hΩ hball hxU hphase hscalar hscalarLow hscalarHigh hcolumn
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
  have hbound := hcorrection Q F Φ Y r Ω hΩ hball hxU hphase hF hscalar hpackLow hjet hmet hcolumn
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
  exact (hbound m).trans ((mul_le_mul_of_nonneg_left (add_le_add hForder' hpackm) (hD m).le).trans_eq
    (by dsimp [C, S]; ring))

/-- The retained scalar/leading budget on `W` and retained null-column lower
bound imply the reserve-fourteen estimate for the SAME correction on any fixed
estimate ball contained in `W`. Both analytic inputs are direct conclusions
of `exists_finite_retained_leading_family_before_geometry`; the original
immersion and scalar low bounds close every other low-budget premise.
The theorem does not select or shrink a covering cell. Its finite-family
consumer must retain `closedBall a σ ⊆ W` before choosing the source scale
(`app:ch_waves:eq:WKB-grading`, `app:ch_waves:thm:individual`). -/
theorem exists_fullCorrectionCovector_retained_bounds
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hballK : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {σ : ℝ} (hσ : 0 < σ)
    (hx : MapsTo Prod.fst (closedBall a σ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hdom : closedBall a σ ⊆ domain T)
    {W : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hW : IsCompact W) (hballW : closedBall a σ ⊆ W)
    (row col : Fin n) (M Mᵣ : ℝ) (B : ℕ → ℝ)
    {κmet κnormal b : ℝ}
    (hκmet : 0 < κmet) (hκnormal : 0 < κnormal) (hb : 0 < b) :
    ∃ Γ : ℕ → ℝ, (∀ k, 0 < Γ k) ∧
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
          IsOpen Ω → W ⊆ Ω → MapsTo Prod.fst Ω U → Ω ⊆ domain T →
          ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω →
          cNorm Kr 14 r ≤ Mᵣ →
          (∀ k, cNorm W k (scalarAmplitude T Q F row col Φ Y r) +
              cNorm W k (fun w ↦ scalarAmplitude T Q F row col Φ Y r w •
                nullvector T Q col w) ≤
            B k * (1 + cNorm K (k + 13) F + cNorm Kr (k + 13) r)) →
          (∀ w ∈ Ω, b ≤ ‖nullvector T Q col w‖) →
          ∀ k, cNorm (closedBall a σ) k (fullCorrectionCovector T Q F row col Φ Y r) ≤
            Γ k * (1 + cNorm K (k + 14) F + cNorm Kr (k + 14) r) := by
  let B' := fun k ↦ 1 + |B k|
  have hB' (k) : 0 < B' k := by dsimp [B']; positivity
  have hBB' (k) : B k ≤ B' k := by
    dsimp [B']
    linarith [le_abs_self (B k)]
  obtain ⟨Γ, hΓ, hbudget⟩ := exists_transport_bounds_of_column (N := N)
    T hK hKU hballK a hσ hx hdom row col M (B' 1 * (1 + M + Mᵣ)) B' hB'
      hκmet hκnormal hb
  refine ⟨Γ, hΓ, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow
  dsimp only
  intro Φ Y r Kr Ω hΩ hWΩ hxU hphase hα hrM hscalar hcolumn
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  have hscalarBall (k) : cNorm (closedBall a σ) k (scalarAmplitude T Q F row col Φ Y r) ≤
      B' k * (1 + cNorm K (k + 13) F + cNorm Kr (k + 13) r) := by
    have hmono := cNorm_mono_set_of_contDiffAt hballW hW
      (fun w hw ↦ (hα.contDiffAt (hΩ.mem_nhds (hWΩ hw))).of_le
        (by simp : (k : ℕ∞ω) ≤ ∞))
    apply hmono.trans
    apply (le_add_of_nonneg_right (cNorm_nonneg W k
      (fun w ↦ scalarAmplitude T Q F row col Φ Y r w • nullvector T Q col w))).trans
    apply (hscalar k).trans
    exact mul_le_mul_of_nonneg_right (hBB' k)
      (by linarith [cNorm_nonneg K (k + 13) F, cNorm_nonneg Kr (k + 13) r])
  have hscalarLow : cNorm (closedBall a σ) 1 (scalarAmplitude T Q F row col Φ Y r) ≤
      B' 1 * (1 + M + Mᵣ) :=
    (hscalarBall 1).trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (le_refl 1) hFM) hrM) (hB' 1).le)
  exact hbudget F hF hi hrank hFM hmet hnormal hlow Φ Y r Kr Ω hΩ
    (hballW.trans hWΩ) hxU hphase hα hscalarLow hscalarBall
    (fun w hw ↦ hcolumn w (hWΩ (hballW hw)))

end JanetCartan.RawPrimary.RetainedCorrection
