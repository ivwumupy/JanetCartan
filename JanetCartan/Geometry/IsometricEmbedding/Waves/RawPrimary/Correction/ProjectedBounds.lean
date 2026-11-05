module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.MinorBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.CoefficientBounds

/-!
# Correction estimates for the actual projected stress frame

For `app:ch_waves:eq:WKB-grading`, specialize the finite-jet bound to the
literal projected stress and Hamilton phase. Their high estimates are
produced from the immersion, and the selected-minor bound is produced from
the original carrier-center denominator gap. Only primitive scalar
smoothness and its `C¹` budget remain as transport inputs. The actual scalar
producer is `FullModulation.exists_scalarAmplitude_joint_tame`; on its
buffered domain a fixed `C¹⁴` immersion and initial-scalar budget gives
exactly this low input. The common-family assembly retains that domain and
must instantiate the center gap on the SAME selected row and column.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.StressFrame

namespace JanetCartan.RawPrimary
open NullTransport ProjectedStressFrame GeometricProfile
open LeadingWave.FullModulation LeadingWave.FullModulation.UniformCoefficients
open ActualCarriers FrozenMenu CurrentFullPhase CorrectionBounds

/-- Uniform correction bounds with the actual projected frame and full
Hamilton phase. The only nongeometric low input is the primitive transported
scalar budget. No phase budget, minor gap, inverse estimate, or correction
estimate is assumed. Constants precede the current immersion, flow and
initial datum, and the finite losses are five for the immersion and one for
the scalar (`app:ch_waves:eq:WKB-grading`). -/
theorem exists_fullCorrectionCovector_projected_bounds
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) (hn : 2 ≤ n)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hballK : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {R : ℝ} (hR : 0 < R)
    (hx : MapsTo Prod.fst (closedBall a R)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hdom : closedBall a R ⊆ domain T) (row col : Fin n)
    (M Lα : ℝ) {κmet κnormal g : ℝ}
    (hκmet : 0 < κmet) (hκnormal : 0 < κnormal) (hg : 0 < g) :
    ∃ η ρ : ℝ, 0 < η ∧ 0 < ρ ∧ 2 * ρ ≤ R ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ ρ →
        ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
        ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
          (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
          cNorm K 4 F ≤ M →
          (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
          (∀ x ∈ K, ∀ v ∈ normalSpace F x,
            κnormal * ‖v‖ ≤ ‖normalPairing F (fun _ ↦ v) x‖) →
          cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < η →
          ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
              (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
          let Q := ⟨projectedStress F,
            contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
          g ≤ |adaptedDenominator T Q row col a| →
          ∀ (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
              Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
            (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
            (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
            IsOpen Ω → closedBall a σ ⊆ Ω → Ω ⊆ closedBall a (2 * ρ) →
            ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω →
            cNorm (closedBall a σ) 1 (scalarAmplitude T Q F row col Φ Y r) ≤ Lα →
            ∀ m, cNorm (closedBall a σ) m (fullCorrectionCovector T Q F row col Φ Y r) ≤
              C m * (1 + cNorm K (m + 5) F +
                cNorm (closedBall a σ) (m + 1) (scalarAmplitude T Q F row col Φ Y r)) := by
  obtain ⟨η, ρ, L, δ, hη, hρ, hL, hδ, hρR, hneigh⟩ :=
    exists_fullPhase_minor_neighborhood T hn a hR hx (hballK.trans hKU) hdom row col hg
  have hbig : closedBall a (2 * ρ) ⊆ closedBall a R := closedBall_subset_closedBall hρR
  refine ⟨min η T.family.threshold, ρ, lt_min hη T.family.threshold_pos, hρ, hρR, ?_⟩
  intro σ hσ hσρ
  have hsmall : closedBall a σ ⊆ closedBall a (2 * ρ) :=
    closedBall_subset_closedBall (by linarith)
  have hxσ := hx.mono (hsmall.trans hbig) (Subset.refl _)
  obtain ⟨A, hA, hinputHigh⟩ := exists_projected_fullInput_bound (N := N)
    T a σ hxσ (hsmall.trans (hbig.trans hdom)) hK hKU hballK M hκmet hκnormal
  obtain ⟨B, hB, hcorrection⟩ := exists_fullCorrectionCovector_bounds (N := N)
    T a hσ hK (fun _ hw ↦ hballK (hxσ hw)) hKU row col (2 * M) (2 * (L + Lα)) hκmet hδ
  let C := fun m ↦ B m * (1 + (m + 2 : ℝ) * (A (m + 1) + 1))
  have hC (m) : 0 < C m := by
    dsimp [C]
    have := hA (m + 1)
    have := hB m
    positivity
  refine ⟨C, hC, ?_⟩
  intro F hF hi hrank hFM hmet hnormal hclose
  have hframe := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hlocal : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < min η T.family.threshold := by
    apply (cNorm_mono_set_of_contDiffAt hballK hK _).trans_lt hclose
    intro x hxK
    exact ((hframe.contDiffAt (hU.mem_nhds (hKU hxK))).sub contDiffAt_const).of_le (by simp)
  have hlow := hlocal.trans_le (min_le_right _ _)
  refine ⟨hlow, ?_⟩
  let Q := (⟨projectedStress F, hframe, hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  change g ≤ |adaptedDenominator T Q row col a| → _
  intro hcenter Φ Y r Ω hΩ hball hΩbig hscalar hscalarLow
  obtain ⟨hinputLow, hminor⟩ := hneigh Q (hlocal.trans_le (min_le_left _ _)) hcenter
  have hspace : MapsTo Prod.fst Ω U :=
    fun w hw ↦ hKU (hballK (hx (hbig (hΩbig hw))))
  have hphase : Ω ⊆ domain T := hΩbig.trans (hbig.trans hdom)
  have hfull : ContDiffOn ℝ ∞ (fullInput T Q) Ω :=
    (smooth_fullInput T Q).mono (fun w hw ↦ ⟨hphase hw, hspace hw⟩)
  have hfullAt (w) (hw : w ∈ closedBall a (2 * ρ)) : ContDiffAt ℝ ∞ (fullInput T Q) w :=
    (smooth_fullInput T Q).contDiffAt ((UniformCoefficients.isOpen_inputDomain T).mem_nhds
      ⟨hdom (hbig hw), hKU (hballK (hx (hbig hw)))⟩)
  have hinputLowσ : cNorm (closedBall a σ) 1 (fullInput T Q) ≤ L :=
    (cNorm_mono_set_of_contDiffAt hsmall (isCompact_closedBall a (2 * ρ))
      (fun w hw ↦ (hfullAt w hw).of_le (by simp))).trans hinputLow
  have hpack (m) : cNorm (closedBall a σ) m (fullPrimitiveValues T Q F row col Φ Y r) ≤
      (m + 1 : ℝ) * (cNorm (closedBall a σ) m (fullInput T Q) +
        cNorm (closedBall a σ) m (scalarAmplitude T Q F row col Φ Y r)) :=
    NullTransport.CoefficientBounds.cNorm_pair_le a m hΩ hball hfull hscalar
  have hpackLow : cNorm (closedBall a σ) 1 (fullPrimitiveValues T Q F row col Φ Y r) ≤
      2 * (L + Lα) := by
    apply (hpack 1).trans
    norm_num only [Nat.cast_one]
    exact mul_le_mul_of_nonneg_left (add_le_add hinputLowσ hscalarLow) (by norm_num)
  have hjet (x) (hxK : x ∈ K) : ‖stressJet F x‖ ≤ 2 * M :=
    (norm_stressJet_le_cNorm_four hK (fun y hy ↦ hF.contDiffAt (hU.mem_nhds (hKU hy))) hxK).trans
      (mul_le_mul_of_nonneg_left hFM (by norm_num))
  have hb := (hcorrection Q F Φ Y r Ω hΩ hball hspace hphase hF hscalar hpackLow hjet hmet
    (fun w hw ↦ (hminor w (hsmall hw)).1)).1
  have ha := hinputHigh F hF hi hrank hFM hmet hnormal hlow
  intro m
  have hv : cNorm (closedBall a σ) (m + 1) (fullPrimitiveValues T Q F row col Φ Y r) ≤
      (m + 2 : ℝ) * (A (m + 1) * (1 + cNorm K (m + 5) F) +
        cNorm (closedBall a σ) (m + 1) (scalarAmplitude T Q F row col Φ Y r)) := by
    apply (hpack (m + 1)).trans
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, show (1 : ℕ) + 4 = 5 from rfl,
      show (1 : ℝ) + 1 = 2 by norm_num, add_assoc] using
      mul_le_mul_of_nonneg_left
        (add_le_add (ha (m + 1)) (le_refl
          (cNorm (closedBall a σ) (m + 1) (scalarAmplitude T Q F row col Φ Y r))))
        (by positivity : (0 : ℝ) ≤ (m + 1 : ℕ) + 1)
  have horder : cNorm K (m + 2) F ≤ cNorm K (m + 5) F := cNorm_mono_order (by omega)
  have hs : 1 + cNorm K (m + 2) F +
      cNorm (closedBall a σ) (m + 1) (fullPrimitiveValues T Q F row col Φ Y r) ≤
      (1 + (m + 2 : ℝ) * (A (m + 1) + 1)) *
        (1 + cNorm K (m + 5) F +
          cNorm (closedBall a σ) (m + 1) (scalarAmplitude T Q F row col Φ Y r)) := by
    have hF0 := cNorm_nonneg K (m + 5) F
    have hα0 := cNorm_nonneg (closedBall a σ) (m + 1) (scalarAmplitude T Q F row col Φ Y r)
    have hA0 := (hA (m + 1)).le
    have hm : (0 : ℝ) ≤ m + 2 := by positivity
    nlinarith [mul_nonneg hm hF0, mul_nonneg (mul_nonneg hm hA0) hα0]
  exact (hb m).trans ((mul_le_mul_of_nonneg_left hs (hB m).le).trans_eq (by dsimp [C]; ring))

end JanetCartan.RawPrimary
