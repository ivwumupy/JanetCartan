module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.Polynomial
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets.Base

/-!
# Joint estimates for the actual background-modulation product

Apply the retained raw reconstruction producer once. Pull its complete
polynomial back along the two fixed coordinate projections and apply the
complex Hermitian product estimate. These bounds include the inverse-frequency
parameter and both covectors, before restriction to the carrier graph. The
constants precede current fields, scalars, scale, colors and band ceiling.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.BackgroundModulation
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer

/-- Coordinate projection and the bilinear product preserve the original
joint reserve (`app:ch_waves:eq:sampling-operator-bounds`). -/
private theorem joint_symmetricHermitianCross_bounds
    {X E G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] E →L[ℝ] G) (poly : ℝ × X → E) (a : X)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hs : ContDiffOn ℝ ∞ poly (univ ×ˢ ball a (2 * ρ)))
    {A : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) {L : ℝ} {rpar : ℕ} (hL : 1 ≤ L)
    (hj : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w ∈ closedBall a ρ, ∀ j,
      ‖iteratedFDeriv ℝ j poly (τ, w)‖ ≤ A j * L ^ (j - rpar)) :
    let H := fun q : ℝ × (X × X) ↦ B (poly (q.1, q.2.1)) (poly (q.1, q.2.2))
    ContDiffOn ℝ ∞ H (univ ×ˢ (ball a (2 * ρ) ×ˢ ball a (2 * ρ))) ∧
      ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w₀ ∈ closedBall a ρ,
        ∀ w₁ ∈ closedBall a ρ, ∀ j,
          ‖iteratedFDeriv ℝ j H (τ, (w₀, w₁))‖ ≤
            productProfile B A A j * L ^ (j - rpar) := by
  let π₀ : ℝ × (X × X) →L[ℝ] ℝ × X :=
    (ContinuousLinearMap.fst ℝ ℝ (X × X)).prod
      ((ContinuousLinearMap.fst ℝ X X).comp (ContinuousLinearMap.snd ℝ ℝ (X × X)))
  let π₁ : ℝ × (X × X) →L[ℝ] ℝ × X :=
    (ContinuousLinearMap.fst ℝ ℝ (X × X)).prod
      ((ContinuousLinearMap.snd ℝ X X).comp (ContinuousLinearMap.snd ℝ ℝ (X × X)))
  have hπ₀ : ‖π₀‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change max ‖q.1‖ ‖q.2.1‖ ≤ 1 * max ‖q.1‖ (max ‖q.2.1‖ ‖q.2.2‖)
    simpa only [one_mul] using max_le_max_left ‖q.1‖ (le_max_left ‖q.2.1‖ ‖q.2.2‖)
  have hπ₁ : ‖π₁‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro q
    change max ‖q.1‖ ‖q.2.2‖ ≤ 1 * max ‖q.1‖ (max ‖q.2.1‖ ‖q.2.2‖)
    simpa only [one_mul] using max_le_max_left ‖q.1‖ (le_max_right ‖q.2.1‖ ‖q.2.2‖)
  have hs₀ : ContDiffOn ℝ ∞ (poly ∘ π₀)
      (univ ×ˢ (ball a (2 * ρ) ×ˢ ball a (2 * ρ))) :=
    hs.comp π₀.contDiff.contDiffOn (fun _ h ↦ ⟨h.1, h.2.1⟩)
  have hs₁ : ContDiffOn ℝ ∞ (poly ∘ π₁)
      (univ ×ˢ (ball a (2 * ρ) ×ˢ ball a (2 * ρ))) :=
    hs.comp π₁.contDiff.contDiffOn (fun _ h ↦ ⟨h.1, h.2.2⟩)
  refine ⟨B.contDiff.comp_contDiffOn hs₀ |>.clm_apply hs₁, ?_⟩
  intro τ hτ w₀ hw₀ w₁ hw₁ j
  have hw₀' : w₀ ∈ ball a (2 * ρ) := closedBall_subset_ball (by linarith) hw₀
  have hw₁' : w₁ ∈ ball a (2 * ρ) := closedBall_subset_ball (by linarith) hw₁
  have hp₀ (k) : ‖iteratedFDeriv ℝ k (poly ∘ π₀) (τ, (w₀, w₁))‖ ≤
      A k * L ^ (k - rpar) := by
    apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le π₀
      (f := poly) (x := (τ, (w₀, w₁)))
      (isOpen_univ.prod isOpen_ball) hs ⟨mem_univ _, hw₀'⟩ k).trans
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hπ₀)).trans
      (hj τ hτ w₀ hw₀ k)
  have hp₁ (k) : ‖iteratedFDeriv ℝ k (poly ∘ π₁) (τ, (w₀, w₁))‖ ≤
      A k * L ^ (k - rpar) := by
    apply (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le π₁
      (f := poly) (x := (τ, (w₀, w₁)))
      (isOpen_univ.prod isOpen_ball) hs ⟨mem_univ _, hw₁'⟩ k).trans
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hπ₁)).trans
      (hj τ hτ w₁ hw₁ k)
  exact jet_bilinear_le B (isOpen_univ.prod (isOpen_ball.prod isOpen_ball)) hs₀ hs₁
    ⟨mem_univ _, hw₀', hw₁'⟩ hL hA hA hp₀ hp₁ j


/-- Prove every joint jet of the actual complex Hermitian product using the
SAME retained leading/correction outputs and original immersion/scalar profiles.
Both covectors share the inverse frequency, with no derivative or kernel bound
assumed for their product. This is the amplitude producer for the actual
background-modulation channels of `app:ch_background:setup:bg-wkb-input` and
`app:ch_waves:eq:sampling-operator-bounds`. -/
theorem exists_retained_crossDerivativePolynomial_budgets
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (hspace : closedBall a.1 (2 * ρ) ⊆ K)
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (I : Set (Euclidean (n - 1) × Euclidean 3))
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF Ar E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j) :
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
          Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
        (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
        (Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))),
      IsOpen Ω → closedBall a (2 * ρ) ⊆ Ω →
      ContDiffOn ℝ ∞ (fullLeadingCovector T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) Ω →
      (∀ j,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
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
      let H := fun q : ℝ ×
          ((Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ×
            (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))) ↦
        crossDerivativePolynomial T Q F row col Φ Y r q.1 q.2.1 q.2.2
      ContDiffOn ℝ ∞ H (univ ×ˢ (ball a (2 * ρ) ×ˢ ball a (2 * ρ))) ∧
        ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w₀ ∈ closedBall a ρ,
          ∀ w₁ ∈ closedBall a ρ, ∀ j,
            ‖iteratedFDeriv ℝ j H (τ, (w₀, w₁))‖ ≤ A j * L ^ (j - rpar) := by
  obtain ⟨A, hA, hpoly⟩ := MeasuredAmplitude.exists_retained_jointPolynomial_budgets
    (N := N) T a hρ hK hKU hball hspace hphase I hγ hκ AF Ar E Γ hAF hAr hE hΓ
  let B := symmetricHermitianCross N n
  let C := productProfile B A A
  have hC (j) : 0 ≤ C j := productProfile_nonneg B (fun j ↦ (hA j).le)
    (fun j ↦ (hA j).le) j
  refine ⟨fun j ↦ 1 + C j, fun j ↦ by linarith [hC j], ?_⟩
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hb₀ hb₁
    hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨hs, hj⟩ := hpoly F hF hi hrank hmetric hnormal hlow row col Φ Y r
    Ω hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨hs', hj'⟩ := joint_symmetricHermitianCross_bounds B _ a hρ hs
    (fun j ↦ (hA j).le) hL hj
  refine ⟨hs', ?_⟩
  intro τ hτ w₀ hw₀ w₁ hw₁ j
  exact (hj' τ hτ w₀ hw₀ w₁ hw₁ j).trans
    (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith)
      (pow_nonneg (le_trans zero_le_one hL) _))

end JanetCartan.Sampling.BackgroundModulation
