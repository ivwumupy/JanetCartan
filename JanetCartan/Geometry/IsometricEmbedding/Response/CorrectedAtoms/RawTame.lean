module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.PolynomialTame
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.ReconstructionTame
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.RawFiniteBounds

/-!
# All-order additive bounds for the retained raw amplitudes

The original leading budgets, complete correction covector, canonical
reconstruction and exact WKB polynomial give reserve sixteen. Constants use
only fixed order-fifteen immersion/scalar budgets. Higher norms are retained
additively, and the original leading tensor and inverse-frequency error are
unchanged. No reference, flow or atom is selected in this deduction.

Consumers: homogeneous raw estimates for preparation, and the fixed offset
in `app:ch_response:cor:current-atoms`. The leading/scalar continuation must
still be applied on the initialized construction's own witnesses.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.CorrectedAtoms
open RawPrimary RawPrimary.FiniteJetSlices RawPrimary.AmplitudeGrades
open RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer

/-- The literal raw derivative and leading matrix have a single high input
norm at every order, with fixed reserve sixteen. The exact raw error retains
`τ`. Only order-fifteen immersion/scalar budgets enter the constants; all high
history dependence remains in the displayed norm. The supplied leading and
correction budgets are the outputs of the SAME retained leading construction
(`app:ch_response:eq:current-atomic-offset`,
`app:ch_response:eq:current-density-lipschitz`). -/
theorem exists_retainedRawAmplitude_oneHigh_bounds
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
    (M Mr : ℝ) (hM : 0 ≤ M) (hMr : 0 ≤ Mr)
    (E Γ : ℕ → ℝ)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j) :
    ∃ C : ℕ → ℝ, (∀ j, 0 < C j) ∧
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
      cNorm K 15 F ≤ M → cNorm I 15 r ≤ Mr →
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
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∀ s,
      let H := 1 + cNorm K (s+16) F + cNorm I (s+16) r
      cNorm (closedBall a ρ) s (fullLeadingPrincipalMatrix T Q F row col Φ Y r) ≤ C s * H ∧
      cNorm (closedBall a ρ) s (fullDerivativeAmplitude T Q F row col Φ Y r τ) ≤ C s * H ∧
      cNorm (closedBall a ρ) s (fullDerivativeAmplitude T Q F row col Φ Y r τ -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r) ≤ τ * C s * H := by
  have hsmall : closedBall a ρ ⊆ closedBall a (2 * ρ) :=
    closedBall_subset_closedBall (by linarith)
  have hJΩ : closedBall a ρ ⊆ ball a (2 * ρ) := closedBall_subset_ball (by linarith)
  obtain ⟨X, hX, hξbound⟩ := exists_phaseGradient_projected_sharp_bound (N := N) T
    (isCompact_closedBall a ρ) (hsmall.trans hphase) hK hKU hball (M+1) hγ hκ
  obtain ⟨B, hB, hcorrection⟩ := exists_fullCorrection_reconstruction_tameBounds
    (N := N) T a hρ hK hKU hball hspace hphase I hγ hκ M Mr hM hMr Γ hΓ
  let L := (E 0 + B 0 + X 0) * (1 + M + Mr)
  obtain ⟨D, hD, hpoly⟩ := exists_derivativePolynomial_tameBounds (N := N) a hρ L
  let C := fun s ↦ D s * (1 + X (s+1) + 2 * E (s+1) + B (s+1))
  have hC (s : ℕ) : 0 < C s := by
    have := hX (s+1); have := hE (s+1); have := hB (s+1)
    exact mul_pos (hD s) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro F hF hi hrank hmetric hnormal hlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  intro row col Φ Y r Ω hΩ hflow hb₀ hb₁ hFM hrM hleading hcorrectionBudget τ hτ hτ1 s
  let J := closedBall a ρ
  let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦ phaseGradient T Q w.1 w.2.2
  let ν₀ := fullLeadingNormal T Q F row col Φ Y r
  let ν₁ := fullCorrectionPrincipalNormal T Q F row col Φ Y r
  let V₀ := fullLeadingReconstruction T Q F row col Φ Y r
  let V₁ := fullCorrectionReconstruction T Q F row col Φ Y r
  have hFM4 : cNorm K 4 F ≤ M+1 := (cNorm_mono_order (by omega : 4 ≤ 15)).trans
    (hFM.trans (by linarith))
  obtain ⟨hν₁, hV₁, hp1⟩ := hcorrection F hF hi hrank hmetric hnormal hlow
    row col Φ Y r Ω hΩ hflow hb₁ hFM hrM hcorrectionBudget
  have hlead (m : ℕ) := fullLeading_finite_of_retained_budget T Q F row col Φ Y r
    a hρ (ball_subset_closedBall.trans (hspace.trans hKU)) hphase hF hi hrank
    (hb₀.mono (ball_subset_closedBall.trans hflow))
    (AF := fun j ↦ cNorm K j F) (Ar := fun j ↦ cNorm I j r)
    m (fun j ↦ (hE j).le) (fun j _ ↦ hleading j) (fun _ _ ↦ le_rfl) (fun _ _ ↦ le_rfl)
  obtain ⟨hν₀, hV₀, _, _⟩ := hlead 0
  have hp0 (j : ℕ) : cNorm J j ν₀ ≤ E j * (1 + cNorm K (j+14) F + cNorm I (j+14) r) ∧
      cNorm J j V₀ ≤ E j * (1 + cNorm K (j+14) F + cNorm I (j+14) r) :=
    ⟨(hlead j).2.2.1 j (by omega), (hlead j).2.2.2 j (by omega)⟩
  have hpξ (j : ℕ) : cNorm J j ξ ≤ X j * (1 + cNorm K (j+4) F) :=
    hξbound F hF hi hrank hFM4 hmetric hnormal hlow j
  have hbase : 0 ≤ 1 + M + Mr := by linarith
  have hL0 : E 0 * (1 + M + Mr) ≤ L := by
    have := hE 0; have := hB 0; have := hX 0
    dsimp [L]; nlinarith
  have hL1 : B 0 * (1 + M + Mr) ≤ L := by
    have := hE 0; have := hB 0; have := hX 0
    dsimp [L]; nlinarith
  have hLX : X 0 * (1 + M) ≤ L := by
    have := hE 0; have := hB 0; have := hX 0
    dsimp [L]; nlinarith
  have hlow0 : 1 + cNorm K (0+14) F + cNorm I (0+14) r ≤ 1 + M + Mr := by
    linarith [cNorm_mono_order (s := K) (f := F) (by omega : 14 ≤ 15),
      cNorm_mono_order (s := I) (f := r) (by omega : 14 ≤ 15)]
  have hν₀L : cNorm J 0 ν₀ ≤ L :=
    ((hp0 0).1.trans (mul_le_mul_of_nonneg_left hlow0 (hE 0).le)).trans hL0
  have hV₀L : cNorm J 0 V₀ ≤ L :=
    ((hp0 0).2.trans (mul_le_mul_of_nonneg_left hlow0 (hE 0).le)).trans hL0
  have h1L : cNorm J 0 ν₁ + cNorm J 0 V₁ ≤ L :=
    ((hp1 0).trans (mul_le_mul_of_nonneg_left (by simpa only [Nat.zero_add] using show 1 + cNorm K 15 F + cNorm I 15 r ≤ 1 + M + Mr by linarith only [hFM, hrM])
      (hB 0).le)).trans hL1
  have hξL : cNorm J 0 ξ ≤ L := by
    apply ((hpξ 0).trans (mul_le_mul_of_nonneg_left _ (hX 0).le)).trans hLX
    linarith [cNorm_mono_order (s := K) (f := F) (by omega : 4 ≤ 15)]
  have hphase' : ∀ w ∈ ball a (2 * ρ), (w.1, w.2.2) ∈ phaseDomain T :=
    fun _ hw ↦ hphase (ball_subset_closedBall hw)
  have hξ : ContDiffOn ℝ ∞ ξ (ball a (2 * ρ)) :=
    (phaseGradient_smooth T Q).comp (contDiffOn_fst.prodMk contDiffOn_snd.snd) hphase'
  have hP := hpoly (ball a (2 * ρ)) isOpen_ball hJΩ ξ ν₀ ν₁ V₀ V₁
    hξ hν₀ hν₁ hV₀ hV₁ hξL hν₀L
    (by linarith [cNorm_nonneg J 0 V₁]) hV₀L
    (by linarith [cNorm_nonneg J 0 ν₁]) τ hτ.le hτ1 s
  let H := 1 + cNorm K (s+16) F + cNorm I (s+16) r
  have hH : 1 ≤ H := by dsimp [H]; linarith [cNorm_nonneg K (s+16) F, cNorm_nonneg I (s+16) r]
  have hxH : cNorm J (s+1) ξ ≤ X (s+1) * H := by
    apply (hpξ (s+1)).trans
    apply mul_le_mul_of_nonneg_left _ (hX (s+1)).le
    dsimp [H]
    linarith [cNorm_mono_order (s := K) (f := F) (by omega : s+1+4 ≤ s+16),
      cNorm_nonneg I (s+16) r]
  have h0H : E (s+1) * (1 + cNorm K (s+1+14) F + cNorm I (s+1+14) r) ≤ E (s+1) * H := by
    apply mul_le_mul_of_nonneg_left _ (hE (s+1)).le
    dsimp [H]
    linarith only [cNorm_mono_order (s := K) (f := F) (by omega : s+1+14 ≤ s+16),
      cNorm_mono_order (s := I) (f := r) (by omega : s+1+14 ≤ s+16)]
  have hn0H := (hp0 (s+1)).1.trans h0H
  have hv0H := (hp0 (s+1)).2.trans h0H
  have h1H : cNorm J (s+1) ν₁ + cNorm J (s+1) V₁ ≤ B (s+1) * H := by
    simpa only [H, Nat.add_assoc, Nat.reduceAdd] using hp1 (s+1)
  have htotal : 1 + cNorm J (s+1) ξ + cNorm J (s+1) ν₀ + cNorm J (s+1) ν₁ +
      cNorm J (s+1) V₀ + cNorm J (s+1) V₁ ≤
        (1 + X (s+1) + 2 * E (s+1) + B (s+1)) * H := by
    nlinarith only [hH, hxH, hn0H, hv0H, h1H]
  have hS := contDiffOn_fullPhase T Q hphase'
  have heq : cNorm J s (fullDerivativeAmplitude T Q F row col Φ Y r τ) =
      cNorm J s (derivativePolynomial τ ξ ν₀ ν₁ V₀ V₁) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro w hw
    filter_upwards [isOpen_ball.mem_nhds (hJΩ hw)] with y hy
    exact fullDerivativeAmplitude_eq_polynomial T Q F row col Φ Y r hτ.ne'
      ((hS.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
      ((hν₀.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
      ((hν₁.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
      ((hV₀.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
      ((hV₁.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
  have herr : cNorm J s (fullDerivativeAmplitude T Q F row col Φ Y r τ -
      fullLeadingPrincipalMatrix T Q F row col Φ Y r) =
      cNorm J s (derivativeError τ ξ ν₀ ν₁ V₀ V₁) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq
    intro w hw
    filter_upwards [isOpen_ball.mem_nhds (hJΩ hw)] with y hy
    exact fullDerivativeAmplitude_sub_principal_eq T Q F row col Φ Y r hτ.ne'
      ((hS.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
      ((hν₀.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
      ((hν₁.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
      ((hV₀.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
      ((hV₁.contDiffAt (isOpen_ball.mem_nhds hy)).differentiableAt (by simp))
  have hleadEq : fullLeadingPrincipalMatrix T Q F row col Φ Y r =
      fun w ↦ -(normalTensor n N (ξ w) (ν₀ w)) :=
    funext (fullLeadingPrincipalMatrix_eq_tensor T Q F row col Φ Y r)
  rw [hleadEq, heq]
  refine ⟨hP.1.trans ?_, hP.2.1.trans ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left htotal (hD s).le).trans_eq (by dsimp [C, H]; ring)
  · exact (mul_le_mul_of_nonneg_left htotal (hD s).le).trans_eq (by dsimp [C, H]; ring)
  · rw [← hleadEq, herr]
    exact hP.2.2.trans ((mul_le_mul_of_nonneg_left htotal (mul_nonneg hτ.le (hD s).le)).trans_eq
      (by dsimp [C, H]; ring))

end JanetCartan.CorrectedAtoms
