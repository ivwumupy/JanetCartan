module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.FiniteJetSlices.Amplitudes

/-!
# Finite raw leading and error bounds for corrected atoms

The density estimate `app:ch_response:eq:current-density-lipschitz` needs the
inverse-frequency factor in the raw error, not only bounded full amplitudes.
Here the exact polynomial and the retained finite coefficient budgets supply
that factor on the same working ball. No all-order bounded profile is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.CorrectedAtoms
open RawPrimary RawPrimary.FiniteJetSlices RawPrimary.AmplitudeGrades
open RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseTransfer AmbientResponse ProjectedStressFrame

/-- The literal raw error retains its inverse-frequency factor using only
coefficient jets through `j+1`. The constant is the existing derivative profile;
its nonnegative leading summand bounds the error profile. Consumer: finite raw
bounds for `app:ch_response:eq:current-density-lipschitz`, from the polynomial
identity `app:ch_waves:eq:WKB-amplitude-difference`. -/
theorem fullDerivativeError_jet_le_finite_coefficients
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
      Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1)))
    (r : Euclidean (n-1) × Euclidean 3 → ℝ)
    {J Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    (hJ : IsCompact J) (hΩ : IsOpen Ω) (hJΩ : J ⊆ Ω)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω)
    (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
    (hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω)
    (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {j : ℕ}
    {C A₀ A₁ B₀ B₁ : ℕ → ℝ}
    (hξ : ∀ k ≤ j+1, cNorm J k (fun w ↦ phaseGradient T Q w.1 w.2.2) ≤ C k)
    (hn₀ : ∀ k ≤ j+1, cNorm J k (fullLeadingNormal T Q F row col Φ Y r) ≤ A₀ k)
    (hn₁ : ∀ k ≤ j+1, cNorm J k (fullCorrectionPrincipalNormal T Q F row col Φ Y r) ≤ A₁ k)
    (hv₀ : ∀ k ≤ j+1, cNorm J k (fullLeadingReconstruction T Q F row col Φ Y r) ≤ B₀ k)
    (hv₁ : ∀ k ≤ j+1, cNorm J k (fullCorrectionReconstruction T Q F row col Φ Y r) ≤ B₁ k)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n-1))} (hw : w ∈ J) :
    ‖iteratedFDeriv ℝ j (fullDerivativeAmplitude T Q F row col Φ Y r τ -
      fullLeadingPrincipalMatrix T Q F row col Φ Y r) w‖ ≤
      τ * derivativeProfile n N C A₀ A₁ B₀ B₁ j := by
  let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n-1)) ↦ phaseGradient T Q w.1 w.2.2
  let ν₀ := fullLeadingNormal T Q F row col Φ Y r
  let ν₁ := fullCorrectionPrincipalNormal T Q F row col Φ Y r
  let V₀ := fullLeadingReconstruction T Q F row col Φ Y r
  let V₁ := fullCorrectionReconstruction T Q F row col Φ Y r
  have hS := contDiffOn_fullPhase T Q hphase
  have hξs : ContDiffOn ℝ ∞ ξ Ω :=
    (phaseGradient_smooth T Q).comp
      (contDiffOn_fst.prodMk contDiffOn_snd.snd) hphase
  have hx := hJΩ hw
  have hd : (fullDerivativeAmplitude T Q F row col Φ Y r τ -
      fullLeadingPrincipalMatrix T Q F row col Φ Y r) =ᶠ[𝓝 w]
      derivativeError τ ξ ν₀ ν₁ V₀ V₁ := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact fullDerivativeAmplitude_sub_principal_eq T Q F row col Φ Y r (ne_of_gt hτ)
      ((hS.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hν₀.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hν₁.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hV₀.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hV₁.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
  rw [(hd.iteratedFDeriv (𝕜 := ℝ) (n := j)).eq_of_nhds]
  have hh := jet_error_profile (rpar := 0) (L := 1)
    (C := fun k ↦ ‖iteratedFDeriv ℝ k ξ w‖)
    (A₀ := fun k ↦ ‖iteratedFDeriv ℝ k ν₀ w‖)
    (A₁ := fun k ↦ ‖iteratedFDeriv ℝ k ν₁ w‖)
    (B₀ := fun k ↦ ‖iteratedFDeriv ℝ k V₀ w‖)
    (B₁ := fun k ↦ ‖iteratedFDeriv ℝ k V₁ w‖)
    hΩ hξs hν₀ hν₁ hV₀ hV₁ hx hτ.le hτ1 (le_refl 1)
    (fun k ↦ norm_nonneg _) (fun k ↦ norm_nonneg _) (fun k ↦ norm_nonneg _)
    (fun k ↦ norm_nonneg _) (fun k ↦ norm_nonneg _)
    (by intro k; simp only [one_pow, mul_one]; exact le_refl _)
    (by intro k; simp only [one_pow, mul_one]; exact le_refl _)
    (by intro k; simp only [one_pow, mul_one]; exact le_refl _)
    (by intro k; simp only [one_pow, mul_one]; exact le_refl _)
    (by intro k; simp only [one_pow, mul_one]; exact le_refl _) j
  simp only [one_pow, mul_one] at hh
  have hc {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → E}
      (hf : ContDiffOn ℝ ∞ f Ω) (k : ℕ) :
      ‖iteratedFDeriv ℝ k f w‖ ≤ cNorm J k f :=
    norm_iteratedFDeriv_le_cNorm_of_contDiffAt hJ
      (fun y hy ↦ (hf.contDiffAt (hΩ.mem_nhds (hJΩ hy))).of_le (by simp)) hw le_rfl
  have herr : errorProfile n N
      (fun k ↦ ‖iteratedFDeriv ℝ k ξ w‖)
      (fun k ↦ ‖iteratedFDeriv ℝ k ν₀ w‖)
      (fun k ↦ ‖iteratedFDeriv ℝ k ν₁ w‖)
      (fun k ↦ ‖iteratedFDeriv ℝ k V₀ w‖)
      (fun k ↦ ‖iteratedFDeriv ℝ k V₁ w‖) j ≤
      derivativeProfile n N
      (fun k ↦ ‖iteratedFDeriv ℝ k ξ w‖)
      (fun k ↦ ‖iteratedFDeriv ℝ k ν₀ w‖)
      (fun k ↦ ‖iteratedFDeriv ℝ k ν₁ w‖)
      (fun k ↦ ‖iteratedFDeriv ℝ k V₀ w‖)
      (fun k ↦ ‖iteratedFDeriv ℝ k V₁ w‖) j := by
    exact le_add_of_nonneg_left (productProfile_nonneg (normalTensor n N)
      (fun k ↦ norm_nonneg _) (fun k ↦ norm_nonneg _) j)
  apply hh.trans (mul_le_mul_of_nonneg_left (herr.trans ?_) hτ.le)
  exact derivativeProfile_mono_finite n N
    (C := fun k ↦ ‖iteratedFDeriv ℝ k ξ w‖)
    (A₀ := fun k ↦ ‖iteratedFDeriv ℝ k ν₀ w‖)
    (A₁ := fun k ↦ ‖iteratedFDeriv ℝ k ν₁ w‖)
    (B₀ := fun k ↦ ‖iteratedFDeriv ℝ k V₀ w‖)
    (B₁ := fun k ↦ ‖iteratedFDeriv ℝ k V₁ w‖)
    (C' := C) (A₀' := A₀) (A₁' := A₁) (B₀' := B₀) (B₁' := B₁)
    (fun k ↦ norm_nonneg _) (fun k ↦ norm_nonneg _) (fun k ↦ norm_nonneg _)
    (fun k ↦ norm_nonneg _) (fun k ↦ norm_nonneg _)
    (fun k hk ↦ (hc hξs k).trans (hξ k hk))
    (fun k hk ↦ (hc hν₀ k).trans (hn₀ k hk))
    (fun k hk ↦ (hc hν₁ k).trans (hn₁ k hk))
    (fun k hk ↦ (hc hV₀ k).trans (hv₀ k hk))
    (fun k hk ↦ (hc hV₁ k).trans (hv₁ k hk))

/-- The SAME retained finite primitive budgets give leading and raw-error
seminorm bounds, including the error's inverse-frequency factor. The constants
precede the immersion, projected frame, row, flows, scalar and frequency. Only
input orders through `m+16` are used; the original reserve fourteen is unchanged.
Consumer: the homogeneous raw bounds in
`app:ch_response:eq:current-density-lipschitz`. -/
theorem exists_retainedRawDensity_finiteBounds
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
      ∀ m : ℕ,
      (∀ j ≤ m + 1,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
          phaseGradient T Q w.1 w.2.2
        let ν := fun w ↦ principalNormal (canonicalNormalCompletion F w.1) (ξ w) (b₀ w)
        let V := fun w ↦ reconstruction F (canonicalNormalCompletion F) (fun x ↦ b₀ (x, w.2)) w.1
        cNorm J j (fun w ↦ phase T Q w.1 w.2.2) + cNorm J j b₀ +
          cNorm J j ν + cNorm J j V + cNorm J j (fun w ↦ principalMatrix (ν w) (ξ w)) ≤
            E j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      (∀ j ≤ m + 2, cNorm (closedBall a ρ) j (fullCorrectionCovector T Q F row col Φ Y r) ≤
        Γ j * (1 + cNorm K (j + 14) F + cNorm I (j + 14) r)) →
      (∀ j ≤ m + 16, cNorm K j F ≤ AF j) →
      (∀ j ≤ m + 16, cNorm I j r ≤ Ar j) →
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∀ s ≤ m,
      cNorm (closedBall a ρ) s (fullLeadingPrincipalMatrix T Q F row col Φ Y r) ≤
        2 * C s ∧
      cNorm (closedBall a ρ) s (fullDerivativeAmplitude T Q F row col Φ Y r τ -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r) ≤ τ * C s := by
  have hsmall : closedBall a ρ ⊆ closedBall a (2 * ρ) :=
    closedBall_subset_closedBall (by linarith)
  have hJΩ : closedBall a ρ ⊆ ball a (2 * ρ) := closedBall_subset_ball (by linarith)
  obtain ⟨X, hX, hξbound⟩ := exists_phaseGradient_projected_sharp_bound (N := N) T
    (isCompact_closedBall a ρ) (hsmall.trans hphase) hK hKU hball (AF 4 + 1) hγ hκ
  obtain ⟨B, hB, hcorrection⟩ := exists_fullCorrection_reconstruction_finiteJets
    (N := N) T a hρ hK hKU hball hspace hphase I hγ hκ AF Ar Γ hAF hAr hΓ
  let Pξ := fun j ↦ X j * (1 + AF (j+4))
  let A₀ := fun j ↦ E j * (1 + AF (j+14) + Ar (j+14))
  have hPξ (j) : 0 ≤ Pξ j := mul_nonneg (hX j).le (by have := hAF (j+4); positivity)
  have hA₀ (j) : 0 ≤ A₀ j := by
    have := hAF (j+14); have := hAr (j+14); have := hE j
    dsimp [A₀]; positivity
  let D := fun j ↦ derivativeProfile n N Pξ A₀ B A₀ B j
  have hD (j) : 0 ≤ D j :=
    (polynomialProfiles_nonneg n N hPξ hA₀ (fun j ↦ (hB j).le)
      hA₀ (fun j ↦ (hB j).le) j).2.2.2.2
  let C := fun j ↦ 1 + ∑ k ∈ Finset.range (j + 1), D k
  have hC (j) : 0 < C j := by
    have := Finset.sum_nonneg (s := Finset.range (j + 1)) (fun k _ ↦ hD k)
    dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro F hF hi hrank hmetric hnormal hlow
  dsimp only
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  intro row col Φ Y r Ω hΩ hflow hb₀ hb₁ m hleading hcorrectionBudget hpF hpr τ hτ hτ1
  have hFM : cNorm K 4 F ≤ AF 4 + 1 := (hpF 4 (by omega)).trans (by linarith)
  obtain ⟨hν₁, hV₁, hpν₁, hpV₁⟩ := hcorrection F hF hi hrank hmetric hnormal hlow
    row col Φ Y r Ω hΩ hflow hb₁ m hcorrectionBudget hpF hpr
  obtain ⟨hν₀, hV₀, hpν₀, hpV₀⟩ := fullLeading_finite_of_retained_budget T Q F row col Φ Y r
    a hρ (ball_subset_closedBall.trans (hspace.trans hKU)) hphase hF hi hrank
    (hb₀.mono (ball_subset_closedBall.trans hflow)) m (fun j ↦ (hE j).le) hleading hpF hpr
  have hphase' : ∀ w ∈ ball a (2 * ρ), (w.1, w.2.2) ∈ phaseDomain T :=
    fun _ hw ↦ hphase (ball_subset_closedBall hw)
  have hpξ (j : ℕ) (hj : j ≤ m+1) :
      cNorm (closedBall a ρ) j (fun w ↦ phaseGradient T Q w.1 w.2.2) ≤ Pξ j :=
    (hξbound F hF hi hrank hFM hmetric hnormal hlow j).trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) (hpF (j+4) (by omega))) (hX j).le)
  have herr (t : ℝ) (ht : 0 < t) (ht₁ : t ≤ 1) (s : ℕ) (hs : s ≤ m) :
      cNorm (closedBall a ρ) s (fullDerivativeAmplitude T Q F row col Φ Y r t -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r) ≤
        t * ∑ k ∈ Finset.range (s + 1), D k := by
    rw [Finset.mul_sum]
    apply cNorm_le_sum_of_bounds (fun k _ ↦ mul_nonneg ht.le (hD k))
    intro j hj w hw
    exact fullDerivativeError_jet_le_finite_coefficients T Q F row col Φ Y r
      (isCompact_closedBall a ρ) isOpen_ball hJΩ hphase' hν₀ hν₁ hV₀ hV₁ ht ht₁
      (fun k hk ↦ hpξ k (by omega)) (fun k hk ↦ hpν₀ k (by omega))
      (fun k hk ↦ hpν₁ k (by omega)) (fun k hk ↦ hpV₀ k (by omega))
      (fun k hk ↦ hpV₁ k (by omega)) hw
  have hraw (s : ℕ) (hs : s ≤ m) :
      cNorm (closedBall a ρ) s (fullDerivativeAmplitude T Q F row col Φ Y r 1) ≤
        ∑ k ∈ Finset.range (s + 1), D k := by
    apply cNorm_le_sum_of_bounds (fun k _ ↦ hD k)
    intro j hj w hw
    exact fullDerivativeAmplitude_jet_le_finite_coefficients T Q F row col Φ Y r
      (isCompact_closedBall a ρ) isOpen_ball hJΩ hphase' hν₀ hν₁ hV₀ hV₁ zero_lt_one le_rfl
      (fun k hk ↦ hpξ k (by omega)) (fun k hk ↦ hpν₀ k (by omega))
      (fun k hk ↦ hpν₁ k (by omega)) (fun k hk ↦ hpV₀ k (by omega))
      (fun k hk ↦ hpV₁ k (by omega)) hw
  have hrawSmooth := (contDiffOn_fullAmplitudes_of_coefficients T Q F row col Φ Y r
    isOpen_ball hphase' hν₀ hν₁ hV₀ hV₁ (one_ne_zero : (1 : ℝ) ≠ 0)).2
  have hξSmooth : ContDiffOn ℝ ∞
      (fun w ↦ phaseGradient T Q w.1 w.2.2) (ball a (2 * ρ)) :=
    (phaseGradient_smooth T Q).comp
      (contDiffOn_fst.prodMk contDiffOn_snd.snd) hphase'
  have hleadSmooth : ContDiffOn ℝ ∞
      (fullLeadingPrincipalMatrix T Q F row col Φ Y r) (ball a (2 * ρ)) := by
    apply (contDiffOn_normalTensor hξSmooth hν₀).neg.congr
    intro w _
    exact fullLeadingPrincipalMatrix_eq_tensor T Q F row col Φ Y r w
  intro s hs
  have he := herr 1 zero_lt_one le_rfl s hs
  simp only [one_mul] at he
  have hb := cNorm_add_le_of_contDiffAt (isCompact_closedBall a ρ)
    (fun w hw ↦ (hrawSmooth.contDiffAt (isOpen_ball.mem_nhds (hJΩ hw))).of_le
      (by simp : (s : ℕ∞ω) ≤ ∞))
    (fun w hw ↦ (((hrawSmooth.sub hleadSmooth).neg).contDiffAt
      (isOpen_ball.mem_nhds (hJΩ hw))).of_le (by simp : (s : ℕ∞ω) ≤ ∞))
  have heq : fullDerivativeAmplitude T Q F row col Φ Y r 1 +
      -(fullDerivativeAmplitude T Q F row col Φ Y r 1 -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r) =
      fullLeadingPrincipalMatrix T Q F row col Φ Y r := by abel
  change cNorm (closedBall a ρ) s
    (fullDerivativeAmplitude T Q F row col Φ Y r 1 +
      -(fullDerivativeAmplitude T Q F row col Φ Y r 1 -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r)) ≤
    cNorm (closedBall a ρ) s (fullDerivativeAmplitude T Q F row col Φ Y r 1) +
      cNorm (closedBall a ρ) s (-(fullDerivativeAmplitude T Q F row col Φ Y r 1 -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r)) at hb
  rw [heq, cNorm_neg] at hb
  refine ⟨hb.trans ((add_le_add (hraw s hs) he).trans (by dsimp [C]; linarith)), ?_⟩
  exact (herr τ hτ hτ1 s hs).trans
    (mul_le_mul_of_nonneg_left (by dsimp [C]; linarith) hτ.le)

end JanetCartan.CorrectedAtoms
