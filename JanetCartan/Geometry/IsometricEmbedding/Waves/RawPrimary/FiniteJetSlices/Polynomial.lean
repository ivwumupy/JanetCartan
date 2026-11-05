module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Assembly

/-!
# Finite coefficient jets of the literal derivative polynomial

The consumer is the finite-jet raw slice estimate in
`app:ch_waves:eq:individual-raw-slice`. Only coefficient orders through `j+1`
enter the polynomial at order `j`; no all-order bounded profile is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.FiniteJetSlices
open AmplitudeGrades AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseTransfer AmbientResponse

private theorem productProfile_mono_finite
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) {A C A' C' : ℕ → ℝ} {j : ℕ}
    (hA : ∀ k, 0 ≤ A k) (hC : ∀ k, 0 ≤ C k)
    (ha : ∀ k ≤ j, A k ≤ A' k) (hc : ∀ k ≤ j, C k ≤ C' k) :
    productProfile B A C j ≤ productProfile B A' C' j := by
  unfold productProfile
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg B)
  apply Finset.sum_le_sum
  intro k hk
  have hk' : k ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  exact mul_le_mul (mul_le_mul_of_nonneg_left (ha k hk') (Nat.cast_nonneg _))
    (hc (j-k) (Nat.sub_le _ _)) (hC _) (mul_nonneg (Nat.cast_nonneg _)
      ((hA k).trans (ha k hk')))

/-- At order `j` the exact derivative polynomial depends on its five
coefficient profiles only through `j+1`. Consumer: the finite primitive
amplitude assembly (`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem derivativeProfile_mono_finite (n N : ℕ)
    {C A₀ A₁ B₀ B₁ C' A₀' A₁' B₀' B₁' : ℕ → ℝ} {j : ℕ}
    (hC : ∀ k, 0 ≤ C k) (hA₀ : ∀ k, 0 ≤ A₀ k)
    (hA₁ : ∀ k, 0 ≤ A₁ k) (hB₀ : ∀ k, 0 ≤ B₀ k) (hB₁ : ∀ k, 0 ≤ B₁ k)
    (hc : ∀ k ≤ j + 1, C k ≤ C' k) (ha₀ : ∀ k ≤ j + 1, A₀ k ≤ A₀' k)
    (ha₁ : ∀ k ≤ j + 1, A₁ k ≤ A₁' k) (hb₀ : ∀ k ≤ j + 1, B₀ k ≤ B₀' k)
    (hb₁ : ∀ k ≤ j + 1, B₁ k ≤ B₁' k) :
    derivativeProfile n N C A₀ A₁ B₀ B₁ j ≤
      derivativeProfile n N C' A₀' A₁' B₀' B₁' j := by
  have ht₀ := productProfile_mono_finite (j := j) (normalTensor n N) hC hA₀
    (fun k hk ↦ hc k (by omega)) (fun k hk ↦ ha₀ k (by omega))
  have ht₁ := productProfile_mono_finite (j := j) (normalTensor n N) hC hA₁
    (fun k hk ↦ hc k (by omega)) (fun k hk ↦ ha₁ k (by omega))
  have hv₀ := productProfile_mono_finite (j := j) (normalTensor n N) hC hB₀
    (fun k hk ↦ hc k (by omega)) (fun k hk ↦ hb₀ k (by omega))
  have hv₁ := productProfile_mono_finite (j := j) (normalTensor n N) hC hB₁
    (fun k hk ↦ hc k (by omega)) (fun k hk ↦ hb₁ k (by omega))
  have hd₀ := mul_le_mul_of_nonneg_left (ha₀ (j+1) le_rfl) (norm_nonneg (Polynomial.differentialMatrix n N))
  have hd₁ := mul_le_mul_of_nonneg_left (ha₁ (j+1) le_rfl) (norm_nonneg (Polynomial.differentialMatrix n N))
  have he₀ := mul_le_mul_of_nonneg_left (hb₀ (j+1) le_rfl) (norm_nonneg (Polynomial.differentialMatrix n N))
  have he₁ := mul_le_mul_of_nonneg_left (hb₁ (j+1) le_rfl) (norm_nonneg (Polynomial.differentialMatrix n N))
  exact add_le_add ht₀ (add_le_add (add_le_add
    (add_le_add ht₁ (add_le_add hv₀ hd₀))
    (add_le_add (add_le_add hv₁ hd₁) he₀)) he₁)

/-- The SAME full derivative amplitude at order `j` from bounded coefficient
jets through `j+1`. The auxiliary profiles in the proof are the actual pointwise jet norms,
which are bounded by the finite `cNorm`s using finite monotonicity. Thus no bounded
all-order hypothesis is introduced (`app:ch_waves:eq:individual-raw-slice`). -/
theorem fullDerivativeAmplitude_jet_le_finite_coefficients
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
    ‖iteratedFDeriv ℝ j (fullDerivativeAmplitude T Q F row col Φ Y r τ) w‖ ≤
      derivativeProfile n N C A₀ A₁ B₀ B₁ j := by
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
  have hd : fullDerivativeAmplitude T Q F row col Φ Y r τ =ᶠ[𝓝 w]
      derivativePolynomial τ ξ ν₀ ν₁ V₀ V₁ := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact fullDerivativeAmplitude_eq_polynomial T Q F row col Φ Y r (ne_of_gt hτ)
      ((hS.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hν₀.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hν₁.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hV₀.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hV₁.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
  rw [(hd.iteratedFDeriv (𝕜 := ℝ) (n := j)).eq_of_nhds]
  have hh := jet_derivative_profile (rpar := 0) (L := 1)
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
  exact hh.trans (derivativeProfile_mono_finite n N
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
    (fun k hk ↦ (hc hV₁ k).trans (hv₁ k hk)))

end JanetCartan.RawPrimary.FiniteJetSlices
