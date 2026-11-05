module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedBackground.JointBudgets
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.Measurement

/-!
# Compact extension of the retained background polynomial

The auxiliary working-ball cutoff is one on its fixed inner plateau. Thus it
preserves the prescribed spatial/carrier measurements whenever their support
lies on that plateau. It supplies a globally smooth tensor from the original
local polynomial. The carrier pullback must prove this plateau condition on
the original measurement; the auxiliary extension does not replace it.

Consumer: `app:ch_waves:eq:background-quadrature`, including its L2-valued
Taylor expansion, physical rough bound and adjacent transport comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.RetainedBackground
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open MeasuredAmplitude

/-- The fixed working-ball extension, multiplied by the prescribed physical
measurement. It is a tensor cutoff, not a cutoff inside the wave differential
(`app:ch_waves:eq:background-quadrature`). -/
def supportedJointTensor {n : ℕ}
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) {ρ : ℝ} (hρ : 0 < ρ)
    (χ : Euclidean n → ℝ)
    (H : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) → Matrix (Fin n) (Fin n) ℝ)
    (q : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))) : Matrix (Fin n) (Fin n) ℝ :=
  (retainedAmplitudeCutoff a hρ q.2 * χ q.2.1) • H q

/-- The auxiliary extension preserves the original physical tensor exactly
on the retained plateau (`app:ch_waves:eq:background-quadrature`). -/
theorem supportedJointTensor_eq {n : ℕ}
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) {ρ : ℝ} (hρ : 0 < ρ)
    (χ : Euclidean n → ℝ)
    (H : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℝ) {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : w ∈ closedBall a (ρ / 2)) :
    supportedJointTensor a hρ χ H (τ, w) = χ w.1 • H (τ, w) := by
  rw [supportedJointTensor, retainedAmplitudeCutoff_one a hρ hw, one_mul]

/-- The compact extension has a common physical support before all fields,
frequencies and carrier labels (`app:ch_waves:eq:background-quadrature`). -/
theorem supportedJointTensor_eq_zero_off_physical {n : ℕ}
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) {ρ : ℝ} (hρ : 0 < ρ)
    (χ : Euclidean n → ℝ)
    (H : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) → Matrix (Fin n) (Fin n) ℝ)
    (τ : ℝ) (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    (hw : w.1 ∉ closedBall a.1 (3 * ρ / 4)) :
    supportedJointTensor a hρ χ H (τ, w) = 0 := by
  have hh : w ∉ closedBall a (3 * ρ / 4) := by
    rw [← closedBall_prod_same]
    exact fun h ↦ hw h.1
  have hz : retainedAmplitudeCutoff a hρ w = 0 :=
    image_eq_zero_of_notMem_tsupport (by
      simpa only [ContDiffBump.tsupport_eq, retainedAmplitudeCutoff] using hh)
  simp [supportedJointTensor, hz]

/-- Fixed-cutoff multiplication preserves the retained joint reserve. The
only varying tensor inputs are the local smoothness and jets produced by
`exists_retained_backgroundPolynomial_budgets`, applied below. This proves
global regularity rather than assuming an L2 regularity package
(`app:ch_waves:eq:background-quadrature`). -/
theorem exists_supportedJointTensor_budgets {n : ℕ}
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) {ρ : ℝ} (hρ : 0 < ρ)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ B : ℕ → ℝ, (∀ j, 0 < B j) ∧
      ∀ (H : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) →
        Matrix (Fin n) (Fin n) ℝ),
      ContDiffOn ℝ ∞ H (univ ×ˢ ball a (2 * ρ)) →
      ∀ (L : ℝ) (rpar : ℕ), 1 ≤ L →
      (∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w ∈ closedBall a ρ, ∀ j,
        ‖iteratedFDeriv ℝ j H (τ, w)‖ ≤ A j * L ^ (j - rpar)) →
      ContDiff ℝ ∞ (supportedJointTensor a hρ χ H) ∧
        ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w, ∀ j,
          ‖iteratedFDeriv ℝ j (supportedJointTensor a hρ χ H) (τ, w)‖ ≤
            B j * L ^ (j - rpar) := by
  let mask := fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
    retainedAmplitudeCutoff a hρ w * χ w.1
  have hmask : ContDiff ℝ ∞ mask :=
    (retainedAmplitudeCutoff a hρ).contDiff.mul (hχ.comp contDiff_fst)
  let b := fun j ↦ cNorm (closedBall a ρ) j mask
  have hb (j) : 0 ≤ b j := cNorm_nonneg _ _ _
  let B := productProfile (ContinuousLinearMap.lsmul ℝ ℝ
    (E := Matrix (Fin n) (Fin n) ℝ)) b A
  have hB (j) : 0 ≤ B j := productProfile_nonneg _ hb hA j
  refine ⟨fun j ↦ 1 + B j, fun j ↦ by linarith [hB j], ?_⟩
  intro H hH L rpar hL hj
  have hms : ContDiff ℝ ∞ (fun q : ℝ ×
      (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ↦ mask q.2) :=
    hmask.comp contDiff_snd
  have hzero (τ : ℝ) (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
      (hw : w ∉ closedBall a (3 * ρ / 4)) :
      supportedJointTensor a hρ χ H =ᶠ[𝓝 (τ, w)] 0 := by
    have hz : (retainedAmplitudeCutoff a hρ : _ → ℝ) =ᶠ[𝓝 w] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (by
        simpa only [ContDiffBump.tsupport_eq, retainedAmplitudeCutoff] using hw)
    filter_upwards [hz.comp_tendsto (continuous_snd.tendsto (τ, w))] with q hq
    change retainedAmplitudeCutoff a hρ q.2 = 0 at hq
    simp only [supportedJointTensor, hq, zero_mul, zero_smul, Pi.zero_apply]
  have hs : ContDiff ℝ ∞ (supportedJointTensor a hρ χ H) := by
    rw [contDiff_iff_contDiffAt]
    rintro ⟨τ, w⟩
    by_cases hw : w ∈ closedBall a (3 * ρ / 4)
    · exact (hms.contDiffOn.smul hH).contDiffAt
        ((isOpen_univ.prod isOpen_ball).mem_nhds
          ⟨mem_univ _, closedBall_subset_ball (by linarith) hw⟩)
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero τ w hw)
  refine ⟨hs, ?_⟩
  intro τ hτ w hwj
  by_cases hw : w ∈ closedBall a ρ
  · have hmj (k : ℕ) : ‖iteratedFDeriv ℝ k
        (fun q : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ↦ mask q.2)
          (τ, w)‖ ≤ b k * L ^ (k - rpar) := by
      let pr := ContinuousLinearMap.snd ℝ ℝ (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
      have hh := norm_iteratedFDeriv_preAffine_le pr 0 isOpen_univ hmask.contDiffOn
        (x := (τ, w)) (mem_univ _) k
      have hh' : ‖iteratedFDeriv ℝ k
          (fun q : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ↦ mask q.2)
            (τ, w)‖ ≤ ‖iteratedFDeriv ℝ k mask w‖ := by
        simpa [pr] using hh.trans (mul_le_of_le_one_right (norm_nonneg _)
          (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le _ _ _)))
      exact (hh'.trans (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
        (hmask.of_le (by simp)) hw le_rfl)).trans
          (le_mul_of_one_le_right (hb k) (one_le_pow₀ hL))
    have hw' : (τ, w) ∈ (univ : Set ℝ) ×ˢ ball a (2 * ρ) :=
      ⟨mem_univ _, closedBall_subset_ball (by linarith) hw⟩
    have hbound := jet_bilinear_le (ContinuousLinearMap.lsmul ℝ ℝ
        (E := Matrix (Fin n) (Fin n) ℝ)) (isOpen_univ.prod isOpen_ball)
      hms.contDiffOn hH hw' hL hb hA hmj (hj τ hτ w hw) hwj
    exact hbound.trans (mul_le_mul_of_nonneg_right
      (show B hwj ≤ 1 + B hwj by linarith) (pow_nonneg (zero_le_one.trans hL) _))
  · have hz := hzero τ w (fun h ↦ hw (closedBall_subset_closedBall (by linarith) h))
    rw [(hz.iteratedFDeriv ℝ hwj).eq_of_nhds]
    simp only [Pi.zero_apply, iteratedFDeriv_zero, norm_zero]
    exact mul_nonneg (by linarith [hB hwj]) (pow_nonneg (zero_le_one.trans hL) _)

/-- Construct the globally smooth compact tensor from the original retained
profiles. The cutoff constants precede the varying immersion, scalar, inverse
frequency and scale; its plateau identity preserves the physical measurement
when restricted to the retained carrier graph
(`app:ch_waves:eq:background-quadrature`). -/
theorem exists_retained_supportedBackground_budgets
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
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) :
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
      let H := fun q : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ↦
        backgroundPolynomial T Q F row col Φ Y r q.1 q.2
      ContDiff ℝ ∞ (supportedJointTensor a hρ χ H) ∧
        ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w, ∀ j,
          ‖iteratedFDeriv ℝ j (supportedJointTensor a hρ χ H) (τ, w)‖ ≤
            A j * L ^ (j - rpar) := by
  obtain ⟨A, hA, hraw⟩ := exists_retained_backgroundPolynomial_budgets
    (N := N) T a hρ hK hKU hball hspace hphase I hγ hκ AF Ar E Γ hAF hAr hE hΓ
  obtain ⟨B, hB, hcut⟩ := exists_supportedJointTensor_budgets a hρ χ hχ A
    (fun j ↦ (hA j).le)
  refine ⟨B, hB, ?_⟩
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hb₀ hb₁
    hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨hs, hj⟩ := hraw F hF hi hrank hmetric hnormal hlow row col Φ Y r
    Ω hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  exact hcut _ hs L rpar hL hj

end JanetCartan.Sampling.RetainedBackground
