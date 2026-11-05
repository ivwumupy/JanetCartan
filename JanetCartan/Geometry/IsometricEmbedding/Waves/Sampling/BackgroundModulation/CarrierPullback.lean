module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.MeasuredJoint
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.KernelExtensions

/-!
# The original carrier substitution in the measured Hermitian product

The background uses the retained carrier and the modulated factor retains
its independent covector. Both have the same inverse frequency. The global
extension is used only outside the common plateau, where it changes none of
the original measured kernels.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.BackgroundModulation
open ActualCarriers FrozenMenu CurrentFullPhase RawPrimary LeadingWave LeadingWave.FullModulation
open RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open ProjectedStressFrame AmbientResponse ResponseTransfer MeasuredAmplitude
open RawPrimary.SliceBounds FourierIntegral.NormalOneHigh

variable {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- One inverse frequency and two covector slots, with the first set to
the SAME retained carrier (`app:ch_background:setup:bg-wkb-input`). -/
def retainedCarrierPair
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    (q : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))) :
    ℝ × ((Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1))) ×
      (Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))) :=
  (q.1, ((q.2.1, (q.2.2.1, extendedRetainedCarrier T a.2.1 hρ q.2.2.1)), q.2))

/-- Smoothness of the literal substitution uses the existing buffered
carrier extension (`app:ch_waves:setup:oscillatory`). -/
theorem contDiff_retainedCarrierPair {c C : ℝ} (hP : P.IsValid c C)
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius)) :
    ContDiff ℝ ∞ (retainedCarrierPair T a hρ) := by
  have hb : ContDiff ℝ ∞
      (fun q : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1))) ↦
        extendedRetainedCarrier T a.2.1 hρ q.2.2.1) :=
    (contDiff_extendedRetainedCarrier T hP a.2.1 hρ hcarrier).comp (by fun_prop)
  exact contDiff_fst.prodMk
    ((contDiff_fst.comp contDiff_snd).prodMk
      ((contDiff_fst.comp (contDiff_snd.comp contDiff_snd)).prodMk hb) |>.prodMk contDiff_snd)

variable
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
  (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1))) →
    Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
  (r : Euclidean ((m + 1) - 1) × Euclidean 3 → ℝ) (χ : Euclidean (m + 1) → ℝ)
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
  {ρ : ℝ} (hρ : 0 < ρ)

/-- The original background-modulation amplitude with the two retained
cutoffs, using the fixed carrier extension only outside its plateau. This
is the globally smooth input to the existing normalized pullback machinery
(`app:ch_background:setup:bg-wkb-input`). -/
def supportedBackgroundModulationPolynomial (τ : ℝ) (z : Euclidean 3)
    (x : Euclidean (m + 1)) (ξ : Euclidean ((m + 1) - 1)) : EuclideanSpace ℂ (Fin (m + 1)) :=
  supportedMeasuredCrossDerivativePolynomial T Q F row col Φ Y r χ a hρ τ
    (x, (z, extendedRetainedCarrier T a.2.1 hρ z)) (x, (z, ξ))

/-- Off the modulated factor's original cutoff, the complete supported
product vanishes on a neighborhood, including every joint derivative
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem supportedBackgroundModulationPolynomial_eventually_zero
    (τ : ℝ) (w : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
    (hw : w ∉ closedBall a (3 * ρ / 4)) :
    (fun q : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1))) ↦
      supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ
        q.1 q.2.2.1 q.2.1 q.2.2.2) =ᶠ[𝓝 (τ, w)] 0 := by
  have hz : (retainedAmplitudeCutoff a hρ : _ → ℝ) =ᶠ[𝓝 w] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (by
      rw [ContDiffBump.tsupport_eq]
      exact hw)
  have hs := hz.comp_tendsto (continuous_snd.tendsto (τ, w))
  filter_upwards [hs] with q hq
  change retainedAmplitudeCutoff a hρ q.2 = 0 at hq
  simp only [supportedBackgroundModulationPolynomial, supportedMeasuredCrossDerivativePolynomial,
    hq, mul_zero, zero_smul, Pi.zero_apply]

/-- The extension equals the original measured Hermitian product for
every physical point on the common measured carrier buffer, at positive or
zero inverse frequency (`app:ch_background:setup:bg-wkb-input`). -/
theorem supportedBackgroundModulationPolynomial_eq_raw
    (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    {z : Euclidean 3}
    (hz : (z, T.reference.spatialPatch z) ∈ closedBall a.2 (ρ / 4))
    (τ : ℝ) (x : Euclidean (m + 1)) (d : Euclidean ((m + 1) - 1))
    (hd : ‖d‖ ≤ ρ / 4) :
    supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ
        τ z x (T.reference.spatialPatch z + d) =
      measuredBackgroundModulationPolynomial T Q F row col Φ Y r χ
        τ z x (T.reference.spatialPatch z + d) := by
  by_cases hx : χ x = 0
  · simp only [supportedBackgroundModulationPolynomial, supportedMeasuredCrossDerivativePolynomial,
      measuredCrossDerivativePolynomial, measuredBackgroundModulationPolynomial,
      hx, Complex.ofReal_zero, zero_smul, smul_zero]
  have hz' : z ∈ closedBall a.2.1 ρ := by
    rw [← closedBall_prod_same] at hz
    exact closedBall_subset_closedBall (by linarith) hz.1
  rw [supportedBackgroundModulationPolynomial, extendedRetainedCarrier_eq T a.2.1 hρ hz',
    supportedMeasuredCrossDerivativePolynomial_eq T Q F row col Φ Y r χ a hρ τ
      (by
        simpa only [add_zero] using retained_shift_mem_plateau T a (hχ hx) hz
          (d := 0) (by simp; positivity))
      (retained_shift_mem_plateau T a (hχ hx) hz hd)]
  rfl

/-- Construct all globally supported carrier-product jets on the actual
retained family. The carrier substitution uses fixed geometry, so it spends
no additional immersion/scalar reserve. Constants precede all varying fields
and scales (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_retained_backgroundModulation_budgets
    {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall a.2.1 (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    {K : Set (Euclidean (m + 1))} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius ⊆ K)
    (hspace : closedBall a.1 (2 * ρ) ⊆ K)
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    (I : Set (Euclidean ((m + 1) - 1) × Euclidean 3))
    {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 < κ)
    (AF Ar E Γ : ℕ → ℝ) (hAF : ∀ j, 0 ≤ AF j) (hAr : ∀ j, 0 ≤ Ar j)
    (hE : ∀ j, 0 < E j) (hΓ : ∀ j, 0 < Γ j)
    (χ : Euclidean (m + 1) → ℝ) (hχ : ContDiffOn ℝ ∞ χ U) :
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (F : Euclidean (m + 1) → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      (∀ x ∈ K, ∀ v, γ * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ hlow : cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (m + 1)) < T.family.threshold,
      let Q := ⟨projectedStress F,
        contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
      ∀ (row col : Fin (m + 1))
        (Φ Y : ℝ × (Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1))) →
          Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
        (r : Euclidean ((m + 1) - 1) × Euclidean 3 → ℝ)
        (Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))),
      IsOpen Ω → closedBall a (2 * ρ) ⊆ Ω →
      ContDiffOn ℝ ∞ (fullLeadingCovector T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionCovector T Q F row col Φ Y r) Ω →
      (∀ j,
        let J := closedBall a ρ
        let b₀ := fullLeadingCovector T Q F row col Φ Y r
        let ξ := fun w : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)) ↦
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
      let f := fun q : ℝ ×
          (Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1))) ↦
        supportedBackgroundModulationPolynomial T Q F row col Φ Y r χ a hρ
          q.1 q.2.2.1 q.2.1 q.2.2.2
      ContDiff ℝ ∞ f ∧ ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w, ∀ j,
        ‖iteratedFDeriv ℝ j f (τ, w)‖ ≤ A j * L ^ (j - rpar) := by
  obtain ⟨A, hA, hjoint⟩ := exists_retained_measuredCrossDerivativePolynomial_budgets
    (N := N) T a hρ hK hKU hball hspace hphase I hγ hκ AF Ar E Γ hAF hAr hE hΓ χ hχ
  let sub := retainedCarrierPair T a hρ
  have hs : ContDiff ℝ ∞ sub := contDiff_retainedCarrierPair T hP a hρ hcarrier
  let J := Icc (-1 : ℝ) 1 ×ˢ closedBall a ρ
  have hJ : IsCompact J := isCompact_Icc.prod (isCompact_closedBall _ _)
  let b := fun j ↦ cNorm J j sub
  have hb (j) : 0 ≤ b j := cNorm_nonneg _ _ _
  let B := compositionBudget A b
  have hB (j) : 0 ≤ B j := compositionBudget_nonneg (fun j ↦ (hA j).le) hb j
  refine ⟨fun j ↦ 1 + B j, fun j ↦ by linarith [hB j], ?_⟩
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hb₀ hb₁
    hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨_, _, hss, hsj⟩ := hjoint F hF hi hrank hmetric hnormal hlow row col Φ Y r
    Ω hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  let f := fun q : ℝ ×
      ((Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1))) ×
        (Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))) ↦
    supportedMeasuredCrossDerivativePolynomial T Q F row col Φ Y r χ a hρ q.1 q.2.1 q.2.2
  change ContDiff ℝ ∞ (f ∘ sub) ∧ _
  refine ⟨hss.comp hs, ?_⟩
  intro τ hτ w j
  change ‖iteratedFDeriv ℝ j (f ∘ sub) (τ, w)‖ ≤ _
  by_cases hw : w ∈ closedBall a ρ
  · have hinner (k) : ‖iteratedFDeriv ℝ k sub (τ, w)‖ ≤ b k :=
      norm_iteratedFDeriv_le_cNorm hJ (hs.of_le (by simp)) ⟨hτ, hw⟩ le_rfl
    have houter (k) : ‖iteratedFDeriv ℝ k f (sub (τ, w))‖ ≤ A k * L ^ (k - rpar) :=
      hsj τ hτ _ _ k
    exact (norm_iteratedFDeriv_comp_le_sliceGrade hs.contDiffAt hss.contDiffAt
      (fun k _ ↦ (hA k).le) hL (fun k _ ↦ houter k) (fun k _ _ ↦ hinner k)).trans
      (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith)
        (pow_nonneg (zero_le_one.trans hL) _))
  · have hz := supportedBackgroundModulationPolynomial_eventually_zero
      T Q F row col Φ Y r χ a hρ τ w
      (fun hh ↦ hw (closedBall_subset_closedBall (by linarith) hh))
    change (f ∘ sub) =ᶠ[𝓝 (τ, w)] 0 at hz
    rw [(hz.iteratedFDeriv ℝ j).eq_of_nhds]
    simp only [Pi.zero_apply, iteratedFDeriv_zero, norm_zero]
    exact mul_nonneg (by linarith [hB j]) (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.Sampling.BackgroundModulation
