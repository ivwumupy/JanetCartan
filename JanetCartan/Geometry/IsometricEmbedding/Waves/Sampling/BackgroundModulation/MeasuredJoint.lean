module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundModulation.StressBudgets
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.Measurement

/-!
# Measured joint Hermitian product on the retained family

Apply the actual projected-stress budget to the same two raw polynomial
factors. The existing retained amplitude cutoff on each factor gives a
globally smooth extension with a common plateau. No kernel or normal bound
is an input, and the constants precede all current fields and history scales.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.BackgroundModulation
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer MeasuredAmplitude

/-- Multiplication by the two original retained cutoffs extends the joint
product without spending its reserve (`app:ch_waves:setup:oscillatory`). -/
private theorem supported_pair_bounds
    {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [HasContDiffBump X]
    (a : X) {ρ : ℝ} (hρ : 0 < ρ) (cutoff : ContDiffBump a) (hout : cutoff.rOut < ρ)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ D : ℕ → ℝ, (∀ j, 0 ≤ D j) ∧
      ∀ (f : ℝ × (X × X) → V),
      ContDiffOn ℝ ∞ f (univ ×ˢ (ball a (2 * ρ) ×ˢ ball a (2 * ρ))) →
      ∀ (L : ℝ) (rpar : ℕ), 1 ≤ L →
      (∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w₀ ∈ closedBall a ρ, ∀ w₁ ∈ closedBall a ρ, ∀ j,
        ‖iteratedFDeriv ℝ j f (τ, (w₀, w₁))‖ ≤ A j * L ^ (j - rpar)) →
      let g := fun q : ℝ × (X × X) ↦ (cutoff q.2.1 * cutoff q.2.2) • f q
      ContDiff ℝ ∞ g ∧ ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w₀ w₁, ∀ j,
        ‖iteratedFDeriv ℝ j g (τ, (w₀, w₁))‖ ≤ D j * L ^ (j - rpar) := by
  let mask := fun w : X × X ↦ cutoff w.1 * cutoff w.2
  have hm : ContDiff ℝ ∞ mask :=
    (cutoff.contDiff.comp contDiff_fst).mul (cutoff.contDiff.comp contDiff_snd)
  let b := fun j ↦ cNorm (closedBall (a, a) ρ) j mask
  have hb (j) : 0 ≤ b j := cNorm_nonneg _ _ _
  let sm := ContinuousLinearMap.lsmul ℝ ℝ (E := V)
  refine ⟨productProfile sm b A, productProfile_nonneg sm hb hA, ?_⟩
  intro f hf L rpar hL hfjet
  let g := fun q : ℝ × (X × X) ↦ mask q.2 • f q
  have hmask : ContDiff ℝ ∞ (fun q : ℝ × (X × X) ↦ mask q.2) := hm.comp contDiff_snd
  have hzero (τ : ℝ) (w : X × X) (hw : w ∉ closedBall (a, a) cutoff.rOut) :
      g =ᶠ[𝓝 (τ, w)] 0 := by
    rw [← closedBall_prod_same, mem_prod] at hw
    have hz (x : X) (hx : x ∉ closedBall a cutoff.rOut) :
        (cutoff : X → ℝ) =ᶠ[𝓝 x] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (by simpa only [cutoff.tsupport_eq] using hx)
    by_cases hw₀ : w.1 ∈ closedBall a cutoff.rOut
    · have hz₁ := (hz w.2 (fun hh ↦ hw ⟨hw₀, hh⟩)).comp_tendsto
        ((continuous_snd.comp continuous_snd).tendsto (τ, w))
      filter_upwards [hz₁] with q hq
      change cutoff q.2.2 = 0 at hq
      simp only [g, mask, hq, mul_zero, zero_smul, Pi.zero_apply]
    · have hz₀ := (hz w.1 hw₀).comp_tendsto
        ((continuous_fst.comp continuous_snd).tendsto (τ, w))
      filter_upwards [hz₀] with q hq
      change cutoff q.2.1 = 0 at hq
      simp only [g, mask, hq, zero_mul, zero_smul, Pi.zero_apply]
  have hg : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    rintro ⟨τ, w⟩
    by_cases hw : w ∈ closedBall (a, a) cutoff.rOut
    · rw [← closedBall_prod_same] at hw
      exact (hmask.contDiffOn.smul hf).contDiffAt
        ((isOpen_univ.prod (isOpen_ball.prod isOpen_ball)).mem_nhds
          ⟨mem_univ _, closedBall_subset_ball (by linarith) hw.1,
            closedBall_subset_ball (by linarith) hw.2⟩)
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero τ w hw)
  refine ⟨hg, ?_⟩
  intro τ hτ w₀ w₁ j
  by_cases hw : (w₀, w₁) ∈ closedBall (a, a) ρ
  · have hw' := hw
    rw [← closedBall_prod_same] at hw'
    have hbjet (k) : ‖iteratedFDeriv ℝ k (fun q : ℝ × (X × X) ↦ mask q.2)
        (τ, (w₀, w₁))‖ ≤ b k * L ^ (k - rpar) := by
      let pr := ContinuousLinearMap.snd ℝ ℝ (X × X)
      have hh := NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le pr
        (f := mask) (x := (τ, (w₀, w₁))) isOpen_univ hm.contDiffOn (mem_univ _) k
      exact ((hh.trans (mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le _ _ _)))).trans
        (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
          (hm.of_le (by simp)) hw le_rfl)).trans
        (le_mul_of_one_le_right (hb k) (one_le_pow₀ hL))
    exact jet_bilinear_le sm (isOpen_univ.prod (isOpen_ball.prod isOpen_ball))
      hmask.contDiffOn hf
      ⟨mem_univ _, closedBall_subset_ball (by linarith) hw'.1,
        closedBall_subset_ball (by linarith) hw'.2⟩ hL hb hA hbjet
      (hfjet τ hτ w₀ hw'.1 w₁ hw'.2) j
  · have hz := hzero τ (w₀, w₁) (fun hh ↦ hw (closedBall_subset_closedBall hout.le hh))
    rw [(hz.iteratedFDeriv ℝ j).eq_of_nhds]
    simp only [Pi.zero_apply, iteratedFDeriv_zero, norm_zero]
    exact mul_nonneg (productProfile_nonneg sm hb hA j) (pow_nonneg (zero_le_one.trans hL) _)

/-- The joint Hermitian tensor is measured at the modulated physical point;
fixed coordinate pullback and evaluation preserve its reserve
(`app:ch_background:setup:bg-wkb-input`). -/
private theorem measured_pair_bounds
    {X E V G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (a : X) {ρ : ℝ} (hρ : 0 < ρ) (p : X →L[ℝ] E) (hp : ‖p‖ ≤ 1)
    {O : Set E} (hO : IsOpen O) (hmap : MapsTo p (ball a (2 * ρ)) O)
    (meas : E → V →L[ℝ] G) (poly : ℝ × (X × X) → V)
    (hms : ContDiffOn ℝ ∞ meas O)
    (hs : ContDiffOn ℝ ∞ poly (univ ×ˢ (ball a (2 * ρ) ×ˢ ball a (2 * ρ))))
    {A B : ℕ → ℝ} (hA : ∀ j, 0 ≤ A j) (hB : ∀ j, 0 ≤ B j)
    {L : ℝ} {rpar : ℕ} (hL : 1 ≤ L)
    (hmj : ∀ w ∈ closedBall a ρ, ∀ j,
      ‖iteratedFDeriv ℝ j meas (p w)‖ ≤ B j * L ^ (j - rpar))
    (hj : ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w₀ ∈ closedBall a ρ,
      ∀ w₁ ∈ closedBall a ρ, ∀ j,
        ‖iteratedFDeriv ℝ j poly (τ, (w₀, w₁))‖ ≤ A j * L ^ (j - rpar)) :
    let measured := fun q : ℝ × (X × X) ↦ meas (p q.2.2) (poly q)
    ContDiffOn ℝ ∞ measured (univ ×ˢ (ball a (2 * ρ) ×ˢ ball a (2 * ρ))) ∧
      ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w₀ ∈ closedBall a ρ,
        ∀ w₁ ∈ closedBall a ρ, ∀ j,
          ‖iteratedFDeriv ℝ j measured (τ, (w₀, w₁))‖ ≤
            productProfile (ContinuousLinearMap.apply ℝ G (E' := V)).flip B A j *
              L ^ (j - rpar) := by
  let pr : ℝ × (X × X) →L[ℝ] E :=
    p.comp ((ContinuousLinearMap.snd ℝ X X).comp (ContinuousLinearMap.snd ℝ ℝ (X × X)))
  have hpr : ‖pr‖ ≤ 1 := by
    apply pr.opNorm_le_bound zero_le_one
    intro q
    exact (p.le_opNorm q.2.2).trans ((mul_le_of_le_one_left (norm_nonneg _) hp).trans
      ((norm_snd_le q.2).trans (by simpa using norm_snd_le q)))
  have hm : ContDiffOn ℝ ∞ (meas ∘ pr)
      (univ ×ˢ (ball a (2 * ρ) ×ˢ ball a (2 * ρ))) :=
    hms.comp pr.contDiff.contDiffOn (fun _ h ↦ hmap h.2.2)
  refine ⟨hm.clm_apply hs, ?_⟩
  intro τ hτ w₀ hw₀ w₁ hw₁ j
  have hmjet (k) : ‖iteratedFDeriv ℝ k (meas ∘ pr) (τ, (w₀, w₁))‖ ≤
      B k * L ^ (k - rpar) :=
    ((NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le pr
      (f := meas) (x := (τ, (w₀, w₁))) hO hms
      (hmap (closedBall_subset_ball (by linarith) hw₁)) k).trans
      (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hpr))).trans
      (hmj w₁ hw₁ k)
  exact jet_bilinear_le (ContinuousLinearMap.apply ℝ G (E' := V)).flip
    (isOpen_univ.prod (isOpen_ball.prod isOpen_ball)) hm hs
    ⟨mem_univ _, closedBall_subset_ball (by linarith) hw₀,
      closedBall_subset_ball (by linarith) hw₁⟩ hL hB hA hmjet
    (hj τ hτ w₀ hw₀ w₁ hw₁) j

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (χ : Euclidean n → ℝ)

/-- The actual stress measurement of the joint polynomial, using the
physical point in its modulated slot (`app:ch_background:setup:bg-wkb-input`). -/
def measuredCrossDerivativePolynomial (τ : ℝ)
    (w₀ w₁ : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) :
    EuclideanSpace ℂ (Fin n) :=
  (χ w₁.1 : ℂ) • complexStressContraction (Q.1 w₁.1)
    (crossDerivativePolynomial T Q F row col Φ Y r τ w₀ w₁)

/-- The same fixed amplitude cutoff on both factors extends their measured
product. On the common plateau it is the original product
(`app:ch_waves:setup:oscillatory`). -/
def supportedMeasuredCrossDerivativePolynomial
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) {ρ : ℝ} (hρ : 0 < ρ)
    (τ : ℝ) (w₀ w₁ : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) :
    EuclideanSpace ℂ (Fin n) :=
  (retainedAmplitudeCutoff a hρ w₀ * retainedAmplitudeCutoff a hρ w₁) •
    measuredCrossDerivativePolynomial T Q F row col Φ Y r χ τ w₀ w₁

/-- Exact agreement for both original covectors, including inverse
frequency zero (`app:ch_background:setup:bg-wkb-input`). -/
theorem supportedMeasuredCrossDerivativePolynomial_eq
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) {ρ : ℝ} (hρ : 0 < ρ)
    (τ : ℝ) {w₀ w₁ : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw₀ : w₀ ∈ closedBall a (ρ / 2)) (hw₁ : w₁ ∈ closedBall a (ρ / 2)) :
    supportedMeasuredCrossDerivativePolynomial T Q F row col Φ Y r χ a hρ τ w₀ w₁ =
      measuredCrossDerivativePolynomial T Q F row col Φ Y r χ τ w₀ w₁ := by
  rw [supportedMeasuredCrossDerivativePolynomial, retainedAmplitudeCutoff_one a hρ hw₀,
    retainedAmplitudeCutoff_one a hρ hw₁, one_mul, one_smul]

/-- Construct the actual measured Hermitian product and all its supported
joint jets from the retained leading/correction outputs and the immersion
profile. Constants precede the immersion, scalar, scales, colors and finite
history (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_retained_measuredCrossDerivativePolynomial_budgets
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
    (χ : Euclidean n → ℝ) (hχ : ContDiffOn ℝ ∞ χ U) :
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
      let measured := fun q : ℝ ×
          ((Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ×
            (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))) ↦
        measuredCrossDerivativePolynomial T Q F row col Φ Y r χ q.1 q.2.1 q.2.2
      let supported := fun q : ℝ ×
          ((Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ×
            (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))) ↦
        supportedMeasuredCrossDerivativePolynomial T Q F row col Φ Y r χ a hρ q.1 q.2.1 q.2.2
      ContDiffOn ℝ ∞ measured (univ ×ˢ (ball a (2 * ρ) ×ˢ ball a (2 * ρ))) ∧
        (∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w₀ ∈ closedBall a ρ, ∀ w₁ ∈ closedBall a ρ, ∀ j,
          ‖iteratedFDeriv ℝ j measured (τ, (w₀, w₁))‖ ≤ A j * L ^ (j - rpar)) ∧
        ContDiff ℝ ∞ supported ∧ ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w₀ w₁, ∀ j,
          ‖iteratedFDeriv ℝ j supported (τ, (w₀, w₁))‖ ≤ A j * L ^ (j - rpar) := by
  obtain ⟨A, hA, hpoly⟩ := exists_retained_crossDerivativePolynomial_budgets
    (N := N) T a hρ hK hKU hball hspace hphase I hγ hκ AF Ar E Γ hAF hAr hE hΓ
  have hsmall : closedBall a.1 ρ ⊆ K :=
    (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans hspace
  obtain ⟨B, hB, hmeas⟩ := exists_projectedStressMeasurement_jet_budgets
    (N := N) hU a.1 hρ hK hKU hsmall hγ hκ AF hAF χ hχ
  let ev := (ContinuousLinearMap.apply ℝ (EuclideanSpace ℂ (Fin n))
    (E' := Matrix (Fin n) (Fin n) ℂ)).flip
  let C := productProfile ev B A
  have hC (j) : 0 ≤ C j := productProfile_nonneg ev (fun j ↦ (hB j).le)
    (fun j ↦ (hA j).le) j
  obtain ⟨D, hD, hsupport⟩ := supported_pair_bounds (V := EuclideanSpace ℂ (Fin n)) a hρ (retainedAmplitudeCutoff a hρ)
    (by change 3 * ρ / 4 < ρ; linarith) C hC
  refine ⟨fun j ↦ 1 + C j + D j, fun j ↦ by linarith [hC j, hD j], ?_⟩
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hb₀ hb₁
    hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨hs, hj⟩ := hpoly F hF hi hrank hmetric hnormal hlow row col Φ Y r
    Ω hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨hms, hmj⟩ := hmeas F hF hi hrank hmetric hnormal RF rpar L hL
    (by omega) (by omega) hpF
  let poly := fun q : ℝ ×
      ((Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ×
        (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))) ↦
    crossDerivativePolynomial T Q F row col Φ Y r q.1 q.2.1 q.2.2
  let meas := fun x ↦ χ x • (complexStressContraction (projectedStress F x)).restrictScalars ℝ
  let measured := fun q : ℝ ×
      ((Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ×
        (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))) ↦ meas q.2.2.1 (poly q)
  have hmap : MapsTo (ContinuousLinearMap.fst ℝ (Euclidean n)
      (Euclidean 3 × Euclidean (n - 1))) (ball a (2 * ρ)) U := by
    intro w hw
    have hw' := ball_subset_closedBall hw
    rw [← closedBall_prod_same] at hw'
    exact hKU (hspace hw'.1)
  have hmj' (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
      (hw : w ∈ closedBall a ρ) (j : ℕ) :
      ‖iteratedFDeriv ℝ j meas w.1‖ ≤ B j * L ^ (j - rpar) := by
    rw [← closedBall_prod_same] at hw
    exact hmj w.1 hw.1 j
  obtain ⟨hmeasured, hlocal⟩ := measured_pair_bounds a hρ
    (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean 3 × Euclidean (n - 1)))
    (ContinuousLinearMap.norm_fst_le _ _ _) hU hmap meas poly hms hs
    (fun j ↦ (hA j).le) (fun j ↦ (hB j).le) hL hmj' hj
  have heq : (fun q : ℝ ×
      ((Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ×
        (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))) ↦
      measuredCrossDerivativePolynomial T Q F row col Φ Y r χ q.1 q.2.1 q.2.2) = measured := by
    funext q
    change (χ q.2.2.1 : ℂ) • complexStressContraction (projectedStress F q.2.2.1) (poly q) =
      χ q.2.2.1 • complexStressContraction (projectedStress F q.2.2.1) (poly q)
    simp
  change ContDiffOn ℝ ∞ _ _ ∧ _
  dsimp only [supportedMeasuredCrossDerivativePolynomial]
  rw [heq]
  obtain ⟨hss, hsj⟩ := hsupport measured hmeasured L rpar hL hlocal
  refine ⟨hmeasured, ?_, hss, ?_⟩
  · intro τ hτ w₀ hw₀ w₁ hw₁ j
    exact (hlocal τ hτ w₀ hw₀ w₁ hw₁ j).trans (mul_le_mul_of_nonneg_right
      (by linarith [hD j]) (pow_nonneg (zero_le_one.trans hL) _))
  · intro τ hτ w₀ w₁ j
    exact (hsj τ hτ w₀ w₁ j).trans (mul_le_mul_of_nonneg_right
      (by linarith [hC j]) (pow_nonneg (zero_le_one.trans hL) _))

end JanetCartan.Sampling.BackgroundModulation
