module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.RetainedBudgets
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CanonicalAmplitude
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The nonzero measured polynomial on the retained raw fields

Apply the fixed physical measurement and complex-linear tensor contraction to
the original WKB polynomial. Both quadratures and the zero principal endpoint
are retained. The constants precede the varying immersion, scalar, raw fields,
scale and frequency. The normalized carrier/input pullback and support choices
remain separate obligations of the full normal-data construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.MeasuredAmplitude
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial RawKernel
open LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ProjectedStressFrame AmbientResponse ResponseTransfer
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets

/-- A fixed cutoff inside one retained raw working ball. Its plateau is
used after the existing buffered refinement, so no original measured kernel
is changed where the parent proves agreement
(`app:ch_waves:setup:oscillatory`). -/
def retainedAmplitudeCutoff {n : ℕ}
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) : ContDiffBump a :=
  ⟨ρ / 2, 3 * ρ / 4, by positivity, by linarith⟩

/-- Exact plateau for the extension of the retained measured polynomial
(`app:ch_waves:eq:individual-representation`). -/
theorem retainedAmplitudeCutoff_one {n : ℕ}
    (a : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
    {ρ : ℝ} (hρ : 0 < ρ) {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : w ∈ closedBall a (ρ / 2)) : retainedAmplitudeCutoff a hρ w = 1 :=
  (retainedAmplitudeCutoff a hρ).one_of_mem_closedBall hw

/-- Joint homotopy bounds for `fullMeasuredDerivativePolynomial` on the SAME
retained fields. The fixed smooth measurement is one of the selected tensor
contractions allowed by `app:ch_waves:thm:sampling`. Its seminorms are derived
from its actual smooth functions on the compact physical ball. The ambient
coefficient bounds are proved by the reconstruction producers, not assumed.
This endpoint keeps the literal nonzero polynomial and its principal zero
value; it does not assert the final supported-normal construction. -/
theorem exists_retained_measuredPolynomial_budgets
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
    (χ : Euclidean n → ℝ)
    (measurement : Euclidean n → Matrix (Fin N) (Fin n) ℂ →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hχ : ContDiffOn ℝ ∞ χ U) (hm : ContDiffOn ℝ ∞ measurement U) :
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
      let measured := fun q : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ↦
        fullMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ
          q.1 q.2.2.1 q.2.1 q.2.2.2
      let supported := fun q : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ↦
        retainedAmplitudeCutoff a hρ q.2 • measured q
      ContDiffOn ℝ ∞ measured (univ ×ˢ ball a (2 * ρ)) ∧
        (∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w ∈ closedBall a ρ, ∀ j,
          ‖iteratedFDeriv ℝ j measured (τ, w)‖ ≤ A j * L ^ (j - rpar)) ∧
        ContDiff ℝ ∞ supported ∧
        ∀ τ ∈ Icc (-1 : ℝ) 1, ∀ w, ∀ j,
          ‖iteratedFDeriv ℝ j supported (τ, w)‖ ≤ A j * L ^ (j - rpar) := by
  obtain ⟨A, hA, hpoly⟩ := exists_retained_jointPolynomial_budgets (N := N) T a hρ
    hK hKU hball hspace hphase I hγ hκ AF Ar E Γ hAF hAr hE hΓ
  let meas : Euclidean n → Matrix (Fin N) (Fin n) ℂ →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    fun x ↦ χ x • (measurement x).restrictScalars ℝ
  have hmeas : ContDiffOn ℝ ∞ meas U := hχ.smul
    ((ContinuousLinearMap.restrictScalarsL ℂ (Matrix (Fin N) (Fin n) ℂ)
      (EuclideanSpace ℂ (Fin n)) ℝ ℝ).contDiff.comp_contDiffOn hm)
  let B : ℕ → ℝ := fun j ↦ cNorm (closedBall a.1 ρ) j meas
  have hB (j) : 0 ≤ B j := cNorm_nonneg _ _ _
  let ev := (ContinuousLinearMap.apply ℝ (EuclideanSpace ℂ (Fin n))
    (E' := Matrix (Fin N) (Fin n) ℂ)).flip
  let C := productProfile ev B A
  have hC (j) : 0 ≤ C j := productProfile_nonneg ev hB (fun j ↦ (hA j).le) j
  let cutoff := retainedAmplitudeCutoff a hρ
  let bc := fun j ↦ cNorm (closedBall a ρ) j (cutoff : _ → ℝ)
  have hbc (j) : 0 ≤ bc j := cNorm_nonneg _ _ _
  let D := productProfile (ContinuousLinearMap.lsmul ℝ ℝ
    (E := EuclideanSpace ℂ (Fin n))) bc C
  have hD (j) : 0 ≤ D j := productProfile_nonneg _ hbc hC j
  refine ⟨fun j ↦ 1 + C j + D j, fun j ↦ by linarith [hC j, hD j], ?_⟩
  intro F hF hi hrank hmetric hnormal hlow Q row col Φ Y r Ω hΩ hflow hb₀ hb₁
    hleading hcorrection
    RF Rr rpar L hL hRF hRr hpF hpr
  obtain ⟨hs, hb⟩ := hpoly F hF hi hrank hmetric hnormal hlow
    row col Φ Y r Ω hΩ hflow hb₀ hb₁ hleading hcorrection RF Rr rpar L hL hRF hRr hpF hpr
  let poly := fun q : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ↦
    derivativePolynomial q.1 (fun w ↦ phaseGradient T Q w.1 w.2.2)
      (fullLeadingNormal T Q F row col Φ Y r)
      (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
      (fullLeadingReconstruction T Q F row col Φ Y r)
      (fullCorrectionReconstruction T Q F row col Φ Y r) q.2
  let pr : (ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))) →L[ℝ] Euclidean n :=
    (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
  have hprnorm : ‖pr‖ ≤ 1 := by
    apply pr.opNorm_le_bound zero_le_one
    intro q
    exact (norm_fst_le q.2).trans (by simpa using norm_snd_le q)
  have hsmall : closedBall a.1 ρ ⊆ U :=
    (closedBall_subset_closedBall (by linarith : ρ ≤ 2 * ρ)).trans (hspace.trans hKU)
  have hmap : MapsTo pr (univ ×ˢ ball a (2 * ρ)) U := by
    intro q hq
    have hx : q.2.1 ∈ closedBall a.1 (2 * ρ) := by
      have hw := ball_subset_closedBall hq.2
      rw [← closedBall_prod_same] at hw
      exact hw.1
    exact hKU (hspace hx)
  have hms : ContDiffOn ℝ ∞ (fun q ↦ meas (pr q)) (univ ×ˢ ball a (2 * ρ)) :=
    hmeas.comp pr.contDiff.contDiffOn hmap
  have heq : (fun q : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ↦
      fullMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ
        q.1 q.2.2.1 q.2.1 q.2.2.2) = (fun q ↦ meas (pr q) (poly q)) := by
    funext q
    change (χ q.2.1 : ℂ) • measurement q.2.1 (poly q) =
      χ q.2.1 • measurement q.2.1 (poly q)
    simp
  change ContDiffOn ℝ ∞ _ _ ∧ _
  rw [heq]
  let measured := fun q ↦ meas (pr q) (poly q)
  let supported := fun q : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ↦
    cutoff q.2 • measured q
  have hmeasured : ContDiffOn ℝ ∞ measured (univ ×ˢ ball a (2 * ρ)) := hms.clm_apply hs
  have hlocal (τ : ℝ) (hτ : τ ∈ Icc (-1 : ℝ) 1)
      (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))) (hw : w ∈ closedBall a ρ)
      (j : ℕ) : ‖iteratedFDeriv ℝ j measured (τ, w)‖ ≤ C j * L ^ (j - rpar) := by
    have hx : w.1 ∈ closedBall a.1 ρ := by
      rw [← closedBall_prod_same] at hw
      exact hw.1
    have hw' : (τ, w) ∈ (univ : Set ℝ) ×ˢ ball a (2 * ρ) :=
      ⟨mem_univ _, closedBall_subset_ball (by linarith) hw⟩
    have hmjet (k : ℕ) : ‖iteratedFDeriv ℝ k (fun q ↦ meas (pr q)) (τ, w)‖ ≤
        B k * L ^ (k - rpar) := by
      have hh := norm_iteratedFDeriv_preAffine_le pr 0 hU hmeas
        (x := (τ, w)) (by simpa [pr] using hsmall hx) k
      have hh' : ‖iteratedFDeriv ℝ k (fun q ↦ meas (pr q)) (τ, w)‖ ≤
          ‖iteratedFDeriv ℝ k meas w.1‖ := by
        simpa [pr] using
          hh.trans (mul_le_of_le_one_right (norm_nonneg _)
            (pow_le_one₀ (norm_nonneg _) hprnorm))
      apply (hh'.trans (norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
        (fun x hx ↦ (hmeas.contDiffAt (hU.mem_nhds (hsmall hx))).of_le (by simp)) hx le_rfl)).trans
      exact le_mul_of_one_le_right (hB k) (one_le_pow₀ hL)
    exact jet_bilinear_le ev (isOpen_univ.prod isOpen_ball) hms hs hw' hL hB
      (fun k ↦ (hA k).le) hmjet (hb τ hτ w hw) j
  have hcut : ContDiff ℝ ∞ (fun q : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ↦
      cutoff q.2) := cutoff.contDiff.comp contDiff_snd
  have hzero (τ : ℝ) (w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
      (hw : w ∉ closedBall a (3 * ρ / 4)) : supported =ᶠ[𝓝 (τ, w)] 0 := by
    have hz : (cutoff : _ → ℝ) =ᶠ[𝓝 w] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (by
        rw [ContDiffBump.tsupport_eq]
        exact hw)
    have hc := hz.comp_tendsto (continuous_snd.tendsto (τ, w))
    filter_upwards [hc] with q hq
    change cutoff q.2 = 0 at hq
    change cutoff q.2 • measured q = 0
    rw [hq, zero_smul]
  have hsupported : ContDiff ℝ ∞ supported := by
    rw [contDiff_iff_contDiffAt]
    rintro ⟨τ, w⟩
    by_cases hw : w ∈ closedBall a (3 * ρ / 4)
    · exact (hcut.contDiffOn.smul hmeasured).contDiffAt
        ((isOpen_univ.prod isOpen_ball).mem_nhds
          ⟨mem_univ _, closedBall_subset_ball (by linarith) hw⟩)
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero τ w hw)
  refine ⟨hmeasured, ?_, hsupported, ?_⟩
  · intro τ hτ w hw j
    exact (hlocal τ hτ w hw j).trans (mul_le_mul_of_nonneg_right
      (by linarith [hD j]) (pow_nonneg (le_trans zero_le_one hL) _))
  intro τ hτ w j
  by_cases hw : w ∈ closedBall a ρ
  · have hw' : (τ, w) ∈ (univ : Set ℝ) ×ˢ ball a (2 * ρ) :=
      ⟨mem_univ _, closedBall_subset_ball (by linarith) hw⟩
    have hj (k : ℕ) : ‖iteratedFDeriv ℝ k
        (fun q : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ↦ cutoff q.2) (τ, w)‖ ≤
        bc k * L ^ (k - rpar) := by
      let snd := ContinuousLinearMap.snd ℝ ℝ (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))
      have hh := norm_iteratedFDeriv_preAffine_le snd 0 isOpen_univ cutoff.contDiff.contDiffOn
        (x := (τ, w)) (mem_univ _) k
      have hh' : ‖iteratedFDeriv ℝ k
          (fun q : ℝ × (Euclidean n × (Euclidean 3 × Euclidean (n - 1))) ↦ cutoff q.2) (τ, w)‖ ≤
          ‖iteratedFDeriv ℝ k (cutoff : _ → ℝ) w‖ := by
        simpa [snd] using hh.trans (mul_le_of_le_one_right (norm_nonneg _)
          (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le _ _ _)))
      exact (hh'.trans (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
        cutoff.contDiff hw le_rfl)).trans (le_mul_of_one_le_right (hbc k) (one_le_pow₀ hL))
    exact (jet_bilinear_le (ContinuousLinearMap.lsmul ℝ ℝ)
      (isOpen_univ.prod isOpen_ball) hcut.contDiffOn hmeasured hw' hL hbc hC
      hj (hlocal τ hτ w hw) j).trans (mul_le_mul_of_nonneg_right
        (by dsimp [D]; linarith [hC j]) (pow_nonneg (le_trans zero_le_one hL) _))
  · have hz := hzero τ w (fun hh ↦ hw (closedBall_subset_closedBall (by linarith) hh))
    rw [(hz.iteratedFDeriv ℝ j).eq_of_nhds]
    simp only [Pi.zero_apply, iteratedFDeriv_zero, norm_zero]
    exact mul_nonneg (by linarith [hC j, hD j]) (pow_nonneg (le_trans zero_le_one hL) _)

end JanetCartan.Sampling.MeasuredAmplitude
