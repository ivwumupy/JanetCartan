module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.CrossAmplitude
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.Jets

/-!
# Joint measured transport jets from the original corrected profiles

Apply Hermitian product calculus and the original normalized pullback to the
explicit fixed-frequency transport path. Every constant is chosen before the
varying raw fields, response, history scale and band count.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedTransport
open CanonicalRowComparison CurrentMean CorrectedMean RawPrimary.SliceBounds
open RawPrimary.AmplitudeGrades.Polynomial FourierIntegral.NormalOneHigh
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open MeasuredAmplitude CorrectedAtoms RawPrimary RawPrimary.AmplitudeGrades
open FullNormalGeometry.PhaseJets

/-- Joint Hermitian calculus for the transport parameter, retaining the
original carrier insertion (`app:ch_waves:eq:colored-normal-comparison`). -/
private theorem exists_jointCarrierCrossCoefficient_budgets
    {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C₀ : ℝ} (hP : P.IsValid c C₀)
    (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    {K : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))}
    (hK : IsCompact K)
    (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
    (hκK : tsupport κ ⊆ K)
    (A M : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) (hM : ∀ j, 0 ≤ M j) :
    ∃ D : ℕ → ℝ, (∀ j, 0 ≤ D j) ∧
      ∀ (C : Euclidean (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
        Euclidean (m + 1)), ContDiff ℝ ∞ C →
      ∀ (f : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
        Matrix (Fin N) (Fin (m + 1)) ℂ), ContDiff ℝ ∞ f →
      (∀ w, κ w.2 = 0 → f w = 0) →
      ∀ (L : ℝ) (rpar : ℕ), 1 ≤ L →
      (∀ k, ∀ x ∈ Prod.fst '' K, ‖iteratedFDeriv ℝ k C x‖ ≤ M k * L ^ (k - rpar)) →
      (∀ w, w.1 ∈ Icc (-1 : ℝ) 1 → ∀ j,
        ‖iteratedFDeriv ℝ j f w‖ ≤ A j * L ^ (j - rpar)) →
      let H := fun w ↦ complexCrossMeasurement (C w.2.1)
        (f (w.1, retainedCarrierInsertion T z₀ hρ w.2)) (f w)
      ContDiff ℝ ∞ H ∧ ∀ w, w.1 ∈ Icc (-1 : ℝ) 1 → ∀ j,
        ‖iteratedFDeriv ℝ j H w‖ ≤ D j * L ^ (j - rpar) := by
  let g := fun w : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) ↦
    (w.1, retainedCarrierInsertion T z₀ hρ w.2)
  have hg : ContDiff ℝ ∞ g := contDiff_fst.prodMk
    ((contDiff_retainedCarrierInsertion T hP z₀ hρ hcarrier).comp contDiff_snd)
  let Kp := Icc (-1 : ℝ) 1 ×ˢ K
  have hKp : IsCompact Kp := isCompact_Icc.prod hK
  let b := fun j ↦ cNorm Kp j g
  have hb (j) : 0 ≤ b j := cNorm_nonneg _ _ _
  let A₀ := compositionBudget A b
  have hA₀ (j) : 0 ≤ A₀ j := compositionBudget_nonneg hA hb j
  let HB := hermitianContinuousBilinear (m := Fin N) (n := Fin (m + 1))
  let E := (ContinuousLinearMap.apply ℝ (Euclidean (m + 1))
    (E' := Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)).flip
  let D₀ := productProfile E M (productProfile HB A₀ A)
  have hD₀ (j) : 0 ≤ D₀ j :=
    productProfile_nonneg E hM (productProfile_nonneg HB hA₀ hA) j
  let Iout : Euclidean (m + 1) →L[ℝ] EuclideanSpace ℂ (Fin (m + 1)) :=
    euclideanComplexInclusion
  refine ⟨fun j ↦ 2 * ‖Iout‖ * D₀ j,
    fun j ↦ mul_nonneg (by positivity) (hD₀ j), ?_⟩
  intro C hC f hf hfzero L rpar hL hCjet hfjet H
  let meas := fun w : ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) ↦ C w.2.1
  have hm : ContDiff ℝ ∞ meas := hC.comp (contDiff_fst.comp contDiff_snd)
  let f₀ := f ∘ g
  let fI := fun w ↦ Complex.I • f w
  have hf₀ : ContDiff ℝ ∞ f₀ := hf.comp hg
  have hfI : ContDiff ℝ ∞ fI := hf.const_smul Complex.I
  let p₀ := fun w ↦ HB (f₀ w) (f w)
  let pI := fun w ↦ HB (f₀ w) (fI w)
  have hp₀ : ContDiff ℝ ∞ p₀ := (HB.contDiff.comp hf₀).clm_apply hf
  have hpI : ContDiff ℝ ∞ pI := (HB.contDiff.comp hf₀).clm_apply hfI
  let v₀ := fun w ↦ meas w (p₀ w)
  let vI := fun w ↦ meas w (pI w)
  have hv₀ : ContDiff ℝ ∞ v₀ := hm.clm_apply hp₀
  have hvI : ContDiff ℝ ∞ vI := hm.clm_apply hpI
  have heq : H = fun w ↦ Iout (v₀ w) - Complex.I • Iout (vI w) := rfl
  rw [heq]
  have hu₀ : ContDiff ℝ ∞ (fun w ↦ Iout (v₀ w)) := Iout.contDiff.comp hv₀
  have huI : ContDiff ℝ ∞ (fun w ↦ Iout (vI w)) := Iout.contDiff.comp hvI
  refine ⟨hu₀.sub (huI.const_smul Complex.I), ?_⟩
  intro w ht j
  by_cases hw : w.2 ∈ tsupport κ
  · have hwK : w ∈ Kp := ⟨ht, hκK hw⟩
    have hf₀jet (k) : ‖iteratedFDeriv ℝ k f₀ w‖ ≤ A₀ k * L ^ (k - rpar) :=
      norm_iteratedFDeriv_comp_le_sliceGrade hg.contDiffAt hf.contDiffAt
        (fun i _ ↦ hA i) hL (fun i _ ↦ hfjet (g w) ht i)
        (fun i _ _ ↦ norm_iteratedFDeriv_le_cNorm hKp (hg.of_le (by simp)) hwK le_rfl)
    have hfIjet (k) : ‖iteratedFDeriv ℝ k fI w‖ ≤ A k * L ^ (k - rpar) := by
      rw [show fI = fun y ↦ Complex.I • f y from rfl, jet_const_smul hf.contDiffAt,
        Complex.norm_I, one_mul]
      exact hfjet w ht k
    have hmjet (k) : ‖iteratedFDeriv ℝ k meas w‖ ≤ M k * L ^ (k - rpar) := by
      let pr : (ℝ × (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))) →L[ℝ]
          Euclidean (m + 1) :=
        (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)
      have hpr : ‖pr‖ ≤ 1 := by
        apply pr.opNorm_le_bound zero_le_one
        intro q
        exact (norm_fst_le q.2).trans (by simpa using norm_snd_le q)
      have hh := NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le pr
        (x := w) isOpen_univ hC.contDiffOn (mem_univ _) k
      exact (hh.trans (mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) hpr))).trans
          (hCjet k w.2.1 ⟨w.2, hκK hw, rfl⟩)
    have hp₀jet (k) : ‖iteratedFDeriv ℝ k p₀ w‖ ≤ productProfile HB A₀ A k * L ^ (k - rpar) :=
      jet_bilinear_le HB isOpen_univ hf₀.contDiffOn hf.contDiffOn (mem_univ _)
        hL hA₀ hA hf₀jet (hfjet w ht) k
    have hpIjet (k) : ‖iteratedFDeriv ℝ k pI w‖ ≤ productProfile HB A₀ A k * L ^ (k - rpar) :=
      jet_bilinear_le HB isOpen_univ hf₀.contDiffOn hfI.contDiffOn (mem_univ _)
        hL hA₀ hA hf₀jet hfIjet k
    have hv₀jet : ‖iteratedFDeriv ℝ j v₀ w‖ ≤ D₀ j * L ^ (j - rpar) :=
      jet_bilinear_le E isOpen_univ hm.contDiffOn hp₀.contDiffOn (mem_univ _)
        hL hM (productProfile_nonneg HB hA₀ hA) hmjet hp₀jet j
    have hvIjet : ‖iteratedFDeriv ℝ j vI w‖ ≤ D₀ j * L ^ (j - rpar) :=
      jet_bilinear_le E isOpen_univ hm.contDiffOn hpI.contDiffOn (mem_univ _)
        hL hM (productProfile_nonneg HB hA₀ hA) hmjet hpIjet j
    have hu₀jet := (Iout.norm_iteratedFDeriv_comp_left hv₀.contDiffAt
      (by simp : (j : ℕ∞ω) ≤ ∞)).trans (mul_le_mul_of_nonneg_left hv₀jet (norm_nonneg _))
    have huIjet := (Iout.norm_iteratedFDeriv_comp_left hvI.contDiffAt
      (by simp : (j : ℕ∞ω) ≤ ∞)).trans (mul_le_mul_of_nonneg_left hvIjet (norm_nonneg _))
    change ‖iteratedFDeriv ℝ j ((fun y ↦ Iout (v₀ y)) -
      (fun y ↦ Complex.I • Iout (vI y))) w‖ ≤ _
    rw [iteratedFDeriv_sub_apply (hu₀.contDiffAt.of_le (by simp))
      ((huI.const_smul Complex.I).contDiffAt.of_le (by simp))]
    apply (norm_sub_le _ _).trans
    rw [jet_const_smul huI.contDiffAt, Complex.norm_I, one_mul]
    exact (add_le_add hu₀jet huIjet).trans_eq (by ring)
  · have hz : H =ᶠ[𝓝 w] 0 := by
      filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hw).comp_tendsto
        (continuous_snd.tendsto w)] with y hy
      change κ y.2 = 0 at hy
      simp only [H, hfzero y hy, map_zero, Pi.zero_apply]
    rw [← heq, (hz.iteratedFDeriv ℝ j).eq_of_nhds]
    simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (hD₀ j))
      (pow_nonneg (zero_le_one.trans hL) _)


/-- The normalized corrected transport amplitude has all original joint
jet grades, proved from the raw/response profiles and the actual measurement
jets. Constants precede the varying measurement, immersion, solver, positive
rate, history scale and every band. The same response is used throughout the
path (`app:ch_waves:setup:oscillatory`, `app:ch_waves:eq:colored-normal-comparison`). -/
theorem exists_correctedTransportNormalAmplitude_budgets_of_profiles
    {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C₀ : ℝ} (hP : P.IsValid c C₀)
    (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    {K Ω : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
    (hκ : ContDiff ℝ ∞ κ) (hκK : tsupport κ ⊆ K)
    (Cjet A₀ A₁ B₀ B₁ Cresp Cmeas : ℕ → ℝ)
    (hCjet : ∀ j, 0 ≤ Cjet j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) (hCresp : ∀ j, 0 ≤ Cresp j)
    (hCmeas : ∀ j, 0 ≤ Cmeas j)
    (M : ℝ) {e : ℝ} (he : e ≤ 1)
    {S : Set (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1)))}
    (hS : IsCompact S) (hSM : S ⊆ tripleDomain T M)
    (ψ : SeparatedSampling.Point → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (angular : Euclidean (m + 1 - 1) → ℂ) (highPass : Euclidean (m + 1 - 1) → ℝ)
    (ha : ∀ θ, θ ≠ 0 → ContDiffAt ℝ ∞ angular θ)
    (hah : ∀ t : ℝ, 0 < t → ∀ θ, angular (t • θ) = angular θ)
    (hhigh : ContDiff ℝ ∞ highPass) (hhigh₁ : ∀ η, 2 ≤ ‖η‖ → highPass η = 1) :
    ∃ D : ℕ → ℝ, (∀ k, 0 < D k) ∧
      ∀ (C : Euclidean (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
        Euclidean (m + 1)), ContDiff ℝ ∞ C →
      ∀ (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
        ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})
        (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
        (Φ Y : ℝ × (Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) →
          Euclidean (m + 1 - 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))
        (χ : Euclidean (m + 1) → ℝ)
        (B : MetricField (m + 1) →ₗ[ℝ] (Euclidean (m + 1) → Euclidean N))
        (r : Euclidean (m + 1 - 1) × Euclidean 3 → ℝ),
      (∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T) →
      ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω →
      ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω →
      ∀ (τ L : ℝ) (rpar : ℕ), 0 < τ → τ ≤ 1 → 1 ≤ L →
      (∀ k, ∀ x ∈ Prod.fst '' K,
        ‖iteratedFDeriv ℝ k C x‖ ≤ Cmeas k * L ^ (k - rpar)) →
      HasDerivativeProfile K (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L Cjet →
      HasDerivativeProfile K (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀ →
      HasDerivativeProfile K (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
        (rpar + 1) L A₁ →
      HasDerivativeProfile K (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L B₀ →
      HasDerivativeProfile K (fullCorrectionReconstruction T Q F row col Φ Y r)
        (rpar + 1) L B₁ →
      ContDiffOn ℝ ∞ (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω →
      (∀ j, ∀ w ∈ K,
        ‖iteratedFDeriv ℝ j (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
          τ * Cresp j * L ^ (j - rpar)) →
      ∀ j,
        let f := fun q : ℝ × (Euclidean 2 × (Euclidean (m + 1) × Euclidean (m + 1))) ↦
          correctedTransportNormalAmplitude T Q F row col Φ Y χ B r κ C z₀ hρ τ
            angular highPass ψ j q.2.1 q.1 q.2.2.1 q.2.2.2
        ContDiffOn ℝ ∞ f (univ ×ˢ tripleDomain T M) ∧
          (∀ q ∈ Icc (-e) e ×ˢ S, ∀ k,
            ‖iteratedFDeriv ℝ k f q‖ ≤ D k * L ^ (k - rpar)) ∧
          ∀ q ∈ Icc (-e) e ×ˢ S, ∀ k ≤ rpar,
            ‖iteratedFDeriv ℝ k f q‖ ≤ D k := by
  let sm := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
    Matrix (Fin N) (Fin (m + 1)) ℂ →L[ℝ] Matrix (Fin N) (Fin (m + 1)) ℂ)
  let Acut := fun j ↦ cNorm K j κ
  have hAcut (j) : 0 ≤ Acut j := cNorm_nonneg _ _ _
  let CA := productProfile sm Acut
    (fun k ↦ derivativeProfile (m + 1) N Cjet A₀ A₁ B₀ B₁ k + Cresp k)
  let CE := productProfile sm Acut
    (fun k ↦ errorProfile (m + 1) N Cjet A₀ A₁ B₀ B₁ k + Cresp k)
  have hCA (k) : 0 ≤ CA k := productProfile_nonneg _ hAcut
    (fun k ↦ add_nonneg
      ((polynomialProfiles_nonneg (m + 1) N hCjet hA₀ hA₁ hB₀ hB₁ k).2.2.2.2) (hCresp k)) k
  have hCE (k) : 0 ≤ CE k := productProfile_nonneg _ hAcut
    (fun k ↦ add_nonneg
      ((polynomialProfiles_nonneg (m + 1) N hCjet hA₀ hA₁ hB₀ hB₁ k).2.2.2.1) (hCresp k)) k
  let A := fun k ↦ CA k + CE k + productProfile sm
    (fun j ↦ cNorm (Icc (-1 : ℝ) 1) j (fun t : ℝ ↦ t)) CE k
  have hA (k) : 0 ≤ A k := add_nonneg (add_nonneg (hCA k) (hCE k))
    (productProfile_nonneg _ (fun _ ↦ cNorm_nonneg _ _ _) hCE k)
  obtain ⟨Across, hAcross, hcross⟩ := exists_jointCarrierCrossCoefficient_budgets (N := N)
    T hP z₀ hρ hcarrier hK κ hκK A Cmeas hA hCmeas
  obtain ⟨D, hD, hpull⟩ := exists_normalizedMeasuredPullback_budgets T hP M he hS hSM
    ψ hψ angular highPass ha hah hhigh hhigh₁ Across hAcross
  refine ⟨fun k ↦ 1 + D k, fun k ↦ by linarith [hD k], ?_⟩
  intro C hC Q F row col Φ Y χ B r hphase hν₀ hν₁ hV₀ hV₁ τ L rpar hτ hτ₁ hL
    hCpoint hpξ hpν₀ hpν₁ hpV₀ hpV₁ hresponse hresponseJets j
  let path := correctedTransportDerivativeHomotopy T Q F row col Φ Y χ B r κ τ
  have hpath : ContDiff ℝ ∞ path := contDiff_correctedTransportDerivativeHomotopy
    T Q F row col Φ Y χ B r κ hΩ hκ (hκK.trans hKΩ)
    hphase hν₀ hν₁ hV₀ hV₁ hτ.ne' hresponse
  have hzero (w) (hw : κ w.2 = 0) : path w = 0 := by
    simp only [path, correctedTransportDerivativeHomotopy, correctedTransportScaledError,
      hw, zero_smul, smul_zero, add_zero]
  have hpathJet (w) (hw : w.1 ∈ Icc (-1 : ℝ) 1) (k) :
      ‖iteratedFDeriv ℝ k path w‖ ≤ A k * L ^ (k - rpar) := by
    have hh := correctedTransportDerivativeHomotopy_joint_bounds_of_profiles
      (d := m) (N := N) (Kjoint := K) (Ω := Ω) (rpar := rpar)
      (Cjet := Cjet) (A₀ := A₀) (A₁ := A₁) (B₀ := B₀) (B₁ := B₁)
      (Cresp := Cresp) (Acut := Acut) (L := L) (τ := τ)
      T Q F row col Φ Y χ B r κ hK hΩ hKΩ hκ hκK hphase hν₀ hν₁ hV₀ hV₁
      hCjet hA₀ hA₁ hB₀ hB₁ hCresp hAcut
      (fun k w hw ↦ norm_iteratedFDeriv_le_cNorm hK (hκ.of_le (by simp)) hw le_rfl)
      hτ hτ₁ hL hpξ hpν₀ hpν₁ hpV₀ hpV₁ hresponse hresponseJets hw k w.2
    exact hh
  obtain ⟨hcrossSmooth, hcrossJet⟩ := hcross C hC path hpath hzero L rpar hL hCpoint hpathJet
  let cross := correctedTransportCrossHomotopy T Q F row col Φ Y χ B r κ C z₀ hρ τ
  have hcs : ContDiff ℝ ∞ cross := hcrossSmooth
  have hcj (t) (ht : t ∈ Icc (-1 : ℝ) 1) (w) (k) :
      ‖iteratedFDeriv ℝ k cross (t, w)‖ ≤ Across k * L ^ (k - rpar) :=
    hcrossJet (t, w) ht k
  obtain ⟨hs, hj⟩ := hpull cross hcs L rpar hL hcj j
  refine ⟨hs, ?_, ?_⟩
  · intro q hq k
    exact (hj q hq k).trans
      (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (zero_le_one.trans hL) _))
  · intro q hq k hk
    have hh := hj q hq k
    rw [Nat.sub_eq_zero_of_le hk, pow_zero, mul_one] at hh
    exact hh.trans (le_add_of_nonneg_left zero_le_one)

end JanetCartan.Sampling.CorrectedTransport
