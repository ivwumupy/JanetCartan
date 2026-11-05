module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedTransport.Amplitude

/-!
# Uniform jets of the fixed-frequency corrected transport path

The response frequency remains fixed. The original inverse-frequency error
cancels the slope normalization; fixed cutoff and raw profiles bound every
joint interpolation/physical/carrier derivative with the original reserve.
These estimates supply the corrected transport homotopy, not its eventual
normal or sampling conclusion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedTransport
open CorrectedAtoms RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation

/-- Fixed algebraic interpolation spends no spatial reserve
(`app:ch_waves:eq:colored-normal-comparison`). -/
private theorem norm_joint_affine_amplitude_jet_le
    {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a e : X → V} (ha : ContDiff ℝ ∞ a) (he : ContDiff ℝ ∞ e)
    {A E : ℕ → ℝ} (_hA : ∀ k, 0 ≤ A k) (hE : ∀ k, 0 ≤ E k)
    {L : ℝ} {rpar : ℕ} (hL : 1 ≤ L)
    (haj : ∀ k x, ‖iteratedFDeriv ℝ k a x‖ ≤ A k * L ^ (k - rpar))
    (hej : ∀ k x, ‖iteratedFDeriv ℝ k e x‖ ≤ E k * L ^ (k - rpar))
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) (x : X) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun q : ℝ × X ↦ a q.2 + q.1 • e q.2) (t, x)‖ ≤
      (A j + productProfile (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)
        (fun k ↦ cNorm (Icc (-1 : ℝ) 1) k (fun t : ℝ ↦ t)) E j) * L ^ (j - rpar) := by
  let pr := ContinuousLinearMap.snd ℝ ℝ X
  have hjpr (f : X → V) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
      ‖iteratedFDeriv ℝ k (fun q : ℝ × X ↦ f q.2) (t, x)‖ ≤
        ‖iteratedFDeriv ℝ k f x‖ := by
    exact (NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le pr
      isOpen_univ hf.contDiffOn (mem_univ _) k).trans
      (mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le _ _ _)))
  let b := fun k ↦ cNorm (Icc (-1 : ℝ) 1) k (fun t : ℝ ↦ t)
  have hb (k) : 0 ≤ b k := cNorm_nonneg _ _ _
  have htj (k) : ‖iteratedFDeriv ℝ k (fun q : ℝ × X ↦ q.1) (t, x)‖ ≤ b k := by
    have hh := NormalComparison.norm_iteratedFDeriv_comp_linear_on_open_le
      (ContinuousLinearMap.fst ℝ ℝ X) (f := fun t : ℝ ↦ t)
      (x := (t, x)) isOpen_univ contDiffOn_id (mem_univ _) k
    apply (hh.trans (mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le _ _ _)))).trans
    exact norm_iteratedFDeriv_le_cNorm isCompact_Icc ((contDiff_id : ContDiff ℝ ∞ (fun t : ℝ ↦ t)).of_le (by simp)) ht le_rfl
  have hprod := jet_bilinear_le (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)
    isOpen_univ contDiffOn_fst (he.comp contDiff_snd).contDiffOn (mem_univ (t, x)) hL hb hE
    (fun k ↦ (htj k).trans (le_mul_of_one_le_right (hb k) (one_le_pow₀ hL)))
    (fun k ↦ (hjpr e he k).trans (hej k x)) j
  exact (jet_add_le (ha.comp contDiff_snd).contDiffAt
    (contDiff_fst.smul (he.comp contDiff_snd)).contDiffAt j).trans
    ((add_le_add ((hjpr a ha j).trans (haj j x)) hprod).trans_eq (by ring))

variable {d N : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1) // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d + 1)) < T.family.threshold})
    (F : Euclidean (d + 1) → Euclidean N) (row col : Fin (d + 1))
    (Φ Y : ℝ × (Euclidean ((d + 1) - 1) × (Euclidean 3 × Euclidean ((d + 1) - 1))) →
      Euclidean ((d + 1) - 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)))
    (χ : Euclidean (d + 1) → ℝ)
    (B : MetricField (d + 1) →ₗ[ℝ] (Euclidean (d + 1) → Euclidean N))
    (r : Euclidean ((d + 1) - 1) × Euclidean 3 → ℝ)
    (κ : Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)) → ℝ)


variable {Kjoint Ω : Set (Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)))}
    (hjoint : IsCompact Kjoint) (hΩ : IsOpen Ω) (hjointΩ : Kjoint ⊆ Ω)
    (hκ : ContDiff ℝ ∞ κ) (hκsupport : tsupport κ ⊆ Kjoint)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω)
    (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
    (hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω)
    (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
    {rpar : ℕ} {Cjet A₀ A₁ B₀ B₁ Cresp Acut : ℕ → ℝ}
    (hCjet : ∀ j, 0 ≤ Cjet j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) (hCresp : ∀ j, 0 ≤ Cresp j)
    (hAcut : ∀ j, 0 ≤ Acut j)
    (hκjets : ∀ j, ∀ w ∈ Kjoint, ‖iteratedFDeriv ℝ j κ w‖ ≤ Acut j)
    {L τ : ℝ} (hτ : 0 < τ) (hτ₁ : τ ≤ 1) (hL : 1 ≤ L)
    (hpξ : HasDerivativeProfile Kjoint (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L Cjet)
    (hpν₀ : HasDerivativeProfile Kjoint (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀)
    (hpν₁ : HasDerivativeProfile Kjoint (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
      (rpar + 1) L A₁)
    (hpV₀ : HasDerivativeProfile Kjoint (fullLeadingReconstruction T Q F row col Φ Y r)
      (rpar + 2) L B₀)
    (hpV₁ : HasDerivativeProfile Kjoint (fullCorrectionReconstruction T Q F row col Φ Y r)
      (rpar + 1) L B₁)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω)
    (hresponseJets : ∀ j, ∀ w ∈ Kjoint,
      ‖iteratedFDeriv ℝ j
        (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ) w‖ ≤
          τ * Cresp j * L ^ (j - rpar))

include hjoint hΩ hjointΩ hκ hκsupport hphase hν₀ hν₁ hV₀ hV₁ hCjet hA₀ hA₁ hB₀ hB₁ hCresp
  hAcut hκjets hτ hτ₁ hL hpξ hpν₀ hpν₁ hpV₀ hpV₁ hresponse hresponseJets

/-- The apparent inverse-frequency singularity of the transport slope cancels
against the proved corrected-minus-leading error, at every spatial/carrier jet
and on the whole ambient space. The constant contains only the original fixed
profiles (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem correctedTransportScaledError_joint_bounds_of_profiles
    (j : ℕ) (w : Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1))) :
    ‖iteratedFDeriv ℝ j (correctedTransportScaledError T Q F row col Φ Y χ B r κ τ) w‖ ≤
      productProfile (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
        Matrix (Fin N) (Fin (d + 1)) ℂ →L[ℝ] Matrix (Fin N) (Fin (d + 1)) ℂ)
        Acut (fun k ↦ errorProfile (d + 1) N Cjet A₀ A₁ B₀ B₁ k + Cresp k) j *
          L ^ (j - rpar) := by
  let CE := productProfile (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
    Matrix (Fin N) (Fin (d + 1)) ℂ →L[ℝ] Matrix (Fin N) (Fin (d + 1)) ℂ)
    Acut (fun k ↦ errorProfile (d + 1) N Cjet A₀ A₁ B₀ B₁ k + Cresp k)
  have hCE (k) : 0 ≤ CE k := productProfile_nonneg _ hAcut
    (fun k ↦ add_nonneg
      ((polynomialProfiles_nonneg (d + 1) N hCjet hA₀ hA₁ hB₀ hB₁ k).2.2.2.1) (hCresp k)) k
  by_cases hw : w ∈ tsupport κ
  · have hs := contDiff_correctedTransportScaledError T Q F row col Φ Y χ B r κ
      hΩ hκ (hκsupport.trans hjointΩ) hphase hν₀ hν₁ hV₀ hV₁ hτ.ne' hresponse
    let err := fun w ↦ κ w •
      (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r w)
    have herr : ContDiff ℝ ∞ err := by
      have he : err = fun w ↦ τ • correctedTransportScaledError T Q F row col Φ Y χ B r κ τ w := by
        funext w
        rw [correctedTransportScaledError, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
      rw [he]
      exact hs.const_smul τ
    change ‖iteratedFDeriv ℝ j (fun w ↦ τ⁻¹ • err w) w‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (herr.contDiffAt.of_le (by simp)),
      norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hτ.le)]
    have hb := cutCorrectedDerivativeAmplitude_error_joint_bounds_of_profiles
      T Q F row col Φ Y χ B r κ (fun _ : Unit ↦ τ)
      hjoint hΩ hjointΩ hphase hν₀ hν₁ hV₀ hV₁ hCjet hA₀ hA₁ hB₀ hB₁ hCresp
      (fun _ ↦ hτ) (fun _ ↦ hτ₁) hL hpξ hpν₀ hpν₁ hpV₀ hpV₁
      (fun _ ↦ hresponse) (fun _ ↦ hresponseJets) hκ.contDiffOn hAcut hκjets () j (hκsupport hw)
    apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hτ.le)).trans_eq
    simp only [← mul_assoc, inv_mul_cancel₀ hτ.ne', one_mul]
  · have hz : correctedTransportScaledError T Q F row col Φ Y χ B r κ τ =ᶠ[𝓝 w] 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hw] with y hy
      change κ y = 0 at hy
      simp only [correctedTransportScaledError, hy, zero_smul, smul_zero, Pi.zero_apply]
    rw [(hz.iteratedFDeriv ℝ j).eq_of_nhds]
    simp only [Pi.zero_apply, iteratedFDeriv_zero, norm_zero]
    exact mul_nonneg (hCE j) (pow_nonneg (zero_le_one.trans hL) _)


/-- All joint parameter/physical/carrier jets of the explicit transport path
are bounded by fixed raw, response and cutoff profiles. The response is always
at the original positive frequency, and no frequency derivative of the solver
is a premise (`app:ch_waves:setup:oscillatory`,
`app:ch_waves:eq:colored-normal-comparison`). -/
theorem correctedTransportDerivativeHomotopy_joint_bounds_of_profiles
    {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1)
    (j : ℕ) (w : Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1))) :
    let sm := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
      Matrix (Fin N) (Fin (d + 1)) ℂ →L[ℝ] Matrix (Fin N) (Fin (d + 1)) ℂ)
    let CA := productProfile sm Acut
      (fun k ↦ derivativeProfile (d + 1) N Cjet A₀ A₁ B₀ B₁ k + Cresp k)
    let CE := productProfile sm Acut
      (fun k ↦ errorProfile (d + 1) N Cjet A₀ A₁ B₀ B₁ k + Cresp k)
    ‖iteratedFDeriv ℝ j (correctedTransportDerivativeHomotopy T Q F row col Φ Y χ B r κ τ)
      (t, w)‖ ≤
      (CA j + CE j + productProfile sm
        (fun k ↦ cNorm (Icc (-1 : ℝ) 1) k (fun t : ℝ ↦ t)) CE j) * L ^ (j - rpar) := by
  intro sm CA CE
  have hCA (k) : 0 ≤ CA k := productProfile_nonneg _ hAcut
    (fun k ↦ add_nonneg
      ((polynomialProfiles_nonneg (d + 1) N hCjet hA₀ hA₁ hB₀ hB₁ k).2.2.2.2) (hCresp k)) k
  have hCE (k) : 0 ≤ CE k := productProfile_nonneg _ hAcut
    (fun k ↦ add_nonneg
      ((polynomialProfiles_nonneg (d + 1) N hCjet hA₀ hA₁ hB₀ hB₁ k).2.2.2.1) (hCresp k)) k
  let a := fun w ↦ κ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w
  let e := correctedTransportScaledError T Q F row col Φ Y χ B r κ τ
  let c := fun w ↦ κ w • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ w
  have hs := contDiff_correctedTransportDerivativeHomotopy T Q F row col Φ Y χ B r κ
    hΩ hκ (hκsupport.trans hjointΩ) hphase hν₀ hν₁ hV₀ hV₁ hτ.ne' hresponse
  have ha : ContDiff ℝ ∞ a := by
    simpa only [Function.comp_def, id_eq, correctedTransportDerivativeHomotopy_zero] using
      hs.comp ((contDiff_const (c := (0 : ℝ))).prodMk contDiff_id)
  have he : ContDiff ℝ ∞ e := contDiff_correctedTransportScaledError
    T Q F row col Φ Y χ B r κ hΩ hκ (hκsupport.trans hjointΩ)
    hphase hν₀ hν₁ hV₀ hV₁ hτ.ne' hresponse
  have hc : ContDiff ℝ ∞ c := contDiff_cutCorrectedDerivativeAmplitude
    T Q F row col Φ Y χ B r κ hΩ hκ (hκsupport.trans hjointΩ)
    hphase hν₀ hν₁ hV₀ hV₁ hτ.ne' hresponse
  have hej (k : ℕ) (x) : ‖iteratedFDeriv ℝ k e x‖ ≤ CE k * L ^ (k - rpar) :=
    correctedTransportScaledError_joint_bounds_of_profiles
      T Q F row col Φ Y χ B r κ hjoint hΩ hjointΩ hκ hκsupport hphase hν₀ hν₁ hV₀ hV₁
      hCjet hA₀ hA₁ hB₀ hB₁ hCresp hAcut hκjets hτ hτ₁ hL hpξ hpν₀ hpν₁ hpV₀ hpV₁
      hresponse hresponseJets k x
  have hcj (k : ℕ) (x) : ‖iteratedFDeriv ℝ k c x‖ ≤ CA k * L ^ (k - rpar) := by
    by_cases hx : x ∈ tsupport κ
    · exact cutCorrectedDerivativeAmplitude_joint_bounds_of_profiles
        T Q F row col Φ Y χ B r κ (fun _ : Unit ↦ τ)
        hjoint hΩ hjointΩ hphase hν₀ hν₁ hV₀ hV₁ hCjet hA₀ hA₁ hB₀ hB₁ hCresp
        (fun _ ↦ hτ) (fun _ ↦ hτ₁) hL hpξ hpν₀ hpν₁ hpV₀ hpV₁
        (fun _ ↦ hresponse) (fun _ ↦ hresponseJets) hκ.contDiffOn hAcut hκjets () k (hκsupport hx)
    · have hz : c =ᶠ[𝓝 x] 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        change κ y = 0 at hy
        simp only [c, hy, zero_smul, Pi.zero_apply]
      rw [(hz.iteratedFDeriv ℝ k).eq_of_nhds]
      simp only [Pi.zero_apply, iteratedFDeriv_zero, norm_zero]
      exact mul_nonneg (hCA k) (pow_nonneg (zero_le_one.trans hL) _)
  have haj (k : ℕ) (x) : ‖iteratedFDeriv ℝ k a x‖ ≤ (CA k + CE k) * L ^ (k - rpar) := by
    have heq : a = c - τ • e := by
      funext y
      change κ y • fullLeadingPrincipalMatrix T Q F row col Φ Y r y =
        κ y • fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r τ y -
          τ • correctedTransportScaledError T Q F row col Φ Y χ B r κ τ y
      rw [correctedTransportScaledError, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul, smul_sub]
      abel
    rw [heq]
    change ‖iteratedFDeriv ℝ k (fun y ↦ c y - τ • e y) x‖ ≤ _
    rw [show (fun y ↦ c y - τ • e y) = c - (fun y ↦ τ • e y) from rfl,
      iteratedFDeriv_sub_apply (f := c) (g := fun y ↦ τ • e y) (hc.contDiffAt.of_le (by simp))
      ((he.const_smul τ).contDiffAt.of_le (by simp)),
      iteratedFDeriv_const_smul_apply' (he.contDiffAt.of_le (by simp))]
    apply (norm_sub_le _ _).trans
    rw [norm_smul, Real.norm_of_nonneg hτ.le]
    calc
      _ ≤ CA k * L ^ (k - rpar) + τ * (CE k * L ^ (k - rpar)) :=
        add_le_add (hcj k x) (mul_le_mul_of_nonneg_left (hej k x) hτ.le)
      _ ≤ CA k * L ^ (k - rpar) + CE k * L ^ (k - rpar) :=
        add_le_add le_rfl (mul_le_of_le_one_left
          (mul_nonneg (hCE k) (pow_nonneg (zero_le_one.trans hL) _)) hτ₁)
      _ = _ := by ring
  exact norm_joint_affine_amplitude_jet_le ha he (fun k ↦ add_nonneg (hCA k) (hCE k))
    hCE hL haj hej ht w j

end JanetCartan.Sampling.CorrectedTransport
