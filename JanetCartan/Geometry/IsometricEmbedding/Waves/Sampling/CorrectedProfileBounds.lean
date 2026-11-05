module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedKernelBounds

/-!
# Corrected sampling trace from the retained coefficient profiles

Apply the published raw polynomial and SAME response derivative estimates to
`correctedColoredCrossBandData`. Its uniform amplitude, column integral and
every grouped-prefix trace follow with explicit constants. No bound on its
arbitrary compactness witness and no kernel estimate is a premise.

The primitive coefficient profiles and response jets are the named outputs of
`RawPrimary.AmplitudeGrades` and `CorrectedAtoms.JointProfiles`; their actual
history instantiation and the sharp band/mean/transport estimates remain
separate obligations. Consumer: `app:ch_waves:eq:sampling-all-prefixes`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Set MeasureTheory Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.Sampling
open CanonicalRowComparison CanonicalAtomRealization CurrentMean CorrectedAtoms
open SamplingKernelBounds RawInputPartition RawInputRealization
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open RawPrimary RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial

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
    (hκc : HasCompactSupport κ)
    {γ : Type*} [Finite γ] (rate : γ → ℝ)
    (hA : ∀ c, Continuous (fun w ↦ κ w •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w))
    (C : Euclidean (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →L[ℝ] Euclidean (d + 1))
    (hC : Continuous C)
    {ι : Type*} [TopologicalSpace ι] [FirstCountableTopology ι] [LocallyCompactSpace ι]
    [TopologicalSpace γ] [DiscreteTopology γ]
    (color : ι → γ) (hcolor : Continuous color)
    (node : ι → Euclidean 3) (hnode : Continuous node)
    {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀) (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    (hrate : ∀ c, rate c ≠ 0)
    (mask : Euclidean ((d + 1) - 1) → ℂ) (hd : Continuous mask)
    (Md : ℝ) (hMd : 0 ≤ Md) (hdb : ∀ ξ, ‖mask ξ‖ ≤ Md)

variable {Kjoint Ω : Set (Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1)))}
    (hjoint : IsCompact Kjoint) (hΩ : IsOpen Ω) (hjointΩ : Kjoint ⊆ Ω)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hν₀ : ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω)
    (hν₁ : ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω)
    (hV₀ : ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω)
    (hV₁ : ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω)
    {rpar : ℕ} {Cjet A₀ A₁ B₀ B₁ Cresp : ℕ → ℝ}
    (hCjet : ∀ j, 0 ≤ Cjet j) (hA₀ : ∀ j, 0 ≤ A₀ j) (hA₁ : ∀ j, 0 ≤ A₁ j)
    (hB₀ : ∀ j, 0 ≤ B₀ j) (hB₁ : ∀ j, 0 ≤ B₁ j) (hCresp : ∀ j, 0 ≤ Cresp j)
    {L : ℝ} (hτ : ∀ c, 0 < rate c) (hτ₁ : ∀ c, rate c ≤ 1) (hL : 1 ≤ L)
    (hpξ : HasDerivativeProfile Kjoint (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L Cjet)
    (hpν₀ : HasDerivativeProfile Kjoint (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀)
    (hpν₁ : HasDerivativeProfile Kjoint (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
      (rpar + 1) L A₁)
    (hpV₀ : HasDerivativeProfile Kjoint (fullLeadingReconstruction T Q F row col Φ Y r)
      (rpar + 2) L B₀)
    (hpV₁ : HasDerivativeProfile Kjoint (fullCorrectionReconstruction T Q F row col Φ Y r)
      (rpar + 1) L B₁)
    (hresponse : ∀ c, ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B (rate c) r w.2 w.1) Ω)
    (hresponseJets : ∀ c j, ∀ w ∈ Kjoint,
      ‖iteratedFDeriv ℝ j
        (fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r (rate c)) w‖ ≤
          rate c * Cresp j * L ^ (j - rpar))

include hjoint hΩ hjointΩ hphase hν₀ hν₁ hV₀ hV₁ hCjet hA₀ hA₁ hB₀ hB₁ hCresp
  hτ hτ₁ hL hpξ hpν₀ hpν₁ hpV₀ hpV₁ hresponse hresponseJets

/-- On the literal corrected colored family, the five retained coefficient
profiles and the SAME response's derivative jets prove the uniform sampling
amplitude and trace bounds. All prefixes use the original grouped input and
one original detector. The constant contains only fixed low profile values,
cutoff/measurement bounds and the original Fourier scalar
(`app:ch_waves:eq:sampling-operator-bounds`,
`app:ch_response:eq:current-atomic-amplitudes`). -/
theorem correctedColoredCrossBandData_uniform_bounds_of_profiles
    {Mκ MC : ℝ} (hMκ : 0 ≤ Mκ) (hMC : 0 ≤ MC)
    (hκsupport : tsupport κ ⊆ Kjoint) (hκbound : ∀ w, |κ w| ≤ Mκ)
    (hCbound : ∀ x ∈ Prod.fst '' tsupport κ, ‖C x‖ ≤ MC) (J : ℕ) :
    let D := correctedColoredCrossBandData T Q F row col Φ Y χ B r κ hκc rate hA C hC
      color hcolor node hnode hP z₀ hρ hcarrier hrate mask hd Md hMd hdb J
    let M := (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2) *
      (2 * MC * (Mκ * (derivativeProfile (d + 1) N Cjet A₀ A₁ B₀ B₁ 0 + Cresp 0)) ^ 2)
    (∀ q η x, ‖D.amplitude ((q, η), x)‖ ≤ M) ∧
    (∀ R : ℝ, 0 ≤ R → ∀ q,
      (∫ η, ‖D.column q η‖ ^ 2 ∂annularMeasure (d + 1) R) ≤
        (volume.real (Prod.fst '' tsupport κ) * Md ^ 2 * M ^ 2 * unitBallVolume (d + 1)) *
          R ^ (d + 1)) ∧
    (∀ {δ : Type} (b : HilbertBasis δ ℂ (RefinedInput (d + 1) J)) (Lprefix : ℕ) (q : ι),
      hilbertSchmidtSq b (refinedKernelPrefix D Lprefix q) ≤
        ((volume.real (Prod.fst '' tsupport κ) * Md ^ 2 * M ^ 2 * unitBallVolume (d + 1)) *
          (1 + (2 : ℝ) ^ (d + 1))) * ((2 : ℝ) ^ J) ^ (d + 1)) := by
  intro D M
  have hMA : 0 ≤ derivativeProfile (d + 1) N Cjet A₀ A₁ B₀ B₁ 0 + Cresp 0 :=
    add_nonneg ((polynomialProfiles_nonneg (d + 1) N hCjet hA₀ hA₁ hB₀ hB₁ 0).2.2.2.2)
      (hCresp 0)
  have hAbound (c : γ) (w) (hw : w ∈ tsupport κ) :
      ‖fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w‖ ≤
        derivativeProfile (d + 1) N Cjet A₀ A₁ B₀ B₁ 0 + Cresp 0 := by
    simpa only [norm_iteratedFDeriv_zero, Nat.zero_sub, pow_zero, mul_one] using
      (fullCorrectedDerivativeAmplitude_joint_bounds T Q F row col Φ Y χ B r
        hjoint hΩ hjointΩ hphase hν₀ hν₁ hV₀ hV₁ hCjet hA₀ hA₁ hB₀ hB₁ hCresp
        (hτ c) (hτ₁ c) hL hpξ hpν₀ hpν₁ hpV₀ hpV₁ (hresponse c)
        (hresponseJets c) 0 (hκsupport hw)).1
  have ha := norm_correctedColoredCrossBandData_amplitude_le T Q F row col Φ Y χ B r κ hκc
    rate hA C hC color hcolor node hnode hP z₀ hρ hcarrier hrate mask hd Md hMd hdb
    hMκ hMC hMA hκbound hCbound hAbound J
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨ha, ?_, ?_⟩
  · intro R hR q
    exact integral_norm_column_sq_le_of_uniform_bounds D (by omega)
      (hκc.image continuous_fst) hR hM hMd D.amplitude_eq_zero ha hdb q
  · intro δ b Lprefix q
    exact hilbertSchmidtSq_refinedKernelPrefix_le_of_uniform_bounds D (by omega)
      (hκc.image continuous_fst) hM hMd D.amplitude_eq_zero ha hdb b Lprefix q

omit [Finite γ] [TopologicalSpace γ] [DiscreteTopology γ] in
/-- The supplied compact extension preserves the corrected amplitude's
original joint reserve. Its fixed cutoff jets and the five raw coefficient
profiles give the exact finite-jet input for the corrected canonical slice;
no derivative bound for the cut amplitude is assumed
(`app:ch_waves:eq:individual-raw-slice`,
`app:ch_response:eq:current-atomic-amplitudes`). -/
theorem cutCorrectedDerivativeAmplitude_joint_bounds_of_profiles
    (hκ : ContDiffOn ℝ ∞ κ Ω) {Aκ : ℕ → ℝ} (hAκ : ∀ j, 0 ≤ Aκ j)
    (hκjets : ∀ j, ∀ w ∈ Kjoint, ‖iteratedFDeriv ℝ j κ w‖ ≤ Aκ j)
    (c : γ) (j : ℕ) {w : Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1))}
    (hw : w ∈ Kjoint) :
    ‖iteratedFDeriv ℝ j (fun w ↦ κ w •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w) w‖ ≤
      productProfile (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
        Matrix (Fin N) (Fin (d + 1)) ℂ →L[ℝ] Matrix (Fin N) (Fin (d + 1)) ℂ)
        Aκ (fun k ↦ derivativeProfile (d + 1) N Cjet A₀ A₁ B₀ B₁ k + Cresp k) j *
          L ^ (j - rpar) := by
  have hraw := (contDiffOn_fullAmplitudes_of_coefficients T Q F row col Φ Y r
    hΩ hphase hν₀ hν₁ hV₀ hV₁ (hτ c).ne').2
  have hr := contDiffOn_fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y r
    hΩ hphase χ B (rate c) (hresponse c)
  have hcorr : ContDiffOn ℝ ∞
      (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c)) Ω := hraw.sub hr
  apply jet_bilinear_le (ContinuousLinearMap.lsmul ℝ ℝ) hΩ hκ hcorr (hjointΩ hw) hL
    hAκ (fun k ↦ add_nonneg
      ((polynomialProfiles_nonneg (d + 1) N hCjet hA₀ hA₁ hB₀ hB₁ k).2.2.2.2) (hCresp k))
  · intro k
    exact (hκjets k w hw).trans (le_mul_of_one_le_right (hAκ k) (one_le_pow₀ hL))
  · intro k
    exact (fullCorrectedDerivativeAmplitude_joint_bounds T Q F row col Φ Y χ B r
      hjoint hΩ hjointΩ hphase hν₀ hν₁ hV₀ hV₁ hCjet hA₀ hA₁ hB₀ hB₁ hCresp
      (hτ c) (hτ₁ c) hL hpξ hpν₀ hpν₁ hpV₀ hpV₁ (hresponse c)
      (hresponseJets c) k hw).1


omit [Finite γ] [TopologicalSpace γ] [DiscreteTopology γ] in
/-- The SAME compact cutoff preserves the inverse-frequency error in every
joint jet. The reference is the literal leading principal matrix with the
same scalar and flow. These jets supply the amplitude-error term in the
corrected transport comparison (`app:ch_waves:eq:colored-normal-comparison`,
`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem cutCorrectedDerivativeAmplitude_error_joint_bounds_of_profiles
    (hκ : ContDiffOn ℝ ∞ κ Ω) {Aκ : ℕ → ℝ} (hAκ : ∀ j, 0 ≤ Aκ j)
    (hκjets : ∀ j, ∀ w ∈ Kjoint, ‖iteratedFDeriv ℝ j κ w‖ ≤ Aκ j)
    (c : γ) (j : ℕ) {w : Euclidean (d + 1) × (Euclidean 3 × Euclidean ((d + 1) - 1))}
    (hw : w ∈ Kjoint) :
    ‖iteratedFDeriv ℝ j (fun w ↦ κ w •
      (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c) w -
        fullLeadingPrincipalMatrix T Q F row col Φ Y r w)) w‖ ≤
      rate c * productProfile (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
        Matrix (Fin N) (Fin (d + 1)) ℂ →L[ℝ] Matrix (Fin N) (Fin (d + 1)) ℂ)
        Aκ (fun k ↦ errorProfile (d + 1) N Cjet A₀ A₁ B₀ B₁ k + Cresp k) j *
          L ^ (j - rpar) := by
  have hraw := (contDiffOn_fullAmplitudes_of_coefficients T Q F row col Φ Y r
    hΩ hphase hν₀ hν₁ hV₀ hV₁ (hτ c).ne').2
  have hr := contDiffOn_fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y r
    hΩ hphase χ B (rate c) (hresponse c)
  have hcorr : ContDiffOn ℝ ∞
      (fullCorrectedDerivativeAmplitude T Q F row col Φ Y χ B r (rate c)) Ω := hraw.sub hr
  have hξ : ContDiffOn ℝ ∞ (fun w ↦ phaseGradient T Q w.1 w.2.2) Ω :=
    (phaseGradient_smooth T Q).comp (contDiffOn_fst.prodMk contDiffOn_snd.snd) hphase
  have hleading : ContDiffOn ℝ ∞ (fullLeadingPrincipalMatrix T Q F row col Φ Y r) Ω := by
    apply (contDiffOn_normalTensor hξ hν₀).neg.congr
    intro x _
    exact fullLeadingPrincipalMatrix_eq_tensor T Q F row col Φ Y r x
  let E := fun k ↦ errorProfile (d + 1) N Cjet A₀ A₁ B₀ B₁ k + Cresp k
  have hE (k) : 0 ≤ E k := add_nonneg
    ((polynomialProfiles_nonneg (d + 1) N hCjet hA₀ hA₁ hB₀ hB₁ k).2.2.2.1) (hCresp k)
  have hb := jet_bilinear_le (ContinuousLinearMap.lsmul ℝ ℝ)
    hΩ hκ (hcorr.sub hleading) (hjointΩ hw) hL hAκ
    (fun k ↦ mul_nonneg (hτ c).le (hE k))
    (fun k ↦ (hκjets k w hw).trans
      (le_mul_of_one_le_right (hAκ k) (one_le_pow₀ hL)))
    (fun k ↦ (fullCorrectedDerivativeAmplitude_joint_bounds T Q F row col Φ Y χ B r
      hjoint hΩ hjointΩ hphase hν₀ hν₁ hV₀ hV₁ hCjet hA₀ hA₁ hB₀ hB₁ hCresp
      (hτ c) (hτ₁ c) hL hpξ hpν₀ hpν₁ hpV₀ hpV₁ (hresponse c)
      (hresponseJets c) k hw).2) j
  apply hb.trans_eq
  dsimp only [productProfile]
  rw [Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end JanetCartan.Sampling
