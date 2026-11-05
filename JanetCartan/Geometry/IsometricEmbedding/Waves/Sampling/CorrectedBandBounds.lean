module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedBandNorm
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedSliceBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CorrectedProfileBounds

/-!
# Sharp original bands for the corrected colored family

Apply the canonical matrix slice estimate to the literal corrected derivative,
using the five retained raw profiles and the SAME response jets. The original
measurement, unmasked zero atom, detector and two annular measures are retained.
The physical cutoff and every constant precede the current field, response,
color rates, scale and band count. The order-zero slice applies below the
coefficient scale as well as above it.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.Sampling
open CanonicalRowComparison CanonicalAtomRealization CorrectedAtoms
open SamplingKernelBounds RawInputPartition RawInputRealization MeasuredAmplitude
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open RawPrimary RawPrimary.SliceBounds MeanNormalBound ProjectedStressFrame
open RawPrimary.AmplitudeGrades RawPrimary.AmplitudeGrades.Polynomial

/-- The actual corrected cross kernel has the sharp squared bound on every
original wide band and both original annular restrictions. The proof constructs
its order-zero Sobolev extension from the retained raw and response jets;
neither a band estimate nor a successful sample is an input. Its geometric
radii precede the immersion budgets, geometric gaps and all coefficient
profiles. The source cap and actual cutoff may therefore be chosen on those
radii before the reference and its derivative budgets
(`app:ch_waves:eq:sampling-operator-bounds`,
`app:ch_response:eq:current-atomic-amplitudes`). -/
theorem exists_uniform_correctedColoredCrossBand_bound_before_immersion_bounds {d : ℕ} (hdim : 1 ≤ d)
    {P : Patch (d + 1)} {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (z₀ : Euclidean 3) (ζ₀ : Euclidean d) {σ : ℝ} (hσ : 0 < σ) :
    ∃ a b e δ : ℝ, 0 < a ∧ 0 < b ∧ 0 < e ∧ 0 < δ ∧
      4 * a ≤ σ / 2 ∧ b ≤ σ / 4 ∧ 16 * e < b ∧ δ ≤ T.family.threshold ∧
    ∃ θ : Euclidean (d + 1) → ℝ,
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      EqOn θ 1 (closedBall 0 (a / 8)) ∧ tsupport θ ⊆ closedBall 0 (a / 4) ∧
    ∀ {Kgeom : Set (Euclidean (d + 1))} (_hKgeom : IsCompact Kgeom) (_hKU : Kgeom ⊆ U)
    (_hball : closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius ⊆ Kgeom)
    (Mgeom : ℝ) {gmetric gnormal : ℝ} (_hgmetric : 0 < gmetric) (_hgnormal : 0 < gnormal)
    (Cjet A₀ A₁ B₀ B₁ Cresp CP : ℕ → ℝ)
    (_hCjet : ∀ k, 0 ≤ Cjet k) (_hA₀ : ∀ k, 0 ≤ A₀ k) (_hA₁ : ∀ k, 0 ≤ A₁ k)
    (_hB₀ : ∀ k, 0 ≤ B₀ k) (_hB₁ : ∀ k, 0 ≤ B₁ k) (_hCresp : ∀ k, 0 ≤ Cresp k)
    (_hCP : ∀ k, 0 ≤ CP k),
    ∀ (Acut : ℕ → ℝ), (∀ k, 0 ≤ Acut k) →
    ∀ (angular : Euclidean d → ℂ) (H : Euclidean d → ℝ)
      (hang : ∀ η, η ≠ 0 → ContDiffAt ℝ ∞ angular η)
      (_hhom : ∀ t : ℝ, 0 < t → ∀ η, angular (t • η) = angular η)
      (hH : ContDiff ℝ ∞ H) (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
      (_hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1),
    ∀ MC : ℝ, 0 ≤ MC →
    ∃ Cband ≥ (0 : ℝ),
    ∀ (F : Euclidean (d + 1) → Euclidean (embeddingDimension (d + 1)))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm Kgeom (20 * (d + 1) + 5) F ≤ Mgeom →
      (∀ x ∈ Kgeom, ∀ v, gmetric * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ Kgeom, ∀ w ∈ normalSpace F x,
        gnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (d + 1)) < δ →
    ∀ hlow : cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (d + 1)) < T.family.threshold,
    let Q : {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1) //
      ContDiffOn ℝ ∞ Q U ∧ cNorm (closedBall (0 : Euclidean (d + 1))
        T.data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress (d + 1)) <
          T.family.threshold} := ⟨projectedStress F,
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) (2 * σ) ⊆ domain T →
    ∀ (row col : Fin (d + 1))
      (Φ Y : ℝ × (Euclidean d × (Euclidean 3 × Euclidean d)) →
        Euclidean d × (Euclidean 3 × Euclidean d))
      (sourceCutoff : Euclidean (d + 1) → ℝ)
      (response : MetricField (d + 1) →ₗ[ℝ]
        (Euclidean (d + 1) → Euclidean (embeddingDimension (d + 1))))
      (r : Euclidean d × Euclidean 3 → ℝ)
      (κcut : Euclidean (d + 1) × (Euclidean 3 × Euclidean d) → ℝ)
      (_hκcut : ContDiff ℝ ∞ κcut) (hκc : HasCompactSupport κcut),
    let Kjoint := closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) σ
    let Ω := ball ((0 : Euclidean (d + 1)), (z₀, ζ₀)) (2 * σ)
    tsupport κcut ⊆ Kjoint →
    (∀ k, ∀ w ∈ Kjoint, ‖iteratedFDeriv ℝ k κcut w‖ ≤ Acut k) →
    ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω →
    ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω →
    ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω →
    ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω →
    ∀ (L : ℝ), 1 ≤ L →
    let rpar := rawSliceParameterOrder (d + 1)
    HasDerivativeProfile Kjoint (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L Cjet →
    HasDerivativeProfile Kjoint (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀ →
    HasDerivativeProfile Kjoint (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
      (rpar + 1) L A₁ →
    HasDerivativeProfile Kjoint (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L B₀ →
    HasDerivativeProfile Kjoint (fullCorrectionReconstruction T Q F row col Φ Y r)
      (rpar + 1) L B₁ →
    (∀ k ≤ rawSliceJetOrder (d + 1) + 1, ∀ w ∈ Kjoint,
      ‖iteratedFDeriv ℝ k (fun q : Euclidean (d + 1) × (Euclidean 3 × Euclidean d) ↦
        fderiv ℝ (phase T Q q.1) q.2.2) w‖ ≤ CP k * L ^ (k - 1 - (rpar + 2))) →
    ∀ {colors : Type*} [Finite colors] [TopologicalSpace colors] [DiscreteTopology colors]
      (rate : colors → ℝ) (hτ : ∀ c, 0 < rate c) (_hτ₁ : ∀ c, rate c ≤ 1),
    (∀ c, ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y sourceCutoff response (rate c) r w.2 w.1) Ω) →
    (∀ c k, ∀ w ∈ Kjoint,
      ‖iteratedFDeriv ℝ k (fullPrimaryResponseDerivativeAmplitude
        T Q F row col Φ Y sourceCutoff response r (rate c)) w‖ ≤
          rate c * Cresp k * L ^ (k - rpar)) →
    ∀ (hA : ∀ c, Continuous (fun w ↦ κcut w •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y sourceCutoff response r (rate c) w))
      (C : Euclidean (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →L[ℝ] Euclidean (d + 1))
      (hC : Continuous C),
    (∀ x, ‖C x‖ ≤ MC) → Function.support C ⊆ closedBall 0 (a / 8) →
    ∀ {ι : Type*} [TopologicalSpace ι] [FirstCountableTopology ι] [LocallyCompactSpace ι]
      (color : ι → colors) (hcolor : Continuous color)
      (node : ι → Euclidean 3) (hnode : Continuous node)
      (hcarrier : closedBall z₀ (2 * σ) ⊆ parameterInterior (2 * P.radius))
      (Md : ℝ) (hMd : 0 ≤ Md)
      (hdb : ∀ η, ‖MaskProfiles.detectorMask (n := d + 1) angular H η‖ ≤ Md)
      (J : ℕ) (p : ι),
    node p ∈ parameterCube P.radius →
    (node p, T.reference.spatialPatch (node p)) ∈ ball (z₀, ζ₀) (σ / 4) →
    ∀ j : Fin J, 2 * (rate (color p) * (2 : ℝ) ^ j.val) ≤ e →
    let D := correctedColoredCrossBandData T Q F row col Φ Y sourceCutoff response r κcut hκc
      rate hA C hC color hcolor node hnode hP z₀ hσ hcarrier (fun c ↦ (hτ c).ne')
      (MaskProfiles.detectorMask angular H)
      (MaskProfiles.contDiff_detectorMask (n := d + 1) angular H hang hH hH₀).continuous Md hMd hdb J
    ‖wideBandKernelOperator D j.val (j, p)‖ ^ 2 ≤ Cband * (2 : ℝ) ^ j.val ∧
      ∀ q : Fin 2, ‖D.operator (refinedRadius (j, q)) (j, p)‖ ^ 2 ≤
        Cband * refinedRadius (j, q) := by
  obtain ⟨a, b, e, δ, ha, hb, he, hδ, hacap, hbcap, heb, hδcap,
    θ, hθ, hθc, hθone, hθsmall, hsliceGeometry⟩ :=
    exists_uniform_canonical_cutCorrectedSliceSobolev_before_immersion_bounds hdim hP T z₀ ζ₀ hσ
  refine ⟨a, b, e, δ, ha, hb, he, hδ, hacap, hbcap, heb, hδcap,
    θ, hθ, hθc, hθone, hθsmall, ?_⟩
  intro Kgeom hKgeom hKU hball Mgeom gmetric gnormal hgmetric hgnormal
    Cjet A₀ A₁ B₀ B₁ Cresp CP hCjet hA₀ hA₁ hB₀ hB₁ hCresp hCP
    Acut hAcut angular H hang hhom hH hH₀ hH₁ MC hMC
  have hslice := hsliceGeometry hKgeom hKU hball Mgeom hgmetric hgnormal
  let CA := productProfile (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ]
    Matrix (Fin (embeddingDimension (d + 1))) (Fin (d + 1)) ℂ →L[ℝ]
      Matrix (Fin (embeddingDimension (d + 1))) (Fin (d + 1)) ℂ)
    Acut (fun k ↦ derivativeProfile (d + 1) (embeddingDimension (d + 1)) Cjet A₀ A₁ B₀ B₁ k + Cresp k)
  have hCA (k) : 0 ≤ CA k := productProfile_nonneg _ hAcut
    (fun k ↦ add_nonneg ((polynomialProfiles_nonneg (d + 1) (embeddingDimension (d + 1))
      hCjet hA₀ hA₁ hB₀ hB₁ k).2.2.2.2) (hCresp k)) k
  obtain ⟨Bslice, hBslice, hbound⟩ := hslice CA CP hCA hCP (fun _ ↦ angular) H univ isOpen_univ (subset_univ _)
    (fun _ _ η hη ↦ (hang η hη).comp _ contDiffAt_snd) (fun _ ↦ hhom) hH hH₀ hH₁
  let cf : ℝ := (2 * Real.pi) ^ (-((d + 1 : ℕ) : ℝ) / 2)
  have hcf : 0 < cf := Real.rpow_pos_of_pos (by positivity) _
  let Cband := (cf * (2 * MC * CA 0) * Bslice 0) ^ 2
  refine ⟨Cband, sq_nonneg _, ?_⟩
  intro F hF hi hrank hFM hmetric hnormal hclose hlow Q hphase row col Φ Y sourceCutoff response r
    κcut hκcut hκc Kjoint Ω hκsupport hκjets hν₀ hν₁ hV₀ hV₁ L hL rpar hpξ hpν₀ hpν₁ hpV₀ hpV₁
    hpD colors _ _ _ rate hτ hτ₁ hresponse hresponseJets hA C hC hCbound hCsupport
    ι _ _ _ color hcolor node hnode hcarrier Md hMd hdb J p hz hzball j hwin D
  have hjoint : IsCompact Kjoint := isCompact_closedBall _ _
  have hΩ : IsOpen Ω := isOpen_ball
  have hjointΩ : Kjoint ⊆ Ω := closedBall_subset_ball (by linarith)
  have hphaseΩ : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T :=
    fun w hw ↦ hphase (ball_subset_closedBall hw)
  have hraw := (contDiffOn_fullAmplitudes_of_coefficients T Q F row col Φ Y r
    hΩ hphaseΩ hν₀ hν₁ hV₀ hV₁ (hτ (color p)).ne').2
  have hresponse' := contDiffOn_fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y r
    hΩ hphaseΩ sourceCutoff response (rate (color p)) (hresponse (color p))
  have hAsmooth := hκcut.contDiffOn.smul (hraw.sub hresponse')
  have hAj (k : ℕ) (w) (hw : w ∈ Kjoint) :
      ‖iteratedFDeriv ℝ k (fun w ↦ κcut w • fullCorrectedDerivativeAmplitude
        T Q F row col Φ Y sourceCutoff response r (rate (color p)) w) w‖ ≤
          CA k * L ^ (k - rpar) :=
    cutCorrectedDerivativeAmplitude_joint_bounds_of_profiles
      T Q F row col Φ Y sourceCutoff response r κcut rate hjoint hΩ hjointΩ hphaseΩ
      hν₀ hν₁ hV₀ hV₁ hCjet hA₀ hA₁ hB₀ hB₁ hCresp hτ hτ₁ hL hpξ hpν₀ hpν₁ hpV₀ hpV₁
      hresponse hresponseJets hκcut.contDiffOn hAcut hκjets (color p) k hw
  have hzero (x) : ‖κcut (x, node p, T.reference.spatialPatch (node p)) •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y sourceCutoff response r
        (rate (color p)) (x, node p, T.reference.spatialPatch (node p))‖ ≤ CA 0 := by
    by_cases hw : (x, node p, T.reference.spatialPatch (node p)) ∈ tsupport κcut
    · simpa only [norm_iteratedFDeriv_zero, Nat.zero_sub, pow_zero, mul_one] using
        hAj 0 _ (hκsupport hw)
    · rw [image_eq_zero_of_notMem_tsupport hw, zero_smul, norm_zero]
      exact hCA 0
  have hK : 1 ≤ (2 : ℝ) ^ j.val := one_le_pow₀ (by norm_num)
  have hscale : |rate (color p)| * (2 : ℝ) ^ j.val ≤ σ / 8 := by
    rw [abs_of_pos (hτ (color p))]
    linarith
  have hCsupport' : Function.support C ⊆ closedBall 0 (σ / 2) :=
    hCsupport.trans (closedBall_subset_closedBall (by linarith))
  let mask := MaskProfiles.detectorMask (n := d + 1) angular H
  have hd : Continuous mask := (MaskProfiles.contDiff_detectorMask (n := d + 1) angular H hang hH hH₀).continuous
  let j' : Fin (cutoffCount ((2 : ℝ) ^ j.val)) :=
    ⟨j.val, by rw [cutoffCount_two_pow]; omega⟩
  have hCAzero : 0 ≤ CA 0 := hCA 0
  have hBzero : 0 < Bslice 0 := hBslice 0
  have hwide : ‖wideBandKernelOperator D j.val (j, p)‖ ≤
      cf * (2 * MC * CA 0) * Bslice 0 * ((2 : ℝ) ^ j.val) ^ (1 / 2 : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro f
    obtain ⟨u, _hu, ext, hext, _hjet, hnorm, _hcart, _hres⟩ := hbound F hF hi hrank
      hFM hmetric hnormal hclose hlow
      ((closedBall_subset_closedBall (by linarith : σ ≤ 2 * σ)).trans hphase)
      (node p) hz hzball row col Φ Y sourceCutoff response r κcut
      ((2 : ℝ) ^ j.val) L (rate (color p)) hK hL (hτ (color p)) hwin hAsmooth 0
      (Or.inr rfl) (fun k _ w hw ↦ hAj k w hw)
      (fun k hk w hw ↦ hpD k (by simpa only [zero_add] using hk) w hw)
      (PiLp.single 2 j' f) univ
    have ht := norm_correctedColoredCrossBandData_wideBand_le_original_slice
      T Q F row col Φ Y sourceCutoff response r κcut hκc rate hA C hC color hcolor node hnode
      hP z₀ hσ hcarrier (fun c ↦ (hτ c).ne') mask hd Md hMd hdb ζ₀ hphase hCsupport'
      J j p (ball_subset_closedBall hzball) hscale f θ ext hext
      (fun x hx ↦ hθone (hCsupport hx)) hMC (hCA 0) hCbound hzero
    have hn : ext.jetNorm ≤ Bslice 0 * ((2 : ℝ) ^ j.val) ^ (1 / 2 : ℝ) * ‖f‖ := by
      simpa only [Nat.cast_zero, zero_add, PiLp.norm_single] using hnorm
    exact ht.trans ((mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (by ring))
  have hsq : ‖wideBandKernelOperator D j.val (j, p)‖ ^ 2 ≤ Cband * (2 : ℝ) ^ j.val := by
    apply (pow_le_pow_left₀ (norm_nonneg _) hwide 2).trans_eq
    have hsqrt : (((2 : ℝ) ^ j.val) ^ (1 / 2 : ℝ)) ^ 2 = (2 : ℝ) ^ j.val := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show (1 / 2 : ℝ) * (2 : ℕ) = 1 by norm_num, Real.rpow_one]
    rw [mul_pow, hsqrt]
  refine ⟨hsq, ?_⟩
  intro q
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_annularOperator_le_wideBand D j.val (j, p) q) 2).trans
  apply hsq.trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)

/-- Preserve the original sharp-band interface by specializing the
construction with geometry before the immersion and coefficient budgets
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_uniform_correctedColoredCrossBand_bound_before_cutoff {d : ℕ} (hdim : 1 ≤ d)
    {P : Patch (d + 1)} {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (z₀ : Euclidean 3) (ζ₀ : Euclidean d) {σ : ℝ} (hσ : 0 < σ)
    {Kgeom : Set (Euclidean (d + 1))} (hKgeom : IsCompact Kgeom) (hKU : Kgeom ⊆ U)
    (hball : closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius ⊆ Kgeom)
    (Mgeom : ℝ) {gmetric gnormal : ℝ} (hgmetric : 0 < gmetric) (hgnormal : 0 < gnormal)
    (Cjet A₀ A₁ B₀ B₁ Cresp CP : ℕ → ℝ)
    (hCjet : ∀ k, 0 ≤ Cjet k) (hA₀ : ∀ k, 0 ≤ A₀ k) (hA₁ : ∀ k, 0 ≤ A₁ k)
    (hB₀ : ∀ k, 0 ≤ B₀ k) (hB₁ : ∀ k, 0 ≤ B₁ k) (hCresp : ∀ k, 0 ≤ Cresp k)
    (hCP : ∀ k, 0 ≤ CP k) :
    ∃ a b e δ : ℝ, 0 < a ∧ 0 < b ∧ 0 < e ∧ 0 < δ ∧
      4 * a ≤ σ / 2 ∧ b ≤ σ / 4 ∧ 16 * e < b ∧ δ ≤ T.family.threshold ∧
    ∃ θ : Euclidean (d + 1) → ℝ,
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      EqOn θ 1 (closedBall 0 (a / 8)) ∧ tsupport θ ⊆ closedBall 0 (a / 4) ∧
    ∀ (Acut : ℕ → ℝ), (∀ k, 0 ≤ Acut k) →
    ∀ (angular : Euclidean d → ℂ) (H : Euclidean d → ℝ)
      (hang : ∀ η, η ≠ 0 → ContDiffAt ℝ ∞ angular η)
      (_hhom : ∀ t : ℝ, 0 < t → ∀ η, angular (t • η) = angular η)
      (hH : ContDiff ℝ ∞ H) (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
      (_hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1),
    ∀ MC : ℝ, 0 ≤ MC →
    ∃ Cband ≥ (0 : ℝ),
    ∀ (F : Euclidean (d + 1) → Euclidean (embeddingDimension (d + 1)))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm Kgeom (20 * (d + 1) + 5) F ≤ Mgeom →
      (∀ x ∈ Kgeom, ∀ v, gmetric * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ Kgeom, ∀ w ∈ normalSpace F x,
        gnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (d + 1)) < δ →
    ∀ hlow : cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (d + 1)) < T.family.threshold,
    let Q : {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1) //
      ContDiffOn ℝ ∞ Q U ∧ cNorm (closedBall (0 : Euclidean (d + 1))
        T.data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress (d + 1)) <
          T.family.threshold} := ⟨projectedStress F,
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) (2 * σ) ⊆ domain T →
    ∀ (row col : Fin (d + 1))
      (Φ Y : ℝ × (Euclidean d × (Euclidean 3 × Euclidean d)) →
        Euclidean d × (Euclidean 3 × Euclidean d))
      (sourceCutoff : Euclidean (d + 1) → ℝ)
      (response : MetricField (d + 1) →ₗ[ℝ]
        (Euclidean (d + 1) → Euclidean (embeddingDimension (d + 1))))
      (r : Euclidean d × Euclidean 3 → ℝ)
      (κcut : Euclidean (d + 1) × (Euclidean 3 × Euclidean d) → ℝ)
      (_hκcut : ContDiff ℝ ∞ κcut) (hκc : HasCompactSupport κcut),
    let Kjoint := closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) σ
    let Ω := ball ((0 : Euclidean (d + 1)), (z₀, ζ₀)) (2 * σ)
    tsupport κcut ⊆ Kjoint →
    (∀ k, ∀ w ∈ Kjoint, ‖iteratedFDeriv ℝ k κcut w‖ ≤ Acut k) →
    ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω →
    ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω →
    ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω →
    ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω →
    ∀ (L : ℝ), 1 ≤ L →
    let rpar := rawSliceParameterOrder (d + 1)
    HasDerivativeProfile Kjoint (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L Cjet →
    HasDerivativeProfile Kjoint (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀ →
    HasDerivativeProfile Kjoint (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
      (rpar + 1) L A₁ →
    HasDerivativeProfile Kjoint (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L B₀ →
    HasDerivativeProfile Kjoint (fullCorrectionReconstruction T Q F row col Φ Y r)
      (rpar + 1) L B₁ →
    (∀ k ≤ rawSliceJetOrder (d + 1) + 1, ∀ w ∈ Kjoint,
      ‖iteratedFDeriv ℝ k (fun q : Euclidean (d + 1) × (Euclidean 3 × Euclidean d) ↦
        fderiv ℝ (phase T Q q.1) q.2.2) w‖ ≤ CP k * L ^ (k - 1 - (rpar + 2))) →
    ∀ {colors : Type*} [Finite colors] [TopologicalSpace colors] [DiscreteTopology colors]
      (rate : colors → ℝ) (hτ : ∀ c, 0 < rate c) (_hτ₁ : ∀ c, rate c ≤ 1),
    (∀ c, ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y sourceCutoff response (rate c) r w.2 w.1) Ω) →
    (∀ c k, ∀ w ∈ Kjoint,
      ‖iteratedFDeriv ℝ k (fullPrimaryResponseDerivativeAmplitude
        T Q F row col Φ Y sourceCutoff response r (rate c)) w‖ ≤
          rate c * Cresp k * L ^ (k - rpar)) →
    ∀ (hA : ∀ c, Continuous (fun w ↦ κcut w •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y sourceCutoff response r (rate c) w))
      (C : Euclidean (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →L[ℝ] Euclidean (d + 1))
      (hC : Continuous C),
    (∀ x, ‖C x‖ ≤ MC) → Function.support C ⊆ closedBall 0 (a / 8) →
    ∀ {ι : Type*} [TopologicalSpace ι] [FirstCountableTopology ι] [LocallyCompactSpace ι]
      (color : ι → colors) (hcolor : Continuous color)
      (node : ι → Euclidean 3) (hnode : Continuous node)
      (hcarrier : closedBall z₀ (2 * σ) ⊆ parameterInterior (2 * P.radius))
      (Md : ℝ) (hMd : 0 ≤ Md)
      (hdb : ∀ η, ‖MaskProfiles.detectorMask (n := d + 1) angular H η‖ ≤ Md)
      (J : ℕ) (p : ι),
    node p ∈ parameterCube P.radius →
    (node p, T.reference.spatialPatch (node p)) ∈ ball (z₀, ζ₀) (σ / 4) →
    ∀ j : Fin J, 2 * (rate (color p) * (2 : ℝ) ^ j.val) ≤ e →
    let D := correctedColoredCrossBandData T Q F row col Φ Y sourceCutoff response r κcut hκc
      rate hA C hC color hcolor node hnode hP z₀ hσ hcarrier (fun c ↦ (hτ c).ne')
      (MaskProfiles.detectorMask angular H)
      (MaskProfiles.contDiff_detectorMask (n := d + 1) angular H hang hH hH₀).continuous Md hMd hdb J
    ‖wideBandKernelOperator D j.val (j, p)‖ ^ 2 ≤ Cband * (2 : ℝ) ^ j.val ∧
      ∀ q : Fin 2, ‖D.operator (refinedRadius (j, q)) (j, p)‖ ^ 2 ≤
        Cband * refinedRadius (j, q) := by
  obtain ⟨a, b, e, δ, ha, hb, he, hδ, hacap, hbcap, heb, hδcap,
    θ, hθ, hθc, hθone, hθsmall, hall⟩ :=
    exists_uniform_correctedColoredCrossBand_bound_before_immersion_bounds hdim hP T z₀ ζ₀ hσ
  exact ⟨a, b, e, δ, ha, hb, he, hδ, hacap, hbcap, heb, hδcap,
    θ, hθ, hθc, hθone, hθsmall,
    hall hKgeom hKU hball Mgeom hgmetric hgnormal Cjet A₀ A₁ B₀ B₁ Cresp CP
      hCjet hA₀ hA₁ hB₀ hB₁ hCresp hCP⟩

/-- Preserve the original corrected sharp-band interface by specializing
its geometry, which is independent of the cutoff derivative budget
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_uniform_correctedColoredCrossBand_bound_of_profiles {d : ℕ} (hdim : 1 ≤ d)
    {P : Patch (d + 1)} {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (z₀ : Euclidean 3) (ζ₀ : Euclidean d) {σ : ℝ} (hσ : 0 < σ)
    {Kgeom : Set (Euclidean (d + 1))} (hKgeom : IsCompact Kgeom) (hKU : Kgeom ⊆ U)
    (hball : closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius ⊆ Kgeom)
    (Mgeom : ℝ) {gmetric gnormal : ℝ} (hgmetric : 0 < gmetric) (hgnormal : 0 < gnormal)
    (Cjet A₀ A₁ B₀ B₁ Cresp Acut CP : ℕ → ℝ)
    (hCjet : ∀ k, 0 ≤ Cjet k) (hA₀ : ∀ k, 0 ≤ A₀ k) (hA₁ : ∀ k, 0 ≤ A₁ k)
    (hB₀ : ∀ k, 0 ≤ B₀ k) (hB₁ : ∀ k, 0 ≤ B₁ k) (hCresp : ∀ k, 0 ≤ Cresp k)
    (hAcut : ∀ k, 0 ≤ Acut k) (hCP : ∀ k, 0 ≤ CP k) :
    ∃ a b e δ : ℝ, 0 < a ∧ 0 < b ∧ 0 < e ∧ 0 < δ ∧
      4 * a ≤ σ / 2 ∧ b ≤ σ / 4 ∧ 16 * e < b ∧ δ ≤ T.family.threshold ∧
    ∃ θ : Euclidean (d + 1) → ℝ,
      ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      EqOn θ 1 (closedBall 0 (a / 8)) ∧ tsupport θ ⊆ closedBall 0 (a / 4) ∧
    ∀ (angular : Euclidean d → ℂ) (H : Euclidean d → ℝ)
      (hang : ∀ η, η ≠ 0 → ContDiffAt ℝ ∞ angular η)
      (_hhom : ∀ t : ℝ, 0 < t → ∀ η, angular (t • η) = angular η)
      (hH : ContDiff ℝ ∞ H) (hH₀ : ∀ η, ‖η‖ ≤ 1 → H η = 0)
      (_hH₁ : ∀ η, 2 ≤ ‖η‖ → H η = 1),
    ∀ MC : ℝ, 0 ≤ MC →
    ∃ Cband ≥ (0 : ℝ),
    ∀ (F : Euclidean (d + 1) → Euclidean (embeddingDimension (d + 1)))
      (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
      cNorm Kgeom (20 * (d + 1) + 5) F ≤ Mgeom →
      (∀ x ∈ Kgeom, ∀ v, gmetric * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ Kgeom, ∀ w ∈ normalSpace F x,
        gnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (d + 1)) < δ →
    ∀ hlow : cNorm (closedBall (0 : Euclidean (d + 1)) T.data.localReference.stateRadius) 6
        (projectedStress F - fun _ ↦ cubeStress (d + 1)) < T.family.threshold,
    let Q : {Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1) //
      ContDiffOn ℝ ∞ Q U ∧ cNorm (closedBall (0 : Euclidean (d + 1))
        T.data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress (d + 1)) <
          T.family.threshold} := ⟨projectedStress F,
      contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
    closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) (2 * σ) ⊆ domain T →
    ∀ (row col : Fin (d + 1))
      (Φ Y : ℝ × (Euclidean d × (Euclidean 3 × Euclidean d)) →
        Euclidean d × (Euclidean 3 × Euclidean d))
      (sourceCutoff : Euclidean (d + 1) → ℝ)
      (response : MetricField (d + 1) →ₗ[ℝ]
        (Euclidean (d + 1) → Euclidean (embeddingDimension (d + 1))))
      (r : Euclidean d × Euclidean 3 → ℝ)
      (κcut : Euclidean (d + 1) × (Euclidean 3 × Euclidean d) → ℝ)
      (_hκcut : ContDiff ℝ ∞ κcut) (hκc : HasCompactSupport κcut),
    let Kjoint := closedBall ((0 : Euclidean (d + 1)), (z₀, ζ₀)) σ
    let Ω := ball ((0 : Euclidean (d + 1)), (z₀, ζ₀)) (2 * σ)
    tsupport κcut ⊆ Kjoint →
    (∀ k, ∀ w ∈ Kjoint, ‖iteratedFDeriv ℝ k κcut w‖ ≤ Acut k) →
    ContDiffOn ℝ ∞ (fullLeadingNormal T Q F row col Φ Y r) Ω →
    ContDiffOn ℝ ∞ (fullCorrectionPrincipalNormal T Q F row col Φ Y r) Ω →
    ContDiffOn ℝ ∞ (fullLeadingReconstruction T Q F row col Φ Y r) Ω →
    ContDiffOn ℝ ∞ (fullCorrectionReconstruction T Q F row col Φ Y r) Ω →
    ∀ (L : ℝ), 1 ≤ L →
    let rpar := rawSliceParameterOrder (d + 1)
    HasDerivativeProfile Kjoint (fun w ↦ phaseGradient T Q w.1 w.2.2) (rpar + 3) L Cjet →
    HasDerivativeProfile Kjoint (fullLeadingNormal T Q F row col Φ Y r) (rpar + 2) L A₀ →
    HasDerivativeProfile Kjoint (fullCorrectionPrincipalNormal T Q F row col Φ Y r)
      (rpar + 1) L A₁ →
    HasDerivativeProfile Kjoint (fullLeadingReconstruction T Q F row col Φ Y r) (rpar + 2) L B₀ →
    HasDerivativeProfile Kjoint (fullCorrectionReconstruction T Q F row col Φ Y r)
      (rpar + 1) L B₁ →
    (∀ k ≤ rawSliceJetOrder (d + 1) + 1, ∀ w ∈ Kjoint,
      ‖iteratedFDeriv ℝ k (fun q : Euclidean (d + 1) × (Euclidean 3 × Euclidean d) ↦
        fderiv ℝ (phase T Q q.1) q.2.2) w‖ ≤ CP k * L ^ (k - 1 - (rpar + 2))) →
    ∀ {colors : Type*} [Finite colors] [TopologicalSpace colors] [DiscreteTopology colors]
      (rate : colors → ℝ) (hτ : ∀ c, 0 < rate c) (_hτ₁ : ∀ c, rate c ≤ 1),
    (∀ c, ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y sourceCutoff response (rate c) r w.2 w.1) Ω) →
    (∀ c k, ∀ w ∈ Kjoint,
      ‖iteratedFDeriv ℝ k (fullPrimaryResponseDerivativeAmplitude
        T Q F row col Φ Y sourceCutoff response r (rate c)) w‖ ≤
          rate c * Cresp k * L ^ (k - rpar)) →
    ∀ (hA : ∀ c, Continuous (fun w ↦ κcut w •
      fullCorrectedDerivativeAmplitude T Q F row col Φ Y sourceCutoff response r (rate c) w))
      (C : Euclidean (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ →L[ℝ] Euclidean (d + 1))
      (hC : Continuous C),
    (∀ x, ‖C x‖ ≤ MC) → Function.support C ⊆ closedBall 0 (a / 8) →
    ∀ {ι : Type*} [TopologicalSpace ι] [FirstCountableTopology ι] [LocallyCompactSpace ι]
      (color : ι → colors) (hcolor : Continuous color)
      (node : ι → Euclidean 3) (hnode : Continuous node)
      (hcarrier : closedBall z₀ (2 * σ) ⊆ parameterInterior (2 * P.radius))
      (Md : ℝ) (hMd : 0 ≤ Md)
      (hdb : ∀ η, ‖MaskProfiles.detectorMask (n := d + 1) angular H η‖ ≤ Md)
      (J : ℕ) (p : ι),
    node p ∈ parameterCube P.radius →
    (node p, T.reference.spatialPatch (node p)) ∈ ball (z₀, ζ₀) (σ / 4) →
    ∀ j : Fin J, 2 * (rate (color p) * (2 : ℝ) ^ j.val) ≤ e →
    let D := correctedColoredCrossBandData T Q F row col Φ Y sourceCutoff response r κcut hκc
      rate hA C hC color hcolor node hnode hP z₀ hσ hcarrier (fun c ↦ (hτ c).ne')
      (MaskProfiles.detectorMask angular H)
      (MaskProfiles.contDiff_detectorMask (n := d + 1) angular H hang hH hH₀).continuous Md hMd hdb J
    ‖wideBandKernelOperator D j.val (j, p)‖ ^ 2 ≤ Cband * (2 : ℝ) ^ j.val ∧
      ∀ q : Fin 2, ‖D.operator (refinedRadius (j, q)) (j, p)‖ ^ 2 ≤
        Cband * refinedRadius (j, q) := by
  obtain ⟨a, b, e, δ, ha, hb, he, hδ, hacap, hbcap, heb, hδcap,
      θ, hθ, hθc, hθone, hθsmall, hband⟩ :=
    exists_uniform_correctedColoredCrossBand_bound_before_cutoff hdim hP T z₀ ζ₀ hσ
      hKgeom hKU hball Mgeom hgmetric hgnormal Cjet A₀ A₁ B₀ B₁ Cresp CP
      hCjet hA₀ hA₁ hB₀ hB₁ hCresp hCP
  exact ⟨a, b, e, δ, ha, hb, he, hδ, hacap, hbcap, heb, hδcap,
    θ, hθ, hθc, hθone, hθsmall, hband Acut hAcut⟩

end JanetCartan.Sampling
