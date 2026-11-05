module

public import JanetCartan.Iteration.PhysicalSmoothing
public import JanetCartan.Iteration.PhysicalSmoothing.Measurement
public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.ProductBounds.Profiles

/-!
# Original-data measured normalized sources at the revised exponents

The source term of `new:eq:mean-source` is constructed on the SAME smooth
auxiliary source space as the finite Picard run.  Physical finite-moment
smoothing, the actual geometric measurement producer, exact localized tensor
norm transfer, and the derivative convolution are all instantiated here.
The same-event background residual and aggregated E/Q estimates are separate
obligations: this theorem does not assert the completed mean solver.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.PhysicalSmoothing

open LocalSobolev CurrentMean ContinuumRow CanonicalCarrier CorrectedPositiveInverse
  ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame AmplitudeBound
  DefectSmoothing AuxiliaryRawBand

private theorem measured_power_le_admissible (n s : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    R ^ ((s : ℝ) - 2 * RevisedScales.forcingExponent n) ≤
      R ^ (-separationExponent) * R ^ (s - RevisedScales.sourceOrder n) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  rw [← Real.rpow_natCast R (s - RevisedScales.sourceOrder n), ← Real.rpow_add hRp]
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hs : (s : ℝ) ≤ (RevisedScales.sourceOrder n : ℝ) +
      ((s - RevisedScales.sourceOrder n : ℕ) : ℝ) := by
    exact_mod_cast (show s ≤ RevisedScales.sourceOrder n + (s - RevisedScales.sourceOrder n) by omega)
  have hgap := (RevisedScales.source_order_and_forcing_gap n).2.2.1
  have hβ : separationExponent < 1 := by norm_num [separationExponent]
  linarith

/-- The actual measured normalized source for the finite same-source run
(`new:eq:mean-source`, `main:prop:mean`).  The measurement is the literal
corrected canonical carrier's measurement on `projectedStress F`, with the
original fixed cutoff.  The finite-moment source uses the prescribed work
domain and the ORIGINAL normalized target and physical Schwartz history.

The initial geometry threshold, target interval and compact support precede
accuracy.  For each finite smoothing order, all constants precede the target
parameter, history, current defect, carrier flow and background density.
Only the current defect budget and original geometric inclusions are inputs;
there is no measured-source profile or solver-success premise. -/
theorem exists_original_measured_normalized_source_profiles {n : ℕ}
    (D : LocalDomain) (G : FlatReference n) {ρ : ℝ} (hρ : 0 < ρ)
    {g : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (h0 : (0 : Euclidean n) ∈ U) (hg : IsRiemannianMetricOn g U) (hg0 : g 0 = 1)
    {r Rc : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (h4rRc : 4 * r < Rc) (hRc : Rc < G.domain.chartRadius)
    {B : ℝ} (hB : 1 ≤ B) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
      (∀ s ∈ Icc (0 : ℝ) s₀, ∀ x ∈ D.closureChart n, (s * ρ) • x ∈ U) ∧
      ∃ K : Set (Euclidean n), IsCompact K ∧ K ⊆ D.chart n ∧
      ∀ m : ℕ, 1 ≤ m → ∃ (Rmin : ℝ) (C : ℕ → ℝ),
        2 ≤ Rmin ∧ (2 : ℝ) * m ≤ Rmin ∧ (∀ q, 0 < C q) ∧
        ∀ s ∈ Icc (0 : ℝ) s₀, ∀ R₀ : ℝ, S ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
          (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
        let R := iterationScale R₀ growthExponent j
        Rmin ≤ R → ∀ δ : ℝ, 0 < δ →
        cNorm (D.core n) 0
          (inducedMetric (RevisedGlobal.finiteMap G.map u) - scaledMetric g (s * ρ)) ≤ δ ^ 2 →
        let gs := scaledMetric g (s * ρ)
        let F := RevisedGlobal.finiteMap G.map u
        ContDiff ℝ ∞ (normalizedSource D R m δ gs G.map u) ∧
        tsupport (normalizedSource D R m δ gs G.map u) ⊆ K ∧
        ∀ {P : Patch n} (T : PatchQuantitativeFamily P (ball 0 Rc) isOpen_ball)
          (Q : {Q : Euclidean n → Fin n → MetricTensor n //
            ContDiffOn ℝ ∞ Q (ball 0 Rc) ∧
            cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
              (Q - fun _ ↦ cubeStress n) < T.family.threshold}),
        Q.1 = projectedStress F → ∀ (row col : Fin n)
          (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
          (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
          (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ)
          (w : CarrierVariable n → ℝ),
        let d := correctedCarrierData (data T Q F row col Φ Y initial hr hcell angular high) w
        ∃ target : SmoothResidual n,
          (∀ z, target.val z () = measuredNormalizedSource d D R m δ gs G.map u z) ∧
          (∀ q : ℕ, periodicSobolevNorm q (fun z ↦ target.val z ()) ≤
            C q * R ^ ((q : ℝ) - 2 * RevisedScales.forcingExponent n)) ∧
          (periodicSobolevNorm (RevisedScales.sourceOrder n) (fun z ↦ target.val z ()) ≤
            C (RevisedScales.sourceOrder n) * R ^ (-1 : ℝ)) ∧
          (∀ q : ℕ, periodicSobolevNorm q (fun z ↦ target.val z ()) ≤
            C q * R ^ (-separationExponent) * R ^ (q - RevisedScales.sourceOrder n)) := by
  have honeStar : (1 : ℝ) ≤ rStar := by exact_mod_cast (show 1 ≤ rStar by omega)
  have hband : 0 ≤ bandExponent := by norm_num [bandExponent]
  have horderOne : RevisedScales.displacementLoss n +
      bandExponent * (1 + (n : ℝ) / 2) + 2 < (kMin : ℝ) := by nlinarith
  obtain ⟨S, hS, A, hA, hmeasurement⟩ :=
    exists_history_preparation_measurement_profiles G hr hcell h4rRc hRc hB hStar
      (reserve := 0) (by omega) horder
  obtain ⟨s₀, hs₀, hs₁, hmaps, K, hK, hKD, hsmoothing⟩ :=
    exists_original_target_history_smoothing D G hρ hU h0 hg hg0 hB horderOne
  refine ⟨S, hS, s₀, hs₀, hs₁, hmaps, K, hK, hKD, ?_⟩
  intro m hm
  obtain ⟨Rmin, _L, Ln, _Cs, _Ch, hRmin, hRm, _hL, hLn, _hCs, _hCh, hsmooth⟩ := hsmoothing m hm
  let H : ℕ → ℝ := fun q ↦ Real.sqrt (q.factorial : ℝ) * Ln q
  let C : ℕ → ℝ := fun q ↦ 1 + coefficientBandConstant n q A H
  have hC (q : ℕ) : 0 < C q := by
    have := coefficientBandConstant_nonneg n q A H
    dsimp only [C]
    linarith
  refine ⟨Rmin, C, hRmin, hRm, hC, ?_⟩
  intro s hs R₀ hR₀ j u ell hu R hR δ hδ hsmall gs F
  have hR₀two : 2 ≤ R₀ := hS.trans hR₀
  have hRone : 1 ≤ R := (by norm_num : (1 : ℝ) ≤ 2).trans (hRmin.trans hR)
  have hRpos : 0 < R := zero_lt_one.trans_le hRone
  obtain ⟨_, _, _, _, _, _, _, _, hsource, hsourceSupp, _, _, _, hsourceProfile, _, _, _⟩ :=
    hsmooth s hs R₀ hR₀two j u ell hu hR δ hδ hsmall
  refine ⟨hsource, hsourceSupp, ?_⟩
  intro P T Q hQ row col Φ Y initial angular high w d
  obtain ⟨hmeas, hmeasProfile⟩ := hmeasurement R₀ hR₀ j u ell hu
    T Q hQ row col Φ Y initial angular high w
  let f := tensorPeriodization (normalizedSource D R m δ gs G.map u)
  have hf : IsSmoothPeriodic f := isSmoothPeriodic_tensorPeriodization
    D.chartRadius_lt_half (hsourceSupp.trans hKD) hsource
  have hout : IsSmoothPeriodic (measuredNormalizedSource d D R m δ gs G.map u) :=
    ⟨hmeas.1.clm_apply hf.1, hmeas.2.clm_apply hf.2⟩
  let target : SmoothResidual n := ⟨fun z _ ↦ measuredNormalizedSource d D R m δ gs G.map u z,
    fun _ ↦ hout⟩
  have hsplit (q : ℕ) : R ^ q * R ^ (-2 * RevisedScales.forcingExponent n) =
      R ^ ((q : ℝ) - 2 * RevisedScales.forcingExponent n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hRpos]
    congr 1
    ring
  have hfield (q : ℕ) : periodicSobolevNorm q f ≤
      H q * R ^ q * R ^ (-2 * RevisedScales.forcingExponent n) := by
    have hp := (le_add_of_nonneg_left (cNorm_nonneg univ q
      (normalizedSource D R m δ gs G.map u))).trans (hsourceProfile q)
    have ht := (periodicSobolevNorm_tensorPeriodization_le D.chartRadius_lt_half
      (hsourceSupp.trans hKD) hsource q).trans
        (mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg _))
    apply ht.trans_eq
    dsimp only [H]
    rw [← hsplit q]
    ring
  have hscaleOne : 1 ≤ currentCoefficientScale R₀ j :=
    one_le_currentCoefficientScale (by linarith) j
  have hscaleR : currentCoefficientScale R₀ j ≤ R := by
    change R ^ coefficientExponent ≤ R
    calc
      _ ≤ R ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hRone (by norm_num [coefficientExponent])
      _ = R := Real.rpow_one R
  have hprofile (q : ℕ) : periodicSobolevNorm q (fun z ↦ target.val z ()) ≤
      C q * R ^ ((q : ℝ) - 2 * RevisedScales.forcingExponent n) := by
    have hh := periodicSobolevNorm_clm_apply_le_of_profiles q A H
      (preparationMeasurement d) f hmeas hf hscaleOne hscaleR
      (Real.rpow_nonneg hRpos.le _)
      (fun k _ ↦ by simpa only [Nat.sub_zero] using hmeasProfile k)
      (fun k _ ↦ hfield k)
    change periodicSobolevNorm q (fun z ↦ preparationMeasurement d z (f z)) ≤ _
    apply hh.trans
    calc
      _ = coefficientBandConstant n q A H *
          R ^ ((q : ℝ) - 2 * RevisedScales.forcingExponent n) := by rw [mul_assoc, hsplit]
      _ ≤ C q * R ^ ((q : ℝ) - 2 * RevisedScales.forcingExponent n) :=
        mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (Real.rpow_nonneg hRpos.le _)
  refine ⟨target, fun _ ↦ rfl, hprofile, ?_, ?_⟩
  · have hgap : (RevisedScales.sourceOrder n : ℝ) - 2 * RevisedScales.forcingExponent n = -1 := by
      linarith [(RevisedScales.source_order_and_forcing_gap n).2.2.1]
    simpa only [hgap] using hprofile (RevisedScales.sourceOrder n)
  · intro q
    rw [mul_assoc]
    exact (hprofile q).trans
      (mul_le_mul_of_nonneg_left (measured_power_le_admissible n q hRone) (hC q).le)

end JanetCartan.PhysicalSmoothing
