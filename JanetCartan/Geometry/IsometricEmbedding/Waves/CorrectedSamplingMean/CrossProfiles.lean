module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.CorrectedSamplingMean.Literal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.CorrectedSamplingMean.CutoffProfiles

/-!
# Jets of the literal corrected Hermitian coefficient

The background and modulated factors have the same fixed physical rate.
The supplied real measurement is applied by its literal complexification.
All product and carrier-substitution constants precede the varying corrected
factors and history scale (`app:ch_waves:eq:sampling-operator-bounds`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.Sampling.CorrectedMean
open CanonicalRowComparison CurrentMean RawPrimary.SliceBounds
open RawPrimary.AmplitudeGrades.Polynomial FourierIntegral.NormalOneHigh
open LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open MeasuredAmplitude

/-- Fixed carrier substitution in the original coefficient coordinates.
The physical rate is absent from this map
(`app:ch_mean_pairs:defn:mean-canonical`). -/
def retainedCarrierInsertion {m : ℕ} {P : Patch (m + 1)}
    {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (w : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1))) :
    Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) :=
  (w.1, w.2.1, extendedRetainedCarrier T z₀ hρ w.2.1)

/-- All carrier substitution jets are geometric: smoothness uses the SAME
supplied extension and its original carrier buffer
(`app:ch_waves:setup:oscillatory`). -/
theorem contDiff_retainedCarrierInsertion {m : ℕ} {P : Patch (m + 1)}
    {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius)) :
    ContDiff ℝ ∞ (retainedCarrierInsertion T z₀ hρ) :=
  contDiff_fst.prodMk ((contDiff_fst.comp contDiff_snd).prodMk
    ((contDiff_extendedRetainedCarrier T hP z₀ hρ hcarrier).comp (by fun_prop)))

/-- Joint carrier-product calculus for the supplied compact cutoff. The
hypotheses on `f` are produced for the literal corrected factor by
`cutCorrectedDerivativeAmplitude_budgets_of_profiles`; no normal or mean
estimate is assumed. The measurement profile precedes the varying measurement. The original Hermitian polarization
are retained, including both complex quadratures
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_carrierCrossCoefficient_budgets_of_measurement_profiles
    {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C₀ : ℝ} (hP : P.IsValid c C₀)
    (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    {K : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))}
    (hK : IsCompact K)
    (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
    (hκK : tsupport κ ⊆ K)
    (M : ℕ → ℝ) (hM : ∀ j, 0 ≤ M j)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ D : ℕ → ℝ, (∀ j, 0 ≤ D j) ∧
      ∀ (C : Euclidean (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
        Euclidean (m + 1)), ContDiff ℝ ∞ C →
      ∀ (f : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) →
        Matrix (Fin N) (Fin (m + 1)) ℂ), ContDiff ℝ ∞ f →
      (∀ w, κ w = 0 → f w = 0) →
      ∀ (L : ℝ) (rpar : ℕ), 1 ≤ L →
      (∀ w j, ‖iteratedFDeriv ℝ j f w‖ ≤ A j * L ^ (j - rpar)) →
      HasDerivativeProfile K (fun w ↦ C w.1) rpar L M →
      let H := fun w ↦ complexCrossMeasurement (C w.1)
        (f (retainedCarrierInsertion T z₀ hρ w)) (f w)
      ContDiff ℝ ∞ H ∧ ∀ w j, ‖iteratedFDeriv ℝ j H w‖ ≤ D j * L ^ (j - rpar) := by
  let g := retainedCarrierInsertion T z₀ hρ
  have hg : ContDiff ℝ ∞ g := contDiff_retainedCarrierInsertion T hP z₀ hρ hcarrier
  let b := fun j ↦ cNorm K j g
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
  intro C hC f hf hfzero L rpar hL hfjet hmeas H
  let meas := fun w : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) ↦ C w.1
  have hm : ContDiff ℝ ∞ meas := hC.comp contDiff_fst
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
  intro w j
  by_cases hw : w ∈ tsupport κ
  · have hwK := hκK hw
    have hf₀jet (k) : ‖iteratedFDeriv ℝ k f₀ w‖ ≤ A₀ k * L ^ (k - rpar) :=
      norm_iteratedFDeriv_comp_le_sliceGrade hg.contDiffAt hf.contDiffAt
        (fun i _ ↦ hA i) hL (fun i _ ↦ hfjet (g w) i)
        (fun i _ _ ↦ norm_iteratedFDeriv_le_cNorm hK (hg.of_le (by simp)) hwK le_rfl)
    have hfIjet (k) : ‖iteratedFDeriv ℝ k fI w‖ ≤ A k * L ^ (k - rpar) := by
      rw [show fI = fun y ↦ Complex.I • f y from rfl, jet_const_smul hf.contDiffAt,
        Complex.norm_I, one_mul]
      exact hfjet w k
    have hmjet (k) : ‖iteratedFDeriv ℝ k meas w‖ ≤ M k * L ^ (k - rpar) :=
      (norm_iteratedFDeriv_le_cNorm hK (hm.of_le (by simp)) hwK le_rfl).trans (hmeas k)
    have hp₀jet (k) : ‖iteratedFDeriv ℝ k p₀ w‖ ≤ productProfile HB A₀ A k * L ^ (k - rpar) :=
      jet_bilinear_le HB isOpen_univ hf₀.contDiffOn hf.contDiffOn (mem_univ _)
        hL hA₀ hA hf₀jet (hfjet w) k
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
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hw] with y hy
      simp only [H, hfzero y hy, map_zero, Pi.zero_apply]
    rw [← heq, (hz.iteratedFDeriv ℝ j).eq_of_nhds]
    simp only [iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (hD₀ j))
      (pow_nonneg (zero_le_one.trans hL) _)

/-- Joint carrier-product calculus for the supplied compact cutoff. The
hypotheses on `f` are produced for the literal corrected factor by
`cutCorrectedDerivativeAmplitude_budgets_of_profiles`; no normal or mean
estimate is assumed. The real measurement and original Hermitian polarization
are retained, including both complex quadratures
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_carrierCrossCoefficient_budgets
    {m N : ℕ} {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C₀ : ℝ} (hP : P.IsValid c C₀)
    (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hcarrier : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius))
    {K : Set (Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)))}
    (hK : IsCompact K)
    (κ : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) → ℝ)
    (hκK : tsupport κ ⊆ K)
    (C : Euclidean (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ →L[ℝ]
      Euclidean (m + 1)) (hC : ContDiff ℝ ∞ C)
    (A : ℕ → ℝ) (hA : ∀ j, 0 ≤ A j) :
    ∃ D : ℕ → ℝ, (∀ j, 0 ≤ D j) ∧
      ∀ (f : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) →
        Matrix (Fin N) (Fin (m + 1)) ℂ), ContDiff ℝ ∞ f →
      (∀ w, κ w = 0 → f w = 0) →
      ∀ (L : ℝ) (rpar : ℕ), 1 ≤ L →
      (∀ w j, ‖iteratedFDeriv ℝ j f w‖ ≤ A j * L ^ (j - rpar)) →
      let H := fun w ↦ complexCrossMeasurement (C w.1)
        (f (retainedCarrierInsertion T z₀ hρ w)) (f w)
      ContDiff ℝ ∞ H ∧ ∀ w j, ‖iteratedFDeriv ℝ j H w‖ ≤ D j * L ^ (j - rpar) := by
  let meas := fun w : Euclidean (m + 1) × (Euclidean 3 × Euclidean (m + 1 - 1)) ↦ C w.1
  let M := fun j ↦ cNorm K j meas
  have hM (j) : 0 ≤ M j := cNorm_nonneg _ _ _
  obtain ⟨D, hD, hall⟩ := exists_carrierCrossCoefficient_budgets_of_measurement_profiles
    (N := N) T hP z₀ hρ hcarrier hK κ hκK M hM A hA
  refine ⟨D, hD, ?_⟩
  intro f hf hfzero L rpar hL hfjet
  apply hall C hC f hf hfzero L rpar hL hfjet
  intro j
  exact le_mul_of_one_le_right (hM j) (one_le_pow₀ hL)

end JanetCartan.Sampling.CorrectedMean
