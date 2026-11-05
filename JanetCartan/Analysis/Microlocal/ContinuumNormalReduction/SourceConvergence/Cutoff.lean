module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.SourceConvergence.Integrability

/-!
# Source-first cutoff convergence under an output test

For `app:ch_background:eq:bg-full-complex-amplitude`, the source decay estimate
is uniform in the output position. Its integrable majorant permits integration
against a compact output test. These are Euclidean Lebesgue integrals; the
normal construction still supplies the chart change and torus-source matching.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff FourierTransform Topology RealInnerProductSpace
namespace JanetCartan.ContinuumRow.TransportKernel.SourceConvergence
open ContinuumNormalReduction TransportSymbol Pseudodifferential
variable {n : ℕ}

/-- The explicit integrable frequency majorant after `n+1` source derivatives,
for the original full amplitude in `app:ch_background:eq:bg-full-complex-amplitude`.
The finite Leibniz budget keeps the amplitude bounds linear. -/
def sourceTestMajorant (f : Euclidean n → ℂ) (M : ℕ → ℝ) (ξ : Euclidean n) : ℝ :=
  (2 ^ n * (1 + 2 ^ (n + 1)) * sourceLeibnizBudget f M (n + 1)) *
    (1 + ‖ξ‖) ^ (-(n + 1 : ℝ))

/-- The source-test majorant has an integrable tail, including the frequency
origin (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem integrable_sourceTestMajorant (f : Euclidean n → ℂ) (M : ℕ → ℝ) :
    Integrable (sourceTestMajorant f M) := by
  apply (integrable_one_add_norm (E := Euclidean n) (μ := volume)
    (r := (n + 1 : ℝ)) (by simp)).const_mul

/-- Primitive full-symbol jets give one majorant independent of the output
point, with the original amplitude kept intact
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem norm_sourceAmplitudeTransform_le_sourceTestMajorant
    (c : Euclidean n → Euclidean n → Euclidean n → ℂ)
    (hc : ContDiff ℝ ∞ (fun p : Variables n ↦ c p.1 p.2.1 p.2.2))
    (f : Euclidean n → ℂ) (hf : ContDiff ℝ (n + 1) f) (hfc : HasCompactSupport f)
    (M : ℕ → ℝ)
    (hM : ∀ x y ξ k, k ≤ n + 1 →
      ‖iteratedFDeriv ℝ k (fun p : Variables n ↦ c p.1 p.2.1 p.2.2) (x, y, ξ)‖ ≤ M k)
    (x ξ : Euclidean n) :
    ‖sourceAmplitudeTransform c f x ξ‖ ≤ sourceTestMajorant f M ξ := by
  have hs : ContDiff ℝ (n + 1) (fun y ↦ c x y ξ) :=
    (hc.comp (f := fun y : Euclidean n ↦ (x, y, ξ)) (by fun_prop)).of_le (by simp)
  have hprod := hf.smul hs
  have hi (k : ℕ) (hk : k ≤ n + 1) :
      Integrable (iteratedFDeriv ℝ k (fun y ↦ f y • c x y ξ)) :=
    (hprod.continuous_iteratedFDeriv (by exact_mod_cast hk)).integrable_of_hasCompactSupport
      (hfc.smul_right.iteratedFDeriv k)
  have hmass := sourceDerivativeMass_smul_le f (fun y ↦ c x y ξ) (n + 1) hf hfc hs M
    (fun k hk y ↦ (norm_iteratedFDeriv_source_le_joint c hc x y ξ k).trans (hM x y ξ k hk))
  have hdecay := one_add_norm_pow_mul_norm_fourier_le_sourceDerivativeMass
    (fun y ↦ f y • c x y ξ) (n + 1) hprod hi ξ
  have hbound : (1 + ‖ξ‖) ^ (n + 1) * ‖sourceAmplitudeTransform c f x ξ‖ ≤
      (2 ^ n * (1 + 2 ^ (n + 1))) * sourceLeibnizBudget f M (n + 1) :=
    hdecay.trans (by simpa using (mul_le_mul_of_nonneg_left hmass
      (by positivity : 0 ≤ (2 : ℝ) ^ (n + 1 - 1) * (1 + 2 ^ (n + 1)))))
  have hp : 0 < 1 + ‖ξ‖ := by positivity
  rw [sourceTestMajorant, Real.rpow_neg (le_of_lt hp),
    show (n + 1 : ℝ) = ((n + 1 : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast,
    ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos hp _)).mpr (by simpa [mul_comm] using hbound)

/-- The literal source-first operator is measurable in the output position,
by two parameter integrals (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem stronglyMeasurable_fullAmplitudeOperator
    (c : Euclidean n → Euclidean n → Euclidean n → ℂ)
    (hc : Continuous (fun p : Variables n ↦ c p.1 p.2.1 p.2.2))
    (f : Euclidean n → ℂ) (hf : Continuous f) :
    StronglyMeasurable (fullAmplitudeOperator c f) := by
  have hs : StronglyMeasurable (fun p : Euclidean n × Euclidean n ↦
      sourceAmplitudeTransform c f p.1 p.2) := by
    simp only [sourceAmplitudeTransform, Real.fourier_eq]
    apply StronglyMeasurable.integral_prod_right
    apply Continuous.stronglyMeasurable
    change Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      Real.fourierChar (-⟪p.2, p.1.2⟫) • (f p.2 • c p.1.1 p.2 p.1.2))
    exact (by fun_prop : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      Real.fourierChar (-⟪p.2, p.1.2⟫))).smul
      ((hf.comp continuous_snd).smul (hc.comp
        (f := fun p : (Euclidean n × Euclidean n) × Euclidean n ↦ (p.1.1, p.2, p.1.2))
        (by fun_prop)))
  change StronglyMeasurable (fun x ↦ 𝓕⁻ (sourceAmplitudeTransform c f x) x)
  simp only [Real.fourierInv_eq]
  apply StronglyMeasurable.integral_prod_right
  exact (by fun_prop : Continuous (fun p : Euclidean n × Euclidean n ↦
    Real.fourierChar ⟪p.2, p.1⟫)).stronglyMeasurable.smul hs

/-- A uniform bound for the actual source-first cutoff operators. It is proved
from primitive jets, before any output test is introduced; `C` is only the
fixed cutoff bound (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem norm_fullAmplitudeOperator_cutoff_le
    (c : Euclidean n → Euclidean n → Euclidean n → ℂ)
    (hc : ContDiff ℝ ∞ (fun p : Variables n ↦ c p.1 p.2.1 p.2.2))
    (f : Euclidean n → ℂ) (hf : ContDiff ℝ (n + 1) f) (hfc : HasCompactSupport f)
    (M : ℕ → ℝ)
    (hM : ∀ x y ξ k, k ≤ n + 1 →
      ‖iteratedFDeriv ℝ k (fun p : Variables n ↦ c p.1 p.2.1 p.2.2) (x, y, ξ)‖ ≤ M k)
    (χ : Euclidean n → ℝ) {C : ℝ} (hC : ∀ ξ, |χ ξ| ≤ C)
    (R : ℝ) (x : Euclidean n) :
    ‖fullAmplitudeOperator (fun x y ξ ↦ χ (R⁻¹ • ξ) • c x y ξ) f x‖ ≤
      C * ∫ ξ, sourceTestMajorant f M ξ := by
  have hC0 : 0 ≤ C := (abs_nonneg (χ 0)).trans (hC 0)
  simp only [fullAmplitudeOperator, Real.fourierInv_eq, sourceAmplitudeTransform_frequency_smul]
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le ((integrable_sourceTestMajorant f M).const_mul C)
  filter_upwards [] with ξ
  simp only [Circle.norm_smul, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left
      (norm_sourceAmplitudeTransform_le_sourceTestMajorant c hc f hf hfc M hM x ξ) hC0)

/-- The uncut full operator has the same output-uniform source bound,
for `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem norm_fullAmplitudeOperator_le
    (c : Euclidean n → Euclidean n → Euclidean n → ℂ)
    (hc : ContDiff ℝ ∞ (fun p : Variables n ↦ c p.1 p.2.1 p.2.2))
    (f : Euclidean n → ℂ) (hf : ContDiff ℝ (n + 1) f) (hfc : HasCompactSupport f)
    (M : ℕ → ℝ)
    (hM : ∀ x y ξ k, k ≤ n + 1 →
      ‖iteratedFDeriv ℝ k (fun p : Variables n ↦ c p.1 p.2.1 p.2.2) (x, y, ξ)‖ ≤ M k)
    (x : Euclidean n) :
    ‖fullAmplitudeOperator c f x‖ ≤ ∫ ξ, sourceTestMajorant f M ξ := by
  simpa using norm_fullAmplitudeOperator_cutoff_le c hc f hf hfc M hM
    (fun _ ↦ 1) (C := 1) (by simp) 1 x

/-- The compact output test is integrable against each source-first cutoff,
with its domination supplied by the primitive jets
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem integrable_test_fullAmplitudeOperator_cutoff
    (c : Euclidean n → Euclidean n → Euclidean n → ℂ)
    (hc : ContDiff ℝ ∞ (fun p : Variables n ↦ c p.1 p.2.1 p.2.2))
    (f : Euclidean n → ℂ) (hf : ContDiff ℝ (n + 1) f) (hfc : HasCompactSupport f)
    (M : ℕ → ℝ)
    (hM : ∀ x y ξ k, k ≤ n + 1 →
      ‖iteratedFDeriv ℝ k (fun p : Variables n ↦ c p.1 p.2.1 p.2.2) (x, y, ξ)‖ ≤ M k)
    (v : Euclidean n → ℂ) (hv : Continuous v) (hvc : HasCompactSupport v)
    (χ : Euclidean n → ℝ) (hχ : Continuous χ)
    {C : ℝ} (hC : ∀ ξ, |χ ξ| ≤ C) (R : ℝ) :
    Integrable (fun x ↦ v x *
      fullAmplitudeOperator (fun x y ξ ↦ χ (R⁻¹ • ξ) • c x y ξ) f x) := by
  apply ((hv.integrable_of_hasCompactSupport hvc).norm.mul_const
    (C * ∫ ξ, sourceTestMajorant f M ξ)).mono'
  · exact hv.aestronglyMeasurable.mul
      (stronglyMeasurable_fullAmplitudeOperator _
        ((hχ.comp (by fun_prop)).smul hc.continuous) f hf.continuous).aestronglyMeasurable
  · filter_upwards [] with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_fullAmplitudeOperator_cutoff_le c hc f hf hfc M hM χ hC R x) (norm_nonneg _)

/-- The uncut original full amplitude is integrable against a compact output
test, using the same source majorant
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem integrable_test_fullAmplitudeOperator
    (c : Euclidean n → Euclidean n → Euclidean n → ℂ)
    (hc : ContDiff ℝ ∞ (fun p : Variables n ↦ c p.1 p.2.1 p.2.2))
    (f : Euclidean n → ℂ) (hf : ContDiff ℝ (n + 1) f) (hfc : HasCompactSupport f)
    (M : ℕ → ℝ)
    (hM : ∀ x y ξ k, k ≤ n + 1 →
      ‖iteratedFDeriv ℝ k (fun p : Variables n ↦ c p.1 p.2.1 p.2.2) (x, y, ξ)‖ ≤ M k)
    (v : Euclidean n → ℂ) (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable (fun x ↦ v x * fullAmplitudeOperator c f x) := by
  simpa using integrable_test_fullAmplitudeOperator_cutoff c hc f hf hfc M hM v hv hvc
    (fun _ ↦ 1) continuous_const (C := 1) (by simp) 1

/-- The ORIGINAL full-amplitude cutoff converges under every compact continuous
output test. The uniform domination and all source Fourier integrability are
derived from the finite primitive jets; neither is an input. Consumer: the
full-amplitude distributional limit in `realNormal_principal_reduction_of_test_limit`
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem tendsto_integral_test_fullAmplitudeOperator_cutoff
    (c : Euclidean n → Euclidean n → Euclidean n → ℂ)
    (hc : ContDiff ℝ ∞ (fun p : Variables n ↦ c p.1 p.2.1 p.2.2))
    (f : Euclidean n → ℂ) (hf : ContDiff ℝ (n + 1) f) (hfc : HasCompactSupport f)
    (M : ℕ → ℝ)
    (hM : ∀ x y ξ k, k ≤ n + 1 →
      ‖iteratedFDeriv ℝ k (fun p : Variables n ↦ c p.1 p.2.1 p.2.2) (x, y, ξ)‖ ≤ M k)
    (v : Euclidean n → ℂ) (hv : Continuous v) (hvc : HasCompactSupport v)
    (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχ0 : χ 0 = 1)
    {C : ℝ} (hC : ∀ ξ, |χ ξ| ≤ C) :
    Tendsto (fun R : ℝ ↦ ∫ x, v x *
      fullAmplitudeOperator (fun x y ξ ↦ χ (R⁻¹ • ξ) • c x y ξ) f x) atTop
      (𝓝 (∫ x, v x * fullAmplitudeOperator c f x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ ‖v x‖ * (C * ∫ ξ, sourceTestMajorant f M ξ))
  · apply Eventually.of_forall
    intro R
    exact hv.aestronglyMeasurable.mul
      (stronglyMeasurable_fullAmplitudeOperator _
        ((hχ.comp (by fun_prop)).smul hc.continuous) f hf.continuous).aestronglyMeasurable
  · apply Eventually.of_forall
    intro R
    filter_upwards [] with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_fullAmplitudeOperator_cutoff_le c hc f hf hfc M hM χ hC R x) (norm_nonneg _)
  · exact (hv.integrable_of_hasCompactSupport hvc).norm.mul_const _
  · filter_upwards [] with x
    apply tendsto_const_nhds.mul
    apply tendsto_fullAmplitudeOperator_frequency_cutoff c f x _ χ hχ hχ0 C hC
    exact (integrable_sourceTestMajorant f M).mono'
      (stronglyMeasurable_sourceFourier (fun ξ y ↦ f y • c x y ξ)
        ((hf.continuous.comp continuous_snd).smul (hc.continuous.comp
          (f := fun p : Euclidean n × Euclidean n ↦ (x, p.2, p.1)) (by fun_prop)))).aestronglyMeasurable
      (Eventually.of_forall (norm_sourceAmplitudeTransform_le_sourceTestMajorant c hc f hf hfc M hM x))

/-- The majorant retains exactly one copy of a common high norm, as does
`TransportSymbol.GlobalNormBounds`
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem sourceTestMajorant_mul (f : Euclidean n → ℂ) (M : ℕ → ℝ)
    (H : ℝ) (ξ : Euclidean n) :
    sourceTestMajorant f (fun j ↦ M j * H) ξ = sourceTestMajorant f M ξ * H := by
  simp only [sourceTestMajorant, sourceLeibnizBudget_mul]
  ring

end JanetCartan.ContinuumRow.TransportKernel.SourceConvergence
