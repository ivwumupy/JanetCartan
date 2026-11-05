module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.SourceConvergence.Cutoff

/-!
# The actual radial carrier cutoff after inverse substitution

The normal density contains `χ(|η|/R)^2`, not a cutoff in the output covector.
For every fixed output covector, the inverse comparison makes this factor
identically one for all sufficiently large `R`, uniformly in both positions
and the spectator. Uniform primitive jets then permit source-first convergence.
Source: `app:ch_background:eq:bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius FourierTransform RealInnerProductSpace
namespace JanetCartan.ContinuumRow.TransportKernel.SourceConvergence
open ContinuumNormalReduction TransportSymbol Pseudodifferential
variable {n N : ℕ}

/-- The actual squared radial carrier cutoff is eventually absent on every
fixed output frequency, uniformly in both physical positions. This uses the
inverse comparison, not an identification of input and output frequencies
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem amplitude_regularized_eq_of_radius
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (χ : ℝ → ℝ) (hχ : ∀ t ∈ Icc (0 : ℝ) 1, χ t = 1)
    {Cupper : ℝ} (hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖)
    (p : Variables n) {R : ℝ} (hR : 0 < R) (hp : Cupper * ‖p.2.2‖ ≤ R) :
    amplitude (regularizedCoefficients a χ R) J u Ω K p = amplitude a J u Ω K p := by
  apply integral_congr_ae
  filter_upwards [] with v
  by_cases hv : (p, v) ∈ Ω
  · simp only [extendedDensity, indicator_of_mem hv, inputDensity_regularized]
    have hb : ‖(inverseCoordinates u (p, v)).2.2‖ / R ∈ Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg (norm_nonneg _) hR.le, (div_le_one hR).mpr ?_⟩
      exact (hupper (p, v) hv).trans hp
    rw [hχ _ hb, one_pow, one_smul]
  · simp only [extendedDensity, indicator_of_notMem hv]

/-- Eventual equality of the source transforms at each fixed frequency for
the actual carrier regularization. The square in the density and reflection
are preserved (`app:ch_background:eq:bg-real-symbol`). -/
theorem sourceAmplitudeTransform_reflected_regularized_eventuallyEq
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (χ : ℝ → ℝ) (hχ : ∀ t ∈ Icc (0 : ℝ) 1, χ t = 1)
    {Cupper : ℝ} (hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖)
    (f : Euclidean n → ℂ) (x ξ : Euclidean n) (i j : Fin n) :
    (fun R : ℝ ↦ sourceAmplitudeTransform (fun x y ξ ↦
      (reflectedSymbolAmplitude (regularizedCoefficients a χ R) J u Ω K
        (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x ξ) =ᶠ[atTop]
    (fun _ ↦ sourceAmplitudeTransform (fun x y ξ ↦
      (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x ξ) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_ge_atTop (Cupper * ‖(2 * Real.pi) • ξ‖)] with R hR hb
  have he (y : Euclidean n) :
      reflectedSymbolAmplitude (regularizedCoefficients a χ R) J u Ω K
        (x, y, (2 * Real.pi) • ξ) =
      reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) := by
    unfold reflectedSymbolAmplitude
    rw [amplitude_regularized_eq_of_radius a J u Ω K χ hχ hupper (x, y, (2 * Real.pi) • ξ) hR hb,
      amplitude_regularized_eq_of_radius a J u Ω K χ hχ hupper (x, y, -((2 * Real.pi) • ξ)) hR (by simpa only [norm_neg] using hb)]
  simp only [sourceAmplitudeTransform, he]

/-- Source-first convergence of the actual radial carrier regularization at
one output point. The uniform symbol jets are exactly the output of the
regularized primitive-norm producer; source integrability and operator
convergence are proved, not assumed
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem tendsto_reflected_fullAmplitudeOperator_carrierCutoff
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (χ : ℝ → ℝ) (hχ : ∀ t ∈ Icc (0 : ℝ) 1, χ t = 1)
    {Cupper : ℝ} (hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖)
    (i j : Fin n)
    (hc : ∀ R : ℝ, 1 ≤ R → ContDiff ℝ ∞ (fun p : Variables n ↦
      (reflectedSymbolAmplitude (regularizedCoefficients a χ R) J u Ω K
        (p.1, p.2.1, (2 * Real.pi) • p.2.2) i j : ℂ)))
    (M : ℕ → ℝ)
    (hM : ∀ R : ℝ, 1 ≤ R → ∀ x y ξ k, k ≤ n + 1 →
      ‖iteratedFDeriv ℝ k (fun p : Variables n ↦
        (reflectedSymbolAmplitude (regularizedCoefficients a χ R) J u Ω K
          (p.1, p.2.1, (2 * Real.pi) • p.2.2) i j : ℂ)) (x, y, ξ)‖ ≤ M k)
    (f : Euclidean n → ℂ) (hf : ContDiff ℝ (n + 1) f) (hfc : HasCompactSupport f)
    (x : Euclidean n) :
    Tendsto (fun R : ℝ ↦ fullAmplitudeOperator (fun x y ξ ↦
      (reflectedSymbolAmplitude (regularizedCoefficients a χ R) J u Ω K
        (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x) atTop
      (𝓝 (fullAmplitudeOperator (fun x y ξ ↦
        (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x)) := by
  simp only [fullAmplitudeOperator, Real.fourierInv_eq]
  apply tendsto_integral_filter_of_dominated_convergence (sourceTestMajorant f M)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact (by fun_prop : Continuous (fun ξ : Euclidean n ↦
      Real.fourierChar ⟪ξ, x⟫)).aestronglyMeasurable.smul
      (stronglyMeasurable_sourceFourier _
        ((hf.continuous.comp continuous_snd).smul ((hc R hR).continuous.comp
          (f := fun p : Euclidean n × Euclidean n ↦ (x, p.2, p.1))
          (by fun_prop)))).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    filter_upwards [] with ξ
    simp only [Circle.norm_smul]
    exact norm_sourceAmplitudeTransform_le_sourceTestMajorant (fun x y ξ ↦ (reflectedSymbolAmplitude (regularizedCoefficients a χ R) J u Ω K
        (x, y, (2 * Real.pi) • ξ) i j : ℂ)) (hc R hR) f hf hfc M (hM R hR) x ξ
  · exact integrable_sourceTestMajorant f M
  · filter_upwards [] with ξ
    apply tendsto_const_nhds.smul
    exact tendsto_const_nhds.congr'
      (sourceAmplitudeTransform_reflected_regularized_eventuallyEq a J u Ω K χ hχ hupper f x ξ i j).symm

/-- The original radial carrier cutoff converges after integration against a
compact output test, with a uniform majorant in the output point. This is the
Euclidean source-first part of the original full-amplitude distributional
limit, before diagonal reduction
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem tendsto_integral_reflected_fullAmplitudeOperator_carrierCutoff
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (χ : ℝ → ℝ) (hχ : ∀ t ∈ Icc (0 : ℝ) 1, χ t = 1)
    {Cupper : ℝ} (hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ Cupper * ‖p.1.2.2‖)
    (i j : Fin n)
    (hc : ∀ R : ℝ, 1 ≤ R → ContDiff ℝ ∞ (fun p : Variables n ↦
      (reflectedSymbolAmplitude (regularizedCoefficients a χ R) J u Ω K
        (p.1, p.2.1, (2 * Real.pi) • p.2.2) i j : ℂ)))
    (M : ℕ → ℝ)
    (hM : ∀ R : ℝ, 1 ≤ R → ∀ x y ξ k, k ≤ n + 1 →
      ‖iteratedFDeriv ℝ k (fun p : Variables n ↦
        (reflectedSymbolAmplitude (regularizedCoefficients a χ R) J u Ω K
          (p.1, p.2.1, (2 * Real.pi) • p.2.2) i j : ℂ)) (x, y, ξ)‖ ≤ M k)
    (f : Euclidean n → ℂ) (hf : ContDiff ℝ (n + 1) f) (hfc : HasCompactSupport f)
    (v : Euclidean n → ℂ) (hv : Continuous v) (hvc : HasCompactSupport v) :
    Tendsto (fun R : ℝ ↦ ∫ x, v x * fullAmplitudeOperator (fun x y ξ ↦
      (reflectedSymbolAmplitude (regularizedCoefficients a χ R) J u Ω K
        (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x) atTop
      (𝓝 (∫ x, v x * fullAmplitudeOperator (fun x y ξ ↦
        (reflectedSymbolAmplitude a J u Ω K (x, y, (2 * Real.pi) • ξ) i j : ℂ)) f x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ ‖v x‖ * ∫ ξ, sourceTestMajorant f M ξ)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact hv.aestronglyMeasurable.mul
      (stronglyMeasurable_fullAmplitudeOperator (fun x y ξ ↦ (reflectedSymbolAmplitude (regularizedCoefficients a χ R) J u Ω K
        (x, y, (2 * Real.pi) • ξ) i j : ℂ)) (hc R hR).continuous f hf.continuous).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    filter_upwards [] with x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (norm_fullAmplitudeOperator_le (fun x y ξ ↦ (reflectedSymbolAmplitude (regularizedCoefficients a χ R) J u Ω K
        (x, y, (2 * Real.pi) • ξ) i j : ℂ)) (hc R hR) f hf hfc M (hM R hR) x) (norm_nonneg _)
  · exact (hv.integrable_of_hasCompactSupport hvc).norm.mul_const _
  · filter_upwards [] with x
    exact tendsto_const_nhds.mul
      (tendsto_reflected_fullAmplitudeOperator_carrierCutoff a J u Ω K χ hχ hupper i j hc M hM f hf hfc x)

end JanetCartan.ContinuumRow.TransportKernel.SourceConvergence
