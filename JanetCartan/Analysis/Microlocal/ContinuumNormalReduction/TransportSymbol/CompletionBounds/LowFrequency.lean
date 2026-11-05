module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.NormAssembly
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.FrequencyBounds.Completion

/-!
# The low-frequency gap of the literal completion discrepancy

These identities supply the inner boundary of the fixed annulus used for the
bounded-frequency smoothing estimate following `app:ch_background:eq:bg-symbol`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- The high mask kills the literal density when the upper input-frequency
comparison puts the input below one. Source: `app:ch_background:eq:bg-symbol`.
Consumed by the fixed completion-discrepancy estimate. -/
theorem extendedDensity_eq_zero_of_low_frequency
    (d : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2))
    (hhigh : ∀ r : ℝ, r ≤ 1 → d.high r = 0) {C : ℝ}
    (hcomparison : ∀ p ∈ Ω, ‖(u p).2‖ ≤ C * ‖p.1.2.2‖)
    (p : Variables n × Euclidean 2) (hp : C * ‖p.1.2.2‖ ≤ 1) :
    extendedDensity d J u Ω p = 0 := by
  by_cases hΩ : p ∈ Ω
  · have hh := hhigh _ ((hcomparison p hΩ).trans hp)
    simp [extendedDensity, hΩ, inputDensity, inputWeight, inverseCoordinates, hh]
  · simp [extendedDensity, hΩ]

/-- The literal spectator integral vanishes below the fixed low-frequency
threshold. Source: the paragraph following `app:ch_background:eq:bg-symbol`. -/
theorem amplitude_eq_zero_of_low_frequency
    (d : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hhigh : ∀ r : ℝ, r ≤ 1 → d.high r = 0) {C : ℝ}
    (hcomparison : ∀ p ∈ Ω, ‖(u p).2‖ ≤ C * ‖p.1.2.2‖)
    (p : Variables n) (hp : C * ‖p.2.2‖ ≤ 1) :
    amplitude d J u Ω S p = 0 := by
  have he : (fun v ↦ extendedDensity d J u Ω (p, v)) = 0 := by
    funext v
    exact extendedDensity_eq_zero_of_low_frequency d J u Ω hhigh hcomparison (p, v) hp
  simp [amplitude, he]

/-- All joint jets vanish on the open low-frequency region; no smoothness at
the cone vertex is assumed. Source: `app:ch_background:eq:bg-symbol`. -/
theorem iteratedFDeriv_completion_discrepancy_eq_zero_of_low_frequency
    (d : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hhigh : ∀ r : ℝ, r ≤ 1 → d.high r = 0) {C ℓ : ℝ} (hC : 0 ≤ C)
    (hℓ : ℓ ≤ 1) (hCℓ : C * ℓ ≤ 1)
    (hcomparison : ∀ p ∈ Ω, ‖(u p).2‖ ≤ C * ‖p.1.2.2‖)
    (p : Variables n) (hp : ‖p.2.2‖ < ℓ) (j : ℕ) :
    iteratedFDeriv ℝ j
      (fun x ↦ amplitude d J u Ω S x - completedAmplitude d J u Ω S x) p = 0 := by
  have he : (fun x ↦ amplitude d J u Ω S x - completedAmplitude d J u Ω S x)
      =ᶠ[𝓝 p] 0 := by
    have hopen : IsOpen {x : Variables n | ‖x.2.2‖ < ℓ} :=
      isOpen_lt continuous_snd.snd.norm continuous_const
    filter_upwards [hopen.mem_nhds hp] with x hx
    rw [amplitude_eq_zero_of_low_frequency d J u Ω S hhigh hcomparison x
      ((mul_le_mul_of_nonneg_left hx.le hC).trans hCℓ)]
    simp [completedAmplitude, completionCutoff_eq_zero (hx.le.trans hℓ)]
  simpa using (he.iteratedFDeriv ℝ j).eq_of_nhds

/-- Every joint jet vanishes on the open large-frequency region, by the exact
completion identity. Source: `app:ch_background:eq:bg-symbol`. -/
theorem iteratedFDeriv_completion_discrepancy_eq_zero_of_large_frequency
    (d : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hhigh : ∀ r : ℝ, 2 ≤ r → d.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (p : Variables n) (hp : max 2 (2 * C) < ‖p.2.2‖) (j : ℕ) :
    iteratedFDeriv ℝ j
      (fun x ↦ amplitude d J u Ω S x - completedAmplitude d J u Ω S x) p = 0 := by
  have he : (fun x ↦ amplitude d J u Ω S x - completedAmplitude d J u Ω S x)
      =ᶠ[𝓝 p] 0 := by
    have hopen : IsOpen {x : Variables n | max 2 (2 * C) < ‖x.2.2‖} :=
      isOpen_lt continuous_const continuous_snd.snd.norm
    filter_upwards [hopen.mem_nhds hp] with x hx
    exact sub_eq_zero.mpr (amplitude_eq_completed_of_large_frequency
      d J u Ω S hhigh hC hcomparison x hx.le)
  simpa using (he.iteratedFDeriv ℝ j).eq_of_nhds

end JanetCartan.ContinuumNormalReduction.TransportSymbol
