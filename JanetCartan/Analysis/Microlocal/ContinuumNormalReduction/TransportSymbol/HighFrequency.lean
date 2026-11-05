module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Homogeneity
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Integration

/-!
# Exact bounded-frequency support of the high-cutoff discrepancy

The high cutoff equals one for `|η| ≥ 2`. The geometric comparison
`|k| ≤ C |η|` therefore identifies the literal amplitude with its homogeneous
version outside `|k| ≤ 2C`, as asserted after `app:ch_background:eq:bg-symbol`.
This proves support, not smoothness at zero: constructing a fixed smooth
low-frequency completion and its tame bounds remains a separate obligation.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- The primitive density equals its homogeneous version wherever the
high cutoff is one (`app:ch_background:eq:bg-symbol`). -/
theorem inputDensity_eq_homogeneous_of_high_eq_one
    (a : Coefficients n N) (J : InputVariables n → ℝ) (p : InputVariables n)
    (h : a.high ‖p.2.2‖ = 1) :
    inputDensity a J p = inputDensity (homogeneousCoefficients a) J p := by
  simp [inputDensity, inputWeight, homogeneousCoefficients, h]

/-- Frequency comparability makes the high cutoff irrelevant at large output
frequency. Both positions and the spectator remain in the assertion.
Source: the paragraph following `app:ch_background:eq:bg-symbol`. -/
theorem extendedDensity_eq_homogeneous_of_large_frequency
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2))
    (hhigh : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (p : Variables n × Euclidean 2) (hp : 2 * C ≤ ‖p.1.2.2‖) :
    extendedDensity a J u Ω p = extendedDensity (homogeneousCoefficients a) J u Ω p := by
  by_cases hΩ : p ∈ Ω
  · simp only [extendedDensity, indicator_of_mem hΩ]
    apply inputDensity_eq_homogeneous_of_high_eq_one
    apply hhigh
    have hcomp := hcomparison p hΩ
    change 2 ≤ ‖(u p).2‖
    nlinarith
  · simp [extendedDensity, hΩ]

/-- The cutoff discrepancy of the spectator amplitude is supported in a fixed
bounded frequency region. The constant is geometric and does not depend on a
frequency regularization parameter (`app:ch_background:eq:bg-symbol`). -/
theorem amplitude_eq_homogeneous_of_large_frequency
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (hhigh : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (p : Variables n) (hp : 2 * C ≤ ‖p.2.2‖) :
    amplitude a J u Ω K p = amplitude (homogeneousCoefficients a) J u Ω K p := by
  apply integral_congr_ae
  filter_upwards [] with v
  exact extendedDensity_eq_homogeneous_of_large_frequency a J u Ω hhigh hC
    hcomparison (p, v) hp

/-- Every joint jet of the high-cutoff discrepancy vanishes on the open
large-frequency region. This conclusion does not assert any regularity at zero.
Source: the paragraph following `app:ch_background:eq:bg-symbol`. -/
theorem iteratedFDeriv_high_discrepancy_eq_zero
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (Ω : Set (Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (hhigh : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (p : Variables n) (hp : 2 * C < ‖p.2.2‖) (j : ℕ) :
    iteratedFDeriv ℝ j
      (fun y ↦ amplitude a J u Ω K y - amplitude (homogeneousCoefficients a) J u Ω K y)
      p = 0 := by
  have he : (fun y ↦ amplitude a J u Ω K y -
      amplitude (homogeneousCoefficients a) J u Ω K y) =ᶠ[𝓝 p] 0 := by
    have hopen : IsOpen {y : Variables n | 2 * C < ‖y.2.2‖} :=
      isOpen_lt continuous_const continuous_snd.snd.norm
    filter_upwards [hopen.mem_nhds hp] with y hy
    exact sub_eq_zero.mpr (amplitude_eq_homogeneous_of_large_frequency a J u Ω K
      hhigh hC hcomparison y hy.le)
  simpa using (he.iteratedFDeriv ℝ j).eq_of_nhds

/-- Primitive smoothness survives every radial regularization. Uniform jet
bounds as `R ≥ 1` varies are stronger and are not asserted by this lemma.
Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem PrimitiveRegularity.regularized {a : Coefficients n N}
    {J : InputVariables n → ℝ} {W : Set (InputVariables n)}
    (h : PrimitiveRegularity a J W) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (R : ℝ) :
    PrimitiveRegularity (regularizedCoefficients a χ R) J W := by
  refine { h with high := ?_ }
  exact h.high.mul (hχ.comp (contDiff_id.div_const R))

end JanetCartan.ContinuumNormalReduction.TransportSymbol
