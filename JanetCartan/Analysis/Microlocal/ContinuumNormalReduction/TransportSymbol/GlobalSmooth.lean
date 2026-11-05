module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.GlobalNormBounds

/-!
# Smooth global amplitudes from the conic buffer and the low-frequency gap

The same primitive conic buffer used for the symbol estimates suffices for
smooth zero extension. The high mask handles the cone vertex, so no extension
of the inverse to zero and no additional closed high-frequency support image
are required. This closes the smoothness inputs of the fixed completion in
`app:ch_background:eq:bg-symbol` and bg-frame Step 1.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

section PrimitiveInputs
variable (a : Coefficients n N) (J : InputVariables n → ℝ)
  (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
  (F : InputVariables n → Variables n × Euclidean 2)
  {Ω : Set (Variables n × Euclidean 2)} {W L : Set (InputVariables n)}
  (hΩ : IsOpen Ω) (h : PrimitiveRegularity a J W) (hu : ContDiffOn ℝ ∞ u Ω)
  (hmap : MapsTo (inverseCoordinates u) Ω W)
  (hright : ∀ p ∈ Ω, F (inverseCoordinates u p) = p)
  (hs : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
    a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → p ∈ L)
  (hbuffer : closure (F '' L) ∩ {p | p.1.2.2 ≠ 0} ⊆ Ω)
  (hzero : ∀ r : ℝ, r ≤ 1 → a.high r = 0)
  {C ℓ : ℝ} (hC : 0 ≤ C) (hℓ : 0 < ℓ) (hlow : C * ℓ ≤ 1)
  (hupper : ∀ p ∈ Ω, ‖(u p).2‖ ≤ C * ‖p.1.2.2‖)

include hΩ h hu hmap hright hs hbuffer hzero hC hℓ hlow hupper

/-- Smooth zero extension of the literal density follows from the conic
buffer and the primitive low-frequency gap. In particular no inverse jets
at zero are assumed. Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem extendedDensity_contDiff_of_punctured_buffer :
    ContDiff ℝ ∞ (extendedDensity a J u Ω) := by
  have hd := extendedDensity_contDiffOn_of_relative_buffer a J u F hΩ h hu hmap
    hright (fun p hp h₁ h₂ h₃ _ ↦ hs p hp h₁ h₂ h₃) hbuffer
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p.1.2.2 = 0
  · apply (contDiffAt_const (c := (0 : Matrix (Fin n) (Fin n) ℝ))).congr_of_eventuallyEq
    have hopen : IsOpen {q : Variables n × Euclidean 2 | ‖q.1.2.2‖ < ℓ} :=
      isOpen_lt continuous_fst.snd.snd.norm continuous_const
    filter_upwards [hopen.mem_nhds (by simpa [hp] using hℓ)] with q hq
    exact extendedDensity_eq_zero_of_low_frequency a J u Ω hzero hupper q
      ((mul_le_mul_of_nonneg_left hq.le hC).trans hlow)
  · exact hd.contDiffAt
      ((isOpen_ne_fun continuous_fst.snd.snd continuous_const).mem_nhds hp)

variable {K : Set (Euclidean 2)} (hK : IsCompact K)
include hK

/-- Global smoothness and every derivative-under-integral identity from the
same primitive conic buffer. The spectator measure remains restricted
Lebesgue measure. Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem amplitude_smooth_and_derivatives_of_punctured_buffer :
    ContDiff ℝ ∞ (amplitude a J u Ω K) ∧
    ∀ j : ℕ, ∀ x : Variables n, iteratedFDeriv ℝ j (amplitude a J u Ω K) x =
      ∫ v in K, iteratedFDeriv ℝ j (fun y ↦ extendedDensity a J u Ω (y, v)) x := by
  have hd := extendedDensity_contDiff_of_punctured_buffer a J u F hΩ h hu hmap
    hright hs hbuffer hzero hC hℓ hlow hupper
  refine ⟨?_, fun j x ↦ iteratedFDeriv_spectatorIntegral hK j hd x⟩
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact contDiffOn_univ.mp (contDiffOn_compactParameterIntegral
    isOpen_univ isOpen_univ hK (subset_univ K) hd.contDiffOn)

/-- Smoothness and spectator differentiation for every radial regularization
follow from the original primitives. No new support or smoothness premise on
the composed regularized amplitude is needed. Source: bg-frame Step 1. -/
theorem regularizedAmplitude_smooth_and_derivatives_of_punctured_buffer
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (Q : ℝ) :
    ContDiff ℝ ∞ (amplitude (regularizedCoefficients a χ Q) J u Ω K) ∧
    ∀ j : ℕ, ∀ x : Variables n,
      iteratedFDeriv ℝ j (amplitude (regularizedCoefficients a χ Q) J u Ω K) x =
      ∫ v in K, iteratedFDeriv ℝ j
        (fun y ↦ extendedDensity (regularizedCoefficients a χ Q) J u Ω (y, v)) x := by
  apply amplitude_smooth_and_derivatives_of_punctured_buffer
    (regularizedCoefficients a χ Q) J u F hΩ (h.regularized hχ Q) hu hmap hright
    hs hbuffer _ hC hℓ hlow hupper hK
  intro r hr
  simp [regularizedCoefficients, hzero r hr]

/-- The fixed smooth completion and its bounded-frequency smoothing
remainder use precisely the primitive conic buffer and two frequency
comparisons. Quantitative jets are supplied independently by
`exists_transportCompletion_discrepancy_bound_of_primitiveNorms` (and its
initial-multiplier version), without an extra analytic premise.
Source: the paragraph following `app:ch_background:eq:bg-symbol`. -/
theorem completedAmplitude_and_discrepancy_of_punctured_buffer
    (hone : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C' : ℝ} (hC' : 0 < C')
    (hlower : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C' * ‖(u p).2‖) :
    ContDiff ℝ ∞ (completedAmplitude a J u Ω K) ∧
    ContDiff ℝ ∞ (fun p ↦ amplitude a J u Ω K p - completedAmplitude a J u Ω K p) ∧
    ∀ j : ℕ, tsupport (iteratedFDeriv ℝ j
      (fun p ↦ amplitude a J u Ω K p - completedAmplitude a J u Ω K p)) ⊆
      {p | ‖p.2.2‖ ≤ max 2 (2 * C')} := by
  have ha := (amplitude_smooth_and_derivatives_of_punctured_buffer a J u F hΩ h hu
    hmap hright hs hbuffer hzero hC hℓ hlow hupper hK).1
  have hh := homogeneousAmplitude_contDiffOn_punctured a J u F hΩ h hu hmap hright
    hs hbuffer hK
  exact ⟨completedAmplitude_contDiff a J u Ω K hh,
    completion_discrepancy_contDiff a J u Ω K ha hh,
    tsupport_iteratedFDeriv_completion_discrepancy_subset a J u Ω K hone hC' hlower⟩

end PrimitiveInputs
end JanetCartan.ContinuumNormalReduction.TransportSymbol
