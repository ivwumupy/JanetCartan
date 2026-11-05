module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.CarrierNormalRealization.FiniteIdentification.Locality
public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.CompactPDO.Fubini

/-!
# Finite radial support and the source-frequency interchange

For `app:ch_background:prop:bg-frame`, Step 1, radial support is transported
through the actual inverse chart before applying compact-frequency Fubini.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CarrierNormalRealization
open ContinuumNormal AmplitudeBound Pseudodifferential PeriodicLocalL2 ContinuumNormalReduction TransportKernel TestChartTransfer
variable {n N : ℕ}

/-- The actual radial regularization has compact high-mask support. This
supplies the finite-frequency Fubini hypothesis from the original compact
radial profile (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem regularizedCoefficients_high_hasCompactSupport
    (a : TransportSymbol.Coefficients n N) {κ : ℝ → ℝ}
    (hκ : HasCompactSupport κ) {R : ℝ} (hR : R ≠ 0) :
    HasCompactSupport (TransportSymbol.regularizedCoefficients a κ R).high := by
  have hc : HasCompactSupport (fun t : ℝ ↦ κ (t / R)) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hκ.comp_smul (inv_ne_zero hR)
  exact hc.mul_left

/-- The original compact radial high mask and the inverse-frequency comparison
force compact output frequency support, before taking the spectator integral.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem amplitude_eq_zero_of_compact_high
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    {L C : ℝ} (hC : 0 ≤ C) (hhigh : ∀ t, L ≤ t → a.high t = 0)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (p : TransportSymbol.Variables n) (hp : C * L < ‖p.2.2‖) :
    TransportSymbol.amplitude a J u Ω S p = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [] with v
  by_cases hv : (p, v) ∈ Ω
  · have hL : L ≤ ‖(u (p, v)).2‖ := by
      by_contra hn
      have hbound := mul_le_mul_of_nonneg_left (le_of_lt (not_le.mp hn)) hC
      exact (not_lt_of_ge ((hcomparison (p, v) hv).trans hbound)) hp
    simp [TransportSymbol.extendedDensity, hv, TransportSymbol.inputDensity,
      TransportSymbol.inputWeight, TransportSymbol.inverseCoordinates, hhigh _ hL]
  · simp [TransportSymbol.extendedDensity, hv]

/-- Both positions and the cycle frequency of the finite reflected full symbol
have joint compact support. The frequency support comes from the actual radial
mask through the inverse-frequency comparison, not a source-integrability
premise (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem fullReflectedMatrixAmplitude_hasCompactSupport
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hhigh : HasCompactSupport a.high) {C : ℝ} (hC : 0 ≤ C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (R : ℝ) (hs : ∀ ξ i j, SupportedInCenteredBox R
      (fun z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j)) :
    HasCompactSupport (Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S)) := by
  obtain ⟨L, hL, hzero⟩ := hhigh.exists_pos_le_norm
  have hz (t : ℝ) (ht : L ≤ t) : a.high t = 0 := hzero t (by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hL.le.trans ht)] using ht)
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_closedBall (0 : Euclidean n) (C * L / (2 * Real.pi))).prod
      (DifferentialChart.isCompact_chartBox (d := 2 * n) R))
  intro p hp
  have hn : fullReflectedMatrixAmplitude a J u Ω S p.1 p.2 ≠ 0 := hp
  have hfreq : ‖p.1‖ ≤ C * L / (2 * Real.pi) := by
    by_contra hf
    have hbound : C * L < ‖(2 * Real.pi) • p.1‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      exact (div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)).mp (not_le.mp hf) |>.trans_eq (mul_comm _ _)
    have h₁ := amplitude_eq_zero_of_compact_high a J u Ω S hC hz hcomparison
      (freezingOutputProjection p.2, freezingSourceProjection p.2, (2 * Real.pi) • p.1) hbound
    have h₂ := amplitude_eq_zero_of_compact_high a J u Ω S hC hz hcomparison
      (freezingOutputProjection p.2, freezingSourceProjection p.2, -((2 * Real.pi) • p.1))
      (by simpa only [norm_neg] using hbound)
    apply hn
    ext i j
    simp [fullReflectedMatrixAmplitude, reflectedSymbolAmplitude, h₁, h₂]
  refine ⟨by simpa using hfreq, ?_⟩
  have he : ∃ i j, fullReflectedMatrixAmplitude a J u Ω S p.1 p.2 i j ≠ 0 := by
    by_contra h
    apply hn
    ext i j
    exact not_ne_iff.mp (fun hij ↦ h ⟨i, j, hij⟩)
  obtain ⟨i, j, hij⟩ := he
  exact hs p.1 i j p.2 hij

/-- Finite-frequency Fubini for the original reflected full amplitude, retaining
`k = 2πξ`, both matrix coordinates, both physical positions and the spectator
integral. The compact radial high mask supplies the integrability needed for
interchange (`app:ch_background:eq:bg-real-symbol`). -/
theorem reflectedMatrixKernelAction_eq_testAction_of_compact_high
    (a : TransportSymbol.Coefficients n N) (J : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (S : Set (Euclidean 2))
    (hhigh : HasCompactSupport a.high) {C : ℝ} (hC : 0 ≤ C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (R : ℝ) (hs : ∀ ξ i j, SupportedInCenteredBox R
      (fun z ↦ fullReflectedMatrixAmplitude a J u Ω S ξ z i j))
    (hb : Continuous (Function.uncurry (fullReflectedMatrixAmplitude a J u Ω S)))
    (f : Euclidean n → EuclideanSpace ℂ (Fin n)) (hf : Continuous f)
    (hfc : HasCompactSupport f) (x : Euclidean n) :
    reflectedMatrixKernelAction a J u Ω S (fun j y ↦ f y j) x =
      reflectedMatrixTestAction a J u Ω S (fun j y ↦ f y j) x := by
  have he := FourierIntegral.LowBounds.compactSymbol_matrixFullAmplitudeOperator_eq_cycleIntegral
    (fullReflectedMatrixAmplitude a J u Ω S) hb
    (fullReflectedMatrixAmplitude_hasCompactSupport a J u Ω S hhigh hC hcomparison R hs)
    f hf hfc x
  apply PiLp.ext
  intro i
  have hei := congrFun he i
  rw [matrixFullAmplitudeOperator_fullReflectedMatrixAmplitude] at hei
  rw [hei]
  change (∑ j : Fin n, _) = _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [fullReflectedMatrixAmplitude_pairedPosition, amplitudeKernel_eq_integral,
    smul_eq_mul, real_inner_comm]
end JanetCartan.ContinuumRow.CarrierNormalRealization
