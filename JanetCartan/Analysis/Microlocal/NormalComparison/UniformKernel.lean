module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds
public import JanetCartan.Analysis.Microlocal.NormalComparison.FrequencyNormalization

/-!
# Exact kernels from the uniform buffered geometry

Discharges the chart and phase premises of the exact change of variables in
`app:ch_osc:eq:osc-exact-normal-kernel` using the input-only setup. The mask-free
identity is global in both physical positions and uses the smooth extended
amplitude, in the unit-period convention needed by the amplitude estimate.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- The exact full masked kernel of `app:ch_osc:eq:osc-exact-normal-kernel`
under the manuscript's uniform input hypotheses. Injectivity, the determinant
gap, and the phase identity are all discharged from `UniformNormalData`. -/
theorem UniformNormalData.maskedNormalKernel_eq_inverse_integral
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (K : ℝ) (m : Euclidean n → ℝ) {x y : Euclidean n}
    (hx : x ∈ G.X) (hy : y ∈ G.X) :
    maskedNormalKernel G.D K (F.phase ε) (F.amplitude ε) m x y =
      (K / (2 * Real.pi)) ^ n • ∫ v,
        oscillatoryFactor K (inner ℝ (x - y) v) •
          (averagedGradient (F.phase ε) x y '' G.D).indicator
            (inverseJacobianAmplitude (F.amplitude ε) m x y
              (F.inverseChart ε x y) (fderiv ℝ (averagedGradient (F.phase ε) x y))) v := by
  apply maskedNormalKernel_eq_integral_zeroExtension G.D G.isOpen_D.measurableSet K
    (F.phase ε) (F.amplitude ε) m x y (averagedGradient (F.phase ε) x y)
    (F.inverseChart ε x y) (fderiv ℝ (averagedGradient (F.phase ε) x y))
  · intro u hu
    have hf := (F.averagedGradient_spatial_contDiffOn (F.parameter_subset hε)).contDiffAt (x := (x, (y, u)))
      ((G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)).mem_nhds ⟨hx, hy, hu⟩)
    exact ((hf.comp u (contDiffAt_const.prodMk
      (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  · exact F.gradient_injective ε hε x hx y hy
  · exact fun u hu ↦ F.inverseChart_averagedGradient hε hx hy hu
  · intro u hu
    exact abs_pos.mp (G.gap_pos.trans_le (F.jacobian_gap ε hε x hx y hy u hu))
  · exact fun u hu ↦ F.phase_sub_eq_inner (F.parameter_subset hε) hx hy hu

/-- The smooth mask-free inverse amplitude represents the complete normal
kernel everywhere, including outside either physical box
(`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalData.maskFreeNormalKernel_eq_paired_integral
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (K : ℝ) (x y : Euclidean n) :
    maskedNormalKernel G.D K (F.phase ε) (F.amplitude ε) (fun _ ↦ 1) x y =
      (K / (2 * Real.pi)) ^ n • ∫ v,
        oscillatoryFactor K (inner ℝ (x - y) v) •
          F.pairedInverseAmplitude ε v (pairedPosition x y) := by
  by_cases hxy : x ∈ G.X ∧ y ∈ G.X
  · rw [F.maskedNormalKernel_eq_inverse_integral hε K (fun _ ↦ 1) hxy.1 hxy.2]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with v
    rw [F.pairedInverseAmplitude_eq_image_indicator hε hxy.1 hxy.2]
  · have hout : x ∉ G.X₀ ∨ y ∉ G.X₀ := by
      by_contra! h
      exact hxy ⟨G.X₀_subset h.1, G.X₀_subset h.2⟩
    have hz (v : Euclidean n) : F.pairedInverseAmplitude ε v (pairedPosition x y) = 0 := by
      rw [F.pairedInverseAmplitude_eq hε]
      exact F.maskFreeInverseAmplitude_eq_zero_of_not_mem_physical hε hout v
    simp [maskedNormalKernel, F.normalAmplitude_eq_zero_of_not_mem_physical hε hout, hz]

/-- Full-space kernel formula in exactly the `2π` convention of the completed
amplitude theorem (`app:ch_osc:prop:osc-normal`, Step 1). The prefactor is
absorbed by the frequency Jacobian, not dropped. -/
theorem UniformNormalData.maskFreeNormalKernel_eq_unitFrequency_integral
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {K : ℝ} (hK : 0 < K) (x y : Euclidean n) :
    maskedNormalKernel G.D K (F.phase ε) (F.amplitude ε) (fun _ ↦ 1) x y =
      ∫ ξ, Complex.exp ((2 * Real.pi * inner ℝ (x - y) ξ : ℝ) * Complex.I) •
        unitFrequencyAmplitude K (F.pairedInverseAmplitude ε) ξ (pairedPosition x y) := by
  rw [F.maskFreeNormalKernel_eq_paired_integral hε K]
  exact normal_integral_eq_unitFrequency hK x y _

/-- Uniform physical bounds for the actual rescaled inverse amplitudes of
Step 1, with constants chosen before both the family and the frequency
(`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalGeometry.exists_unitFrequencyAmplitude_bounds
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) :
    ∃ R > 0, ∃ A > 0, ∀ F : UniformNormalData G C,
      ∀ ε ∈ Icc 0 G.ε₀, ∀ K : ℝ,
        MatrixNormalAmplitudeBounds
          (unitFrequencyAmplitude K (F.pairedInverseAmplitude ε)) R A := by
  obtain ⟨R, hR, A, hA, hb⟩ := G.exists_pairedInverseAmplitude_bounds C
  exact ⟨R, hR, A, hA, fun F ε hε K ↦ (hb F ε hε).unitFrequencyAmplitude K⟩

/-- At each frequency the transformed amplitude has compact frequency
support, uniformly over the input family and parameter. This removes the
frequency regularization when identifying the operator in Step 1 of
`app:ch_osc:prop:osc-normal`; the operator norm constants need no such radius. -/
theorem UniformNormalGeometry.exists_unitFrequencyAmplitude_support_radius
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) {K : ℝ} (hK : 0 < K) :
    ∃ ρ > 0, ∀ F : UniformNormalData G C, ∀ ε ∈ Icc 0 G.ε₀,
      ∀ ξ : Euclidean n, ρ < ‖ξ‖ → ∀ z,
        unitFrequencyAmplitude K (F.pairedInverseAmplitude ε) ξ z = 0 := by
  let a := K / (2 * Real.pi)
  have ha : a ≠ 0 := ne_of_gt (div_pos hK (by positivity))
  obtain ⟨ρ, hρ, hb⟩ :=
    (G.compact_closure_V.image (continuous_id.const_smul a)).isBounded.exists_pos_norm_le
  refine ⟨ρ, hρ, ?_⟩
  intro F ε hε ξ hξ z
  by_contra hn
  have hv : a⁻¹ • ξ ∈ closure G.V :=
    (F.support_extendedInverseAmplitude_subset hε
      (show (normalLeftPosition n z, (normalRightPosition n z, a⁻¹ • ξ)) ∈
        Function.support (F.extendedInverseAmplitude ε) from hn)).2.2
  have hi : ξ ∈ (fun v : Euclidean n ↦ a • v) '' closure G.V :=
    ⟨a⁻¹ • ξ, hv, by simp [smul_smul, ha]⟩
  exact (not_lt_of_ge (hb ξ hi)) hξ

/-- Applying the completed two-position amplitude theorem to the actual
inverse amplitude gives frequency-uniform finite-regularization bounds and a
strong limit (`app:ch_osc:prop:osc-normal`, Step 1). Identification of this limit
with `T T*` is the remaining operator-realization step, not a premise here. -/
theorem UniformNormalGeometry.exists_uniformFrequencyNormalOperators
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) :
    ∃ B > 0, ∀ F : UniformNormalData G C, ∀ ε ∈ Icc 0 G.ε₀, ∀ K : ℝ,
      ∃ (N : NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r)
        (Nρ : ℝ → NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r),
        ‖N‖ ≤ B ∧ (∀ ρ, ‖Nρ ρ‖ ≤ B) ∧
        (∀ ρ f i, (Nρ ρ f) i =ᵐ[volume] fun x ↦ ∑ j,
          boxScalarAmplitudeKernel
            (fun ξ z ↦ unitFrequencyAmplitude K (F.pairedInverseAmplitude ε) ξ z i j)
            ρ (f j) x) ∧
        ∀ f, Tendsto (fun ρ ↦ Nρ ρ f) atTop (𝓝 (N f)) := by
  obtain ⟨R, hR, A, hA, hb⟩ := G.exists_unitFrequencyAmplitude_bounds C
  let B := (r : ℝ) * r * (fixedBoxAmplitudeConstant n R * A)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (mul_nonneg (fixedBoxAmplitudeConstant_nonneg n R) hA.le)
  refine ⟨B + 1, by linarith, ?_⟩
  intro F ε hε K
  have h := hb F ε hε K
  obtain ⟨N, Nρ, hN, hNρ, hker, hlim, _⟩ :=
    exists_matrixTwoPositionAmplitudeOperator G.dimension_pos R
      (unitFrequencyAmplitude K (F.pairedInverseAmplitude ε))
      (contDiff_unitFrequencyAmplitude K (F.pairedInverseAmplitude_contDiff hε))
      h.support A h.derivative
  have hN' : ‖N‖ ≤ B := by simpa [B] using hN
  have hNρ' : ∀ ρ, ‖Nρ ρ‖ ≤ B := by simpa [B] using hNρ
  exact ⟨N, Nρ, hN'.trans (by linarith),
    fun ρ ↦ (hNρ' ρ).trans (by linarith), hker, hlim⟩

end JanetCartan.NormalComparison
