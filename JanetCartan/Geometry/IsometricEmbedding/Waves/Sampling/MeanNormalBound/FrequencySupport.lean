module

public import JanetCartan.Analysis.Microlocal.NormalComparison.UniformKernel

/-!
# Supported frequency gaps for sampling normals

The finite-overlap argument following
`app:ch_waves:eq:sampling-operator-bounds` needs a lower frequency radius.
`UniformNormalGeometry` alone only supplies an upper radius. Here the missing
primitive input is stated on the original averaged gradient, on the compact
amplitude support in both positions and the original input variable. It is
transported through the actual inverse Jacobian and the exact `2π` substitution.

The canonical producer is
`FullPhaseCharts.ActualInverses.exists_actual_buffered_inverses_with_caps`:
its annular conclusion must be identified with this SAME averaged gradient on
the supported chart. This module does not assert that identification or an
unconditional sampling bound.
-/

@[expose] public noncomputable section
open Set
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeanNormalBound
open NormalComparison AmplitudeBound

variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- A nonzero full inverse amplitude comes from the original compact input
support, at the same two physical positions
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem inverseAmplitude_support_preimage (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) {x y v : Euclidean n}
    (hne : F.maskFreeInverseAmplitude ε x y v ≠ 0) :
    x ∈ G.X₀ ∧ y ∈ G.X₀ ∧ v ∈ G.V ∧
      F.inverseChart ε x y v ∈ G.D₀ ∧
      averagedGradient (F.phase ε) x y (F.inverseChart ε x y v) = v := by
  classical
  have hxy : x ∈ G.X₀ ∧ y ∈ G.X₀ := by
    by_contra h
    exact hne (F.maskFreeInverseAmplitude_eq_zero_of_not_mem_physical hε
      (not_and_or.mp h) v)
  have hv : v ∈ G.V := by
    by_contra h
    exact hne (by simp [UniformNormalData.maskFreeInverseAmplitude, h])
  have hu : F.inverseChart ε x y v ∈ G.D₀ := by
    by_contra h
    exact hne (by simp [UniformNormalData.maskFreeInverseAmplitude, hv,
      inverseJacobianAmplitude, F.normalAmplitude_eq_zero_of_not_mem_input hε x y h])
  exact ⟨hxy.1, hxy.2, hv, hu,
    F.averagedGradient_inverseChart hε (G.X₀_subset hxy.1) (G.X₀_subset hxy.2) hv⟩

/-- The needed nonzero transformed-frequency gap is a primitive phase
condition, not a bound on an already constructed normal amplitude.
It implies the lower support bound for that full amplitude
(`app:ch_seed:eq:seed-normal-annulus`). -/
theorem pairedInverseAmplitude_frequency_lower (F : UniformNormalData G C)
    {ε γ : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (hgap : ∀ x ∈ G.X₀, ∀ y ∈ G.X₀, ∀ u ∈ G.D₀,
      γ ≤ ‖averagedGradient (F.phase ε) x y u‖)
    {v : Euclidean n} {z : Euclidean (2 * n)}
    (hne : F.pairedInverseAmplitude ε v z ≠ 0) : γ ≤ ‖v‖ := by
  rw [← pairedPosition_normalPositions z, F.pairedInverseAmplitude_eq hε] at hne
  obtain ⟨hx, hy, _, hu, he⟩ := inverseAmplitude_support_preimage F hε hne
  simpa only [he] using hgap _ hx _ hy _ hu

/-- The lower annular support after the literal change `ξ = K v / (2π)`.
Neither physical position nor the absolute inverse Jacobian is removed
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem unitFrequencyAmplitude_frequency_lower (F : UniformNormalData G C)
    {ε γ K : ℝ} (hε : ε ∈ Icc 0 G.ε₀) (hK : 0 < K)
    (hgap : ∀ x ∈ G.X₀, ∀ y ∈ G.X₀, ∀ u ∈ G.D₀,
      γ ≤ ‖averagedGradient (F.phase ε) x y u‖)
    {ξ : Euclidean n} {z : Euclidean (2 * n)}
    (hne : unitFrequencyAmplitude K (F.pairedInverseAmplitude ε) ξ z ≠ 0) :
    (γ / (2 * Real.pi)) * K ≤ ‖ξ‖ := by
  have ha : 0 < K / (2 * Real.pi) := div_pos hK (by positivity)
  have hb := pairedInverseAmplitude_frequency_lower F hε hgap hne
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)] at hb
  have hc := mul_le_mul_of_nonneg_left hb ha.le
  rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at hc
  convert hc using 1
  ring

/-- The upper annular coefficient is chosen before the family, parameter
and frequency. Together with the supported primitive gap above this gives
`c K ≤ ‖ξ‖ ≤ C K`, as required by the dyadic finite-overlap argument after
`app:ch_waves:eq:sampling-operator-bounds`. -/
theorem exists_unitFrequencyAmplitude_frequency_upper
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) :
    ∃ β > 0, ∀ F : UniformNormalData G C, ∀ ε ∈ Icc 0 G.ε₀,
      ∀ K > 0, ∀ ξ z,
        unitFrequencyAmplitude K (F.pairedInverseAmplitude ε) ξ z ≠ 0 →
          ‖ξ‖ ≤ β * K := by
  obtain ⟨ρ, hρ, hbound⟩ := G.compact_closure_V.isBounded.exists_pos_norm_le
  refine ⟨ρ / (2 * Real.pi), div_pos hρ (by positivity), ?_⟩
  intro F ε hε K hK ξ z hne
  have ha : 0 < K / (2 * Real.pi) := div_pos hK (by positivity)
  have hv : (K / (2 * Real.pi))⁻¹ • ξ ∈ closure G.V :=
    (F.support_extendedInverseAmplitude_subset hε
      (show (normalLeftPosition n z, (normalRightPosition n z,
        (K / (2 * Real.pi))⁻¹ • ξ)) ∈
          Function.support (F.extendedInverseAmplitude ε) from hne)).2.2
  have hb := hbound _ hv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)] at hb
  have hc := mul_le_mul_of_nonneg_left hb ha.le
  rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at hc
  convert hc using 1
  ring

end JanetCartan.Sampling.MeanNormalBound
