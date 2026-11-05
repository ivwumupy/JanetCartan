module

public import JanetCartan.Analysis.Microlocal.NormalComparison.CompactFrequency
public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.MatrixKernel

/-!
# Uniform bounds for the actual oscillatory operators

Step 1 of `app:ch_osc:prop:osc-normal`: identify the complete Hilbert-adjoint
normal kernel with the compact-frequency amplitude operator. The bound is
chosen before the family, parameter and frequency.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Matrix.Norms.Frobenius RealInnerProductSpace
namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

local instance (r : ℕ) : TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- Entrywise form of the exact rescaled kernel, retaining its frequency
Jacobian and both physical positions (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem UniformNormalData.maskFreeNormalKernel_apply_unitFrequency
    (F : UniformNormalData G C) {ε K : ℝ} (hε : ε ∈ Icc 0 G.ε₀) (hK : 0 < K)
    (x y : Euclidean n) (i j : Fin r) :
    maskedNormalKernel G.D K (F.phase ε) (F.amplitude ε) (fun _ ↦ 1) x y i j =
      ∫ ξ, Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) *
        unitFrequencyAmplitude K (F.pairedInverseAmplitude ε) ξ (pairedPosition x y) i j := by
  obtain ⟨ρ, _, hρ⟩ := G.exists_unitFrequencyAmplitude_support_radius C hK
  let b := unitFrequencyAmplitude K (F.pairedInverseAmplitude ε)
  let H := fun ξ ↦ Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I) •
    b ξ (pairedPosition x y)
  have hb := contDiff_unitFrequencyAmplitude K (F.pairedInverseAmplitude_contDiff hε)
  have hc : Continuous H := by
    have he : Continuous (fun ξ : Euclidean n ↦
        Complex.exp (↑(2 * Real.pi * ⟪x - y, ξ⟫) * Complex.I)) := by fun_prop
    exact he.smul (hb.continuous.comp (continuous_id.prodMk continuous_const))
  have hs : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euclidean n) ρ)
      (by
        intro ξ hξ
        by_contra hout
        have hlt : ρ < ‖ξ‖ := by simpa using hout
        exact hξ (by simp [H, b, hρ F ε hε ξ hlt]))
  rw [F.maskFreeNormalKernel_eq_unitFrequency_integral hε hK]
  exact ((matrixEntryEvaluation i j).integral_comp_comm
    (hc.integrable_of_hasCompactSupport hs)).symm

/-- The mask-free actual normal operator has a frequency-uniform bound from
only the original input data (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalGeometry.exists_uniformOscillatoryNormalOperator_bound
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) :
    ∃ B > 0, ∀ F : UniformNormalData G C, ∀ ε ∈ Icc 0 G.ε₀, ∀ K > 0,
      ∀ g : Lp ℂ ∞ (volume.restrict G.D),
        g =ᵐ[volume.restrict G.D] (fun _ ↦ (1 : ℂ)) →
        ‖F.uniformOscillatoryNormalOperator K g ε‖ ≤ B := by
  obtain ⟨R, _, A, hA, hb⟩ := G.exists_unitFrequencyAmplitude_bounds C
  let B := (r : ℝ) * r * (fixedBoxAmplitudeConstant n R * A)
  have hB : 0 ≤ B := by
    have := fixedBoxAmplitudeConstant_nonneg n R
    dsimp [B]
    positivity
  refine ⟨B + 1, by linarith, ?_⟩
  intro F ε hε K hK g hg
  obtain ⟨ρ, _, hρ⟩ := G.exists_unitFrequencyAmplitude_support_radius C hK
  apply le_trans (norm_compactFrequencyMatrixAmplitudeOperator_le
    G.dimension_pos R
    (unitFrequencyAmplitude K (F.pairedInverseAmplitude ε))
    (contDiff_unitFrequencyAmplitude K (F.pairedInverseAmplitude_contDiff hε)) A
    (hb F ε hε K) (isCompact_closedBall (0 : Euclidean n) ρ)
    (fun ξ hξ z ↦ hρ F ε hε ξ (by simpa using hξ) z)
    (F.uniformOscillatoryNormalOperator K g ε) ?_) (by dsimp [B]; linarith)
  intro f i
  refine (F.uniformOscillatoryNormalOperator_ae_maskedNormalKernel hK.le hε
    (m := fun _ ↦ (1 : ℝ)) continuousOn_const g (by simpa only [Complex.ofReal_one] using hg) f i).trans (Eventually.of_forall fun x ↦ ?_)
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  exact Eventually.of_forall fun y ↦ by
    dsimp only
    rw [F.maskFreeNormalKernel_apply_unitFrequency hε hK]

/-- The entire-input L² estimate `app:ch_osc:eq:osc-normal-basic`.
The constant depends only on the fixed geometry and finite input jets.
It holds in every positive dimension, including the one-dimensional slices
consumed by `SingleChannel.exists_oscillatorySingleChannelOperator` in
`app:ch_osc:prop:osc-channel`. -/
theorem UniformNormalGeometry.exists_uniformOscillatoryOperator_bound
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) :
    ∃ S > 0, ∀ F : UniformNormalData G C, ∀ ε ∈ Icc 0 G.ε₀, ∀ K > 0,
      ‖F.uniformOscillatoryOperator K ε‖ ≤ S := by
  obtain ⟨B, hB, hb⟩ := G.exists_uniformOscillatoryNormalOperator_bound C
  let g : Lp ℂ ∞ (volume.restrict G.D) :=
    boundedSymbol (fun _ ↦ 1) aestronglyMeasurable_const 1 (by simp)
  have hg : g =ᵐ[volume.restrict G.D] fun _ ↦ (1 : ℂ) :=
    boundedSymbol_coeFn _ _ _ _
  have hm : multiplicationOperator g = ContinuousLinearMap.id ℂ
      (Lp ℂ 2 (volume.restrict G.D)) := by
    ext f
    filter_upwards [multiplicationOperator_coeFn g f, hg] with u hu hgu
    simpa [hgu] using hu
  refine ⟨B + 1, by linarith, ?_⟩
  intro F ε hε K hK
  have hn := hb F ε hε K hK g hg
  rw [UniformNormalData.uniformOscillatoryNormalOperator, hm,
    ContinuousLinearMap.id_comp] at hn
  have he := ContinuousLinearMap.norm_adjoint_comp_self
    (F.uniformOscillatoryOperator K ε).adjoint
  simp only [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint.norm_map] at he
  rw [he] at hn
  nlinarith [norm_nonneg (F.uniformOscillatoryOperator K ε)]

end JanetCartan.NormalComparison
