module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ShiftLaw.Expectation
public import JanetCartan.Analysis.Fourier.SeparatedSampling
public import JanetCartan.Analysis.Operator.HilbertSchmidt.Integral

/-!
# Literal continuum sampling mass

The scalar mass bound consumed by the trace estimate in
`app:ch_waves:eq:sampling-operator-bounds`, obtained from the existing sampled mass
bound and the exact uniform-shift expectation. No partition identity is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators
namespace JanetCartan.SamplingKernelBounds.Expectation
open SeparatedSampling Sampling

variable {p : ℕ} {ψ : Point → ℝ} {w : ℝ → ℝ} {B P W h : ℝ}

/-- The literal patch window has compact support
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem compactSupport_patchWeight (hψ : PatchBounds ψ B P) (q : Lattice) :
    HasCompactSupport (fun z ↦ ψ z * blockWeight w h q z) := by
  apply HasCompactSupport.intro (isCompact_Icc :
    IsCompact (Set.Icc (fun _ : Fin 3 ↦ -B) (fun _ : Fin 3 ↦ B)))
  intro z hz
  have hzero : ψ z = 0 := by
    by_contra hn
    exact hz ⟨fun i ↦ (abs_le.mp (hψ.support z hn i)).1,
      fun i ↦ (abs_le.mp (hψ.support z hn i)).2⟩
  simp [hzero]

/-- Integrability of the actual continuum scalar weight
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_patchWeight (hψ : PatchBounds ψ B P)
    (hψc : Continuous ψ) (hwc : Continuous w) (q : Lattice) :
    Integrable (fun z ↦ ψ z * blockWeight w h q z) :=
  (hψc.mul (continuous_blockWeight hwc h q)).integrable_of_hasCompactSupport
    (compactSupport_patchWeight hψ q)

/-- Integrability of the actual sampled mass under the product shift law
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_totalMass (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h) :
    Integrable (fun ω ↦ totalMass p B ψ w h (extendedShift ω)) (shiftLaw p B h) := by
  have hi := integrable_sampleNormal_shiftLaw (E := ℂ) (H := ℂ) (p := p) (B := B)
    hψc hwc hh (fun _ _ ↦ ContinuousLinearMap.id ℂ ℂ) (fun _ ↦ continuous_const)
  have hd := (diagonalCLM (1 : ℂ)).integrable_comp hi
  simpa [totalMass, map_sum, diagonalCLM_apply, atomNormal,
    ContinuousLinearMap.adjoint_id, inner] using hd

/-- The literal sampled mass has exactly the sum of continuum block masses as
expectation (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integral_totalMass (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h) :
    (∫ ω, totalMass p B ψ w h (extendedShift ω) ∂shiftLaw p B h) =
      ∑ q ∈ integerCube (blockCutoff p B h), ∫ z, ψ z * blockWeight w h q z := by
  let T : (Fin 3 → Fin (p + 1)) → Point → ℂ →L[ℂ] ℂ :=
    fun _ _ ↦ ContinuousLinearMap.id ℂ ℂ
  have he := congrArg (diagonalCLM (1 : ℂ))
    (integral_sampleNormal_shiftLaw hw hψ hψc hwc hh T (fun _ ↦ continuous_const))
  rw [← (diagonalCLM (1 : ℂ)).integral_comp_comm
    (integrable_sampleNormal_shiftLaw hψc hwc hh T (fun _ ↦ continuous_const))] at he
  simp only [map_sum] at he
  have hc (q : Lattice) := (diagonalCLM (1 : ℂ)).integral_comp_comm
    (integrable_blockIntegrand hψ hψc hwc h T (fun _ ↦ continuous_const) q)
  simp_rw [← hc] at he
  simpa [T, totalMass, map_sum, diagonalCLM_apply, atomNormal,
    ContinuousLinearMap.adjoint_id, inner] using he

/-- Mesh-independent continuum mass bound, with the exact existing counting
constant (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuum_mass_le (hw : WindowBounds p w W) (hψ : PatchBounds ψ B P)
    (hψc : Continuous ψ) (hwc : Continuous w) (hh : 0 < h) (hh₁ : h ≤ 1) :
    (∑ q ∈ integerCube (blockCutoff p B h), ∫ z, ψ z * blockWeight w h q z) ≤
      countConstant p B * (P * W ^ 3) := by
  rw [← integral_totalMass hw hψ hψc hwc hh]
  have := isProbabilityMeasure_shiftLaw (p := p) (B := B) hh
  calc
    _ ≤ ∫ _ω, countConstant p B * (P * W ^ 3) ∂shiftLaw p B h :=
      integral_mono (integrable_totalMass hψc hwc hh) (integrable_const _)
        (fun _ ↦ totalMass_le hw hψ hh hh₁)
    _ = _ := by simp

end JanetCartan.SamplingKernelBounds.Expectation
