module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.SourceCommutator
/-!
# Literal Schwartz action of the image-normal diagonal terms

The two pieces of the source-square diagonal reduction in
`app:ch_background:prop:bg-frame`, Step 1, are identified with the actual
Bessel Fourier multiplier. In particular the diagonal retains its source
mask; it is not an assertion that the multiplier commutes with a cutoff.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap
open JanetCartan.Pseudodifferential
namespace JanetCartan.ContinuumNormalReduction.ImageNormal
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The full amplitude with a physical source multiplier acts by the
literal Bessel multiplier after source multiplication
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageBessel_masked_fullAmplitude (ψ : E → ℂ) (hψ : ψ.HasTemperateGrowth)
    (u : 𝓢(E, ℂ)) (x : E) :
    fullAmplitudeOperator (fun _ y ξ ↦ imageBesselSymbol ξ • ψ y) u x =
      schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ))
        (SchwartzMap.smulLeftCLM ℂ ψ u) x := by
  have he : fullAmplitudeOperator (fun _ y ξ ↦ imageBesselSymbol ξ • ψ y) u x =
      fullAmplitudeOperator (fun _ _ ξ ↦ (imageBesselSymbol ξ : ℂ))
        (SchwartzMap.smulLeftCLM ℂ ψ u) x := by
    unfold fullAmplitudeOperator sourceAmplitudeTransform
    apply congrArg (fun f : E → ℂ ↦ 𝓕⁻ f x)
    funext ξ
    apply congrArg (fun f : E → ℂ ↦ 𝓕 f ξ)
    funext y
    simp only [SchwartzMap.smulLeftCLM_apply_apply hψ, smul_eq_mul, Complex.real_smul]
    ring
  rw [he, fullAmplitudeOperator_sourceIndependent,
    ← schwartzFrequencyMultiplier_eq_sourceIndependentOperator _
      hasTemperateGrowth_complex_imageBesselSymbol]

/-- The diagonal term in the image source-square reduction keeps its
source cutoff inside the Bessel multiplier
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem imageBessel_diagonal_fullAmplitude (χ β : E → ℝ)
    (hβ : β.HasTemperateGrowth) (u : 𝓢(E, ℂ)) (x : E) :
    fullAmplitudeOperator (diagonalAmplitude
      (fun _ y ξ ↦ imageBesselSymbol ξ • ((χ y)^2 : ℂ)) β) u x =
      (χ x)^2 • schwartzFrequencyMultiplier (fun ξ ↦ (imageBesselSymbol ξ : ℂ))
        (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ)) u) x := by
  have hβℂ : (fun y ↦ (β y : ℂ)).HasTemperateGrowth := by fun_prop
  have hψ : (fun y ↦ β y • ((χ x)^2 : ℂ)).HasTemperateGrowth := by fun_prop
  have he : (fun y ξ ↦ diagonalAmplitude
      (fun _ y ξ ↦ imageBesselSymbol ξ • ((χ y)^2 : ℂ)) β x y ξ) =
      fun y ξ ↦ imageBesselSymbol ξ • (β y • ((χ x)^2 : ℂ)) := by
    funext y ξ
    exact smul_comm _ _ _
  have he' : fullAmplitudeOperator (diagonalAmplitude
      (fun _ y ξ ↦ imageBesselSymbol ξ • ((χ y)^2 : ℂ)) β) u x =
      fullAmplitudeOperator (fun _ y ξ ↦ imageBesselSymbol ξ • (β y • ((χ x)^2 : ℂ))) u x := by
    unfold fullAmplitudeOperator sourceAmplitudeTransform
    apply congrArg (fun f : E → ℂ ↦ 𝓕⁻ f x)
    funext ξ
    apply congrArg (fun f : E → ℂ ↦ 𝓕 f ξ)
    funext y
    rw [show diagonalAmplitude
      (fun _ y ξ ↦ imageBesselSymbol ξ • ((χ y)^2 : ℂ)) β x y ξ =
      imageBesselSymbol ξ • (β y • ((χ x)^2 : ℂ)) from congrFun (congrFun he y) ξ]
  rw [he', imageBessel_masked_fullAmplitude _ hψ]
  have hv : SchwartzMap.smulLeftCLM ℂ (fun y ↦ β y • ((χ x)^2 : ℂ)) u =
      ((χ x)^2 : ℂ) • SchwartzMap.smulLeftCLM ℂ (fun y ↦ (β y : ℂ)) u := by
    ext y
    rw [SchwartzMap.smulLeftCLM_apply_apply hψ]
    simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hβℂ,
      smul_eq_mul, Complex.real_smul]
    ring
  rw [hv]
  simp only [schwartzFrequencyMultiplier,
    ← FourierTransform.fourierCLM_apply (R := ℂ), ← FourierTransform.fourierInvCLM_apply (R := ℂ),
    map_smul, smul_apply, Complex.real_smul, Complex.ofReal_pow, smul_eq_mul]

end JanetCartan.ContinuumNormalReduction.ImageNormal
