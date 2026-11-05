module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Estimates
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FourierReconstruction.FourierDatum

/-!
# The actual vector Fourier multiplier

Coordinate extraction commutes with the L² Fourier extension. Consequently
the vector envelope split is the literal Fourier multiplier, and the physical
low piece satisfies the support premise consumed by the forward and reverse
complement estimates in `app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
open MeasureTheory FourierTransform
open JanetCartan.Pseudodifferential
namespace JanetCartan.ResponseTransfer.Complement
variable {d : ℕ} {I : Type*} [Fintype I]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "VL2" => Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)
local notation "L2" => Lp ℂ 2 (volume : Measure E)

private theorem fourier_coordinate_of_integrable (f : VL2)
    (hf : Integrable (f : E → EuclideanSpace ℂ I)) (i : I) :
    𝓕 (finiteL2CoordinateIsometry volume f i) =
      finiteL2CoordinateIsometry volume (𝓕 f) i := by
  let L := PiLp.proj (𝕜 := ℂ) 2 (fun _ : I ↦ ℂ) i
  change 𝓕 (L.compLp f) = L.compLp (𝓕 f)
  have hL : Integrable (L.compLp f : E → ℂ) :=
    (L.integrable_comp hf).congr (Filter.EventuallyEq.symm (L.coeFn_compLp f))
  apply Lp.ext
  filter_upwards [Localization.fourierTransform_coeFn_ae_integral_hilbert _ hL,
    L.coeFn_compLp (𝓕 f), Localization.fourierTransform_coeFn_ae_integral_hilbert f hf]
    with ξ h₁ h₂ h₃
  rw [h₁, Real.fourier_congr_ae (L.coeFn_compLp f) ξ, h₂, h₃]
  simp only [Real.fourier_eq, Circle.smul_def, ← L.map_smul]
  exact L.integral_comp_comm ((Real.fourierIntegral_convergent_iff ξ).mpr hf)

/-- The proved finite L² coordinates commute with the actual Fourier
extension. This identifies the complete-complement split in
`app:ch_response:thm:response-literal-transfer`. -/
theorem coordinate_fourier (f : VL2) (i : I) :
    finiteL2CoordinateIsometry volume (𝓕 f) i =
      𝓕 (finiteL2CoordinateIsometry volume f i) := by
  symm
  apply DenseRange.induction_on
    (p := fun f : VL2 ↦ 𝓕 (finiteL2CoordinateIsometry volume f i) =
      finiteL2CoordinateIsometry volume (𝓕 f) i)
    (SchwartzMap.denseRange_toLpCLM (F := EuclideanSpace ℂ I)
      (p := 2) ENNReal.ofNat_ne_top) f
  · let L := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : I ↦ ℂ) i).compLpL 2
      (volume : Measure E)
    exact isClosed_eq (continuous_fourier.comp L.continuous)
      (L.continuous.comp continuous_fourier)
  intro g
  exact fourier_coordinate_of_integrable _ (g.integrable.congr (g.coeFn_toLp 2).symm) i

namespace EnvelopeCutoff
variable {Λ B R : ℝ} (χ : EnvelopeCutoff d Λ B R)

/-- Fourier representative of the actual vector low envelope, consumed by the
low-support estimates of `app:ch_response:thm:response-literal-transfer`. -/
theorem fourier_vectorLow_ae (f : VL2) :
    (𝓕 (χ.vectorLow f) : VL2) =ᵐ[volume]
      fun ξ ↦ χ.symbol ξ • (𝓕 f : VL2) ξ := by
  apply (finiteL2CoordinateIsometry_ae_iff _ _ _).mpr
  intro i
  rw [coordinate_fourier, coordinate_vectorLow]
  filter_upwards [χ.fourier_low_ae (finiteL2CoordinateIsometry volume f i),
    finiteL2Coordinates_apply_ae volume (𝓕 f) i] with ξ hξ hi
  rw [← coordinate_fourier] at hξ
  change _ = χ.symbol ξ • (𝓕 f : VL2) ξ i
  exact hξ.trans (congrArg (χ.symbol ξ • ·) hi)

/-- Fourier representative of the exact vector complement, for
`app:ch_response:thm:response-literal-transfer`. -/
theorem fourier_vectorHigh_ae (f : VL2) :
    (𝓕 (χ.vectorHigh f) : VL2) =ᵐ[volume]
      fun ξ ↦ (1 - χ.symbol ξ) • (𝓕 f : VL2) ξ := by
  have hf : 𝓕 (χ.vectorHigh f) = 𝓕 f - 𝓕 (χ.vectorLow f) :=
    map_sub (fourierCLM ℂ VL2) _ _
  rw [hf]
  filter_upwards [Lp.coeFn_sub (𝓕 f) (𝓕 (χ.vectorLow f)), χ.fourier_vectorLow_ae f]
    with ξ hξ hlow
  simp only [hξ, Pi.sub_apply, hlow, sub_smul, one_smul]

/-- The actual vector symbol product is in L²; used to express the cutoff
as the inverse Fourier multiplier in `app:ch_response:thm:response-literal-transfer`. -/
theorem memLp_symbol_vectorFourier (f : VL2) :
    MemLp (fun ξ ↦ χ.symbol ξ • (𝓕 f : VL2) ξ) 2 volume :=
  (Lp.memLp (𝓕 (χ.vectorLow f))).ae_eq (χ.fourier_vectorLow_ae f)

/-- The coordinate construction equals the actual vector L² Fourier multiplier
in `app:ch_response:thm:response-literal-transfer`. -/
theorem vectorLow_eq_fourierInv (f : VL2) :
    χ.vectorLow f = 𝓕⁻ ((χ.memLp_symbol_vectorFourier f).toLp _) := by
  have h : 𝓕 (χ.vectorLow f) = (χ.memLp_symbol_vectorFourier f).toLp _ := by
    apply Lp.ext
    exact (χ.fourier_vectorLow_ae f).trans (χ.memLp_symbol_vectorFourier f).coeFn_toLp.symm
  rw [← h, fourierInv_fourier_eq]

/-- Fourier support of the low vector envelope, for
`app:ch_response:thm:response-literal-transfer`. -/
theorem fourier_vectorLow_zero_outside (f : VL2) :
    ∀ᵐ ξ ∂volume, R * Λ ≤ ‖ξ‖ → (𝓕 (χ.vectorLow f) : VL2) ξ = 0 := by
  filter_upwards [χ.fourier_vectorLow_ae f] with ξ hξ hball
  simp [hξ, χ.zero_outside ξ hball]

/-- The exact physical low-support premise of `forwardComplement_lowSupport_vector`
and `reverseComplement_lowSupport_of_geometry`. The symbol is χ(2πξ), so
support in the paper's covector θ is precisely the radius RΛ
(`app:ch_response:thm:response-literal-transfer`). -/
theorem paperL2FourierTransform_vectorLow_zero_outside {r : ℕ}
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)) :
    ∀ᵐ θ ∂volume, R * Λ < ‖θ‖ →
      LowEnvelope.paperL2FourierTransform (χ.physicalCovectorCutoff.vectorLow f) θ = 0 := by
  have h := (volume.quasiMeasurePreserving_smul
    (inv_ne_zero (by positivity : (2 * Real.pi : ℝ) ≠ 0))).ae
      (χ.physicalCovectorCutoff.fourier_vectorLow_ae f)
  filter_upwards [h] with θ hθ hball
  rw [LowEnvelope.paperL2FourierTransform, hθ]
  change ((2 * Real.pi) ^ d : ℝ)⁻¹ •
    (χ.symbol ((2 * Real.pi) • ((2 * Real.pi)⁻¹ • θ)) • _) = 0
  rw [smul_inv_smul₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0),
    χ.zero_outside θ hball.le, zero_smul, smul_zero]

end EnvelopeCutoff
end JanetCartan.ResponseTransfer.Complement
