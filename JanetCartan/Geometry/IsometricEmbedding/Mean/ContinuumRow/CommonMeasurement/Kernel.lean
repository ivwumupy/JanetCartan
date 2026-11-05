module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Kernel

/-!
# Restriction of the literal carrier kernel

Multiplying the measurement cutoff in `app:ch_background:eq:bg-T` changes
neither the canonical functions nor the initial-variable measure. These identities
are used by `CommonMeasurement.Restriction` for the SAME constructed carrier.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.ContinuumRow.CommonMeasurement
variable {n N : ℕ}

/-- Multiply only the measurement field (`app:ch_background:defn:bg-row`). -/
def restrictData (d : CarrierData n N) (χ : Torus n → ℝ) : CarrierData n N :=
  { d with measurementCutoff := fun x ↦ χ x * d.measurementCutoff x }

/-- The real vector amplitude acquires the literal cutoff factor
(`app:ch_background:eq:bg-T`). -/
theorem carrierAmplitude_restrictData (d : CarrierData n N) (χ : Torus n → ℝ)
    (x : Torus n) (u : CarrierVariable n) :
    carrierAmplitude (restrictData d χ) x u = χ x • carrierAmplitude d x u := by
  simp only [carrierAmplitude, restrictData, reducedCovector, smul_smul]
  congr 1
  ring

/-- The chart indicator is retained, and no carrier measure is changed
(`app:ch_background:eq:bg-T`). -/
theorem carrierKernel_restrictData (d : CarrierData n N) (χ : Torus n → ℝ)
    (x : Torus n) (u : CarrierVariable n) :
    carrierKernel (restrictData d χ) x u = χ x • carrierKernel d x u := by
  classical
  by_cases hx : x ∈ d.outputChart
  · simp only [carrierKernel, restrictData, Set.indicator_of_mem hx]
    change Complex.exp _ • euclideanComplexInclusion
      (carrierAmplitude (restrictData d χ) x u) = _
    rw [carrierAmplitude_restrictData, map_smul, smul_comm]
    rfl
  · simp [carrierKernel, restrictData, hx]

/-- Restriction commutes with the literal initial-variable test integral,
including the total-integral convention (`app:ch_background:eq:bg-T`). -/
theorem carrierTestIntegral_restrictData (d : CarrierData n N) (χ : Torus n → ℝ)
    (f : CarrierVariable n → ℂ) (x : Torus n) :
    carrierTestIntegral (restrictData d χ) f x = χ x • carrierTestIntegral d f x := by
  simp only [carrierTestIntegral, carrierKernel_restrictData, smul_comm (f _) (χ x)]
  exact integral_smul _ _

/-- The literal adjoint moves the real cutoff onto the output test, preserving
complex conjugation and both quadratures (`app:ch_background:eq:bg-realification`). -/
theorem carrierAdjointIntegral_restrictData (d : CarrierData n N) (χ : Torus n → ℝ)
    (w : Torus n → EuclideanSpace ℂ (Fin n)) (u : CarrierVariable n) :
    carrierAdjointIntegral (restrictData d χ) w u =
      carrierAdjointIntegral d (fun x ↦ χ x • w x) u := by
  simp only [carrierAdjointIntegral, carrierKernel_restrictData,
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_left, inner_smul_real_right]

end JanetCartan.ContinuumRow.CommonMeasurement
