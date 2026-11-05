module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSlices.FiniteBand
public import JanetCartan.Analysis.Operator.RealQuadratures
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Real output compression under the carrier integral

The prefix assembly of `app:ch_waves:eq:sampling-prefix-normal` needs the real
compression in `app:ch_background:eq:bg-realification` to commute with a Bochner
integral of complex output operators. The operator-valued integrability input
is retained explicitly; it must come from single-band disintegration.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumRow.CarrierPrefixes

/-- Real output compression as a bounded real-linear map of operator spaces,
for the integral step in `app:ch_background:eq:bg-realification`. -/
def realOutputCompressionCLM (n : ℕ) :
    (ComplexOutputL2 n →L[ℂ] ComplexOutputL2 n) →L[ℝ]
      (OutputL2 n →L[ℝ] OutputL2 n) :=
  LinearMap.mkContinuous
    { toFun := realOutputCompression
      map_add' := by
        intro A B
        ext x
        simp [realOutputCompression]
      map_smul' := by
        intro c A
        ext x
        simp [realOutputCompression] }
    1 (fun A ↦ by simpa using realOutputCompression_norm_le A)

/-- The bounded map is exactly the existing compression, with no change of
output space (`app:ch_background:eq:bg-realification`). -/
@[simp] theorem realOutputCompressionCLM_apply (n : ℕ)
    (A : ComplexOutputL2 n →L[ℂ] ComplexOutputL2 n) :
    realOutputCompressionCLM n A = realOutputCompression A := rfl

/-- The real compression of an integrable carrier normal is integrable,
as required by `app:ch_waves:eq:sampling-prefix-normal`. -/
theorem integrable_realOutputCompression {n : ℕ}
    {F : CarrierParameter → ComplexOutputL2 n →L[ℂ] ComplexOutputL2 n}
    (hF : Integrable F (volume.prod volume)) :
    Integrable (fun z ↦ realOutputCompression (F z)) (volume.prod volume) :=
  (realOutputCompressionCLM n).integrable_comp hF

/-- Real output compression commutes with the literal carrier Lebesgue integral
(`app:ch_background:eq:bg-realification`). -/
theorem realOutputCompression_integral {n : ℕ}
    {F : CarrierParameter → ComplexOutputL2 n →L[ℂ] ComplexOutputL2 n}
    (hF : Integrable F (volume.prod volume)) :
    realOutputCompression (∫ z, F z ∂volume.prod volume) =
      ∫ z, realOutputCompression (F z) ∂volume.prod volume :=
  ((realOutputCompressionCLM n).integral_comp_comm hF).symm

end JanetCartan.ContinuumRow.CarrierPrefixes
