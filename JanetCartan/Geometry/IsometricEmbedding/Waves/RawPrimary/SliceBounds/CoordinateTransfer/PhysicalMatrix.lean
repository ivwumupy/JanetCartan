module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.CoordinateTransfer.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.CoordinateTransfer.Components

/-!
# From full slice components to physical Frobenius matrix fields

The output transfer for `exists_rawSliceBandOperator` is an actual complex
L² isometry equivalence. It changes neither the constant nor the integral in
`app:ch_waves:eq:individual-raw-slice`, and preserves both real quadratures.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceBounds
open ActualCarriers.FrozenPhaseReference SingleChannel

variable {n : ℕ} {ξ : Euclidean n} (a : AdaptedSection ξ) (m : ℕ)

/-- The full product-Lebesgue Euclidean-component slice output, identified
with physical Euclidean-Lebesgue Frobenius matrix L²
(`app:ch_waves:eq:individual-raw-slice`). -/
def physicalMatrixL2Equiv :
    Lp (EuclideanSpace ℂ (Fin (m * n))) 2
        (volume : Measure (ℝ × Euclidean (n - 1))) ≃ₗᵢ[ℂ]
      Lp (Matrix (Fin m) (Fin n) ℂ) 2 (volume : Measure (Euclidean n)) :=
  (adaptedL2Equiv a (EuclideanSpace ℂ (Fin (m * n)))).trans
    (matrixChannelL2Equiv volume m n).symm

/-- Forward representative of the combined coordinate/component transfer
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem physicalMatrixL2Equiv_coeFn
    (f : Lp (EuclideanSpace ℂ (Fin (m * n))) 2
      (volume : Measure (ℝ × Euclidean (n - 1)))) :
    physicalMatrixL2Equiv a m f =ᵐ[volume]
      fun x ↦ (matrixChannelEquiv m n).symm (f ((adaptedPhysicalCoordinates a).symm x)) := by
  filter_upwards [matrixChannelL2Equiv_symm_coeFn volume
      (adaptedL2Equiv a (EuclideanSpace ℂ (Fin (m * n))) f),
    adaptedL2Equiv_coeFn a (EuclideanSpace ℂ (Fin (m * n))) f] with x hx hy
  exact hx.trans (congrArg (matrixChannelEquiv m n).symm hy)

/-- Reverse representative of the same equivalence
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem physicalMatrixL2Equiv_symm_coeFn
    (f : Lp (Matrix (Fin m) (Fin n) ℂ) 2 (volume : Measure (Euclidean n))) :
    (physicalMatrixL2Equiv a m).symm f =ᵐ[volume]
      fun q ↦ matrixChannelComponents (f (adaptedPhysicalCoordinates a q)) := by
  filter_upwards [adaptedL2Equiv_symm_coeFn a (EuclideanSpace ℂ (Fin (m * n)))
      (matrixChannelL2Equiv volume m n f),
    (adaptedPhysicalCoordinates_measurePreserving a).quasiMeasurePreserving.ae
      (matrixChannelL2Equiv_coeFn volume f)] with q hq hr
  exact hq.trans hr

/-- The transfer loses no L² norm and no complex quadrature
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem norm_physicalMatrixL2Equiv
    (f : Lp (EuclideanSpace ℂ (Fin (m * n))) 2
      (volume : Measure (ℝ × Euclidean (n - 1)))) :
    ‖physicalMatrixL2Equiv a m f‖ = ‖f‖ :=
  (physicalMatrixL2Equiv a m).norm_map f

/-- An integral representative in the slice theorem becomes the SAME physical
matrix integral. The premise records that representative only; no operator
bound is assumed in this transfer (`app:ch_waves:eq:individual-raw-slice`). -/
theorem physicalMatrixL2Equiv_integral_coeFn
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (k : (ℝ × Euclidean (n - 1)) → α → Matrix (Fin m) (Fin n) ℂ)
    (f : Lp (EuclideanSpace ℂ (Fin (m * n))) 2
      (volume : Measure (ℝ × Euclidean (n - 1))))
    (hf : f =ᵐ[volume] fun q ↦ ∫ z, matrixChannelComponents (k q z) ∂μ) :
    physicalMatrixL2Equiv a m f =ᵐ[volume]
      fun x ↦ ∫ z, k ((adaptedPhysicalCoordinates a).symm x) z ∂μ := by
  filter_upwards [physicalMatrixL2Equiv_coeFn a m f,
    (adaptedPhysicalCoordinates_symm_measurePreserving a).quasiMeasurePreserving.ae hf] with x hx hf'
  rw [hx, hf', integral_matrixChannelComponents]
  exact (matrixChannelEquiv m n).symm_apply_apply _

end JanetCartan.RawPrimary.SliceBounds
