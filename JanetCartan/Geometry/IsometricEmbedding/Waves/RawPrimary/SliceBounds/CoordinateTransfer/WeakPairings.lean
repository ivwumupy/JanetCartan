module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.CoordinateTransfer.PhysicalMatrix
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.CoordinateTransfer.Derivatives

/-!
# Physical matrix weak pairings from slice components

These identities let the parent of `app:ch_waves:eq:individual-raw-slice`
transfer its actual slice weak jets to physical Frobenius matrix fields.
The coordinate and component integrals commute with no analytic premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceBounds
open ActualCarriers.FrozenPhaseReference SingleChannel

variable {n : ℕ} {ξ : Euclidean n} (a : AdaptedSection ξ) (m : ℕ)

/-- Test pairings for the actual physical matrix field equal the reassembled
slice-component pairings (`app:ch_waves:eq:individual-raw-slice`). -/
theorem integral_smul_physicalMatrixL2Equiv
    (u : Lp (EuclideanSpace ℂ (Fin (m * n))) 2
      (volume : Measure (ℝ × Euclidean (n - 1))))
    (φ : Euclidean n → ℂ) :
    ∫ x, φ x • physicalMatrixL2Equiv a m u x =
      (matrixChannelEquiv m n).symm
        (∫ q, φ (adaptedPhysicalCoordinates a q) • u q) := by
  calc
    _ = ∫ x, (matrixChannelEquiv m n).symm
        (φ x • adaptedL2Equiv a (EuclideanSpace ℂ (Fin (m * n))) u x) := by
      apply integral_congr_ae
      filter_upwards [matrixChannelL2Equiv_symm_coeFn volume
        (adaptedL2Equiv a (EuclideanSpace ℂ (Fin (m * n))) u)] with x hx
      change φ x • ((matrixChannelL2Equiv volume m n).symm
        (adaptedL2Equiv a (EuclideanSpace ℂ (Fin (m * n))) u)) x = _
      rw [hx, map_smul]
    _ = (matrixChannelEquiv m n).symm
        (∫ x, φ x • adaptedL2Equiv a (EuclideanSpace ℂ (Fin (m * n))) u x) :=
      integral_matrixChannelEquiv_symm volume _
    _ = _ := by rw [integral_smul_adaptedL2Equiv]

/-- The physical directional weak pairing is obtained from the actual
slice direction and the same Frobenius reassembly
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem integral_fderiv_smul_physicalMatrixL2Equiv
    (u : Lp (EuclideanSpace ℂ (Fin (m * n))) 2
      (volume : Measure (ℝ × Euclidean (n - 1))))
    (φ : Euclidean n → ℂ) (v : Euclidean n) :
    ∫ x, fderiv ℝ φ x v • physicalMatrixL2Equiv a m u x =
      (matrixChannelEquiv m n).symm
        (∫ q, fderiv ℝ (φ ∘ adaptedPhysicalCoordinates a) q
          ((adaptedPhysicalCoordinates a).symm v) • u q) := by
  rw [integral_smul_physicalMatrixL2Equiv]
  simp only [fderiv_adaptedPhysicalCoordinates_direction]

end JanetCartan.RawPrimary.SliceBounds
