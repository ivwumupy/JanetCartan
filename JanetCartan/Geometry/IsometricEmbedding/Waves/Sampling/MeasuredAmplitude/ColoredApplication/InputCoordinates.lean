module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.CanonicalInputCoordinates
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColoredApplication.WeightedEndpoint

/-!
# The literal carrier pullback for the patch multiplier

The input of the retained normal is the original `(s,θ)` insertion. Its
carrier is exactly `(s,v)` with fixed spectator `v`. This supplies the affine
map used by `exists_patch_powTwo_prefix_transport_bound`, with no hypothesis
on the shape of `UniformNormalGeometry.D`
(`app:ch_waves:eq:colored-normal-comparison`).
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
open ContinuumRow MeanNormalBound.NormalizedFullPhase

/-- The slice coordinate of the actual full input, inserted into the original
three-dimensional carrier. The spectators are supplied by an affine offset
in `app:ch_waves:eq:colored-normal-comparison`. -/
def retainedCarrierProjection (m : ℕ) : Euclidean (m + 1) →L[ℝ] SeparatedSampling.Point :=
  (LinearMap.toContinuousLinearMap carrierSamplingLinearEquiv.toLinearMap).comp
    ((PiLp.proj 2 (fun _ : Fin (m + 1) ↦ ℝ) 0).prod
      (0 : Euclidean (m + 1) →L[ℝ] Euclidean 2))

/-- The affine multiplier pullback keeps the SAME slice and spectator
coordinates as the measured kernel (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem retainedCarrierProjection_affine (m : ℕ) (v : Euclidean 2)
    (u : ℝ × Euclidean m) :
    carrierSamplingEquiv (0, v) + retainedCarrierProjection m (fullInputCoordinates m u) =
      carrierSamplingEquiv (u.1, v) := by
  change carrierSamplingEquiv (0, v) +
    carrierSamplingEquiv ((fullInputCoordinates m u) 0, 0) = _
  rw [fullInputCoordinates_apply]
  change carrierSamplingEquiv (0, v) + carrierSamplingEquiv (u.1, 0) = _
  simp only [carrierSamplingEquiv_apply]
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

end JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
