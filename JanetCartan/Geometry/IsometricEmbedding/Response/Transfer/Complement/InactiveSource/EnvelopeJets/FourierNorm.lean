module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Fourier

/-!
# The vector envelope's actual weighted Fourier norm

The coordinate definition of `MemVectorFourierSobolev` is identified with the
weighted Fourier representative in the original Euclidean Lebesgue L² space.
The norm equality supplies the Sobolev embedding used for the inactive source
in `app:ch_response:thm:response-literal-transfer`; it introduces no change of
measure or dimension-dependent norm comparison.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open JanetCartan.Pseudodifferential

namespace JanetCartan.ResponseTransfer.Complement.InactiveSource

variable {d r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "VL2" => Lp F 2 (volume : Measure E)

private theorem weighted_vectorFourier_coordinate_ae (s : ℝ) (f : VL2) (i : Fin r) :
    (fun ξ ↦ (euclideanSobolevWeight s ξ • (𝓕 f : VL2) ξ) i) =ᵐ[volume]
      weightedL2Fourier s (finiteL2CoordinateIsometry volume f i) := by
  filter_upwards [finiteL2Coordinates_apply_ae volume (𝓕 f) i] with ξ hi
  change (finiteL2CoordinateIsometry volume (𝓕 f) i) ξ = _ at hi
  rw [coordinate_fourier] at hi
  change euclideanSobolevWeight s ξ • (𝓕 f : VL2) ξ i =
    euclideanSobolevWeight s ξ • (𝓕 (finiteL2CoordinateIsometry volume f i)) ξ
  rw [hi]

/-- The actual weighted vector Fourier representative is in L² whenever the
envelope belongs to `MemVectorFourierSobolev`. This supplies the moment
integrability input to the inactive-source embedding in
`app:ch_response:thm:response-literal-transfer`. -/
theorem memLp_weighted_vectorFourier (s : ℝ) (f : VL2)
    (hf : MemVectorFourierSobolev s f) :
    MemLp (fun ξ ↦ euclideanSobolevWeight s ξ • (𝓕 f : VL2) ξ) 2 volume := by
  apply MemLp.of_eval_piLp
  intro i
  exact (hf i).ae_eq (weighted_vectorFourier_coordinate_ae s f i).symm

/-- Exact equality between the actual weighted Fourier L² norm and the
coordinate-based `vectorFourierSobolevNorm`. The consumer is the envelope jet
bound for `app:ch_response:thm:response-literal-transfer`. -/
theorem eLpNorm_weighted_vectorFourier (s : ℝ) (f : VL2)
    (hf : MemVectorFourierSobolev s f) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ξ • (𝓕 f : VL2) ξ) 2 volume).toReal =
      vectorFourierSobolevNorm s f := by
  let g := fun ξ ↦ euclideanSobolevWeight s ξ • (𝓕 f : VL2) ξ
  have hg : MemLp g 2 volume := memLp_weighted_vectorFourier s f hf
  have hcoord (i : Fin r) :
      ‖finiteL2CoordinateIsometry volume (hg.toLp g) i‖ =
        fourierSobolevNorm s (finiteL2CoordinateIsometry volume f i) := by
    rw [finiteL2CoordinateIsometry_toLp]
    change ‖(hg.eval_piLp i).toLp (fun ξ ↦ g ξ i)‖ = _
    rw [Lp.norm_toLp, eLpNorm_congr_ae (weighted_vectorFourier_coordinate_ae s f i)]
    rfl
  have hsq : ‖hg.toLp g‖ ^ 2 = vectorFourierSobolevNorm s f ^ 2 := by
    rw [← (finiteL2CoordinateIsometry volume).norm_map (hg.toLp g),
      PiLp.norm_sq_eq_of_L2, vectorFourierSobolevNorm, matrixFourierSobolevNorm_sq]
    exact Finset.sum_congr rfl (fun i _ ↦ congrArg (fun t : ℝ ↦ t ^ 2) (hcoord i))
  rw [← Lp.norm_toLp _ hg]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end JanetCartan.ResponseTransfer.Complement.InactiveSource
