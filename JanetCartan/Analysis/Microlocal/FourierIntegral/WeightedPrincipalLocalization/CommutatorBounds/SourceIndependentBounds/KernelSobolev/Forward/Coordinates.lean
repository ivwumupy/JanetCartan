module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.OperatorLimit
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.MatrixComposition.Schwartz
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Extension.SchwartzDensity

/-!
# Fourier coordinates for the forward frequency-kernel estimate

The weighted integral in Steps 1 and 3 of
`app:ch_regular_base:thm:actual-calculus` takes values in the Euclidean
fiber. These identities connect its literal Fourier representative to the
existing coordinate definition of `MemVectorFourierSobolev`, with no norm
loss. The consumer is `exists_frequencyKernel_forward_sobolev_constant`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open JanetCartan.Pseudodifferential
open JanetCartan.FourierIntegral.LowBounds.FrequencyCutoff

namespace JanetCartan.FourierIntegral.WeightedPrincipalLocalization.SourceIndependentBounds

variable {n r : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "L²" => Lp V 2 (volume : Measure E)
local notation "Q" => finiteL2CoordinateIsometry (I := Fin r) (volume : Measure E)

/-- Scalar coordinates of the actual Schwartz inclusion, for the input
norm in `app:ch_regular_base:eq:fio-input`. -/
theorem frequencyKernel_coordinates_schwartz (u : SchwartzMap E (Fin r → ℂ))
    (i : Fin r) :
    Q (schwartzVectorToLp u) i = (matrixSchwartzCoordinates u i).toLp 2 := by
  apply Lp.ext
  filter_upwards [finiteL2Coordinates_apply_ae volume (schwartzVectorToLp u) i,
    schwartzVectorToLp_ae u, (matrixSchwartzCoordinates u i).coeFn_toLp 2] with x hx hu hi
  exact hx.trans ((congrArg (fun v : V ↦ v i) hu).trans hi.symm)

/-- The Fourier transform of the actual Schwartz inclusion is its literal
Schwartz Fourier transform, for `app:ch_regular_base:eq:fio-input`. -/
theorem frequencyKernel_fourier_schwartz (u : SchwartzMap E (Fin r → ℂ)) :
    𝓕 (schwartzVectorToLp u) = schwartzVectorToLp (𝓕 u) := by
  simp only [schwartzVectorToLp_eq_toEuclideanSchwartz_toLp,
    toEuclideanSchwartz_fourier, SchwartzMap.toLp_fourier_eq]

/-- Fourier transformation commutes with the existing finite L² coordinates.
This identifies the output of the literal frequency integral with the
Sobolev norm in `app:ch_regular_base:eq:fio-input`. -/
theorem frequencyKernel_coordinates_fourier (f : L²) (i : Fin r) :
    Q (𝓕 f) i = 𝓕 (Q f i) := by
  have hc : Continuous (fun f : L² ↦ Q (𝓕 f) i) :=
    (PiLp.proj (𝕜 := ℂ) 2 _ i).continuous.comp
      ((Q).continuous.comp (fourierCLM ℂ L²).continuous)
  have hd : Continuous (fun f : L² ↦ 𝓕 (Q f i)) :=
    (fourierCLM ℂ (Lp ℂ 2 (volume : Measure E))).continuous.comp
      ((PiLp.proj (𝕜 := ℂ) 2 _ i).continuous.comp (Q).continuous)
  apply congrFun (denseRange_graphTestToLp.equalizer hc hd ?_) f
  funext u
  change Q (𝓕 (graphTestToLp u)) i = 𝓕 (Q (graphTestToLp u) i)
  rw [← schwartzVectorToLp_graphTestToSchwartz u, frequencyKernel_fourier_schwartz,
    frequencyKernel_coordinates_schwartz, frequencyKernel_coordinates_schwartz,
    SchwartzMap.toLp_fourier_eq]
  congr 1
  apply SchwartzMap.ext
  intro ξ
  exact (fourier_matrixSchwartzCoordinates _ ξ i).symm

/-- The scalar Fourier representatives agree almost everywhere with the
coordinates of the vector Fourier representative. Source:
`app:ch_regular_base:eq:fio-input`. -/
theorem frequencyKernel_fourier_coordinate_ae (f : L²) (i : Fin r) :
    (𝓕 (Q f i) : Lp ℂ 2 (volume : Measure E)) =ᵐ[volume]
      fun ξ ↦ (𝓕 f : L²) ξ i := by
  rw [← frequencyKernel_coordinates_fourier]
  exact finiteL2Coordinates_apply_ae volume (𝓕 f) i

/-- Weighted scalar Fourier representatives are the coordinates of the
weighted vector Fourier representative in `app:ch_regular_base:eq:fio-input`. -/
theorem frequencyKernel_weighted_coordinate_ae (s : ℝ) (f : L²) (i : Fin r) :
    weightedL2Fourier s (Q f i) =ᵐ[volume]
      fun ξ ↦ (euclideanSobolevWeight s ξ • (𝓕 f : L²) ξ) i := by
  filter_upwards [frequencyKernel_fourier_coordinate_ae f i] with ξ hξ
  simp only [weightedL2Fourier, hξ, PiLp.smul_apply]

/-- Sobolev membership is exactly L² membership of the weighted vector
Fourier representative. This is the membership conversion needed after the
weighted integral estimate in `app:ch_regular_base:eq:fio-input`. -/
theorem frequencyKernel_memLp_weighted_fourier_iff (s : ℝ) (f : L²) :
    MemLp (fun ξ ↦ euclideanSobolevWeight s ξ • (𝓕 f : L²) ξ) 2 volume ↔
      MemVectorFourierSobolev s f := by
  constructor
  · intro h i
    exact MemLp.ae_eq (frequencyKernel_weighted_coordinate_ae s f i).symm (h.eval_piLp i)
  · intro h
    exact MemLp.of_eval_piLp (fun i ↦
      MemLp.ae_eq (frequencyKernel_weighted_coordinate_ae s f i) (h i))

/-- The weighted vector L² norm equals the existing Hilbert Sobolev norm,
with no fiber factor. This converts the forward weighted integral estimate
to `app:ch_regular_base:eq:fio-input`. -/
theorem frequencyKernel_eLpNorm_weighted_fourier (s : ℝ) (f : L²)
    (hf : MemVectorFourierSobolev s f) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ξ • (𝓕 f : L²) ξ) 2 volume).toReal =
      vectorFourierSobolevNorm s f := by
  let w := fun ξ ↦ euclideanSobolevWeight s ξ • (𝓕 f : L²) ξ
  have hw : MemLp w 2 volume := (frequencyKernel_memLp_weighted_fourier_iff s f).mpr hf
  have hfi (i : Fin r) : MemLp (weightedL2Fourier s (Q f i)) 2 volume := hf i
  have hcoord (i : Fin r) : Q (hw.toLp w) i =
      (hfi i).toLp (weightedL2Fourier s (Q f i)) := by
    apply Lp.ext
    filter_upwards [finiteL2Coordinates_apply_ae volume (hw.toLp w) i,
      hw.coeFn_toLp, (hfi i).coeFn_toLp,
      frequencyKernel_weighted_coordinate_ae s f i] with ξ h₁ h₂ h₃ h₄
    exact h₁.trans ((congrArg (fun v : V ↦ v i) h₂).trans (h₄.symm.trans h₃.symm))
  rw [← Lp.norm_toLp w hw, ← (Q).norm_map]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  change _ = matrixFourierSobolevNorm s (Q f) ^ 2
  rw [matrixFourierSobolevNorm_sq]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcoord, Lp.norm_toLp]
  rfl

/-- Actual vector Schwartz inputs have all Fourier Sobolev orders. This
supplies input membership in the frequency integral proof of
`app:ch_regular_base:eq:fio-input`. -/
theorem frequencyKernel_schwartz_memSobolev (s : ℝ)
    (u : SchwartzMap E (Fin r → ℂ)) :
    MemVectorFourierSobolev s (schwartzVectorToLp u) := by
  intro i
  change MemFourierSobolev s (Q (schwartzVectorToLp u) i)
  rw [frequencyKernel_coordinates_schwartz]
  exact memFourierSobolev_schwartz s _

/-- The literal Schwartz Fourier integral has precisely the Sobolev input
norm used in `app:ch_regular_base:eq:fio-input`. At order zero this is
Plancherel with the original Euclidean volume. -/
theorem frequencyKernel_eLpNorm_schwartz_fourier (s : ℝ)
    (u : SchwartzMap E (Fin r → ℂ)) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ξ •
      (WithLp.toLp 2 ((𝓕 u) ξ) : V)) 2 volume).toReal =
        vectorFourierSobolevNorm s (schwartzVectorToLp u) := by
  have he : (fun ξ ↦ euclideanSobolevWeight s ξ •
      (𝓕 (schwartzVectorToLp u) : L²) ξ) =ᵐ[volume]
      fun ξ ↦ euclideanSobolevWeight s ξ • (WithLp.toLp 2 ((𝓕 u) ξ) : V) := by
    rw [frequencyKernel_fourier_schwartz]
    filter_upwards [schwartzVectorToLp_ae (𝓕 u)] with ξ hξ
    rw [hξ]
  rw [← eLpNorm_congr_ae he]
  exact frequencyKernel_eLpNorm_weighted_fourier s _ (frequencyKernel_schwartz_memSobolev s u)

end JanetCartan.FourierIntegral.WeightedPrincipalLocalization.SourceIndependentBounds
