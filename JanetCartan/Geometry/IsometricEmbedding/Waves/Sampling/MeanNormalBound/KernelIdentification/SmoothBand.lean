module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.Reassembly

/-!
# Removal of sharp indicators after wide-band reassembly

The primitive amplitude matching here says exactly that the original smooth
`radialBand` occurs in the measured amplitude. RawPrimary's full/leading-wave
construction must supply this equality for the same `BandKernelData`.
It implies that the reassembled forward kernel has no sharp indicator, as
required before the smooth calculus in `app:ch_waves:eq:sampling-operator-bounds`.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.Sampling.MeanNormalBound
open SamplingKernelBounds RawInputPartition

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {n : ℕ}

omit [FirstCountableTopology P] [LocallyCompactSpace P] in
/-- The actual smooth radial factor supplies wide-band support of the physical
kernel, without differentiating a sharp restriction
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem bandKernel_eq_zero_off_wideBand (D : BandKernelData P n) (j : ℕ) (z : P)
    (a : Euclidean (n - 1) → Euclidean n → EuclideanSpace ℂ (Fin n))
    (ha : ∀ η x, D.amplitude ((z, η), x) = (radialBand n j η : ℂ) • a η x)
    {η : Euclidean (n - 1)} (hη : η ∉ wideBand n j) (x : Euclidean n) :
    D.kernel z η x = 0 := by
  simp [BandKernelData.kernel, bandKernel, ha, radialBand_eq_zero_off_wideBand hη]

omit [FirstCountableTopology P] [LocallyCompactSpace P] in
/-- Support of the actual L²-valued columns is derived from the primitive
smooth radial factor (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem bandColumn_eq_zero_off_wideBand (D : BandKernelData P n) (j : ℕ) (z : P)
    (a : Euclidean (n - 1) → Euclidean n → EuclideanSpace ℂ (Fin n))
    (ha : ∀ η x, D.amplitude ((z, η), x) = (radialBand n j η : ℂ) • a η x)
    {η : Euclidean (n - 1)} (hη : η ∉ wideBand n j) : D.column z η = 0 := by
  apply Lp.ext
  filter_upwards [D.column_coe z η,
    Lp.coeFn_zero (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n))]
    with x hx hzero
  rw [hx, bandKernel_eq_zero_off_wideBand D j z a ha hη, hzero]
  rfl

/-- After both sharp pieces are reassembled, the forward integral is the
original globally supported smooth-band kernel, with no shell indicator.
This is the input to full-phase normalization
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem wideBandKernelOperator_apply_of_radialBand (D : BandKernelData P n) (j : ℕ) (z : P)
    (a : Euclidean (n - 1) → Euclidean n → EuclideanSpace ℂ (Fin n))
    (ha : ∀ η x, D.amplitude ((z, η), x) = (radialBand n j η : ℂ) • a η x)
    (f : WideBandL2 n j) :
    wideBandKernelOperator D j z f = ∫ η, f η • D.column z η := by
  rw [wideBandKernelOperator_apply]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro η hη
  rw [bandColumn_eq_zero_off_wideBand D j z a ha hη, smul_zero]

end JanetCartan.Sampling.MeanNormalBound
