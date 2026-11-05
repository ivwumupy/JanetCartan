module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.IntegralSum

/-!
# One original band in the raw slice input

The all-`K` raw slice estimate is applied at `K = 2^j` to a datum supported in
its original `j`th component. This keeps the lower bands at their own scale,
including those below the amplitude scale, and introduces no sharp multiplier
into smooth calculus. The consumer is the actual sampling channel bound in
`app:ch_waves:eq:sampling-operator-bounds`.
-/

@[expose] public noncomputable section
open MeasureTheory

namespace JanetCartan.Sampling.MeasuredAmplitude
open RawInputPartition RawPrimary.SliceBounds

/-- The literal density of a single wide-band datum, on the original
Lebesgue measure (`app:ch_waves:eq:individual-raw-slice`). -/
theorem weightedWideDensity_single_ae {n J : ℕ}
    {d : Euclidean (n - 1) → ℂ} {M : ℝ} (hd : Measurable d)
    (hb : ∀ η, ‖d η‖ ≤ M) (j : Fin J) (f : WideBandL2 n j.val) :
    weightedWideDensity d (PiLp.single 2 j f) =ᵐ[volume]
      fun η ↦ (Real.sqrt ‖η‖ : ℂ) * weightedRadialBand d j.val η * f η := by
  classical
  have he : weightedWideSynthesis hd hb (PiLp.single 2 j f) =
      wideChannel (measurable_weightedRadialBand hd j.val).aestronglyMeasurable
        (Filter.Eventually.of_forall (norm_weightedRadialBand_le hb j.val)) f := by
    simp only [weightedWideSynthesis, wideSynthesis_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      change (wideChannel (n := n) (j := i.val)
        (measurable_weightedRadialBand hd i.val).aestronglyMeasurable
        (Filter.Eventually.of_forall (norm_weightedRadialBand_le hb i.val)))
          ((Pi.single j f : (k : Fin J) → WideBandL2 n k.val) i) = 0
      rw [Pi.single_eq_of_ne hij, map_zero]
    · simp
  refine (weightedWideSynthesis_coeFn hd hb (PiLp.single 2 j f)).symm.trans ?_
  rw [he]
  exact wideChannel_coeFn_of_support
    (measurable_weightedRadialBand hd j.val).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_weightedRadialBand_le hb j.val))
    (fun η hη ↦ weightedRadialBand_eq_zero_off_wideBand d hη) f

/-- The original smooth-band integral is the raw integral of the single
datum, including its half derivative and detector. The equality needs no
integrability premise (`app:ch_waves:eq:individual-raw-slice`). -/
theorem rawSliceBandIntegral_eq_singleDensity {n J : ℕ} {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E]
    (S : X → Euclidean (n - 1) → ℝ) (A : X → Euclidean (n - 1) → E)
    (χ : X → ℝ) (ζ : Euclidean (n - 1)) (τ : ℝ)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ} (hd : Measurable d)
    (hb : ∀ η, ‖d η‖ ≤ M) (j : Fin J) (f : WideBandL2 n j.val) (x : X) :
    rawSliceBandIntegral S A χ ζ τ (weightedRadialBand d j.val) j.val f x =
      (χ x : ℂ) • rawPrimaryDemodulatedIntegral S A ζ τ volume
        (weightedWideDensity d (PiLp.single 2 j f)) x := by
  unfold rawSliceBandIntegral rawPrimaryDemodulatedIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [weightedWideDensity_single_ae hd hb j f] with η hη
  rw [hη]

end JanetCartan.Sampling.MeasuredAmplitude
