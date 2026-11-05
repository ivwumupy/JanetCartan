module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.Synthesis
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Continuous representatives of the uncut density

The geometric mean in `app:ch_background:eq:bg-density-twice` evaluates the
initial density at the actual footpoint. Equality almost everywhere on the
carrier/position product cannot simply be pulled back to this graph.
Weighted raw regularity gives integrable frequency slices; their inverse
integrals are continuous. A continuous representative of the same density
therefore agrees at almost every carrier and EVERY initial position. The
measured integral is unchanged, pointwise in its physical argument.

Constructing the smooth representative and its bounds from the actual
all-order adjoint is a separate obligation. These results do not assume a
mean cancellation or introduce a spatial cutoff.
-/

@[expose] public noncomputable section

open MeasureTheory Filter FourierTransform
open scoped Topology

namespace JanetCartan.PositiveBackground

open ContinuumRow CarrierSobolev RawCutoffBounds UncutDensity ContinuumAdjoint.DensityMultiplier

variable {n N : ℕ}

/-- An integrable frequency slice has a continuous literal real synthesis,
with the original radian convention (`app:ch_background:eq:bg-density-four`). -/
theorem continuous_initialDensity_slice (d : CarrierData n N) (c : ℝ)
    (f : CarrierVariable n → ℂ) (z : CarrierParameter)
    (hf : Integrable (fun η ↦ carrierDensitySymbol d (z, η) * f (z, η))) :
    Continuous (fun y ↦ initialDensity d c f (z, y)) := by
  have hfourier : Continuous (𝓕⁻ (fun η ↦ carrierDensitySymbol d (z, η) * f (z, η))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (-innerSL ℝ).continuous₂ hf
  simp only [initialDensity, radianInverseIntegral_eq_fourierInv]
  exact continuous_const.mul (Complex.continuous_re.comp
    (hfourier.comp (continuous_id.const_smul ((2 * Real.pi)⁻¹ : ℝ))))

/-- Upgrade product almost-everywhere equality to equality for every initial
position at almost every carrier. Weighted raw regularity supplies slice
integrability (`app:ch_background:eq:bg-density-twice`). -/
theorem initialDensity_eq_continuousRepresentative (d : CarrierData n N)
    (s : ℕ) (hs : n - 1 < 2 * s)
    (hρm : Measurable (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hhm : Measurable d.highCutoff) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hρ : ∀ z η, |d.angularCutoff z η| ≤ A)
    (hhi : ∀ r, |d.highCutoff r| ≤ B)
    (c : ℝ) (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f)
    {v : CarrierVariable n → ℝ} (hv : Continuous v)
    (heq : initialDensity d c f =ᵐ[carrierMeasure n] v) :
    ∀ᵐ z ∂(volume.prod volume : Measure CarrierParameter),
      ∀ y, initialDensity d c f (z, y) = v (z, y) := by
  have hslices := integrable_slice_of_weighted_density s hs
    (memLp_weighted_densitySymbol d s hρm hhm hA hB hρ hhi f hf)
  filter_upwards [hslices, Measure.ae_ae_of_ae_prod heq] with z hz he
  exact congrFun (MeasureTheory.Measure.eq_of_ae_eq he (continuous_initialDensity_slice d c f z hz)
    (hv.comp (continuous_const.prodMk continuous_id)))

/-- Replacing uncut synthesis by a continuous representative preserves the
actual mean integral at every physical point, including evaluation at its
original footpoint (`app:ch_background:eq:bg-density-twice`). -/
theorem measuredIncrement_continuousRepresentative (d : CarrierData n N)
    (s : ℕ) (hs : n - 1 < 2 * s)
    (hρm : Measurable (fun p : CarrierVariable n ↦ (d.angularCutoff p.1 p.2 : ℂ)))
    (hhm : Measurable d.highCutoff) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hρ : ∀ z η, |d.angularCutoff z η| ≤ A)
    (hhi : ∀ r, |d.highCutoff r| ≤ B)
    (c : ℝ) (f : CarrierL2 n) (hf : CarrierWeightedMem (etaBesselWeight (s + 1)) f)
    {v : CarrierVariable n → ℝ} (hv : Continuous v)
    (heq : initialDensity d c f =ᵐ[carrierMeasure n] v) (ψ : CarrierParameter → ℝ) :
    measuredIncrement d ψ (initialDensity d c f) = measuredIncrement d ψ v := by
  funext x
  apply congrArg (fun w : Torus n → Euclidean n ↦ d.outputChart.indicator w x)
  funext x
  apply integral_congr_ae
  filter_upwards [initialDensity_eq_continuousRepresentative d s hs hρm hhm
    hA hB hρ hhi c f hf hv heq] with z hz
  rw [hz]

/-- The external carrier plateau product also passes to a continuous
representative pointwise, without any cutoff in the initial position
(`app:ch_background:eq:bg-density-twice`). -/
theorem externalWeight_mul_continuousRepresentative (d : CarrierData n N)
    (χ : CarrierParameter → ℝ) (hχc : Continuous χ)
    (hχ : ∀ z η, d.angularCutoff z η ≠ 0 → χ z = 1)
    (c : ℝ) (f : CarrierVariable n → ℂ)
    {v : CarrierVariable n → ℝ} (hv : Continuous v)
    (heq : initialDensity d c f =ᵐ[carrierMeasure n] v) :
    ∀ p, χ p.1 ^ 2 * v p = v p := by
  let : (carrierMeasure n).IsOpenPosMeasure := by
    unfold carrierMeasure
    infer_instance
  have hae : (fun p : CarrierVariable n ↦ χ p.1 ^ 2 * v p) =ᵐ[carrierMeasure n] v := by
    filter_upwards [heq] with p hp
    rw [← hp]
    exact externalWeight_mul_initialDensity d χ hχ c f p
  exact congrFun (Measure.eq_of_ae_eq hae ((hχc.comp continuous_fst).pow 2 |>.mul hv) hv)

end JanetCartan.PositiveBackground
