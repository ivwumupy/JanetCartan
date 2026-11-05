module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Spaces
public import JanetCartan.Analysis.Fourier.SeparatedSampling.Geometry
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Literal carrier coordinates for sampling

The parameter `z = (s,v)` of `app:ch_background:eq:bg-T` and the three
coordinates of `app:ch_waves:eq:sampling-prefix-normal` have the same Lebesgue
measure. The equivalences below identify only these parameter coordinates;
they do not change the initial Fourier variable or use a transported measure.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.ContinuumRow

/-- The measurable coordinate identification `z = (s,v₀,v₁)` used in
`app:ch_waves:eq:sampling-prefix-normal`. -/
def carrierSamplingEquiv : CarrierParameter ≃ᵐ SeparatedSampling.Point :=
  ((MeasurableEquiv.refl ℝ).prodCongr
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm).trans
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm

/-- Explicit coordinate formula for `app:ch_waves:eq:sampling-prefix-normal`. -/
theorem carrierSamplingEquiv_apply (z : CarrierParameter) :
    carrierSamplingEquiv z = Fin.cons z.1 (fun i ↦ z.2 i) := by
  simp only [carrierSamplingEquiv, MeasurableEquiv.trans_apply,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  change Fin.insertNth (α := fun _ : Fin 3 ↦ ℝ) 0 z.1 (fun i ↦ z.2 i) = _
  simp only [Fin.insertNth_zero]
  rfl

/-- The same identification is real linear (`app:ch_background:eq:bg-T`). -/
def carrierSamplingLinearEquiv : CarrierParameter ≃ₗ[ℝ] SeparatedSampling.Point where
  toEquiv := carrierSamplingEquiv.toEquiv
  map_add' z w := by
    change carrierSamplingEquiv (z + w) = carrierSamplingEquiv z + carrierSamplingEquiv w
    simp only [carrierSamplingEquiv_apply]
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  map_smul' c z := by
    change carrierSamplingEquiv (c • z) = c • carrierSamplingEquiv z
    simp only [carrierSamplingEquiv_apply]
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp

/-- Product Lebesgue measure on `(s,v)` is exactly the sampling Lebesgue
measure, with no normalization factor (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem carrierSamplingEquiv_measurePreserving :
    MeasurePreserving carrierSamplingEquiv (volume.prod volume) volume :=
  ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 ↦ ℝ) 0).symm).comp
    ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_ofLp (Fin 2)))

/-- Literal pushforward identity for `app:ch_waves:eq:sampling-prefix-normal`. -/
theorem map_carrierSamplingEquiv_volume :
    Measure.map carrierSamplingEquiv (volume.prod volume) = volume :=
  carrierSamplingEquiv_measurePreserving.map_eq

/-- Change of carrier coordinates in a Bochner integral
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integral_carrierSamplingEquiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : SeparatedSampling.Point → E) :
    (∫ z, f (carrierSamplingEquiv z) ∂volume.prod volume) = ∫ z, f z :=
  carrierSamplingEquiv_measurePreserving.integral_comp' f

/-- Coordinate identification on the full initial space, fixing `η`
(`app:ch_background:eq:bg-T`). -/
def carrierVariableSamplingEquiv (n : ℕ) :
    CarrierVariable n ≃ᵐ SeparatedSampling.Point × Euclidean (n - 1) :=
  carrierSamplingEquiv.prodCongr (MeasurableEquiv.refl _)

/-- The entire initial product measure is preserved in sampling coordinates
(`app:ch_background:eq:bg-T`, `app:ch_waves:eq:sampling-prefix-normal`). -/
theorem carrierVariableSamplingEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (carrierVariableSamplingEquiv n) (carrierMeasure n)
      (volume.prod volume) :=
  carrierSamplingEquiv_measurePreserving.prod (MeasurePreserving.id volume)

end JanetCartan.ContinuumRow
