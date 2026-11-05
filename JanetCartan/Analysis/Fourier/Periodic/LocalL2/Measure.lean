module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Periodization.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Lebesgue measure in the auxiliary torus chart

The measure comparison used in `app:ch_background:defn:bg-row` and Step 1 of
`app:ch_background:prop:bg-frame`. The centered half-open cell is used to choose
unique representatives. Its measure is literal Euclidean Lebesgue measure;
there is no frequency normalization factor.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace JanetCartan.PeriodicLocalL2

open AmplitudeBound

variable {n : ℕ}

/-- The half-open version of `fundamentalCell`, for the measure comparison in
`app:ch_background:prop:bg-frame`, Step 1. -/
def halfOpenCell (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, x i ∈ Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)}

/-- The chart cell is Lebesgue measurable (`app:ch_background:prop:bg-frame`). -/
theorem measurableSet_halfOpenCell : MeasurableSet (halfOpenCell n) :=
  (MeasurableSet.univ_pi' fun _ : Fin n ↦
    measurableSet_Ico (a := -(1 / 2 : ℝ)) (b := -(1 / 2 : ℝ) + 1)).preimage
      (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).measurable

/-- The chosen cell lies in the project's closed fundamental cell
(`app:ch_background:prop:bg-frame`). -/
theorem halfOpenCell_subset_fundamentalCell : halfOpenCell n ⊆ fundamentalCell n := by
  intro x hx i
  exact ⟨(hx i).1, by linarith [(hx i).2]⟩

/-- The centered representative belongs to the half-open cell
(`app:ch_background:prop:bg-frame`). -/
theorem representative_mem_halfOpenCell (z : Torus n) :
    centeredTorusRepresentative z ∈ halfOpenCell n :=
  fun i ↦ (AddCircle.equivIco (1 : ℝ) (-(1 / 2 : ℝ)) (z i)).property

/-- Centered representatives invert the quotient on the half-open cell
(`app:ch_background:prop:bg-frame`). -/
theorem centeredTorusRepresentative_quotient {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ halfOpenCell n) : centeredTorusRepresentative (torusQuotient x) = x := by
  ext i
  exact congrArg Subtype.val (AddCircle.equivIco_coe_eq (hx i))

/-- The quotient carries unit-cell Lebesgue measure to normalized torus Haar
measure (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem measurePreserving_quotient :
    MeasurePreserving (@torusQuotient n) (volume.restrict (halfOpenCell n)) volume := by
  have hcircle : MeasurePreserving (fun x : ℝ ↦ (x : AddCircle (1 : ℝ)))
      (volume.restrict (Ico (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1))) volume := by
    rw [Measure.restrict_congr_set (Ico_ae_eq_Ioc' (measure_singleton _)
      (measure_singleton _))]
    exact AddCircle.measurePreserving_mk 1 _
  have hp := measurePreserving_pi _ _ (fun _ : Fin n ↦ hcircle)
  rw [← Measure.restrict_pi_pi] at hp
  have he := (PiLp.volume_preserving_ofLp (Fin n)).restrict_preimage
    (MeasurableSet.univ_pi' fun _ : Fin n ↦
      measurableSet_Ico (a := -(1 / 2 : ℝ)) (b := -(1 / 2 : ℝ) + 1))
  simp only [Set.pi, mem_univ, forall_const] at hp
  exact hp.comp he

/-- Centered representatives carry Haar measure back to restricted Euclidean
Lebesgue measure (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem measurePreserving_representative :
    MeasurePreserving (centeredTorusRepresentative (n := n)) volume
      (volume.restrict (halfOpenCell n)) := by
  refine ⟨measurable_centeredTorusRepresentative, ?_⟩
  rw [← measurePreserving_quotient.map_eq,
    Measure.map_map measurable_centeredTorusRepresentative measurePreserving_quotient.measurable]
  calc
    Measure.map (centeredTorusRepresentative ∘ torusQuotient)
        (volume.restrict (halfOpenCell n)) =
        Measure.map id (volume.restrict (halfOpenCell n)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem measurableSet_halfOpenCell] with x hx
      exact centeredTorusRepresentative_quotient hx
    _ = _ := Measure.map_id

/-- The representative is a measurable embedding, allowing exact integral
comparison without additional regularity (`app:ch_background:prop:bg-frame`). -/
theorem measurableEmbedding_representative :
    MeasurableEmbedding (centeredTorusRepresentative (n := n)) :=
  measurable_centeredTorusRepresentative.measurableEmbedding
    (Function.LeftInverse.injective torusQuotient_centeredTorusRepresentative)

/-- Exact torus-to-cell integration (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_representative {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : EuclideanSpace ℝ (Fin n) → F) :
    (∫ z : Torus n, f (centeredTorusRepresentative z)) = ∫ x in halfOpenCell n, f x :=
  measurePreserving_representative.integral_comp measurableEmbedding_representative f

/-- Integrating a periodic lift only over one cell preserves the integral
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem integral_periodicLift {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Torus n → F) : (∫ x in halfOpenCell n, periodicLift f x) = ∫ z, f z := by
  rw [← integral_representative]
  simp only [periodicLift, Function.comp_apply, torusQuotient_centeredTorusRepresentative]

/-- Exact lower-integral comparison for the chart representative
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem lintegral_representative (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :
    (∫⁻ z : Torus n, f (centeredTorusRepresentative z)) = ∫⁻ x in halfOpenCell n, f x :=
  measurePreserving_representative.lintegral_comp_emb measurableEmbedding_representative f

/-- The normalized torus corresponds to a unit-volume Euclidean cell
(`app:ch_background:prop:bg-frame`, Step 1). -/
theorem volume_halfOpenCell : volume (halfOpenCell n) = 1 := by
  have h := (measurePreserving_representative (n := n)).measure_preimage MeasurableSet.univ
  calc
    volume (halfOpenCell n) = (volume.restrict (halfOpenCell n)) univ := by simp
    _ = volume (centeredTorusRepresentative ⁻¹' (univ : Set (EuclideanSpace ℝ (Fin n)))) := h.symm
    _ = 1 := by simp [Measure.pi_univ, volume_pi, AddCircle.measure_univ]

end JanetCartan.PeriodicLocalL2
